use std;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use llvm_sys::prelude::*;
use llvm_sys::core::*;
use ty;

const START_BLOCK: Block = Block(0);
const END_BLOCK: Block = Block(1);

#[allow(dead_code)]
pub enum Cmp {
    Eq,
    Ne,
    Lt,
    Lte,
    Gt,
    Gte,
}

#[derive(Debug)]
pub struct Function {
    ty: ty::Function,
    //locals: HashMap<String, Lvalue>,
    blocks: Vec<BlockData>,
}

impl Function {
    pub fn new(ty: ty::Function) -> Function {
        let mut ret = Function {
            ty: ty,
            blocks: Vec::new(),
        };
        assert_eq!(START_BLOCK, ret.new_block());
        assert_eq!(END_BLOCK, ret.new_block());
        END_BLOCK.terminate(&mut ret, Terminator::Return);
        ret
    }

    pub fn start_block(&self) -> Block {
        START_BLOCK
    }

    fn new_block(&mut self) -> Block {
        self.blocks.push(BlockData::new());
        Block(self.blocks.len() - 1)
    }

    fn get_block(&mut self, blk: &Block) -> &mut BlockData {
        &mut self.blocks[blk.0]
    }

    fn build(self, llfunc: LLVMValueRef,
            _functions: &HashMap<String, LLVMValueRef>) {
        unsafe {
            let builder = LLVMCreateBuilder();
            let mut llblks = Vec::new();
            for i in 0..self.blocks.len() {
                llblks.push(LLVMAppendBasicBlock(llfunc,
                    CString::new(format!("bb{}", i)).unwrap().as_ptr()));
            }

            LLVMPositionBuilderAtEnd(builder, llblks[0]);
            let ret_ptr = LLVMBuildAlloca(builder, self.ty.output().to_llvm(),
                cstr!("ret"));

            for (i, blk) in self.blocks.into_iter().enumerate() {
                LLVMPositionBuilderAtEnd(builder, llblks[i]);
                for stmt in blk.statements {
                    stmt.to_llvm(ret_ptr, builder);
                }
                blk.terminator.expect("terminator")
                    .to_llvm(ret_ptr, builder, &llblks);
            }
        }
    }
}

#[derive(Clone, Debug)]
enum ValueKind {
    ConstInt {
        value: u64,
        ty: ty::Ty,
    }
}

#[derive(Clone, Debug)]
pub struct Value(ValueKind);

impl Value {
    pub fn const_int(value: u64, ty: ty::Ty) -> Value {
        Value(ValueKind::ConstInt {
            value: value,
            ty: ty,
        })
    }
}

#[derive(Copy, Clone, Debug)]
enum Lvalue {
    Return,
}

#[derive(Debug)]
struct Statement(Lvalue, Value);

impl Statement {
    unsafe fn to_llvm(self, ret_ptr: LLVMValueRef, builder: LLVMBuilderRef) {
        let dst = match self.0 {
            Lvalue::Return => ret_ptr,
        };

        match (self.1).0 {
            ValueKind::ConstInt {
                value,
                ty,
            } => {
                LLVMBuildStore(builder, LLVMConstInt(ty.to_llvm(),
                    value, false as LLVMBool), dst);
            }
        }
    }
}

#[derive(Debug)]
enum Terminator {
    Goto(Block),
    // Normal return; should only happen in the end block
    Return,
}

impl Terminator {
    unsafe fn to_llvm(self, ret_ptr: LLVMValueRef, builder: LLVMBuilderRef,
            blocks: &[LLVMBasicBlockRef]) {
        match self {
            Terminator::Goto(Block(i)) => {
                LLVMBuildBr(builder, blocks[i]);
            },
            Terminator::Return => {
                let value = LLVMBuildLoad(builder, ret_ptr, cstr!(""));
                LLVMBuildRet(builder, value);
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Block(usize);

impl Block {
    pub fn ret(self, function: &mut Function, value: Value) {
        let blk = function.get_block(&self);
        blk.statements.push(Statement(Lvalue::Return, value));
        blk.terminator = Some(Terminator::Goto(END_BLOCK));
    }

    fn terminate(&self, function: &mut Function, terminator: Terminator) {
        let blk = function.get_block(self);
        blk.terminator = Some(terminator);
    }
}

#[derive(Debug)]
struct BlockData {
    statements: Vec<Statement>,
    terminator: Option<Terminator>,
}

impl BlockData {
    fn new() -> BlockData {
        BlockData {
            statements: Vec::new(),
            terminator: None,
        }
    }
}

#[derive(Debug)]
pub struct Mir {
    functions: HashMap<String, Function>,
}

impl Mir {
    pub fn new() -> Mir {
        Mir {
            functions: HashMap::new(),
        }
    }

    pub fn add_function(&mut self, name: String, func: Function) {
        self.functions.insert(name, func);
    }

    pub fn build(self) {
        unsafe {
            let mut main_output = None;
            let mut llvm_functions = HashMap::new();
            let module = LLVMModuleCreateWithName(cstr!(""));
            for (name, function) in self.functions {
                if name == "main" {
                    main_output = Some(function.ty.output());
                }
                let llfunc = LLVMAddFunction(module,
                    CString::new(name.clone()).unwrap().as_ptr(),
                    function.ty.to_llvm());
                llvm_functions.insert(name, llfunc);

                function.build(llfunc, &llvm_functions);
            }
            if let Some(f) = llvm_functions.get("main") {
                Self::run(main_output.unwrap(), module, *f)
            }
        }
    }

    unsafe fn run(ty: ty::Ty, module: LLVMModuleRef, function: LLVMValueRef) {
        use llvm_sys::analysis::*;
        use llvm_sys::execution_engine::*;
        use llvm_sys::target::*;
        use std::io::Write;

        LLVMDumpModule(module);

        let mut error: *mut i8 = std::mem::uninitialized();
        LLVMVerifyModule(module,
            LLVMVerifierFailureAction::LLVMAbortProcessAction, &mut error);
        LLVMDisposeMessage(error);

        println!("--- RUNNING ---");
        let mut engine: LLVMExecutionEngineRef = std::mem::uninitialized();
        error = std::ptr::null_mut();
        LLVMLinkInMCJIT();
        LLVM_InitializeNativeTarget();
        LLVM_InitializeNativeAsmPrinter();
        if LLVMCreateJITCompilerForModule(&mut engine, module,
                0, &mut error) != 0 {
            writeln!(std::io::stderr(),
                "failed to create execution engine: {:?}",
                CStr::from_ptr(error)).unwrap();
            LLVMDisposeMessage(error);
            std::process::exit(-1);
        }

        let res = LLVMRunFunction(engine, function, 0, std::ptr::null_mut());
        match ty {
            ty::Ty::SInt(ty::Int::I32) => {
                let val = LLVMGenericValueToInt(res, true as LLVMBool);
                println!("{}", val as i32);
            }
            ty::Ty::UInt(ty::Int::I32) => {
                let val = LLVMGenericValueToInt(res, true as LLVMBool);
                println!("{}", val as u32);
            }
            ty::Ty::Unit => {}
            ref ty => {
                println!("Pink does not yet support printing the \
                    {:?} return type", ty);
            }
        }

        LLVMDisposeGenericValue(res);
        LLVMDisposeExecutionEngine(engine);
    }
}

impl std::fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        for (i, block) in self.blocks.iter().enumerate() {
            try!(writeln!(f, "  bb{}: {{", i));
            for stmt in &block.statements {
                try!(writeln!(f, "    {};", stmt));
            }
            if let Some(ref t) = block.terminator {
                try!(writeln!(f, "    {};", t));
            }
            try!(writeln!(f, "  }}"));
        }
        Ok(())
    }
}

impl std::fmt::Display for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Terminator::Goto(ref b) => write!(f, "goto -> bb{}", b.0),
            Terminator::Return => write!(f, "return"),
        }
    }
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{} = {}", self.0, self.1)
    }
}

impl std::fmt::Display for Lvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Lvalue::Return => write!(f, "return"),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self.0 {
            ValueKind::ConstInt {
                value,
                ty,
            } => write!(f, "const {}{}", value, ty),
        }
    }
}

impl std::fmt::Display for Mir {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        for (name, function) in &self.functions {
            try!(writeln!(f, "fn {}(...) -> ret {{", name));
            try!(writeln!(f, "{}", function));
            try!(writeln!(f, "}}"));
        }
        Ok(())
    }
}

/*
#[derive(Debug)]
struct module {
    raw: LLVMModuleRef,
    opt: LLVMPassManagerRef,
}

impl module {
    fn new(name: &str) -> module {
        use llvm_sys::transforms::scalar::*;
        unsafe {
            let raw = LLVMModuleCreateWithName(CString::new(name)
                .expect("passed a string with a nul to module::new").as_ptr());
            let opt = LLVMCreateFunctionPassManagerForModule(raw);

            // NOTE: add optimizations here
            LLVMAddBasicAliasAnalysisPass(opt);
            LLVMAddInstructionCombiningPass(opt);
            LLVMAddReassociatePass(opt);
            LLVMAddGVNPass(opt);
            LLVMAddCFGSimplificationPass(opt);
            LLVMAddDeadStoreEliminationPass(opt);

            LLVMInitializeFunctionPassManager(opt);

            module {
                raw: raw,
                opt: opt,
            }
        }
    }

    unsafe fn add_func(&self, name: &str, ret_ty: &ty, args: &[LLVMTypeRef])
            -> LLVMValueRef {
        let ty = LLVMFunctionType(ret_ty.to_llvm_ret(),
            args.as_ptr() as *mut _, args.len() as u32, false as LLVMBool);
        LLVMAddFunction(self.raw, CString::new(name.to_owned())
            .expect("name should not have a nul in it").as_ptr(), ty)
    }

    fn optimize_function(&self, func: &function) {
        unsafe {
            LLVMVerifyFunction(func.raw, LLVMAbortProcessAction);
            LLVMRunFunctionPassManager(self.opt, func.raw);
        }
    }
}
*/

