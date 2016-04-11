use std;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use llvm_sys::prelude::*;
use llvm_sys::core::*;
use ty::{self, Type, TypeVariant, TypeContext};

const START_BLOCK: Block = Block(0);
const END_BLOCK: Block = Block(1);

#[derive(Debug)]
pub struct Function<'t> {
    ty: ty::Function<'t>,
    temporaries: Vec<Type<'t>>,
    locals: Vec<Type<'t>>,
    blocks: Vec<BlockData<'t>>,
}
#[derive(Copy, Clone, Debug)]
pub struct Variable(u32);
#[derive(Copy, Clone, Debug)]
struct Temporary(u32);
#[derive(Copy, Clone, Debug)]
struct Parameter(u32);

impl<'t> Function<'t> {
    pub fn new(ty: ty::Function<'t>) -> Self {
        let mut ret = Function {
            ty: ty,
            temporaries: Vec::new(),
            locals: Vec::new(),
            blocks: Vec::new(),
        };
        assert_eq!(START_BLOCK,
            ret.new_block(Lvalue::Return, Terminator::Goto(END_BLOCK)));
        assert_eq!(END_BLOCK,
            ret.new_block(Lvalue::Return, Terminator::Return));
        let input_types = ret.ty.input().to_owned();
        {
            for ty in &input_types {
                ret.new_local(*ty);
            }
            let blk = ret.get_block(&mut START_BLOCK);
            for i in 0..input_types.len() as u32 {
                blk.statements.push(Statement(Lvalue::Variable(Variable(i)),
                    Value::leaf(ValueLeaf::Parameter(Parameter(i)))))
            }
        }
        END_BLOCK.terminate(&mut ret, Terminator::Return);
        ret
    }

    pub fn start_block(&self) -> Block {
        START_BLOCK
    }

    fn new_block(&mut self, expr: Lvalue, term: Terminator<'t>) -> Block {
        self.blocks.push(BlockData::new(expr, term));
        Block(self.blocks.len() - 1)
    }
    fn new_tmp(&mut self, ty: Type<'t>) -> Temporary {
        self.temporaries.push(ty);
        Temporary(self.temporaries.len() as u32 - 1)
    }
    pub fn new_local(&mut self, ty: Type<'t>) -> Variable {
        self.locals.push(ty);
        Variable(self.locals.len() as u32 - 1)
    }
    pub fn get_param(&mut self, n: u32) -> Variable {
        assert!(n < self.ty.input().len() as u32);
        Variable(n)
    }

    fn get_block(&mut self, blk: &mut Block) -> &mut BlockData<'t> {
        &mut self.blocks[blk.0 as usize]
    }
    fn get_tmp_ty(&self, tmp: &Temporary) -> Type<'t> {
        self.temporaries[tmp.0 as usize]
    }
    fn get_par_ty(&self, par: &Parameter) -> Type<'t> {
        self.ty.input()[par.0 as usize]
    }
    fn get_local_ty(&self, var: &Variable) -> Type<'t> {
        self.locals[var.0 as usize]
    }

    fn get_leaf(&mut self, value: Value<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> ValueLeaf<'t> {
        if let ValueKind::Leaf(leaf) = value.0 {
            leaf
        } else {
            let ty = value.ty(self, fn_types, ctxt);
            let tmp = self.new_tmp(ty);
            block.add_stmt(Lvalue::Temporary(tmp), value, self);
            ValueLeaf::Temporary(tmp)
        }
    }

    fn build(self, llfunc: LLVMValueRef,
             llvm_funcs: &HashMap<String, LLVMValueRef>,
             ctxt: &'t TypeContext<'t>) {
        LlFunction::build(self, llfunc, llvm_funcs, ctxt)
    }
}

struct LlFunction<'t> {
    mir: Function<'t>,
    raw: LLVMValueRef,
    builder: LLVMBuilderRef,
    ret_ptr: LLVMValueRef,
    temporaries: Vec<LLVMValueRef>,
    locals: Vec<LLVMValueRef>,
    blocks: Vec<LLVMBasicBlockRef>,
}

impl<'t> LlFunction<'t> {
    fn build(mir: Function<'t>, llfunc: LLVMValueRef,
            llvm_funcs: &HashMap<String, LLVMValueRef>,
            ctxt: &'t TypeContext<'t>) {
        unsafe {
            let builder = LLVMCreateBuilder();
            let mut blocks = Vec::new();
            for i in 0..mir.blocks.len() {
                blocks.push(LLVMAppendBasicBlock(llfunc,
                    CString::new(format!("bb{}", i)).unwrap().as_ptr()));
            }

            LLVMPositionBuilderAtEnd(builder, blocks[0]);

            let mut tmps = Vec::new();
            for mir_tmp in &mir.temporaries {
                tmps.push(LLVMBuildAlloca(builder, mir_tmp.to_llvm(),
                    cstr!("tmp")));
            }
            let mut locals = Vec::new();
            for mir_local in &mir.locals {
                locals.push(LLVMBuildAlloca(builder, mir_local.to_llvm(),
                    cstr!("var")));
            }

            let ret_ptr = LLVMBuildAlloca(builder, mir.ty.output().to_llvm(),
                cstr!("ret"));

            let mut self_ = LlFunction {
                mir: mir,
                raw: llfunc,
                builder: builder,
                ret_ptr: ret_ptr,
                temporaries: tmps,
                locals: locals,
                blocks: blocks,
            };

            let mut i = self_.mir.blocks.len();
            while let Some(blk) = self_.mir.blocks.pop() {
                i -= 1;
                LLVMPositionBuilderAtEnd(self_.builder, self_.blocks[i]);
                for stmt in blk.statements {
                    stmt.to_llvm(&mut self_, llvm_funcs, ctxt);
                }
                blk.terminator.to_llvm(&self_, ctxt);
            }
        }
    }


    fn get_tmp_ptr(&self, tmp: &Temporary) -> LLVMValueRef {
        self.temporaries[tmp.0 as usize]
    }
    fn get_tmp_value(&self, tmp: &Temporary) -> LLVMValueRef {
        unsafe {
            LLVMBuildLoad(self.builder, self.temporaries[tmp.0 as usize],
                cstr!(""))
        }
    }
    fn get_local_ptr(&self, var: &Variable) -> LLVMValueRef {
        self.locals[var.0 as usize]
    }
    fn get_local_value(&self, var: &Variable) -> LLVMValueRef {
        unsafe {
            LLVMBuildLoad(self.builder, self.locals[var.0 as usize],
                cstr!(""))
        }
    }

    fn get_block(&self, blk: &Block) -> LLVMBasicBlockRef {
        self.blocks[blk.0]
    }
}

#[derive(Clone, Debug)]
enum ValueLeaf<'t> {
    ConstInt {
        value: u64,
        ty: Type<'t>,
    },
    ConstBool(bool),
    ConstUnit,
    Parameter(Parameter),
    Variable(Variable),
    Temporary(Temporary),
}

impl<'t> ValueLeaf<'t> {
    fn ty(&self, function: &Function<'t>, ctxt: &'t TypeContext<'t>)
            -> Type<'t> {
        match *self {
            ValueLeaf::ConstInt {
                ty,
                ..
            } => ty,
            ValueLeaf::ConstBool(_) => Type::bool(ctxt),
            ValueLeaf::ConstUnit => Type::unit(ctxt),
            ValueLeaf::Temporary(ref tmp) => function.get_tmp_ty(tmp),
            ValueLeaf::Parameter(ref par) => function.get_par_ty(par),
            ValueLeaf::Variable(ref var) => function.get_local_ty(var),
        }
    }

    unsafe fn to_llvm(self, function: &LlFunction<'t>,
            ctxt: &'t TypeContext<'t>)
            -> LLVMValueRef {
        match self {
            ValueLeaf::ConstInt {
                value,
                ty,
            } => {
                LLVMConstInt(ty.to_llvm(), value, false as LLVMBool)
            }
            ValueLeaf::ConstBool(value) => {
                LLVMConstInt(Type::bool(ctxt).to_llvm(), value as u64,
                    false as LLVMBool)
            }
            ValueLeaf::ConstUnit => {
                LLVMConstStruct([].as_mut_ptr(), 0, false as LLVMBool)
            }
            ValueLeaf::Temporary(tmp) => {
                function.get_tmp_value(&tmp)
            }
            ValueLeaf::Parameter(par) => {
                LLVMGetParam(function.raw, par.0 as u32)
            }
            ValueLeaf::Variable(var) => {
                function.get_local_value(&var)
            }
        }
    }
}

#[derive(Clone, Debug)]
enum ValueKind<'t> {
    Leaf(ValueLeaf<'t>),

    // -- unops --
    Pos(ValueLeaf<'t>),
    Neg(ValueLeaf<'t>),
    Not(ValueLeaf<'t>),

    Ref(ValueLeaf<'t>),

    // -- binops --
    Add(ValueLeaf<'t>, ValueLeaf<'t>),
    Sub(ValueLeaf<'t>, ValueLeaf<'t>),
    Mul(ValueLeaf<'t>, ValueLeaf<'t>),
    Div(ValueLeaf<'t>, ValueLeaf<'t>),
    Rem(ValueLeaf<'t>, ValueLeaf<'t>),
    And(ValueLeaf<'t>, ValueLeaf<'t>),
    Xor(ValueLeaf<'t>, ValueLeaf<'t>),
    Or(ValueLeaf<'t>, ValueLeaf<'t>),
    Shl(ValueLeaf<'t>, ValueLeaf<'t>),
    Shr(ValueLeaf<'t>, ValueLeaf<'t>),

    // -- comparison --
    Eq(ValueLeaf<'t>, ValueLeaf<'t>),
    Neq(ValueLeaf<'t>, ValueLeaf<'t>),
    Lt(ValueLeaf<'t>, ValueLeaf<'t>),
    Lte(ValueLeaf<'t>, ValueLeaf<'t>),
    Gt(ValueLeaf<'t>, ValueLeaf<'t>),
    Gte(ValueLeaf<'t>, ValueLeaf<'t>),

    // -- other --
    Call {
        callee: String,
        args: Vec<ValueLeaf<'t>>,
    },
}

#[derive(Clone, Debug)]
pub struct Value<'t>(ValueKind<'t>);

// --- CONSTRUCTORS ---
impl<'t> Value<'t> {
    // -- leaves --
    #[inline(always)]
    pub fn const_int(value: u64, ty: Type<'t>) -> Self {
        Value::leaf(
            ValueLeaf::ConstInt {
                value: value,
                ty: ty,
            }
        )
    }
    #[inline(always)]
    pub fn const_bool(value: bool) -> Self {
        Value::leaf(ValueLeaf::ConstBool(value))
    }
    #[inline(always)]
    pub fn const_unit() -> Value<'t> {
        Value::leaf(ValueLeaf::ConstUnit)
    }

    pub fn param(arg_num: u32, function: &mut Function) -> Self {
        assert!(arg_num < function.ty.input().len() as u32);
        Value::leaf(ValueLeaf::Variable(Variable(arg_num)))
    }

    pub fn local(var: Variable) -> Self {
        Value::leaf(ValueLeaf::Variable(var))
    }


    #[inline(always)]
    fn leaf(leaf: ValueLeaf<'t>) -> Self {
        Value(ValueKind::Leaf(leaf))
    }

    // -- unops --
    pub fn pos(inner: Self, function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Pos(function.get_leaf(inner, block, fn_types, ctxt)))
    }
    pub fn neg(inner: Self, function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Neg(function.get_leaf(inner, block, fn_types, ctxt)))
    }
    pub fn not(inner: Self, function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Not(function.get_leaf(inner, block, fn_types, ctxt)))
    }
    pub fn ref_(inner: Self, function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        let inner_ty = inner.ty(function, fn_types, ctxt);
        let ptr = function.new_tmp(Type::ref_(inner_ty));
        block.write_ref(Lvalue::Temporary(ptr), inner, function, fn_types,
            ctxt);
        Value::leaf(ValueLeaf::Temporary(ptr))
    }

    // -- binops --
    pub fn add(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Add(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn sub(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Sub(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn mul(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Mul(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn div(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Div(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn rem(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Rem(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn and(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::And(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn xor(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Xor(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn or(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Or(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn shl(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Shl(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn shr(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Shr(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }

    // -- comparisons --
    pub fn eq(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Eq(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn neq(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Neq(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn lt(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Lt(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn lte(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Lte(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn gt(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>)
            -> Self {
        Value(ValueKind::Gt(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }
    pub fn gte(lhs: Self, rhs: Self, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Value(ValueKind::Gte(
            function.get_leaf(lhs, block, fn_types, ctxt),
            function.get_leaf(rhs, block, fn_types, ctxt)))
    }

    // -- misc --
    pub fn call(callee: String, args: Vec<Self>, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        let args =
            args.into_iter().map(|v|
                function.get_leaf(v, block, fn_types, ctxt)).collect();
        Value(ValueKind::Call {
            callee: callee,
            args: args,
        })
    }
}

impl<'t> Value<'t> {
    fn ty(&self, function: &Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) -> Type<'t> {
        match self.0 {
            ValueKind::Leaf(ref v) => v.ty(function, ctxt),

            ValueKind::Pos(ref inner) | ValueKind::Neg(ref inner)
            | ValueKind::Not(ref inner) => inner.ty(function, ctxt),

            ValueKind::Ref(ref inner) => Type::ref_(inner.ty(function, ctxt)),

            ValueKind::Add(ref lhs, ref rhs)
            | ValueKind::Sub(ref lhs, ref rhs)
            | ValueKind::Mul(ref lhs, ref rhs)
            | ValueKind::Div(ref lhs, ref rhs)
            | ValueKind::Rem(ref lhs, ref rhs)
            | ValueKind::And(ref lhs, ref rhs)
            | ValueKind::Xor(ref lhs, ref rhs)
            | ValueKind::Or(ref lhs, ref rhs)
            => {
                let lhs_ty = lhs.ty(function, ctxt);
                assert_eq!(lhs_ty, rhs.ty(function, ctxt));
                lhs_ty
            }

            ValueKind::Shl(ref lhs, _)
            | ValueKind::Shr(ref lhs, _)
            => {
                lhs.ty(function, ctxt)
            }

            ValueKind::Eq(_, _) | ValueKind::Neq(_, _) | ValueKind::Lt(_, _)
            | ValueKind::Lte(_, _) | ValueKind::Gt(_, _) | ValueKind::Gte(_, _)
                => Type::bool(ctxt),

            ValueKind::Call {
                ref callee,
                ..
            } =>  {
                fn_types.get(callee).expect("ICE: no function prototype")
                    .output()
            }
        }
    }

    unsafe fn to_llvm(self, function: &mut LlFunction<'t>,
            llvm_funcs: &HashMap<String, LLVMValueRef>,
            ctxt: &'t TypeContext<'t>) -> LLVMValueRef {
        use llvm_sys::LLVMIntPredicate::*;
        match self.0 {
            ValueKind::Leaf(v) => {
                v.to_llvm(function, ctxt)
            }
            ValueKind::Pos(inner) => {
                let ty = inner.ty(&function.mir, ctxt);
                let llinner = inner.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) => llinner,
                    _ => panic!("ICE: {} can't be used in unary +", ty),
                }
            }
            ValueKind::Neg(inner) => {
                // TODO: check types
                let ty = inner.ty(&function.mir, ctxt);
                let llinner = inner.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) =>
                        LLVMBuildNeg(function.builder, llinner, cstr!("")),
                    _ => panic!("ICE: {} can't be used in unary -", ty),
                }
            }
            ValueKind::Not(inner) => {
                let ty = inner.ty(&function.mir, ctxt);
                let llinner = inner.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        LLVMBuildNot(function.builder, llinner, cstr!("")),
                    _ => panic!("ICE: {} can't be used in unary !", ty),
                }
            }
            ValueKind::Ref(inner) => {
                match inner {
                    ValueLeaf::Variable(v) => function.get_local_ptr(&v),
                    ValueLeaf::Temporary(t) => function.get_tmp_ptr(&t),
                    ValueLeaf::Parameter(_) =>
                        panic!("Attempted to take reference of parameter"),
                    _ => panic!("Attempted to take reference of const"),
                }
            }
            ValueKind::Add(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) =>
                        LLVMBuildAdd(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary +", ty),
                }
            }
            ValueKind::Sub(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) =>
                        LLVMBuildSub(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary -", ty),
                }
            }
            ValueKind::Mul(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) =>
                        LLVMBuildMul(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary *", ty),
                }
            }
            ValueKind::Div(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) =>
                        LLVMBuildSDiv(function.builder, lhs, rhs, cstr!("")),
                    TypeVariant::UInt(_) =>
                        LLVMBuildUDiv(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary /", ty),
                }
            }
            ValueKind::Rem(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) =>
                        LLVMBuildSRem(function.builder, lhs, rhs, cstr!("")),
                    TypeVariant::UInt(_) =>
                        LLVMBuildURem(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::And(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        LLVMBuildAnd(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Xor(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        LLVMBuildXor(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Or(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        LLVMBuildOr(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Shl(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) =>
                        LLVMBuildShl(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Shr(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) =>
                        LLVMBuildAShr(function.builder, lhs, rhs, cstr!("")),
                    TypeVariant::UInt(_) =>
                        LLVMBuildLShr(function.builder, lhs, rhs, cstr!("")),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Eq(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntEQ,
                            lhs, rhs, cstr!("")),
                    _ =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Neq(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntNE,
                            lhs, rhs, cstr!("")),
                    _ =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Lt(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) =>
                        LLVMBuildICmp(function.builder, LLVMIntSLT,
                            lhs, rhs, cstr!("")),
                    TypeVariant::UInt(_) | TypeVariant::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntULT,
                            lhs, rhs, cstr!("")),
                    _ =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Lte(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) =>
                        LLVMBuildICmp(function.builder, LLVMIntSLE,
                            lhs, rhs, cstr!("")),
                    TypeVariant::UInt(_) | TypeVariant::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntULE,
                            lhs, rhs, cstr!("")),
                    _ =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Gt(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) =>
                        LLVMBuildICmp(function.builder, LLVMIntSGT,
                            lhs, rhs, cstr!("")),
                    TypeVariant::UInt(_) | TypeVariant::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntUGT,
                            lhs, rhs, cstr!("")),
                    _ =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Gte(lhs, rhs) => {
                let ty = lhs.ty(&function.mir, ctxt);
                let lhs = lhs.to_llvm(function, ctxt);
                let rhs = rhs.to_llvm(function, ctxt);
                match *ty.variant {
                    TypeVariant::SInt(_) =>
                        LLVMBuildICmp(function.builder, LLVMIntSGE,
                            lhs, rhs, cstr!("")),
                    TypeVariant::UInt(_) | TypeVariant::Bool =>
                        LLVMBuildICmp(function.builder, LLVMIntUGE,
                            lhs, rhs, cstr!("")),
                    _ =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Call {
                callee,
                args,
            } => {
                let mut args = args.into_iter().map(|a|
                    a.to_llvm(function, ctxt)).collect::<Vec<_>>();
                let callee = *llvm_funcs.get(&callee).unwrap();
                LLVMBuildCall(function.builder, callee, args.as_mut_ptr(),
                    args.len() as u32, cstr!(""))
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum Lvalue {
    Variable(Variable),
    Temporary(Temporary),
    Return,
}

#[derive(Debug)]
struct Statement<'t>(Lvalue, Value<'t>);

impl<'t> Statement<'t> {
    unsafe fn to_llvm(self, function: &mut LlFunction<'t>,
            llvm_funcs: &HashMap<String, LLVMValueRef>,
            ctxt: &'t TypeContext<'t>) {
        let dst = match self.0 {
            Lvalue::Return => function.ret_ptr,
            Lvalue::Temporary(tmp) => function.get_tmp_ptr(&tmp),
            Lvalue::Variable(var) => function.get_local_ptr(&var),
        };
        LLVMBuildStore(function.builder,
            (self.1).to_llvm(function, llvm_funcs, ctxt), dst);
    }
}

#[derive(Debug)]
enum Terminator<'t> {
    Goto(Block),
    If {
        cond: ValueLeaf<'t>,
        then_blk: Block,
        else_blk: Block,
    },
    // Normal return; should only happen in the end block
    Return,
}

impl<'t> Terminator<'t> {
    unsafe fn to_llvm(self, function: &LlFunction<'t>,
            ctxt: &'t TypeContext<'t>) {
        match self {
            Terminator::Goto(mut b) => {
                LLVMBuildBr(function.builder, function.get_block(&mut b));
            },
            Terminator::If {
                cond,
                mut then_blk,
                mut else_blk,
            } => {
                let cond = cond.to_llvm(function, ctxt);
                LLVMBuildCondBr(function.builder, cond,
                    function.get_block(&mut then_blk),
                    function.get_block(&mut else_blk));
            }
            Terminator::Return => {
                match *function.mir.ty.output().variant {
                    TypeVariant::Unit => {
                        LLVMBuildRetVoid(function.builder);
                    },
                    _ => {
                        let value = LLVMBuildLoad(function.builder,
                            function.ret_ptr, cstr!(""));
                        LLVMBuildRet(function.builder, value);
                    }
                }
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Block(usize);

impl Block {
    pub fn write_to_var<'t>(&mut self, var: Variable, val: Value<'t>,
            function: &mut Function<'t>) {
        self.add_stmt(Lvalue::Variable(var), val, function)
    }

    pub fn write_to_tmp<'t>(&mut self, val: Value<'t>,
            function: &mut Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) {
        let ty = val.ty(function, fn_types, ctxt);
        let tmp = function.new_tmp(ty);
        self.add_stmt(Lvalue::Temporary(tmp), val, function)
    }

    fn write_ref<'t>(&mut self, ptr: Lvalue, val: Value<'t>,
            function: &mut Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>) {
        let leaf = function.get_leaf(val, self, fn_types, ctxt);
        self.add_stmt(ptr, Value(ValueKind::Ref(leaf)), function);
    }

    fn add_stmt<'t>(&mut self, lvalue: Lvalue, value: Value<'t>,
            function: &mut Function<'t>) {
        let blk = function.get_block(self);
        blk.statements.push(Statement(lvalue, value))
    }
}
// terminators
impl Block {
    pub fn if_else<'t>(mut self, ty: Type<'t>, cond: Value<'t>,
            function: &mut Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>)
            -> (Block, Block, Block, Value<'t>) {
        let cond = function.get_leaf(cond, &mut self, fn_types, ctxt);
        let tmp = function.new_tmp(ty);

        let mut then = function.new_block(Lvalue::Temporary(tmp),
            Terminator::Goto(Block(0)));
        let mut else_ = function.new_block(Lvalue::Temporary(tmp),
            Terminator::Goto(Block(0)));
        // terminator is not permanent

        let (expr, term) = {
            let blk = function.get_block(&mut self);
            let term = std::mem::replace(&mut blk.terminator,
                Terminator::If {
                    cond: cond,
                    then_blk: Block(then.0),
                    else_blk: Block(else_.0)
                });
            (blk.expr, term)
        };
        let join = function.new_block(expr, term);

        {
            let then_blk = function.get_block(&mut then);
            then_blk.terminator = Terminator::Goto(Block(join.0));
        }
        {
            let else_blk = function.get_block(&mut else_);
            else_blk.terminator = Terminator::Goto(Block(join.0));
        }

        (then, else_, join, Value(ValueKind::Leaf(ValueLeaf::Temporary(tmp))))
    }

    pub fn early_ret<'t>(mut self, function: &mut Function<'t>,
            value: Value<'t>) {
        let blk = function.get_block(&mut self);
        blk.statements.push(Statement(Lvalue::Return, value));
        blk.terminator = Terminator::Goto(END_BLOCK);
    }

    pub fn finish<'t>(mut self, function: &mut Function<'t>,
            value: Value<'t>) {
        let blk = function.get_block(&mut self);
        blk.statements.push(Statement(blk.expr, value));
    }

    fn terminate<'t>(&mut self, function: &mut Function<'t>,
            terminator: Terminator<'t>) {
        let blk = function.get_block(self);
        blk.terminator = terminator;
    }
}

#[derive(Debug)]
struct BlockData<'t> {
    expr: Lvalue,
    statements: Vec<Statement<'t>>,
    terminator: Terminator<'t>,
}

impl<'t> BlockData<'t> {
    fn new(expr: Lvalue, term: Terminator<'t>) -> BlockData<'t> {
        BlockData {
            expr: expr,
            statements: Vec::new(),
            terminator: term,
        }
    }
}

pub struct Mir<'t> {
    functions: HashMap<String, Function<'t>>,
    ctxt: &'t TypeContext<'t>
}

impl<'t> Mir<'t> {
    pub fn new(ctxt: &'t TypeContext<'t>) -> Mir<'t> {
        Mir {
            functions: HashMap::new(),
            ctxt: ctxt,
        }
    }

    pub fn add_function(&mut self, name: String, func: Function<'t>) {
        self.functions.insert(name, func);
    }

    pub fn build(self, print_llir: bool, opt: bool) {
        use llvm_sys::transforms::scalar::*;
        use llvm_sys::analysis::*;
        use llvm_sys::analysis::LLVMVerifierFailureAction::*;
        unsafe {
            let mut main_output = None;
            let mut llvm_functions = HashMap::new();
            let module = LLVMModuleCreateWithName(cstr!(""));

            let optimizer = LLVMCreateFunctionPassManagerForModule(module);

            // NOTE: add optimizations here
            LLVMAddBasicAliasAnalysisPass(optimizer);
            LLVMAddInstructionCombiningPass(optimizer);
            LLVMAddReassociatePass(optimizer);
            LLVMAddGVNPass(optimizer);
            LLVMAddCFGSimplificationPass(optimizer);
            LLVMAddDeadStoreEliminationPass(optimizer);

            LLVMInitializeFunctionPassManager(optimizer);

            for (name, function) in &self.functions {
                if name == "main" {
                    main_output = Some(function.ty.output());
                }
                let llfunc = LLVMAddFunction(module,
                    CString::new(name.clone()).unwrap().as_ptr(),
                    function.ty.to_llvm());
                llvm_functions.insert(name.clone(), llfunc);
            }

            for (name, function) in self.functions {
                let llfunc = *llvm_functions.get(&name).unwrap();
                function.build(llfunc, &llvm_functions, &self.ctxt);
                LLVMVerifyFunction(llfunc, LLVMAbortProcessAction);
                if opt {
                    LLVMRunFunctionPassManager(optimizer, llfunc);
                }
            }

            if let Some(f) = llvm_functions.get("main") {
                Self::run(main_output.unwrap(), module, *f, print_llir)
            }
        }
    }

    unsafe fn run(ty: Type, module: LLVMModuleRef, function: LLVMValueRef,
            print_llir: bool) {
        use llvm_sys::analysis::*;
        use llvm_sys::execution_engine::*;
        use llvm_sys::target::*;
        use std::io::Write;

        if print_llir {
            LLVMDumpModule(module);
        }

        let mut error: *mut ::libc::c_char = std::mem::uninitialized();
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
        match *ty.variant {
            TypeVariant::SInt(ty::Int::I32) => {
                let val = LLVMGenericValueToInt(res, true as LLVMBool);
                println!("{}", val as i32);
            }
            TypeVariant::UInt(ty::Int::I32) => {
                let val = LLVMGenericValueToInt(res, true as LLVMBool);
                println!("{}", val as u32);
            }
            TypeVariant::Unit => {}
            _ => {
                println!("Pink does not yet support printing the \
                    {} return type", ty);
            }
        }

        LLVMDisposeGenericValue(res);
        LLVMDisposeExecutionEngine(engine);
    }
}

impl<'t> std::fmt::Display for Function<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        for (i, var) in self.locals.iter().enumerate() {
            try!(writeln!(f, "  let var{}: {};", i, var));
        }
        for (i, tmp) in self.temporaries.iter().enumerate() {
            try!(writeln!(f, "  let tmp{}: {};", i, tmp));
        }
        for (i, block) in self.blocks.iter().enumerate() {
            try!(writeln!(f, "  bb{}: {{", i));
            for stmt in &block.statements {
                try!(writeln!(f, "    {};", stmt));
            }
            try!(writeln!(f, "    {};", block.terminator));
            try!(writeln!(f, "  }}"));
        }
        Ok(())
    }
}

impl<'t> std::fmt::Display for Terminator<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Terminator::Goto(ref b) => write!(f, "goto -> bb{}", b.0),
            Terminator::Return => write!(f, "return"),
            Terminator::If {
                ref cond,
                ref then_blk,
                ref else_blk,
            } => write!(f, "if({}) -> [true: bb{}, false: bb{}]", cond,
                then_blk.0, else_blk.0),
        }
    }
}

impl<'t> std::fmt::Display for Statement<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{} = {}", self.0, self.1)
    }
}

impl std::fmt::Display for Lvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Lvalue::Return => write!(f, "return"),
            Lvalue::Temporary(ref tmp) => write!(f, "tmp{}", tmp.0),
            Lvalue::Variable(ref var) => write!(f, "var{}", var.0),
        }
    }
}

impl<'t> std::fmt::Display for ValueLeaf<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            ValueLeaf::ConstInt {
                value,
                ty,
            } => {
                match *ty.variant {
                    TypeVariant::UInt(_) => write!(f, "const {}{}", value, ty),
                    TypeVariant::SInt(_) => write!(f, "const {}{}", value as i64, ty),
                    _ => panic!("ICE: non-integer typed integer: {}", ty),
                }
            },
            ValueLeaf::ConstBool(value) => write!(f, "const {}", value),
            ValueLeaf::ConstUnit => write!(f, "const ()"),
            ValueLeaf::Temporary(ref tmp) => write!(f, "tmp{}", tmp.0),
            ValueLeaf::Parameter(ref par) => write!(f, "arg{}", par.0),
            ValueLeaf::Variable(ref var) => write!(f, "var{}", var.0),
        }
    }
}

impl<'t> std::fmt::Display for Value<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self.0 {
            ValueKind::Leaf(ref v) => write!(f, "{}", v),
            ValueKind::Pos(ref inner) => write!(f, "Pos({})", inner),
            ValueKind::Neg(ref inner) => write!(f, "Neg({})", inner),
            ValueKind::Not(ref inner) => write!(f, "Not({})", inner),
            ValueKind::Ref(ref inner) => write!(f, "&{}", inner),
            ValueKind::Add(ref lhs, ref rhs)
                => write!(f, "Add({}, {})", lhs, rhs),
            ValueKind::Sub(ref lhs, ref rhs)
                => write!(f, "Sub({}, {})", lhs, rhs),
            ValueKind::Mul(ref lhs, ref rhs)
                => write!(f, "Mul({}, {})", lhs, rhs),
            ValueKind::Div(ref lhs, ref rhs)
                => write!(f, "Div({}, {})", lhs, rhs),
            ValueKind::Rem(ref lhs, ref rhs)
                => write!(f, "Rem({}, {})", lhs, rhs),
            ValueKind::And(ref lhs, ref rhs)
                => write!(f, "And({}, {})", lhs, rhs),
            ValueKind::Xor(ref lhs, ref rhs)
                => write!(f, "And({}, {})", lhs, rhs),
            ValueKind::Or(ref lhs, ref rhs)
                => write!(f, "And({}, {})", lhs, rhs),
            ValueKind::Shl(ref lhs, ref rhs)
                => write!(f, "Shl({}, {})", lhs, rhs),
            ValueKind::Shr(ref lhs, ref rhs)
                => write!(f, "Shr({}, {})", lhs, rhs),

            ValueKind::Eq(ref lhs, ref rhs)
                => write!(f, "Eq({}, {})", lhs, rhs),
            ValueKind::Neq(ref lhs, ref rhs)
                => write!(f, "Neq({}, {})", lhs, rhs),
            ValueKind::Lt(ref lhs, ref rhs)
                => write!(f, "Lt({}, {})", lhs, rhs),
            ValueKind::Lte(ref lhs, ref rhs)
                => write!(f, "Lte({}, {})", lhs, rhs),
            ValueKind::Gt(ref lhs, ref rhs)
                => write!(f, "Gt({}, {})", lhs, rhs),
            ValueKind::Gte(ref lhs, ref rhs)
                => write!(f, "Gte({}, {})", lhs, rhs),

            ValueKind::Call {
                ref callee,
                ref args,
            } => {
                try!(write!(f, "{}(", callee));
                if args.len() != 0 {
                    for arg in &args[..args.len() - 1] {
                        try!(write!(f, "{}, ", arg));
                    }
                    try!(write!(f, "{}", args[args.len() - 1]));
                }
                write!(f, ")")
            }
        }
    }
}

impl<'t> std::fmt::Display for Mir<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        for (name, function) in &self.functions {
            try!(write!(f, "fn {}(", name));
            let inputs = function.ty.input();
            if inputs.len() != 0 {
                for input in &inputs[..inputs.len() - 1] {
                    try!(write!(f, "{}, ", input));
                }
                try!(write!(f, "{}", inputs[inputs.len() - 1]));
            }
            try!(writeln!(f, ") -> {} {{", function.ty.output()));
            try!(write!(f, "{}", function));
            try!(writeln!(f, "}}\n"));
        }
        Ok(())
    }
}
impl<'t> std::fmt::Debug for Mir<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self)
    }
}
