use std;
use std::collections::HashMap;
use std::ffi::{CString, CStr};
use parse::{lexer, operand, parser, parser_error};
use ty::{ty, int, union_find};

use llvm_sys::LLVMIntPredicate::*;
use llvm_sys::execution_engine::*;
use llvm_sys::target::*;
use llvm_sys::prelude::*;
use llvm_sys::analysis::*;
use llvm_sys::analysis::LLVMVerifierFailureAction::*;
use llvm_sys::core::*;

#[derive(Debug)]
pub enum stmt {
    Let {
        name: String,
        ty: ty,
        value: Box<expr>,
    },
    Expr(expr),
}

#[derive(Debug)]
pub enum expr_kind {
    Call {
        callee: String,
        args: Vec<expr>
    },
    If {
        condition: Box<expr>,
        then_value: Box<expr>,
        else_value: Box<expr>,
    },
    Binop {
        op: operand,
        lhs: Box<expr>,
        rhs: Box<expr>,
    },
    Plus(Box<expr>), // unary plus
    Minus(Box<expr>), // unary minus
    Not(Box<expr>), // !expr
    Variable(String),
    IntLiteral(u64),
    BoolLiteral(bool),
    UnitLiteral,
    Return(Box<expr>),
}

#[derive(Debug)]
pub struct expr {
    pub kind: expr_kind,
    pub ty: ty,
}

impl expr {
    fn translate<'a>(self, function: &'a function, locals: &HashMap<String, value>,
            block: &mut block<'a>, ast: &ast) -> value {
        assert!(self.ty.is_final_type(), "{:?}", self.ty);
        match self.kind {
            expr_kind::IntLiteral(value) => {
                value::int_literal(self.ty, value)
            }
            expr_kind::BoolLiteral(b) => {
                value::bool_literal(self.ty, b)
            }
            expr_kind::UnitLiteral => {
                value::unit_literal(self.ty)
            }
            expr_kind::Variable(ref name) => {
                if let Some(val) = locals.get(name) {
                    assert!(val.ty == self.ty);
                    val.clone()
                } else {
                    value::parameter(self.ty, function, name)
                }
            }
            expr_kind::Binop {
                op: operand::OrOr,
                lhs,
                rhs,
            } => {
                expr {
                    kind: expr_kind::If {
                        condition: lhs,
                        then_value: Box::new(expr::bool_lit(true)),
                        else_value: rhs,
                    },
                    ty: self.ty,
                }.translate(function, locals, block, ast)
            }
            expr_kind::Binop {
                op: operand::AndAnd,
                lhs,
                rhs,
            } => {
                expr {
                    kind: expr_kind::If {
                        condition: Box::new(expr::not(*lhs, Some(ty::Bool))),
                        then_value: Box::new(expr::bool_lit(false)),
                        else_value: rhs,
                    },
                    ty: self.ty,
                }.translate(function, locals, block, ast)
            }
            expr_kind::Binop {
                op,
                lhs,
                rhs,
            } => {
                let lhs = lhs.translate(function, locals, block, ast);
                let rhs = rhs.translate(function, locals, block, ast);
                value::binop(&op, lhs, rhs, block.builder())
            }
            expr_kind::Plus(inner) => {
                inner.translate(function, locals, block, ast)
            }
            expr_kind::Minus(inner) => {
                inner.translate(function, locals, block, ast)
                    .neg(block.builder())
            }
            expr_kind::Not(inner) => {
                inner.translate(function, locals, block, ast)
                    .not(block.builder())
            }
            expr_kind::If {
                condition,
                then_value,
                else_value,
            } => {
                let cond = condition.translate(function, locals, block, ast);
                let res = if block.is_live() {
                    let mut then_blk = block::new(function, "then");
                    let mut else_blk = block::new(function, "else");
                    let mut join_blk = block::new(function, "join");
                    block.conditional_branch(cond, &then_blk, &else_blk);

                    let then_res = then_value.translate(function, locals, &mut then_blk, ast);
                    let then_live = if then_blk.is_live() {
                        then_blk.branch(&join_blk);
                        true
                    } else {
                        false
                    };

                    let else_res = else_value.translate(function, locals, &mut else_blk, ast);
                    let else_live = if else_blk.is_live() {
                        else_blk.branch(&join_blk);
                        true
                    } else {
                        false
                    };

                    // this is not guaranteed to be correct.
                    // I'm going to switch to a better style in the future
                    // (memory writes)
                    let then = if then_live {
                        Some((then_res, &then_blk))
                    } else {
                        None
                    };
                    let else_ = if else_live {
                        Some((else_res, &else_blk))
                    } else {
                        None
                    };
                    let res = join_blk.phi(self.ty, then, else_);
                    *block = join_blk;
                    res
                } else {
                    value::undef(self.ty)
                };
                res
            }
            expr_kind::Call {
                callee,
                args,
            } => {
                let mut llvm_args = Vec::new();
                for arg in args.into_iter() {
                    llvm_args.push(arg.translate(function, locals, block, ast));
                }
                ast.call(&callee, block.builder(), llvm_args)
            }
            expr_kind::Return(expr) => {
                let ret = expr.translate(function, locals, block, ast);
                let ty = ret.ty.clone();
                if block.is_live() {
                    block.ret(ret);
                }
                match ty {
                    ty::Infer(_) | ty::InferInt(_) => unimplemented!(),
                    ty => value::undef(ty),
                }
            }
        }
    }

    fn unify_type(&mut self, to_unify: ty, uf: &mut union_find, function: &function,
        variables: &HashMap<String, ty>, functions: &HashMap<String, function>)
            -> Result<(), ast_error> {
        self.ty.generate_inference_id(uf);
        match self.kind {
            expr_kind::IntLiteral(_) | expr_kind::BoolLiteral(_) | expr_kind::UnitLiteral => {
                uf.unify(self.ty, to_unify).map_err(|()|
                    ast_error::CouldNotUnify {
                        first: self.ty,
                        second: to_unify,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
            }
            expr_kind::Variable(ref name) => {
                if let Some(ty) = variables.get(name) {
                    self.ty = *ty;
                    uf.unify(*ty, to_unify).map_err(|()|
                        ast_error::CouldNotUnify {
                            first: *ty,
                            second: to_unify,
                            function: function.name.clone(),
                            compiler: fl!(),
                        }
                    )
                } else if let Some(&(_, ty)) = function.args.get(name) {
                    self.ty = ty;
                    uf.unify(ty, to_unify).map_err(|()|
                        ast_error::CouldNotUnify {
                            first: ty,
                            second: to_unify,
                            function: function.name.clone(),
                            compiler: fl!(),
                        }
                    )
                } else {
                    Err(ast_error::UndefinedVariableName {
                        name: name.clone(),
                        function: function.name.clone(),
                    })
                }
            }
            expr_kind::Binop {
                op,
                ref mut lhs,
                ref mut rhs,
            } => {
                match op {
                    operand::Mul | operand::Div | operand::Rem | operand::Plus
                    | operand::Minus | operand::Shl | operand::Shr | operand::And
                    | operand::Xor | operand::Or => {
                        let ty = self.ty;
                        try!(lhs.unify_type(self.ty, uf, function, variables, functions));
                        try!(rhs.unify_type(lhs.ty, uf, function, variables, functions));
                        uf.unify(self.ty, to_unify).map_err(|()|
                            ast_error::CouldNotUnify {
                                first: ty,
                                second: to_unify,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }

                    operand::EqualsEquals | operand::NotEquals | operand::LessThan
                    | operand::LessThanEquals | operand::GreaterThan
                    | operand::GreaterThanEquals => {
                        self.ty = ty::Bool;
                        rhs.ty.generate_inference_id(uf);
                        try!(lhs.unify_type(rhs.ty, uf, function, variables, functions));
                        try!(rhs.unify_type(lhs.ty, uf, function, variables, functions));
                        uf.unify(self.ty, to_unify).map_err(|()|
                            ast_error::CouldNotUnify {
                                first: ty::Bool,
                                second: to_unify,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }

                    operand::AndAnd | operand::OrOr => {
                        self.ty = ty::Bool;
                        try!(lhs.unify_type(ty::Bool, uf, function, variables, functions));
                        try!(rhs.unify_type(ty::Bool, uf, function, variables, functions));

                        uf.unify(self.ty, to_unify).map_err(|()|
                            ast_error::CouldNotUnify {
                                first: to_unify,
                                second: ty::Bool,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }

                    operand::Not => {
                        panic!("ICE: Not (`!`) is not a binop")
                    }
                }
            }
            expr_kind::Call {
                ref callee,
                ref mut args,
            } => {
                match functions.get(callee) {
                    Some(f) => {
                        if f.input.len() != args.len() {
                            return Err(ast_error::IncorrectNumberOfArguments {
                                passed: args.len(),
                                expected: f.input.len(),
                                callee: callee.clone(),
                                caller: "".to_owned(), // TODO: fix this
                            })
                        }

                        for (arg_ty, expr) in f.input.iter().zip(args) {
                           try!(expr.unify_type(*arg_ty, uf, function, variables, functions));
                        }
                        self.ty = f.output;
                        let ty = self.ty;
                        uf.unify(self.ty, to_unify).map_err(|()|
                            ast_error::CouldNotUnify {
                                first: ty,
                                second: to_unify,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }
                    None => return Err(ast_error::FunctionDoesntExist(callee.clone()))
                }
            }
            expr_kind::If {
                ref mut condition,
                ref mut then_value,
                ref mut else_value,
            } => {
                try!(condition.unify_type(ty::Bool, uf, function, variables, functions));
                try!(then_value.unify_type(to_unify, uf, function, variables, functions));
                try!(else_value.unify_type(to_unify, uf, function, variables, functions));
                let ty = self.ty;
                uf.unify(self.ty, to_unify).map_err(|()|
                    ast_error::CouldNotUnify {
                        first: ty,
                        second: to_unify,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
            }
            expr_kind::Return(ref mut ret) => {
                self.ty = ty::Diverging;
                ret.unify_type(function.output, uf, function, variables, functions)
            }
            ref ty => panic!("unimplemented: {:#?}", ty),
        }
    }

    fn finalize_type(&mut self, uf: &mut union_find, function: &function) -> Result<(), ast_error> {
        match self.kind {
            expr_kind::IntLiteral(_) | expr_kind::BoolLiteral(_) | expr_kind::UnitLiteral |
                expr_kind::Variable(_) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(ast_error::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                Ok(())
            }
            expr_kind::Binop {
                ref mut lhs,
                ref mut rhs,
                ..
            } => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(ast_error::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(lhs.finalize_type(uf, function));
                rhs.finalize_type(uf, function)
            }
            expr_kind::Call {
                ref mut args,
                ..
            } => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(ast_error::NoActualType {
                        function: function.name.clone(),
                        compiler: fl!(),
                    })
                };
                for arg in args {
                    try!(arg.finalize_type(uf, function));
                }
                Ok(())
            }
            expr_kind::If {
                ref mut condition,
                ref mut then_value,
                ref mut else_value,
            } => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(ast_error::NoActualType {
                        function: function.name.clone(),
                        compiler: fl!(),
                    })
                };
                try!(condition.finalize_type(uf, function));
                try!(then_value.finalize_type(uf, function));
                else_value.finalize_type(uf, function)
            }
            expr_kind::Return(ref mut ret) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t @ ty::Diverging) => t,
                    Some(t) => panic!("ICE: return without Diverging type: {:#?}", t),
                    None => panic!("ICE: return with no type (should be Diverging)")
                };
                ret.finalize_type(uf, function)
            }
            ref ty => panic!("unimplemented: {:#?}", ty),
        }
    }

    pub fn call(callee: String, args: Vec<expr>, ty: Option<ty>) -> expr {
        expr {
            kind: expr_kind::Call {
                callee: callee,
                args: args,
            },
            ty: ty.unwrap_or(ty::Infer(None)),
        }
    }

    pub fn var(name: String, ty: Option<ty>) -> expr {
        expr {
            kind: expr_kind::Variable(name),
            ty: ty.unwrap_or(ty::Infer(None)),
        }
    }

    pub fn if_else(cond: expr, then: expr, else_: expr, ty: Option<ty>) -> expr {
        expr {
            kind: expr_kind::If {
                condition: Box::new(cond),
                then_value: Box::new(then),
                else_value: Box::new(else_),
            },
            ty: ty.unwrap_or(ty::Infer(None)),
        }
    }

    pub fn int_lit(value: u64, ty: Option<ty>) -> expr {
        expr {
            kind: expr_kind::IntLiteral(value),
            ty: ty.unwrap_or(ty::InferInt(None)),
        }
    }

    pub fn bool_lit(value: bool) -> expr {
        expr {
            kind: expr_kind::BoolLiteral(value),
            ty: ty::Bool,
        }
    }

    pub fn unit_lit() -> expr {
        expr {
            kind: expr_kind::UnitLiteral,
            ty: ty::Unit,
        }
    }

    pub fn neg(inner: expr, ty: Option<ty>) -> expr {
        expr {
            kind: expr_kind::Minus(Box::new(inner)),
            ty: ty.unwrap_or(ty::Infer(None)),
        }
    }

    pub fn pos(inner: expr, ty: Option<ty>) -> expr {
        expr {
            kind: expr_kind::Plus(Box::new(inner)),
            ty: ty.unwrap_or(ty::Infer(None)),
        }
    }

    pub fn not(inner: expr, ty: Option<ty>) -> expr {
        expr {
            kind: expr_kind::Not(Box::new(inner)),
            ty: ty.unwrap_or(ty::Infer(None)),
        }
    }

    pub fn ret(ret: expr) -> expr {
        expr {
            kind: expr_kind::Return(Box::new(ret)),
            ty: ty::Diverging,
        }
    }
}


#[derive(Debug)]
pub enum item {
    Function {
        name: String,
        ret: ty,
        args: Vec<(String, ty)>,
        body: (Vec<stmt>, Option<expr>),
    }
}

#[derive(Debug)]
struct function {
    name: String,
    args: HashMap<String, (usize, ty)>,
    output: ty,
    input: Vec<ty>,
    raw: LLVMValueRef,
}

impl function {
    fn new(name: String, ret_ty: ty, args: Vec<(String, ty)>, module: &mut module)
            -> Result<function, parser_error> {
        let mut args_ty = Vec::new();
        let mut args_hashmap = HashMap::new();
        let mut arg_index = 0;

        let raw = unsafe {
            let params_ty = args.iter().map(|&(_, ref t)| t.to_llvm()).collect::<Vec<_>>();
            module.add_func(&name, &ret_ty, &params_ty)
        };

        for (arg_name, arg_ty) in args {
            if !args_hashmap.contains_key(&arg_name) {
                args_ty.push(arg_ty.clone());
                debug_assert!(args_hashmap.insert(arg_name, (arg_index, arg_ty)).is_none());
                arg_index += 1;
            } else {
                return Err(parser_error::DuplicatedFunctionArgument {
                    argument: arg_name,
                    function: name,
                    compiler: fl!(),
                });
            }
        }

        Ok(function {
            name: name,
            args: args_hashmap,
            output: ret_ty,
            input: args_ty,
            raw: raw,
        })
    }

    fn add_body(&self, body: (Vec<stmt>, Option<expr>), ast: &ast) {
        let mut block = block::new(self, "entry");
        let mut locals = HashMap::new();

        for st in body.0 {
            match st {
                stmt::Let {
                    name,
                    ty: _ty, // ignored by this layer
                    value,
                } => {
                    let local = value.translate(self, &locals, &mut block, ast);
                    locals.insert(name, local);
                }
                stmt::Expr(e) => {
                    e.translate(self, &locals, &mut block, ast);
                    if !block.is_live() {
                        break;
                    }
                }
            }
        }

        if let Some(e) = body.1 {
            let ret = e.translate(self, &locals, &mut block, ast);
            if block.is_live() {
                block.ret(ret);
            }
        }

        if block.is_live() {
            if self.output == ty::Unit {
                block.ret(value::unit_literal(ty::Unit))
            } else {
                block.terminate();
                panic!("ICE: typeck passed through non-void void function")
            }
        }
    }
}

#[derive(Debug)]
pub enum ast_error {
    IncorrectNumberOfArguments {
        passed: usize,
        expected: usize,
        callee: String,
        caller: String,
    },
    UndefinedVariableName {
        name: String,
        function: String,
    },
    FunctionDoesntExist(String),
    CouldNotUnify {
        first: ty,
        second: ty,
        function: String,
        compiler: (&'static str, u32),
    },
    NoActualType {
        function: String,
        compiler:  (&'static str, u32),
    },
    UnknownType(&'static str),
    /*
    BinopUnsupported {
        op: operand,
        lhs: ty,
        rhs: ty,
    },
    UnopUnsupported {
        op: operand,
        inner: ty,
    },
    */
}

#[derive(Debug)]
pub struct ast {
    functions: HashMap<String, function>,
    function_blocks: HashMap<String, (Vec<stmt>, Option<expr>)>,
    module: module,
}

impl ast {
    pub fn create(lexer: lexer) -> Result<ast, parser_error> {
        let mut parser = parser::new(lexer);
        let mut functions = HashMap::new();
        let mut function_blocks = HashMap::new();
        let mut module = module::new("test");

        loop {
            match parser.item() {
                Ok(item::Function {
                    name,
                    ret,
                    args,
                    body,
                }) => {
                    if let Some(_) = functions.insert(name.clone(),
                            try!(function::new(name.clone(), ret, args, &mut module))) {
                        return Err(parser_error::DuplicatedFunction {
                            function: name,
                            compiler: fl!(),
                        });
                    }
                    function_blocks.insert(name, body);
                }

                Err(parser_error::ExpectedEof) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(ast {
            functions: functions,
            function_blocks: function_blocks,
            module: module,
        })
    }

    fn typeck(&mut self) -> Result<(), ast_error> {
        for (name, block) in self.function_blocks.iter_mut() {
            let mut uf = union_find::new();
            let mut vars = HashMap::<String, ty>::new();
            let mut live_blk = true;
            let function = match self.functions.get(name) {
                Some(f) => f,
                None => panic!("ICE: block without an associated function: {}", name),
            };
            for stmt in &mut block.0 {
                match *stmt {
                    stmt::Let {
                        ref name,
                        ref mut ty,
                        ref mut value,
                    } => {
                        ty.generate_inference_id(&mut uf);
                        try!(value.unify_type(*ty, &mut uf, function, &vars, &self.functions));
                        vars.insert(name.to_owned(), *ty);
                    }
                    stmt::Expr(ref mut e @ expr {
                        kind: expr_kind::Return(_),
                        ..
                    }) => {
                        try!(e.unify_type(ty::Diverging, &mut uf, function, &vars, &self.functions));
                        live_blk = false;
                        break;
                    }
                    ref st => panic!("unimplemented: {:?}", st)
                }
            }
            if live_blk {
                match block.1 {
                    Some(ref mut expr) => {
                        try!(expr.unify_type(function.output, &mut uf, function, &vars, &self.functions));
                        // at this point the compiler is done inferring types for this functions
                        // and so it starts finalizing types
                        try!(expr.finalize_type(&mut uf, function))
                    },
                    None => {
                        if function.output != ty::Unit {
                            return Err(ast_error::CouldNotUnify {
                                first: ty::Unit,
                                second: function.output,
                                function: function.name.clone(),
                                compiler: fl!(),
                            })
                        }
                    },
                }
            }
            for stmt in &mut block.0 {
                match *stmt {
                    stmt::Let {
                        ref mut ty,
                        ref mut value,
                        ..
                    } => {
                        *ty = match uf.actual_ty(*ty) {
                            Some(t) => t,
                            None => return Err(ast_error::NoActualType {
                                function: function.name.clone(),
                                compiler: fl!(),
                            })
                        };
                        try!(value.finalize_type(&mut uf, function));
                    }
                    stmt::Expr(ref mut e @ expr {
                        kind: expr_kind::Return(_),
                        ..
                    }) => {
                        try!(e.finalize_type(&mut uf, function));
                        break;
                    }
                    _ => unimplemented!(),
                }
            }
        }
        Ok(())
    }

    pub fn build(mut self) -> Result<(), ast_error> {
        use std::io::Write;
        try!(self.typeck());
        for (name, func) in self.functions.iter() {
            match self.function_blocks.remove(name) {
                Some(body) => func.add_body(body, &self),
                None => panic!("ICE: function without an associated block: {}", name),
            }
        }

        unsafe {
            let mut error: *mut i8 = std::mem::uninitialized();
            /*
            LLVMDumpModule(self.module.raw);
            panic!();
            // */
            LLVMVerifyModule(self.module.raw, LLVMAbortProcessAction, &mut error);
            LLVMDisposeMessage(error);

            if let Some(main) = self.functions.get("main") {
                if let ty::Infer(_) = main.output {
                    unreachable!("Infer(_) should not have got past typeck.")
                } else if let ty::InferInt(_) = main.output {
                    unreachable!("InferInt(_) should not have got past typeck.")
                }
                if main.input.len() != 0 {
                    return Err(ast_error::IncorrectNumberOfArguments {
                        passed: 0,
                        expected: main.input.len(),
                        callee: "main".to_owned(),
                        caller: "[program]".to_owned(),
                    });
                }
                let mut engine: LLVMExecutionEngineRef = std::mem::uninitialized();
                error = std::ptr::null_mut();
                LLVMLinkInMCJIT();
                LLVM_InitializeNativeTarget();
                LLVM_InitializeNativeAsmPrinter();
                if LLVMCreateJITCompilerForModule(&mut engine, self.module.raw,
                        0, &mut error) != 0 {
                    writeln!(std::io::stderr(), "failed to create execution engine: {:?}",
                        CStr::from_ptr(error)).unwrap();
                    LLVMDisposeMessage(error);
                    std::process::exit(-1);
                }

                let res = LLVMRunFunction(engine, main.raw, 0, std::ptr::null_mut());
                match main.output {
                    ty::SInt(int::I32) => {
                        println!("{}", LLVMGenericValueToInt(res, true as LLVMBool) as i32);
                    }
                    ty::UInt(int::I32) => {
                        println!("{}", LLVMGenericValueToInt(res, true as LLVMBool) as u32);
                    }
                    ty::Unit => {}
                    ref ty => {
                        println!("Pink does not yet support printing the {:?} return type", ty);
                    }
                }

                LLVMDisposeGenericValue(res);
                LLVMDisposeExecutionEngine(engine);
            } else {
                return Err(ast_error::FunctionDoesntExist("main".to_owned()));
            }
        }

        Ok(())
    }

    fn call(&self, callee: &str, builder: LLVMBuilderRef, args: Vec<value>)
            -> value {
        match self.functions.get(callee) {
            Some(f) => {
                assert!(f.args.len() == args.len());
                unsafe {
                    let res = LLVMBuildCall(builder, f.raw,
                        args.iter().map(|v| v.raw).collect::<Vec<_>>().as_mut_ptr(),
                        args.len() as u32, cstr!(""));
                    value {
                        raw: res,
                        ty: f.output.clone(),
                    }
                }
            },
            None => {
                panic!("ICE: function doesn't exist");
            }
        }
    }

    fn fn_params(&self, name: &str) -> Result<&[ty], ast_error> {
        match self.functions.get(name) {
            Some(f) => Ok(&f.input),
            None => Err(ast_error::FunctionDoesntExist(name.to_owned())),
        }
    }
}
#[derive(Debug)]
struct module {
    raw: LLVMModuleRef,
}

impl module {
    fn new(name: &str) -> module {
        unsafe {
            let raw = LLVMModuleCreateWithName(CString::new(name)
                .expect("passed a string with a nul to module::new").as_ptr());

            module {
                raw: raw
            }
        }
    }

    unsafe fn add_func(&self, name: &str, ret_ty: &ty, args: &[LLVMTypeRef]) -> LLVMValueRef {
        let ty = LLVMFunctionType(ret_ty.to_llvm_ret(), args.as_ptr() as *mut _,
            args.len() as u32, false as LLVMBool);
        LLVMAddFunction(self.raw, CString::new(name.to_owned())
            .expect("name should not have a nul in it").as_ptr(), ty)
    }
}

#[derive(Clone, Debug)]
struct value {
    ty: ty,
    raw: LLVMValueRef,
}

impl value {
    fn int_literal(ty: ty, val: u64) -> value {
        match ty {
            ty::SInt(_) | ty::UInt(_) => {
                let llvm_ty = ty.to_llvm();
                value {
                    ty: ty,
                    raw: unsafe { LLVMConstInt(llvm_ty, val, false as LLVMBool) },
                }
            }
            ty => {
                panic!("ICE: something got past type checking: {:?}", ty)
            }
        }
    }

    fn bool_literal(ty: ty, val: bool) -> value {
        match ty {
            t @ ty::Bool => {
                let llvm_ty = t.to_llvm();
                value {
                    ty: t,
                    raw: unsafe { LLVMConstInt(llvm_ty, val as u64, false as LLVMBool) },
                }
            }
            ty => {
                panic!("ICE: something got past type checking: {:?}", ty)
            }
        }
    }

    fn unit_literal(ty: ty) -> value {
        match ty {
            ty::Unit => {
                value {
                    raw: unsafe { LLVMConstStruct([].as_mut_ptr(), 0, false as LLVMBool) },
                    ty: ty::Unit,
                }
            }
            ty => {
                panic!("ICE: something got past type checking: {:?}", ty)
            }
        }
    }

    fn undef(ty: ty) -> value {
        value {
            raw: unsafe { LLVMGetUndef(ty.to_llvm()) },
            ty: ty,
        }
    }

    fn parameter(ty: ty, function: &function, name: &str) -> value {
        if let Some(&(i, ref param_ty)) = function.args.get(name) {
            assert!(param_ty == &ty);
            value {
                ty: param_ty.clone(),
                raw: unsafe { LLVMGetParam(function.raw, i as u32) },
            }
        } else {
            panic!("ICE: undefined parameter name");
        }
    }

    fn binop(op: &operand, lhs: value, rhs: value, builder: LLVMBuilderRef)
            -> value {
        match *op {
            operand::Mul => lhs.mul(rhs, builder),
            operand::Div => lhs.div(rhs, builder),
            operand::Rem => lhs.rem(rhs, builder),
            operand::Plus => lhs.add(rhs, builder),
            operand::Minus => lhs.sub(rhs, builder),

            operand::Shl => lhs.shl(rhs, builder),
            operand::Shr => lhs.shr(rhs, builder),

            operand::And => lhs.and(rhs, builder),
            operand::Xor => lhs.xor(rhs, builder),
            operand::Or => lhs.or(rhs, builder),

            operand::EqualsEquals => lhs.eq(rhs, builder),
            operand::NotEquals => lhs.neq(rhs, builder),
            operand::LessThan => lhs.le(rhs, builder),
            operand::LessThanEquals => lhs.lte(rhs, builder),
            operand::GreaterThan => lhs.gt(rhs, builder),
            operand::GreaterThanEquals => lhs.gte(rhs, builder),

            operand::AndAnd => unreachable!("should be an if statement"),
            operand::OrOr => unreachable!("should be an if statement"),
            operand::Not => unreachable!("Not (`!`) is not a binop"),
        }
    }

    fn mul(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) => {
                value {
                    raw: unsafe { LLVMBuildMul(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn div(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: unsafe { LLVMBuildSDiv(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            ty::UInt(_) => {
                value {
                    raw: unsafe { LLVMBuildUDiv(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn rem(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: unsafe { LLVMBuildSRem(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            ty::UInt(_) => {
                value {
                    raw: unsafe { LLVMBuildURem(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn add(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) => {
                value {
                    raw: unsafe { LLVMBuildAdd(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn sub(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) => {
                value {
                    raw: unsafe { LLVMBuildSub(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn shl(self, rhs: value, builder: LLVMBuilderRef) -> value {
        match rhs.ty {
            ty::SInt(_) | ty::UInt(_) => {
                match self.ty {
                    ty::SInt(ref lt) | ty::UInt(ref lt) => unsafe {
                        let shift_mask = lt.shift_mask();
                        let safe_rhs = LLVMBuildAnd(builder, rhs.raw,
                            LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool),
                            cstr!(""));
                        return value {
                            raw: LLVMBuildShl(builder, self.raw, safe_rhs, cstr!("")),
                            ty: self.ty.clone(),
                        };
                    },
                    _ => {}
                }
            }
            _ => {}
        }
        panic!("ICE: unsupported operation")
    }
    fn shr(self, rhs: value, builder: LLVMBuilderRef) -> value {
        match rhs.ty {
            ty::SInt(_) | ty::UInt(_) => {
                match self.ty {
                    ty::SInt(ref lt) => unsafe {
                        let shift_mask = lt.shift_mask();
                        let safe_rhs = LLVMBuildAnd(builder, rhs.raw,
                            LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool),
                            cstr!(""));
                        return value {
                            raw: LLVMBuildAShr(builder, self.raw, safe_rhs, cstr!("")),
                            ty: self.ty.clone(),
                        };
                    },
                    ty::UInt(ref lt) => unsafe {
                        let shift_mask = lt.shift_mask();
                        let safe_rhs = LLVMBuildAnd(builder, rhs.raw,
                            LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool),
                            cstr!(""));
                        return value {
                            raw: LLVMBuildLShr(builder, self.raw, safe_rhs, cstr!("")),
                            ty: self.ty.clone(),
                        };
                    },
                    _ => {}
                }
            }
            _ => {}
        }

        panic!("ICE: unsupported operation")
    }
    fn and(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                value {
                    raw: unsafe { LLVMBuildAnd(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn xor(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                value {
                    raw: unsafe { LLVMBuildXor(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn or(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                value {
                    raw: unsafe { LLVMBuildOr(builder, self.raw, rhs.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }

    fn eq(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntEQ, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                },
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn neq(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntNE, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                },
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn le(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntSLT, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                }
            }
            ty::UInt(_) | ty::Bool => {
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntULT, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn lte(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntSLE, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                }
            }
            ty::UInt(_) | ty::Bool => {
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntULE, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn gt(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntSGT, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                }
            }
            ty::UInt(_) | ty::Bool => {
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntUGT, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn gte(self, rhs: value, builder: LLVMBuilderRef) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntSGE, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                }
            }
            ty::UInt(_) | ty::Bool => {
                value {
                    raw: unsafe { LLVMBuildICmp(builder, LLVMIntUGE, self.raw, rhs.raw, cstr!("")) },
                    ty: ty::Bool,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }


    fn neg(self, builder: LLVMBuilderRef) -> value {
        if let ty::SInt(_) = self.ty {
            value {
                raw: unsafe { LLVMBuildNeg(builder, self.raw, cstr!("")) },
                ty: self.ty,
            }
        } else {
            panic!("ICE: unsupported operation")
        }
    }
    fn not(self, builder: LLVMBuilderRef) -> value {
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                value {
                    raw: unsafe { LLVMBuildNot(builder, self.raw, cstr!("")) },
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
}

struct block<'a> {
    raw: LLVMBasicBlockRef,
    builder_: LLVMBuilderRef,
    live: bool,
    dbg_name: String,
    function: std::marker::PhantomData<&'a function>,
}

impl<'a> block<'a> {
    fn new(function: &'a function, name: &'static str) -> Self {
        unsafe {
            let builder = LLVMCreateBuilder();
            let raw = LLVMAppendBasicBlock(function.raw, cstr!("bb"));
            LLVMPositionBuilderAtEnd(builder, raw);
            block {
                raw: raw,
                builder_: builder,
                live: true,
                dbg_name: format!("function: {}, block: {}", function.name, name),
                function: std::marker::PhantomData,
            }
        }
    }

    #[inline(always)]
    pub fn is_live(&self) -> bool {
        self.live
    }

    pub fn builder(&self) -> LLVMBuilderRef {
        assert!(self.live);
        self.builder_
    }

    /// terminator
    fn terminate(&mut self) {
        assert!(self.live);
        self.live = false;
    }

    /// terminator
    fn ret(&mut self, ret: value) {
        assert!(self.live);
        self.live = false;
        if ret.ty == ty::Unit {
            unsafe { LLVMBuildRetVoid(self.builder_); }
        } else {
            unsafe { LLVMBuildRet(self.builder_, ret.raw); }
        }
    }

    /// terminator
    fn conditional_branch(&mut self, cond: value, then_blk: &block, else_blk: &block) {
        assert!(self.live);
        self.live = false;
        unsafe {
            assert!(cond.ty == ty::Bool, "ICE: condition is not a boolean");
            LLVMBuildCondBr(self.builder_, cond.raw, then_blk.raw, else_blk.raw);
        }
    }

    /// terminator
    fn branch(&mut self, block: &block) {
        assert!(self.live);
        self.live = false;
        unsafe {
            LLVMBuildBr(self.builder_, block.raw);
        }
    }

    fn phi(&mut self, ty: ty, then: Option<(value, &block)>,
            else_: Option<(value, &block)>) -> value {
        assert!(self.live);
        match (then, else_) {
            (Some((then_res, then_blk)), Some((else_res, else_blk))) => {
                unsafe {
                    assert!(then_res.ty == ty, then_res.ty == else_res.ty);
                    let ret = LLVMBuildPhi(self.builder_, then_res.ty.to_llvm(), cstr!(""));
                    let mut phi_vals = [then_res.raw, else_res.raw];
                    let mut preds = [then_blk.raw, else_blk.raw];
                    LLVMAddIncoming(ret, phi_vals.as_mut_ptr(), preds.as_mut_ptr(), 2);
                    value { ty: then_res.ty, raw: ret }
                }
            }
            (Some((res, blk)), None) | (None, Some((res, blk))) => {
                unsafe {
                    assert!(res.ty == ty);
                    let ret = LLVMBuildPhi(self.builder_, ty.to_llvm(), cstr!(""));
                    let mut phi_vals = [res.raw];
                    let mut preds = [blk.raw];
                    LLVMAddIncoming(ret, phi_vals.as_mut_ptr(), preds.as_mut_ptr(), 1);
                    value { ty: res.ty, raw: ret }
                }
            }
            (None, None) => {
                value::undef(ty)
            }
        }
    }
}

impl<'a> std::ops::Drop for block<'a> {
    fn drop(&mut self) {
        if self.live {
            println!("dropped live block: {}", self.dbg_name)
        }
        unsafe {
            LLVMDisposeBuilder(self.builder_);
        }
    }
}
