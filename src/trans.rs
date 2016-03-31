use std;
use std::collections::HashMap;
use std::ffi::{CString, CStr};
use parse::{lexer, operand, parser, parser_error};
use ty::{ty, int};

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
pub enum expr {
    Call {
        name: String,
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
    IntLiteral {
        value: u64,
        ty: ty,
    },
    BoolLiteral(bool),
    UnitLiteral,
    Return(Box<expr>),
}

impl expr {
    fn translate<'a>(self, ty: ty, function: &'a function, locals: &HashMap<String, value>,
            block: &mut block<'a>, ast: &ast) -> Result<value, ast_error> {
        match self {
            expr::IntLiteral {value, ty: lit_ty} => {
                if lit_ty == ty::Generic {
                    value::int_literal(ty, value)
                } else if ty == ty::Generic {
                    value::int_literal(lit_ty, value)
                } else if ty == lit_ty {
                    value::int_literal(ty, value)
                } else {
                    Err(ast_error::IncorrectType {
                        expected: ty,
                        found: lit_ty,
                        compiler: fl!(),
                    })
                }
            }
            expr::BoolLiteral(b) => {
                value::bool_literal(ty, b)
            }
            expr::UnitLiteral => {
                value::unit_literal(ty)
            }
            expr::Variable(ref name) => {
                if let Some(val) = locals.get(name) {
                    if val.ty == ty {
                        Ok(val.clone())
                    } else {
                        Err(ast_error::IncorrectType {
                            expected: ty,
                            found: val.ty.clone(),
                            compiler: fl!(),
                        })
                    }
                } else {
                    value::parameter(ty.clone(), function, name)
                }
            }
            expr::Binop {
                op: operand::OrOr,
                lhs,
                rhs,
            } => {
                expr::If {
                    condition: lhs,
                    then_value: Box::new(expr::BoolLiteral(true)),
                    else_value: rhs,
                }.translate(ty, function, locals, block, ast)
            }
            expr::Binop {
                op: operand::AndAnd,
                lhs,
                rhs,
            } => {
                expr::If {
                    condition: Box::new(expr::Not(lhs)),
                    then_value: Box::new(expr::BoolLiteral(false)),
                    else_value: rhs,
                }.translate(ty, function, locals, block, ast)
            }
            expr::Binop {
                op,
                lhs,
                rhs,
            } => {
                let lhs = try!(lhs.translate(ty::Generic, function, locals, block, ast));
                let rhs = try!(rhs.translate(ty::Generic, function, locals, block, ast));
                value::binop(ty, &op, lhs, rhs, block.builder())
            }
            expr::Plus(inner) => {
                inner.translate(ty, function, locals, block, ast)
            }
            expr::Minus(inner) => {
                inner.translate(ty.clone(), function, locals, block, ast)
                    .and_then(|v| v.neg(block.builder(), ty))
            }
            expr::Not(inner) => {
                inner.translate(ty.clone(), function, locals, block, ast)
                    .and_then(|v| v.not(block.builder(), ty))
            }
            expr::If {
                condition,
                then_value,
                else_value,
            } => {
                let cond = try!(condition.translate(ty::Bool, function, locals, block, ast));
                let res = if block.is_live() {
                    let mut then_blk = block::new(function, "then");
                    let mut else_blk = block::new(function, "else");
                    let mut join_blk = block::new(function, "join");
                    block.conditional_branch(cond, &then_blk, &else_blk);

                    let then_res = try!(then_value.translate(ty.clone(), function, locals, &mut then_blk, ast));
                    let then_live = if then_blk.is_live() {
                        then_blk.branch(&join_blk);
                        true
                    } else {
                        false
                    };

                    let else_res = try!(else_value.translate(ty.clone(), function, locals, &mut else_blk, ast));
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
                    let res = join_blk.phi(ty, then, else_);
                    *block = join_blk;
                    res
                } else {
                    value::undef(ty)
                };
                Ok(res)
            }
            expr::Call {
                name,
                args,
            } => {
                let mut llvm_args = Vec::new();
                //let fn_params = ast.fn_params(&name);
                for (arg, ty) in args.into_iter().zip(try!(ast.fn_params(&name)).iter()) {
                    llvm_args.push(try!(arg.translate(ty.clone(), function, locals, block, ast)));
                }
                ast.call(ty, &name, block.builder(), llvm_args)
            }
            expr::Return(expr) => {
                let ret = try!(expr.translate(ty.clone(), function, locals, block, ast));
                if block.is_live() {
                    block.ret(ret);
                }
                match ty {
                    ty::Generic => unimplemented!(),
                    ty => Ok(value::undef(ty)),
                }
            }
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

struct function {
    dbg_name: String,
    args: HashMap<String, (usize, ty)>,
    ret_ty: ty,
    args_ty: Vec<ty>,
    raw: LLVMValueRef,
}

impl function {
    fn new(name: String, ret_ty: ty, args: Vec<(String, ty)>, module: LLVMModuleRef)
            -> Result<function, parser_error> {
        let mut args_ty = Vec::new();
        let mut args_hashmap = HashMap::new();
        let mut arg_index = 0;

        let raw = unsafe {
            let mut params_ty = args.iter().map(|&(_, ref t)| t.to_llvm()).collect::<Vec<_>>();
            let function_ty = LLVMFunctionType(ret_ty.to_llvm_ret(), params_ty.as_mut_ptr(),
                params_ty.len() as u32, false as LLVMBool);

            LLVMAddFunction(module, CString::new(name.clone())
                .expect("name should not have a nul in it").as_ptr(), function_ty)
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
            dbg_name: name,
            args: args_hashmap,
            ret_ty: ret_ty,
            args_ty: args_ty,
            raw: raw,
        })
    }

    fn add_body(&self, body: (Vec<stmt>, Option<expr>), ast: &ast) -> Result<(), ast_error> {
        let mut block = block::new(self, "entry");
        let mut locals = HashMap::new();

        for st in body.0 {
            match st {
                stmt::Let {
                    name,
                    ty,
                    value,
                } => {
                    let local = try!(value.translate(ty, self, &locals, &mut block, ast));
                    locals.insert(name, local);
                }
                stmt::Expr(e) => {
                    try!(e.translate(self.ret_ty.clone(),
                        self, &locals, &mut block, ast));
                    if !block.is_live() {
                        break;
                    }
                }
            }
        }

        if let Some(e) = body.1 {
            let ret = try!(e.translate(self.ret_ty.clone(),
                self, &locals, &mut block, ast));
            if block.is_live() {
                block.ret(ret);
            }
        }

        if block.is_live() {
            if self.ret_ty == ty::Unit {
                block.ret(value::unit_literal(ty::Unit).unwrap())
            } else {
                block.terminate();
                return Err(ast_error::IncorrectType {
                    expected: self.ret_ty.clone(),
                    found: ty::Unit,
                    compiler: fl!(),
                });
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum ast_error {
    IncorrectNumberOfArguments {
        passed: usize,
        expected: usize,
        function: String,
    },
    UndefinedVariableName {
        name: String,
        function: String,
    },
    FunctionDoesntExist(String),
    IncorrectType {
        expected: ty,
        found: ty,
        compiler: (&'static str, u32),
    },
    BinopUnsupported {
        op: operand,
        lhs: ty,
        rhs: ty,
    },
    UnopUnsupported {
        op: operand,
        inner: ty,
    },
    UnknownType(&'static str),
}

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
        let module = module::new("test");

        loop {
            match parser.item() {
                Ok(item::Function {
                    name,
                    ret,
                    args,
                    body,
                }) => {
                    if let Some(_) = functions.insert(name.clone(),
                            try!(function::new(name.clone(), ret, args, module.raw))) {
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

    pub fn build(mut self) -> Result<(), ast_error> {
        use std::io::Write;
        assert!(self.function_blocks.len() == self.functions.len());
        for (name, func) in self.functions.iter() {
            match self.function_blocks.remove(name) {
                Some(body) => try!(func.add_body(body, &self)),
                None => panic!("function without an associated block: {}", name),
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
                if main.ret_ty == ty::Generic {
                    unreachable!("Generic is not a real type. No function should have that type")
                }
                if main.args_ty.len() != 0 {
                    return Err(ast_error::IncorrectNumberOfArguments {
                        passed: 0,
                        expected: main.args_ty.len(),
                        function: "main".to_owned(),
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
                match main.ret_ty {
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

    fn call(&self, ty: ty, callee: &str, builder: LLVMBuilderRef, args: Vec<value>)
            -> Result<value, ast_error> {
        match self.functions.get(callee) {
            Some(f) => {
                if f.args.len() != args.len() {
                    Err(ast_error::IncorrectNumberOfArguments {
                        expected: f.args.len(),
                        passed: args.len(),
                        function: callee.to_owned(),
                    })
                } else if f.ret_ty != ty && ty != ty::Generic {
                    Err(ast_error::IncorrectType {
                        expected: ty,
                        found: f.ret_ty.clone(),
                        compiler: fl!()
                    })
                } else {
                    unsafe {
                        let res = LLVMBuildCall(builder, f.raw,
                            args.iter().map(|v| v.raw).collect::<Vec<_>>().as_mut_ptr(),
                            args.len() as u32, cstr!(""));
                        Ok(value {
                            raw: res,
                            ty: f.ret_ty.clone(),
                        })
                    }
                }
            },
            None => {
                Err(ast_error::FunctionDoesntExist(callee.to_owned()))
            }
        }
    }

    fn fn_params(&self, name: &str) -> Result<&[ty], ast_error> {
        match self.functions.get(name) {
            Some(f) => Ok(&f.args_ty),
            None => Err(ast_error::FunctionDoesntExist(name.to_owned())),
        }
    }
}
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
}

#[derive(Clone, Debug)]
struct value {
    ty: ty,
    raw: LLVMValueRef,
}

impl value {
    fn int_literal(ty: ty, val: u64) -> Result<value, ast_error> {
        match ty {
            ty::SInt(_) | ty::UInt(_) => {
                let llvm_ty = ty.to_llvm();
                Ok(value {
                    ty: ty,
                    raw: unsafe { LLVMConstInt(llvm_ty, val, false as LLVMBool) },
                })
            }
            ty::Generic => {
                Err(ast_error::UnknownType("int literal"))
            }
            ty => {
                Err(ast_error::IncorrectType {
                    expected: ty,
                    found: ty::Generic,
                    compiler: fl!(),
                })
            }
        }
    }

    fn bool_literal(ty: ty, val: bool) -> Result<value, ast_error> {
        match ty {
            ty::Bool | ty::Generic => {
                let ty = ty::Bool;
                let llvm_ty = ty.to_llvm();
                Ok(value {
                    ty: ty,
                    raw: unsafe { LLVMConstInt(llvm_ty, val as u64, false as LLVMBool) },
                })
            }
            ty => {
                Err(ast_error::IncorrectType {
                    expected: ty,
                    found: ty::Generic,
                    compiler: fl!(),
                })
            }
        }
    }

    fn unit_literal(ty: ty) -> Result<value, ast_error> {
        match ty {
            ty::Unit | ty::Generic => {
                Ok(value {
                    raw: unsafe { LLVMConstStruct([].as_mut_ptr(), 0, false as LLVMBool) },
                    ty: ty::Unit,
                })
            }
            ty => {
                Err(ast_error::IncorrectType {
                    expected: ty,
                    found: ty::Unit,
                    compiler: fl!(),
                })
            }
        }
    }

    fn undef(ty: ty) -> value {
        value {
            raw: unsafe { LLVMGetUndef(ty.to_llvm()) },
            ty: ty,
        }
    }

    fn parameter(ty: ty, function: &function, name: &str) -> Result<value, ast_error> {
        if let Some(&(i, ref param_ty)) = function.args.get(name) {
            if param_ty == &ty || ty == ty::Generic {
                Ok(value {
                    ty: param_ty.clone(),
                    raw: unsafe { LLVMGetParam(function.raw, i as u32) },
                })
            } else {
                Err(ast_error::IncorrectType {
                    expected: ty,
                    found: param_ty.clone(),
                    compiler: fl!(),
                })
            }
        } else {
            Err(ast_error::UndefinedVariableName {
                name: name.to_owned(),
                function: function.dbg_name.clone(),
            })
        }
    }

    fn binop(ty: ty, op: &operand, lhs: value, rhs: value, builder: LLVMBuilderRef)
            -> Result<value, ast_error> {
        match *op {
            operand::Mul => lhs.mul(rhs, builder, ty),
            operand::Div => lhs.div(rhs, builder, ty),
            operand::Rem => lhs.rem(rhs, builder, ty),
            operand::Plus => lhs.add(rhs, builder, ty),
            operand::Minus => lhs.sub(rhs, builder, ty),

            operand::Shl => lhs.shl(rhs, builder, ty),
            operand::Shr => lhs.shr(rhs, builder, ty),

            operand::And => lhs.and(rhs, builder, ty),
            operand::Xor => lhs.xor(rhs, builder, ty),
            operand::Or => lhs.or(rhs, builder, ty),

            operand::EqualsEquals => lhs.eq(rhs, builder, ty),
            operand::NotEquals => lhs.neq(rhs, builder, ty),
            operand::LessThan => lhs.le(rhs, builder, ty),
            operand::LessThanEquals => lhs.lte(rhs, builder, ty),
            operand::GreaterThan => lhs.gt(rhs, builder, ty),
            operand::GreaterThanEquals => lhs.gte(rhs, builder, ty),

            operand::AndAnd => unreachable!("should be an if statement"),
            operand::OrOr => unreachable!("should be an if statement"),
            operand::Not => unreachable!("Not (`!`) is not a binop"),
        }
    }

    fn mul(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildMul(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Mul,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn div(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::SInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildSDiv(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildUDiv(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Div,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn rem(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::SInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildSRem(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildURem(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Rem,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn add(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildAdd(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Plus,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn sub(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildSub(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Minus,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    // TODO: assert! that the value is correctly sized
    fn shl(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == ty {
            match rhs.ty {
                ty::SInt(_) | ty::UInt(_) => {
                    match self.ty {
                        ty::SInt(ref lt) | ty::UInt(ref lt) => unsafe {
                            let shift_mask = lt.shift_mask();
                            let safe_rhs = LLVMBuildAnd(builder, rhs.raw,
                                LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool),
                                cstr!(""));
                            return Ok(value {
                                raw: LLVMBuildShl(builder, self.raw, safe_rhs, cstr!("")),
                                ty: ty,
                            });
                        },
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Shl,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn shr(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == ty {
            match rhs.ty {
                ty::SInt(_) | ty::UInt(_) => {
                    match self.ty {
                        ty::SInt(ref lt) => unsafe {
                            let shift_mask = lt.shift_mask();
                            let safe_rhs = LLVMBuildAnd(builder, rhs.raw,
                                LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool),
                                cstr!(""));
                            return Ok(value {
                                raw: LLVMBuildAShr(builder, self.raw, safe_rhs, cstr!("")),
                                ty: ty,
                            });
                        },
                        ty::UInt(ref lt) => unsafe {
                            let shift_mask = lt.shift_mask();
                            let safe_rhs = LLVMBuildAnd(builder, rhs.raw,
                                LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool),
                                cstr!(""));
                            return Ok(value {
                                raw: LLVMBuildLShr(builder, self.raw, safe_rhs, cstr!("")),
                                ty: ty,
                            });
                        },
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Shr,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn and(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildAnd(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::And,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn xor(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildXor(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Xor,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn or(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && self.ty == ty {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildOr(builder, self.raw, rhs.raw, cstr!("")) },
                        ty: self.ty,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::Or,
            lhs: self.ty, rhs: rhs.ty,
        })
    }

    fn eq(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool || ty == ty::Generic {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntEQ, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::EqualsEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn neq(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntNE, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    }),
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::NotEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn le(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            match self.ty {
                ty::SInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntSLT, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    });
                }
                ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntULT, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::LessThan,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn lte(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            match self.ty {
                ty::SInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntSLE, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    });
                }
                ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntULE, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::LessThanEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn gt(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            match self.ty {
                ty::SInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntSGT, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    });
                }
                ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntUGT, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::GreaterThanEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }
    fn gte(self, rhs: value, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == rhs.ty && ty == ty::Bool {
            match self.ty {
                ty::SInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntSGE, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    });
                }
                ty::UInt(_) => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildICmp(builder, LLVMIntUGE, self.raw, rhs.raw, cstr!("")) },
                        ty: ty::Bool,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::BinopUnsupported {
            op: operand::GreaterThanEquals,
            lhs: self.ty, rhs: rhs.ty,
        })
    }


    fn neg(self, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == ty {
            if let ty::SInt(_) = self.ty {
                return Ok(value {
                    raw: unsafe { LLVMBuildNeg(builder, self.raw, cstr!("")) },
                    ty: self.ty,
                });
            }
        }
        Err(ast_error::UnopUnsupported {
            op: operand::Minus,
            inner: self.ty,
        })
    }
    fn not(self, builder: LLVMBuilderRef, ty: ty) -> Result<value, ast_error> {
        if self.ty == ty {
            match self.ty {
                ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                    return Ok(value {
                        raw: unsafe { LLVMBuildNot(builder, self.raw, cstr!("")) },
                        ty: self.ty,
                    });
                }
                _ => {}
            }
        }
        Err(ast_error::UnopUnsupported {
            op: operand::Not,
            inner: self.ty,
        })
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
                dbg_name: format!("function: {}, block: {}", function.dbg_name, name),
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
