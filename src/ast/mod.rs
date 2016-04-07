use std;
use std::collections::HashMap;
use parse;
use ty::{self, Ty};
use mir;

pub mod expr;
use self::expr::{Stmt, Expr};

#[derive(Debug)]
pub struct Ast {
    functions: HashMap<String, (Function, Block)>,
    function_types: HashMap<String, ty::Function>,
}

impl Ast {
    pub fn create(lexer: parse::Lexer) -> Result<Ast, parse::ParserError> {
        let mut parser = parse::Parser::new(lexer);
        let mut functions = HashMap::new();
        let mut function_types = HashMap::new();

        loop {
            match parser.item() {
                Ok(Item::Function {
                    name,
                    ret,
                    args,
                    body,
                }) => {
                    let ty = ty::Function::new(
                        args.iter().map(|&(_, t)| t).collect(), ret);
                    let f = try!(Function::new(name.clone(), ret, args));
                    function_types.insert(name.clone(), ty);
                    if let Some(_) =
                            functions.insert(name.clone(), (f, body)) {
                        return Err(parse::ParserError::DuplicatedFunction {
                            function: name,
                            compiler: fl!(),
                        });
                    }
                }

                Err(parse::ParserError::ExpectedEof) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(Ast {
            functions: functions,
            function_types: function_types,
        })
    }

    pub fn typeck(mut self) -> Result<mir::Mir, AstError> {
        for (_, &mut (ref func, ref mut body))
                in self.functions.iter_mut() {
            let mut uf = ty::UnionFind::new();
            let mut vars = HashMap::<String, Ty>::new();
            try!(Expr::typeck_block(body, func.ret_ty,
                &mut uf, &mut vars, func, &self.function_types));
            try!(Expr::finalize_block_ty(body, &mut uf, func));
        }
        let mut mir = mir::Mir::new();
        let functions = std::mem::replace(&mut self.functions, HashMap::new());
        for (name, (func, body)) in functions {
            mir.add_function(name, func.add_body(body, &self));
        }
        Ok(mir)
    }
}

#[derive(Debug)]
pub enum AstError {
    IncorrectNumberOfArguments {
        passed: usize,
        expected: usize,
        callee: String,
        caller: String,
        //compiler: (&'static str, u32),
    },
    UndefinedVariableName {
        name: String,
        function: String,
        //compiler: (&'static str, u32),
    },
    FunctionDoesntExist(String),
    UnopUnsupported {
        op: parse::Operand,
        inner: Ty,
        function: String,
        compiler: (&'static str, u32),
    },
    CouldNotUnify {
        first: Ty,
        second: Ty,
        function: String,
        compiler: (&'static str, u32),
    },
    NoActualType {
        function: String,
        compiler: (&'static str, u32),
    },
    StatementsAfterReturn {
        function: String,
        compiler: (&'static str, u32),
    },
    /*
    BinopUnsupported {
        op: parse::Operand,
        lhs: Ty,
        rhs: Ty,
    },
    */
}

#[derive(Debug)]
pub enum Item {
    Function {
        name: String,
        ret: Ty,
        args: Vec<(String, Ty)>,
        body: Block,
    }
}

#[derive(Debug)]
pub struct Function {
    name: String,
    ret_ty: Ty,
    args: HashMap<String, (usize, Ty)>,
    raw: mir::Function,
}

impl Function {
    fn new(name: String, ret_ty: Ty, args: Vec<(String, Ty)>)
            -> Result<Function, parse::ParserError> {
        let mut args_ty = Vec::new();
        let mut args_hashmap = HashMap::new();
        let mut arg_index = 0;


        for (arg_name, arg_ty) in args {
            if !args_hashmap.contains_key(&arg_name) {
                args_ty.push(arg_ty);
                debug_assert!(
                    args_hashmap.insert(arg_name, (arg_index, arg_ty))
                    .is_none());
                arg_index += 1;
            } else {
                return Err(parse::ParserError::DuplicatedFunctionArgument {
                    argument: arg_name,
                    function: name,
                    compiler: fl!(),
                });
            }
        }

        let raw = mir::Function::new(ty::Function::new(args_ty, ret_ty));

        Ok(Function {
            name: name,
            ret_ty: ret_ty,
            args: args_hashmap,
            raw: raw,
        })
    }

    fn add_body(mut self, body: Block, ast: &Ast) -> mir::Function {
        let mut block = self.raw.start_block();
        // let mut locals = HashMap::new();

        let ret = Expr::translate_block(body, &mut self, &mut block,
                &ast.function_types);
        block.ret(&mut self.raw, ret);
        self.raw
    }
}

#[derive(Debug)]
pub struct Block {
    stmts: Vec<Stmt>,
    expr: Option<Expr>,
}

impl Block {
    pub fn new(stmts: Vec<Stmt>, expr: Option<Expr>) -> Block {
        Block {
            stmts: stmts,
            expr: expr,
        }
    }

    pub fn expr(e: Expr) -> Block {
        Block {
            stmts: vec![],
            expr: Some(e),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Value {
    ty: Ty,
    raw: mir::Value,
}

impl Value {
    /*
    fn int_literal(ty: Ty, val: u64) -> Value {
        match ty {
            Ty::SInt(_) | Ty::UInt(_) => {
                Value {
                    ty: ty,
                    raw: mir::Value::const_int(val, ty),
                }
            }
            ty => {
                panic!("ICE: something got past type checking: {:?}", ty)
            }
        }
    }
    */
}
