use ast::{AstError, Block, Function};
use std::collections::HashMap;
use ty::{self, Ty};
use parse::Operand;
use mir;

#[derive(Debug)]
pub enum Stmt {
    Let {
        name: String,
        ty: Ty,
        value: Option<Box<Expr>>,
    },
    Expr(Expr),
}

#[derive(Debug)]
pub enum ExprKind {
    Call {
        callee: String,
        args: Vec<Expr>
    },
    If {
        condition: Box<Expr>,
        then_value: Box<Block>,
        else_value: Box<Block>,
    },
    Block(Box<Block>),
    Binop {
        op: Operand,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Pos(Box<Expr>), // unary plus
    Neg(Box<Expr>), // unary minus
    Not(Box<Expr>), // !expr
    Variable(String),
    IntLiteral(u64),
    BoolLiteral(bool),
    UnitLiteral,
    Return(Box<Expr>),
    Assign {
        dst: Box<Expr>,
        src: Box<Expr>
    },
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Ty,
}

// constructors
impl Expr {
    pub fn call(callee: String, args: Vec<Expr>, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::Call {
                callee: callee,
                args: args,
            },
            ty: ty.unwrap_or(Ty::Infer(None)),
        }
    }

    pub fn var(name: String, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::Variable(name),
            ty: ty.unwrap_or(Ty::Infer(None)),
        }
    }

    pub fn if_else(cond: Expr, then: Block,
            else_: Block, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::If {
                condition: Box::new(cond),
                then_value: Box::new(then),
                else_value: Box::new(else_),
            },
            ty: ty.unwrap_or(Ty::Infer(None)),
        }
    }

    pub fn block(inner: Block, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::Block(Box::new(inner)),
            ty: ty.unwrap_or(Ty::Infer(None)),
        }
    }

    pub fn int_lit(value: u64, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::IntLiteral(value),
            ty: ty.unwrap_or(Ty::InferInt(None)),
        }
    }

    pub fn bool_lit(value: bool) -> Expr {
        Expr {
            kind: ExprKind::BoolLiteral(value),
            ty: Ty::Bool,
        }
    }

    pub fn unit_lit() -> Expr {
        Expr {
            kind: ExprKind::UnitLiteral,
            ty: Ty::Unit,
        }
    }

    pub fn neg(inner: Expr, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::Neg(Box::new(inner)),
            ty: ty.unwrap_or(Ty::Infer(None)),
        }
    }

    pub fn pos(inner: Expr, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::Pos(Box::new(inner)),
            ty: ty.unwrap_or(Ty::Infer(None)),
        }
    }

    pub fn not(inner: Expr, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::Not(Box::new(inner)),
            ty: ty.unwrap_or(Ty::Infer(None)),
        }
    }

    pub fn ret(ret: Expr) -> Expr {
        Expr {
            kind: ExprKind::Return(Box::new(ret)),
            ty: Ty::Diverging,
        }
    }

    pub fn assign(dst: Expr, src: Expr) -> Expr {
        Expr {
            kind: ExprKind::Assign {
                dst: Box::new(dst),
                src: Box::new(src),
            },
            ty: Ty::Unit,
        }
    }
}

// parsing
impl Expr {
    pub fn is_block(&self) -> bool {
        match self.kind {
            ExprKind::If {..} | ExprKind::Block(_) => true,
            ExprKind::Call {..} | ExprKind::Binop {..} | ExprKind::Pos(_)
            | ExprKind::Neg(_) | ExprKind::Not(_) | ExprKind::Variable(_)
            | ExprKind::IntLiteral(_) | ExprKind::BoolLiteral(_)
            | ExprKind::UnitLiteral | ExprKind::Return(_)
            | ExprKind::Assign {..} => false,
        }
    }
}

// typechecking
impl Expr {
    pub fn typeck_block(block: &mut Block,
            to_unify: Ty, uf: &mut ty::UnionFind,
            variables: &mut HashMap<String, Ty>, function: &Function,
            functions: &HashMap<String, ty::Function>)
            -> Result<(), AstError> {
        let mut live_blk = true;
        for stmt in block.stmts.iter_mut() {
            match *stmt {
                Stmt::Let {
                    ref name,
                    ref mut ty,
                    ref mut value,
                } => {
                    ty.generate_inference_id(uf);
                    if let Some(ref mut v) = *value {
                        try!(v.unify_type(
                            *ty, uf, variables, function, functions));
                    }
                    variables.insert(name.to_owned(), *ty);
                }
                Stmt::Expr(ref mut e @ Expr {
                    kind: ExprKind::Return(_),
                    ..
                }) => {
                    try!(e.unify_type(Ty::Diverging,
                        uf, variables, function, functions));
                    live_blk = false;
                    break;
                }
                Stmt::Expr(ref mut e) => {
                    let mut ty = Ty::Infer(None);
                    ty.generate_inference_id(uf);
                    try!(e.unify_type(ty, uf, variables, function, functions));
                }
            }
        }
        if live_blk {
            match block.expr {
                Some(ref mut expr) => {
                    try!(expr.unify_type(to_unify,
                        uf, variables, function, functions));
                },
                None => {
                    try!(uf.unify(to_unify, Ty::Unit).map_err(|()|
                        AstError::CouldNotUnify {
                            first: Ty::Unit,
                            second: to_unify,
                            function: function.name.clone(),
                            compiler: fl!(),
                        }
                    ))
                },
            }
        }
        Ok(())
    }

    pub fn unify_type(&mut self, to_unify: Ty, uf: &mut ty::UnionFind,
            variables: &mut HashMap<String, Ty>, function: &Function,
            functions: &HashMap<String, ty::Function>) -> Result<(), AstError> {
        self.ty.generate_inference_id(uf);
        match self.kind {
            ExprKind::IntLiteral(_) | ExprKind::BoolLiteral(_)
            | ExprKind::UnitLiteral => {
                uf.unify(self.ty, to_unify).map_err(|()|
                    AstError::CouldNotUnify {
                        first: self.ty,
                        second: to_unify,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
            }
            ExprKind::Variable(ref name) => {
                if let Some(ty) = variables.get(name) {
                    self.ty = *ty;
                    uf.unify(*ty, to_unify).map_err(|()|
                        AstError::CouldNotUnify {
                            first: *ty,
                            second: to_unify,
                            function: function.name.clone(),
                            compiler: fl!(),
                        }
                    )
                } else if let Some(&(_, ty)) = function.args.get(name) {
                    self.ty = ty;
                    uf.unify(ty, to_unify).map_err(|()|
                        AstError::CouldNotUnify {
                            first: ty,
                            second: to_unify,
                            function: function.name.clone(),
                            compiler: fl!(),
                        }
                    )
                } else {
                    Err(AstError::UndefinedVariableName {
                        name: name.clone(),
                        function: function.name.clone(),
                    })
                }
            }
            ExprKind::Pos(ref mut inner) | ExprKind::Neg(ref mut inner)
            | ExprKind::Not(ref mut inner) => {
                try!(inner.unify_type(to_unify,
                    uf, variables, function, functions));
                let ty = self.ty;
                uf.unify(self.ty, inner.ty).map_err(|()|
                    AstError::CouldNotUnify {
                        first: ty,
                        second: inner.ty,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
            }
            ExprKind::Binop {
                op,
                ref mut lhs,
                ref mut rhs,
            } => {
                match op {
                    Operand::Mul | Operand::Div
                    | Operand::Rem | Operand::Plus
                    | Operand::Minus | Operand::Shl
                    | Operand::Shr | Operand::And
                    | Operand::Xor | Operand::Or => {
                        let ty = self.ty;
                        try!(lhs.unify_type(self.ty,
                            uf, variables, function, functions));
                        try!(rhs.unify_type(lhs.ty,
                            uf, variables, function, functions));
                        uf.unify(self.ty, to_unify).map_err(|()|
                            AstError::CouldNotUnify {
                                first: ty,
                                second: to_unify,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }

                    Operand::EqualsEquals | Operand::NotEquals
                    | Operand::LessThan | Operand::LessThanEquals
                    | Operand::GreaterThan
                    | Operand::GreaterThanEquals => {
                        self.ty = Ty::Bool;
                        rhs.ty.generate_inference_id(uf);
                        try!(lhs.unify_type(rhs.ty,
                            uf, variables, function, functions));
                        try!(rhs.unify_type(lhs.ty,
                            uf, variables, function, functions));
                        uf.unify(self.ty, to_unify).map_err(|()|
                            AstError::CouldNotUnify {
                                first: Ty::Bool,
                                second: to_unify,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }

                    Operand::AndAnd | Operand::OrOr => {
                        self.ty = Ty::Bool;
                        try!(lhs.unify_type(Ty::Bool,
                            uf, variables, function, functions));
                        try!(rhs.unify_type(Ty::Bool,
                            uf, variables, function, functions));

                        uf.unify(self.ty, to_unify).map_err(|()|
                            AstError::CouldNotUnify {
                                first: to_unify,
                                second: Ty::Bool,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }

                    Operand::Not => {
                        panic!("ICE: Not (`!`) is not a binop")
                    }
                }
            }
            ExprKind::Call {
                ref callee,
                ref mut args,
            } => {
                match functions.get(callee) {
                    Some(f) => {
                        if f.input().len() != args.len() {
                            return Err(AstError::IncorrectNumberOfArguments {
                                passed: args.len(),
                                expected: f.input().len(),
                                callee: callee.clone(),
                                caller: function.name.clone(),
                            })
                        }

                        self.ty = f.output();
                        for (arg_ty, expr) in f.input().iter().zip(args) {
                            try!(expr.unify_type(*arg_ty,
                                uf, variables, function, functions));
                        }
                        let ty = self.ty;
                        uf.unify(self.ty, to_unify).map_err(|()|
                            AstError::CouldNotUnify {
                                first: ty,
                                second: to_unify,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }
                    None => return Err(
                        AstError::FunctionDoesntExist(callee.clone()))
                }
            }
            ExprKind::If {
                ref mut condition,
                ref mut then_value,
                ref mut else_value,
            } => {
                try!(condition.unify_type(Ty::Bool,
                    uf, variables, function, functions));
                try!(Self::typeck_block(then_value,
                    to_unify, uf, variables, function, functions));
                try!(Self::typeck_block(else_value,
                    to_unify, uf, variables, function, functions));
                let ty = self.ty;
                uf.unify(self.ty, to_unify).map_err(|()|
                    AstError::CouldNotUnify {
                        first: ty,
                        second: to_unify,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
            }
            ExprKind::Block(ref mut blk) => {
                try!(Self::typeck_block(blk,
                    to_unify, uf, variables, function, functions));
                let ty = self.ty;
                uf.unify(self.ty, to_unify).map_err(|()|
                    AstError::CouldNotUnify {
                        first: ty,
                        second: to_unify,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
            }
            ExprKind::Return(ref mut ret) => {
                self.ty = Ty::Diverging;
                ret.unify_type(function.ret_ty,
                   uf, variables, function, functions)
            }
            ExprKind::Assign {
                ref mut dst,
                ref mut src,
            } => {
                debug_assert!(self.ty == Ty::Unit);
                src.ty.generate_inference_id(uf);
                try!(dst.unify_type(src.ty,
                    uf, variables, function, functions));
                try!(src.unify_type(dst.ty,
                    uf, variables, function, functions));
                uf.unify(self.ty, to_unify).map_err(|()|
                    AstError::CouldNotUnify {
                        first: Ty::Unit,
                        second: to_unify,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
            }
        }
    }

    pub fn finalize_block_ty(block: &mut Block,
            uf: &mut ty::UnionFind, function: &Function)
            -> Result<(), AstError> {
        let mut live_blk = true;

        for stmt in block.stmts.iter_mut() {
            if !live_blk {
                return Err(AstError::StatementsAfterReturn {
                    function: function.name.clone(),
                    compiler: fl!(),
                });
            }
            match *stmt {
                Stmt::Let {
                    ref mut ty,
                    ref mut value,
                    ..
                } => {
                    *ty = match uf.actual_ty(*ty) {
                        Some(t) => t,
                        None => return Err(AstError::NoActualType {
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    };
                    if let Some(ref mut v) = *value {
                        try!(v.finalize_type(uf, function));
                    }
                }
                Stmt::Expr(ref mut e @ Expr {
                    kind: ExprKind::Return(_),
                    ..
                }) => {
                    try!(e.finalize_type(uf, function));
                    live_blk = false;
                }
                Stmt::Expr(ref mut e) => {
                    try!(e.finalize_type(uf, function));
                }
            }
        }

        if let Some(ref mut expr) = block.expr {
            if !live_blk {
                return Err(AstError::StatementsAfterReturn {
                    function: function.name.clone(),
                    compiler: fl!(),
                });
            }
            try!(expr.finalize_type(uf, function));
        }
        Ok(())
    }

    pub fn finalize_type(&mut self, uf: &mut ty::UnionFind,
            function: &Function) -> Result<(), AstError> {
        match self.kind {
            ExprKind::IntLiteral(_) | ExprKind::BoolLiteral(_)
            | ExprKind::UnitLiteral | ExprKind::Variable(_) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(AstError::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                Ok(())
            }
            ExprKind::Pos(ref mut inner) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(AstError::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(inner.finalize_type(uf, function));
                assert!(self.ty == inner.ty);
                match self.ty {
                    Ty::SInt(_) | Ty::UInt(_) => Ok(()),
                    ty => {
                        Err(AstError::UnopUnsupported {
                            op: Operand::Plus,
                            inner: ty,
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    }
                }
            }
            ExprKind::Neg(ref mut inner) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(AstError::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(inner.finalize_type(uf, function));
                assert!(self.ty == inner.ty);
                match self.ty {
                    Ty::SInt(_) => Ok(()),
                    ty => {
                        Err(AstError::UnopUnsupported {
                            op: Operand::Minus,
                            inner: ty,
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    }
                }
            }
            ExprKind::Not(ref mut inner) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(AstError::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(inner.finalize_type(uf, function));
                assert!(self.ty == inner.ty);
                match self.ty {
                    Ty::SInt(_) | Ty::UInt(_) | Ty::Bool => Ok(()),
                    ty => {
                        Err(AstError::UnopUnsupported {
                            op: Operand::Not,
                            inner: ty,
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    }
                }
            }
            ExprKind::Binop {
                ref mut lhs,
                ref mut rhs,
                ..
            } => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(AstError::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(lhs.finalize_type(uf, function));
                rhs.finalize_type(uf, function)
            }
            ExprKind::Call {
                ref mut args,
                ..
            } => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None =>
                        return Err(AstError::NoActualType {
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                };
                for arg in args {
                    try!(arg.finalize_type(uf, function));
                }
                Ok(())
            }
            ExprKind::If {
                ref mut condition,
                ref mut then_value,
                ref mut else_value,
            } => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(AstError::NoActualType {
                        function: function.name.clone(),
                        compiler: fl!(),
                    })
                };
                try!(condition.finalize_type(uf, function));
                try!(Self::finalize_block_ty(then_value, uf, function));
                Self::finalize_block_ty(else_value, uf, function)
            }
            ExprKind::Block(ref mut blk) => {
                Self::finalize_block_ty(blk, uf, function)
            }
            ExprKind::Return(ref mut ret) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t @ Ty::Diverging) => t,
                    Some(t) =>
                        panic!("ICE: return is typed {:#?}; should be {:?}",
                            t, Ty::Diverging),
                    None =>
                        panic!("ICE: return with no type (should be {:?})",
                            Ty::Diverging)
                };
                ret.finalize_type(uf, function)
            }
            ExprKind::Assign {
                ref mut dst,
                ref mut src,
            } => {
                try!(dst.finalize_type(uf, function));
                src.finalize_type(uf, function)
            }
        }
    }
}

// into mir
impl Expr {
    pub fn translate(self, function: &mut Function,
            block: &mut mir::Block, fn_types: &HashMap<String, ty::Function>)
            -> mir::Value {
        assert!(self.ty.is_final_type());
        match self.kind {
            ExprKind::IntLiteral(n) => {
                mir::Value::const_int(n, self.ty)
            }
            ExprKind::BoolLiteral(b) => {
                mir::Value::const_bool(b)
            }
            ExprKind::UnitLiteral => {
                mir::Value::const_unit()
            }
            ExprKind::Pos(e) => {
                let inner = e.translate(function, block, fn_types);
                mir::Value::pos(inner, &mut function.raw, block, fn_types)
            }
            ExprKind::Neg(e) => {
                let inner = e.translate(function, block, fn_types);
                mir::Value::neg(inner, &mut function.raw, block, fn_types)
            }
            ExprKind::Not(e) => {
                let inner = e.translate(function, block, fn_types);
                mir::Value::not(inner, &mut function.raw, block, fn_types)
            }
            ExprKind::Binop {
                op,
                lhs,
                rhs,
            } => {
                let lhs = lhs.translate(function, block, fn_types);
                let rhs = rhs.translate(function, block, fn_types);
                match op {
                    Operand::Plus =>
                        mir::Value::add(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::Minus =>
                        mir::Value::sub(lhs, rhs,
                            &mut function.raw, block, fn_types),

                    Operand::Mul =>
                        mir::Value::mul(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::Div =>
                        mir::Value::div(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::Rem =>
                        mir::Value::rem(lhs, rhs,
                            &mut function.raw, block, fn_types),

                    Operand::And =>
                        mir::Value::and(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::Xor =>
                        mir::Value::xor(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::Or =>
                        mir::Value::or(lhs, rhs,
                            &mut function.raw, block, fn_types),

                    Operand::Shl =>
                        mir::Value::shl(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::Shr =>
                        mir::Value::shr(lhs, rhs,
                            &mut function.raw, block, fn_types),

                    Operand::EqualsEquals =>
                        mir::Value::eq(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::NotEquals =>
                        mir::Value::neq(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::LessThan =>
                        mir::Value::lt(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::LessThanEquals =>
                        mir::Value::lte(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::GreaterThan =>
                        mir::Value::gt(lhs, rhs,
                            &mut function.raw, block, fn_types),
                    Operand::GreaterThanEquals =>
                        mir::Value::gte(lhs, rhs,
                            &mut function.raw, block, fn_types),

                    op => panic!("unimplemented: {:?}", op),
                }
            }
            ExprKind::Call {
                callee,
                args,
            } => {
                mir::Value::call(callee,
                    args.into_iter().map(|e|
                        e.translate(function, block, fn_types)).collect(),
                    &mut function.raw, block, fn_types)
            }
            ExprKind::If {
                condition,
                then_value,
                else_value,
            } => {
                let cond = condition.translate(function, block, fn_types);
                let (mut then_blk, mut else_blk, res) =
                    block.if_else(self.ty, cond, &mut function.raw, fn_types);

                let expr = Self::translate_block(*then_value, function,
                    &mut then_blk, fn_types);
                then_blk.finish(&mut function.raw, expr);

                let expr = Self::translate_block(*else_value, function,
                    &mut else_blk, fn_types);
                else_blk.finish(&mut function.raw, expr);
                res
            }
            e => panic!("unimplemented: {:?}", e),
        }
    }

    pub fn translate_block(body: Block, function: &mut Function,
            block: &mut mir::Block, fn_types: &HashMap<String, ty::Function>)
            -> mir::Value {
        if body.stmts.len() != 0 {
            unimplemented!()
        }
        if let Some(e) = body.expr {
            e.translate(function, block, fn_types)
        }
        else {
            unimplemented!()
        }
    }
}
