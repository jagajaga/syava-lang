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
        dst: String,
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

    pub fn assign(dst: String, src: Expr) -> Expr {
        Expr {
            kind: ExprKind::Assign {
                dst: dst,
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
                        compiler: fl!(),
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
                ref dst,
                ref mut src,
            } => {
                debug_assert!(self.ty == Ty::Unit);
                if let Some(&ty) = variables.get(dst) {
                    try!(src.unify_type(ty,
                        uf, variables, function, functions));
                    uf.unify(self.ty, to_unify).map_err(|()|
                        AstError::CouldNotUnify {
                            first: Ty::Unit,
                            second: to_unify,
                            function: function.name.clone(),
                            compiler: fl!(),
                        }
                    )
                } else {
                    Err(AstError::UndefinedVariableName {
                        name: dst.clone(),
                        function: function.name.clone(),
                        compiler: fl!(),
                    })
                }
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
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(AstError::NoActualType {
                        function: function.name.clone(),
                        compiler: fl!(),
                    })
                };
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
                ref mut src,
                ..
            } => {
                src.finalize_type(uf, function)
            }
        }
    }
}

// into mir
impl Expr {
    pub fn translate(self, function: &mut Function,
            mut block: mir::Block,
            locals: &mut HashMap<String, mir::Variable>,
            fn_types: &HashMap<String, ty::Function>)
            -> (mir::Value, Option<mir::Block>) {
        assert!(self.ty.is_final_type(), "not final type: {:?}", self);
        match self.kind {
            ExprKind::IntLiteral(n) => {
                (mir::Value::const_int(n, self.ty), Some(block))
            }
            ExprKind::BoolLiteral(b) => {
                (mir::Value::const_bool(b), Some(block))
            }
            ExprKind::UnitLiteral => {
                (mir::Value::const_unit(), Some(block))
            }
            ExprKind::Variable(name) => {
                if let Some(var) = locals.get(&name) {
                    (mir::Value::local(*var), Some(block))
                } else if let Some(&(num, _)) = function.args.get(&name) {
                    (mir::Value::param(num as u32, &mut function.raw),
                        Some(block))
                } else {
                    panic!("ICE: unknown variable: {}", name)
                }
            }
            ExprKind::Pos(e) => {
                let (inner, blk) =
                    e.translate(function, block, locals, fn_types);
                if let Some(mut blk) = blk {
                    (mir::Value::pos(inner, &mut function.raw, &mut blk,
                        fn_types), Some(blk))
                } else {
                    (mir::Value::const_unit(), None)
                }
            }
            ExprKind::Neg(e) => {
                let (inner, blk) =
                    e.translate(function, block, locals, fn_types);
                if let Some(mut blk) = blk {
                    (mir::Value::neg(inner, &mut function.raw, &mut blk,
                        fn_types), Some(blk))
                } else {
                    (mir::Value::const_unit(), None)
                }
            }
            ExprKind::Not(e) => {
                let (inner, blk) =
                    e.translate(function, block, locals, fn_types);
                if let Some(mut blk) = blk {
                    (mir::Value::not(inner, &mut function.raw, &mut blk,
                        fn_types), Some(blk))
                } else {
                    (mir::Value::const_unit(), None)
                }
            }
            ExprKind::Binop {
                op: Operand::AndAnd,
                lhs,
                rhs,
            } => {
                Expr {
                    kind: ExprKind::If {
                        condition: Box::new(Expr::not(*lhs, Some(Ty::Bool))),
                        then_value:
                            Box::new(Block::expr(Expr::bool_lit(false))),
                        else_value: Box::new(Block::expr(*rhs)),
                    },
                    ty: self.ty,
                }.translate(function, block, locals, fn_types)
            }
            ExprKind::Binop {
                op: Operand::OrOr,
                lhs,
                rhs,
            } => {
                Expr {
                    kind: ExprKind::If {
                        condition: lhs,
                        then_value:
                            Box::new(Block::expr(Expr::bool_lit(true))),
                        else_value: Box::new(Block::expr(*rhs)),
                    },
                    ty: self.ty,
                }.translate(function, block, locals, fn_types)
            }
            ExprKind::Binop {
                op,
                lhs,
                rhs,
            } => {
                let (lhs, blk) = {
                    let (lhs, blk) =
                        lhs.translate(function, block, locals, fn_types);
                    if let Some(blk) = blk {
                        (lhs, blk)
                    } else {
                        return (lhs, None);
                    }
                };
                let (rhs, mut blk) = {
                    let (rhs, blk) =
                        rhs.translate(function, blk, locals, fn_types);
                    if let Some(blk) = blk {
                        (rhs, blk)
                    } else {
                        return (rhs, None);
                    }
                };
                (match op {
                    Operand::Plus =>
                        mir::Value::add(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::Minus =>
                        mir::Value::sub(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),

                    Operand::Mul =>
                        mir::Value::mul(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::Div =>
                        mir::Value::div(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::Rem =>
                        mir::Value::rem(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),

                    Operand::And =>
                        mir::Value::and(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::Xor =>
                        mir::Value::xor(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::Or =>
                        mir::Value::or(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),

                    Operand::Shl =>
                        mir::Value::shl(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::Shr =>
                        mir::Value::shr(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),

                    Operand::EqualsEquals =>
                        mir::Value::eq(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::NotEquals =>
                        mir::Value::neq(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::LessThan =>
                        mir::Value::lt(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::LessThanEquals =>
                        mir::Value::lte(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::GreaterThan =>
                        mir::Value::gt(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),
                    Operand::GreaterThanEquals =>
                        mir::Value::gte(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types),

                    Operand::AndAnd => unreachable!(),
                    Operand::OrOr => unreachable!(),
                    Operand::Not => panic!("ICE: Not (`!`) is not a binop"),
                }, Some(blk))
            }
            ExprKind::Call {
                callee,
                args,
            } => {
                let mut mir_args = Vec::new();
                for arg in args {
                    let (arg, blk) = arg.translate(function, block, locals,
                        fn_types);
                    if let Some(blk) = blk {
                        block = blk;
                    } else {
                        return (mir::Value::const_unit(), None);
                    }
                    mir_args.push(arg);
                }
                (mir::Value::call(callee, mir_args,
                    &mut function.raw, &mut block, fn_types), Some(block))
            }
            ExprKind::If {
                condition,
                then_value,
                else_value,
            } => {
                let (cond, blk) = condition.translate(function, block,
                    locals, fn_types);
                let (then_blk, else_blk, join, res) = if let Some(blk) = blk {
                    blk.if_else(self.ty, cond, &mut function.raw, fn_types)
                } else {
                    return (mir::Value::const_unit(), None);
                };

                let (expr, then_blk) = Self::translate_block(*then_value,
                    function, then_blk, locals, fn_types);
                if let Some(then_blk) = then_blk {
                    then_blk.finish(&mut function.raw, expr);
                }

                let (expr, else_blk) = Self::translate_block(*else_value, function,
                    else_blk, locals, fn_types);
                if let Some(else_blk) = else_blk {
                    else_blk.finish(&mut function.raw, expr);
                }
                (res, Some(join))
            }
            ExprKind::Return(ret) => {
                let (value, block) = ret.translate(function, block, locals,
                    fn_types);
                if let Some(block) = block {
                    block.early_ret(&mut function.raw, value);
                }
                (mir::Value::const_unit(), None)
            }
            ExprKind::Assign {
                dst,
                src,
            } => {
                let var = if let Some(var) = locals.get(&dst) {
                    *var
                } else if let Some(&(num, _)) = function.args.get(&dst) {
                    function.raw.get_param(num as u32)
                } else {
                    panic!("ICE: unknown variable: {}", dst)
                };
                let (value, mut blk) =
                    src.translate(function, block, locals, fn_types);
                if let Some(ref mut blk) = blk {
                    blk.write_to_var(var, value, &mut function.raw)
                }
                (mir::Value::const_unit(), blk)
            }
            ExprKind::Block(body) => {
                Self::translate_block(*body, function, block, locals,
                    fn_types)
            }
        }
    }

    pub fn translate_block(body: Block, function: &mut Function,
            block: mir::Block,
            locals: &mut HashMap<String, mir::Variable>,
            fn_types: &HashMap<String, ty::Function>)
            -> (mir::Value, Option<mir::Block>) {
        let mut block = Some(block);
        for stmt in body.stmts {
            if let Some(blk) = block.take() {
                match stmt {
                    Stmt::Let {
                        name,
                        ty,
                        value,
                    } => {
                        let var = function.raw.new_local(ty);
                        locals.insert(name, var);
                        if let Some(value) = value {
                            let (value, blk) =
                                value.translate(function, blk,
                                    locals, fn_types);
                            if let Some(mut blk) = blk {
                                blk.write_to_var(var, value,
                                    &mut function.raw);
                                block = Some(blk);
                            }
                        } else {
                            block = Some(blk);
                        }
                    }
                    Stmt::Expr(e) => {
                        let (value, blk) = e.translate(function, blk,
                            locals, fn_types);
                        if let Some(mut blk) = blk {
                            blk.write_to_tmp(value,
                                &mut function.raw, fn_types);
                            block = Some(blk);
                        }
                    }
                }
            } else {
                break;
            }
        }
        if let Some(e) = body.expr {
            if let Some(blk) = block {
                e.translate(function, blk, locals, fn_types)
            } else {
                (mir::Value::const_unit(), None)
            }
        } else {
            (mir::Value::const_unit(), block)
        }
    }
}
