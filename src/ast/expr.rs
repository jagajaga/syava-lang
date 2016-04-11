use ast::{AstError, Block, Function};
use std::collections::HashMap;
use ty::{self, TypeContext, Type, TypeVariant};
use parse::Operand;
use mir;

#[derive(Debug)]
pub enum Stmt<'t> {
    Let {
        name: String,
        ty: Type<'t>,
        value: Option<Box<Expr<'t>>>,
    },
    Expr(Expr<'t>),
}

#[derive(Debug)]
pub enum ExprKind<'t> {
    Call {
        callee: String,
        args: Vec<Expr<'t>>
    },
    If {
        condition: Box<Expr<'t>>,
        then_value: Box<Block<'t>>,
        else_value: Box<Block<'t>>,
    },
    Block(Box<Block<'t>>),
    Binop {
        op: Operand,
        lhs: Box<Expr<'t>>,
        rhs: Box<Expr<'t>>,
    },
    Pos(Box<Expr<'t>>), // unary plus
    Neg(Box<Expr<'t>>), // unary minus
    Not(Box<Expr<'t>>), // !expr
    Ref(Box<Expr<'t>>), // &expr
    Variable(String),
    IntLiteral(u64),
    BoolLiteral(bool),
    UnitLiteral,
    Return(Box<Expr<'t>>),
    Assign {
        dst: String,
        src: Box<Expr<'t>>
    },
}

#[derive(Debug)]
pub struct Expr<'t> {
    pub kind: ExprKind<'t>,
    pub ty: Type<'t>,
}

// constructors
impl<'t> Expr<'t> {
    pub fn call(callee: String, args: Vec<Expr<'t>>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::Call {
                callee: callee,
                args: args,
            },
            ty: Type::infer(ctxt),
        }
    }

    pub fn var(name: String, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::Variable(name),
            ty: Type::infer(ctxt),
        }
    }

    pub fn if_else(cond: Expr<'t>, then: Block<'t>, else_: Block<'t>,
            ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::If {
                condition: Box::new(cond),
                then_value: Box::new(then),
                else_value: Box::new(else_),
            },
            ty: Type::infer(ctxt),
        }
    }

    pub fn block(inner: Block<'t>, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::Block(Box::new(inner)),
            ty: Type::infer(ctxt),
        }
    }

    pub fn int_lit(value: u64, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::IntLiteral(value),
            ty: Type::infer_int(ctxt),
        }
    }

    pub fn int_lit_with_ty(value: u64, ty: Type<'t>) -> Self {
        Expr {
            kind: ExprKind::IntLiteral(value),
            ty: ty,
        }
    }

    pub fn bool_lit(value: bool, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::BoolLiteral(value),
            ty: Type::bool(ctxt),
        }
    }

    pub fn unit_lit(ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::UnitLiteral,
            ty: Type::unit(ctxt),
        }
    }

    pub fn neg(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::Neg(Box::new(inner)),
            ty: Type::infer(ctxt),
        }
    }

    pub fn pos(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::Pos(Box::new(inner)),
            ty: Type::infer(ctxt),
        }
    }

    pub fn not(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::Not(Box::new(inner)),
            ty: Type::infer(ctxt),
        }
    }

    pub fn ref_(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::Ref(Box::new(inner)),
            ty: Type::ref_(Type::infer(ctxt)),
        }
    }

    pub fn ret(ret: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
        Expr {
            kind: ExprKind::Return(Box::new(ret)),
            ty: Type::diverging(ctxt),
        }
    }

    pub fn assign(dst: String, src: Expr<'t>, ctxt: &'t TypeContext<'t>)
            -> Self {
        Expr {
            kind: ExprKind::Assign {
                dst: dst,
                src: Box::new(src),
            },
            ty: Type::unit(ctxt),
        }
    }
}

// parsing
impl<'t> Expr<'t> {
    pub fn is_block(&self) -> bool {
        match self.kind {
            ExprKind::If {..} | ExprKind::Block(_) => true,
            ExprKind::Call {..} | ExprKind::Binop {..} | ExprKind::Pos(_)
            | ExprKind::Neg(_) | ExprKind::Not(_) | ExprKind::Ref(_)
            | ExprKind::Variable(_) | ExprKind::IntLiteral(_)
            | ExprKind::BoolLiteral(_) | ExprKind::UnitLiteral
            | ExprKind::Return(_) | ExprKind::Assign {..} => false,
        }
    }
}

// typechecking
impl<'t> Expr<'t> {
    pub fn typeck_block(block: &mut Block<'t>,
            ctxt: &'t TypeContext<'t>,
            to_unify: Type<'t>, uf: &mut ty::UnionFind<'t>,
            variables: &mut HashMap<String, Type<'t>>,
            function: &Function<'t>,
            functions: &HashMap<String, ty::Function<'t>>)
            -> Result<(), AstError<'t>> {
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
                            ctxt, *ty, uf, variables, function, functions));
                    }
                    variables.insert(name.to_owned(), *ty);
                }
                Stmt::Expr(ref mut e @ Expr {
                    kind: ExprKind::Return(_),
                    ..
                }) => {
                    try!(e.unify_type(ctxt, Type::diverging(ctxt),
                        uf, variables, function, functions));
                    live_blk = false;
                    break;
                }
                Stmt::Expr(ref mut e) => {
                    let mut ty = Type::infer(ctxt);
                    ty.generate_inference_id(uf);
                    try!(e.unify_type(ctxt, ty, uf, variables,
                        function, functions));
                }
            }
        }
        if live_blk {
            match block.expr {
                Some(ref mut expr) => {
                    try!(expr.unify_type(ctxt, to_unify,
                        uf, variables, function, functions))
                },
                None => {
                    try!(uf.unify(to_unify, Type::unit(ctxt))
                        .map_err(|()| AstError::CouldNotUnify {
                            first: Type::unit(ctxt),
                            second: to_unify,
                            function: function.name.clone(),
                            compiler: fl!(),
                        }
                    ))
                },
            };
        }
        Ok(())
    }

    pub fn unify_type(&mut self, ctxt: &'t TypeContext<'t>,
            to_unify: Type<'t>, uf: &mut ty::UnionFind<'t>,
            variables: &mut HashMap<String, Type<'t>>,
            function: &Function<'t>,
            functions: &HashMap<String, ty::Function<'t>>)
            -> Result<(), AstError<'t>> {
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
                try!(inner.unify_type(ctxt, to_unify,
                        uf, variables, function, functions));
                let self_ty = self.ty;
                let inner_ty = inner.ty;
                uf.unify(self.ty, inner.ty).map_err(|()|
                    AstError::CouldNotUnify {
                        first: self_ty,
                        second: inner_ty,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
            }
            ExprKind::Ref(ref mut inner) => {
                if let TypeVariant::Reference(to_unify) = *to_unify.variant {
                    try!(inner.unify_type(ctxt, to_unify,
                        uf, variables, function, functions));
                } else {
                    return Err(AstError::CouldNotUnify {
                        first: to_unify,
                        second: inner.ty,
                        function: function.name.clone(),
                        compiler: fl!(),
                    });
                }

                Ok(uf.unify(self.ty, Type::ref_(inner.ty))
                    .expect("These should never be different"))
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
                        try!(lhs.unify_type(ctxt, self.ty,
                            uf, variables, function, functions));
                        try!(rhs.unify_type(ctxt, lhs.ty,
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
                        self.ty = Type::bool(ctxt);
                        rhs.ty.generate_inference_id(uf);
                        try!(lhs.unify_type(ctxt, rhs.ty,
                            uf, variables, function, functions));
                        try!(rhs.unify_type(ctxt, lhs.ty,
                            uf, variables, function, functions));
                        uf.unify(self.ty, to_unify).map_err(|()|
                            AstError::CouldNotUnify {
                                first: Type::bool(ctxt),
                                second: to_unify,
                                function: function.name.clone(),
                                compiler: fl!(),
                            }
                        )
                    }

                    Operand::AndAnd | Operand::OrOr => {
                        self.ty = Type::bool(ctxt);
                        try!(lhs.unify_type(ctxt, Type::bool(ctxt),
                            uf, variables, function, functions));
                        try!(rhs.unify_type(ctxt, Type::bool(ctxt),
                            uf, variables, function, functions));

                        uf.unify(self.ty, to_unify).map_err(|()|
                            AstError::CouldNotUnify {
                                first: to_unify,
                                second: Type::bool(ctxt),
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
                            try!(expr.unify_type(ctxt, *arg_ty,
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
                try!(condition.unify_type(ctxt, Type::bool(ctxt),
                    uf, variables, function, functions));
                try!(Self::typeck_block(then_value, ctxt,
                    to_unify, uf, variables, function, functions));
                try!(Self::typeck_block(else_value, ctxt,
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
                try!(Self::typeck_block(blk, ctxt,
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
                self.ty = Type::diverging(ctxt);
                ret.unify_type(ctxt, function.ret_ty,
                   uf, variables, function, functions)
            }
            ExprKind::Assign {
                ref dst,
                ref mut src,
            } => {
                debug_assert!(self.ty == Type::unit(ctxt));
                if let Some(&ty) = variables.get(dst) {
                    try!(src.unify_type(ctxt, ty,
                        uf, variables, function, functions));
                    uf.unify(self.ty, to_unify).map_err(|()|
                        AstError::CouldNotUnify {
                            first: Type::unit(ctxt),
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

    pub fn finalize_block_ty(block: &mut Block<'t>,
            uf: &mut ty::UnionFind<'t>, function: &Function<'t>)
            -> Result<(), AstError<'t>> {
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

    pub fn finalize_type(&mut self, uf: &mut ty::UnionFind<'t>,
            function: &Function<'t>) -> Result<(), AstError<'t>> {
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
                match *self.ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) => Ok(()),
                    _ => {
                        Err(AstError::UnopUnsupported {
                            op: Operand::Plus,
                            inner: self.ty,
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
                match *self.ty.variant {
                    TypeVariant::SInt(_) => Ok(()),
                    _ => {
                        Err(AstError::UnopUnsupported {
                            op: Operand::Minus,
                            inner: self.ty,
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
                match *self.ty.variant {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool => Ok(()),
                    _ => {
                        Err(AstError::UnopUnsupported {
                            op: Operand::Not,
                            inner: self.ty,
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    }
                }
            }
            ExprKind::Ref(ref mut inner) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(AstError::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(inner.finalize_type(uf, function));
                assert!(self.ty == Type::ref_(inner.ty),
                    "self: {}, inner: &{}", self.ty, inner.ty);
                Ok(())
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
                    Some(t @ Type { variant: &TypeVariant::Diverging, .. }) => t,
                    Some(t) =>
                        panic!("ICE: return is typed {:#?}; should be {:?}",
                            t, TypeVariant::Diverging),
                    None =>
                        panic!("ICE: return with no type (should be {:?})",
                            TypeVariant::Diverging)
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
impl<'t> Expr<'t> {
    pub fn translate(self, function: &mut Function<'t>,
            mut block: mir::Block,
            locals: &mut HashMap<String, mir::Variable>,
            fn_types: &HashMap<String, ty::Function<'t>>,
            ctxt: &'t TypeContext<'t>)
            -> (mir::Value<'t>, Option<mir::Block>) {
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
                    e.translate(function, block, locals, fn_types, ctxt);
                if let Some(mut blk) = blk {
                    (mir::Value::pos(inner, &mut function.raw, &mut blk,
                        fn_types, ctxt), Some(blk))
                } else {
                    (mir::Value::const_unit(), None)
                }
            }
            ExprKind::Neg(e) => {
                let (inner, blk) =
                    e.translate(function, block, locals, fn_types, ctxt);
                if let Some(mut blk) = blk {
                    (mir::Value::neg(inner, &mut function.raw, &mut blk,
                        fn_types, ctxt), Some(blk))
                } else {
                    (mir::Value::const_unit(), None)
                }
            }
            ExprKind::Not(e) => {
                let (inner, blk) =
                    e.translate(function, block, locals, fn_types, ctxt);
                if let Some(mut blk) = blk {
                    (mir::Value::not(inner, &mut function.raw, &mut blk,
                        fn_types, ctxt), Some(blk))
                } else {
                    (mir::Value::const_unit(), None)
                }
            }
            ExprKind::Ref(e) => {
                let (inner, blk) =
                    e.translate(function, block, locals, fn_types, ctxt);
                if let Some(mut blk) = blk {
                    (mir::Value::ref_(inner, &mut function.raw, &mut blk,
                        fn_types, ctxt),
                    Some(blk))
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
                        condition: Box::new(Expr::not(*lhs, ctxt)),
                        then_value:
                            Box::new(Block::expr(Expr::bool_lit(false, ctxt))),
                        else_value: Box::new(Block::expr(*rhs)),
                    },
                    ty: self.ty,
                }.translate(function, block, locals, fn_types, ctxt)
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
                            Box::new(Block::expr(Expr::bool_lit(true, ctxt))),
                        else_value: Box::new(Block::expr(*rhs)),
                    },
                    ty: self.ty,
                }.translate(function, block, locals, fn_types, ctxt)
            }
            ExprKind::Binop {
                op,
                lhs,
                rhs,
            } => {
                let (lhs, blk) = {
                    let (lhs, blk) =
                        lhs.translate(function, block, locals, fn_types, ctxt);
                    if let Some(blk) = blk {
                        (lhs, blk)
                    } else {
                        return (lhs, None);
                    }
                };
                let (rhs, mut blk) = {
                    let (rhs, blk) =
                        rhs.translate(function, blk, locals, fn_types, ctxt);
                    if let Some(blk) = blk {
                        (rhs, blk)
                    } else {
                        return (rhs, None);
                    }
                };
                (match op {
                    Operand::Plus =>
                        mir::Value::add(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::Minus =>
                        mir::Value::sub(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),

                    Operand::Mul =>
                        mir::Value::mul(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::Div =>
                        mir::Value::div(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::Rem =>
                        mir::Value::rem(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),

                    Operand::And =>
                        mir::Value::and(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::Xor =>
                        mir::Value::xor(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::Or =>
                        mir::Value::or(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),

                    Operand::Shl =>
                        mir::Value::shl(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::Shr =>
                        mir::Value::shr(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),

                    Operand::EqualsEquals =>
                        mir::Value::eq(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::NotEquals =>
                        mir::Value::neq(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::LessThan =>
                        mir::Value::lt(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::LessThanEquals =>
                        mir::Value::lte(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::GreaterThan =>
                        mir::Value::gt(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),
                    Operand::GreaterThanEquals =>
                        mir::Value::gte(lhs, rhs,
                            &mut function.raw, &mut blk, fn_types, ctxt),

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
                        fn_types, ctxt);
                    if let Some(blk) = blk {
                        block = blk;
                    } else {
                        return (mir::Value::const_unit(), None);
                    }
                    mir_args.push(arg);
                }
                (mir::Value::call(callee, mir_args,
                    &mut function.raw, &mut block, fn_types, ctxt),
                Some(block))
            }
            ExprKind::If {
                condition,
                then_value,
                else_value,
            } => {
                let (cond, blk) = condition.translate(function, block,
                    locals, fn_types, ctxt);
                let (then_blk, else_blk, join, res) = if let Some(blk) = blk {
                    blk.if_else(self.ty, cond, &mut function.raw, fn_types,
                        ctxt)
                } else {
                    return (mir::Value::const_unit(), None);
                };

                let (expr, then_blk) = Self::translate_block(*then_value, ctxt,
                    function, then_blk, locals, fn_types);
                if let Some(then_blk) = then_blk {
                    then_blk.finish(&mut function.raw, expr);
                }

                let (expr, else_blk) = Self::translate_block(*else_value, ctxt,
                    function, else_blk, locals, fn_types);
                if let Some(else_blk) = else_blk {
                    else_blk.finish(&mut function.raw, expr);
                }
                (res, Some(join))
            }
            ExprKind::Return(ret) => {
                let (value, block) = ret.translate(function, block, locals,
                    fn_types, ctxt);
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
                    src.translate(function, block, locals, fn_types, ctxt);
                if let Some(ref mut blk) = blk {
                    blk.write_to_var(var, value, &mut function.raw)
                }
                (mir::Value::const_unit(), blk)
            }
            ExprKind::Block(body) => {
                Self::translate_block(*body, ctxt, function, block, locals,
                    fn_types)
            }
        }
    }

    pub fn translate_block(body: Block<'t>, ctxt: &'t TypeContext<'t>,
            function: &mut Function<'t>, block: mir::Block,
            locals: &mut HashMap<String, mir::Variable>,
            fn_types: &HashMap<String, ty::Function<'t>>)
            -> (mir::Value<'t>, Option<mir::Block>) {
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
                                    locals, fn_types, ctxt);
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
                            locals, fn_types, ctxt);
                        if let Some(mut blk) = blk {
                            blk.write_to_tmp(value,
                                &mut function.raw, fn_types,
                                ctxt);
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
                e.translate(function, blk, locals, fn_types, ctxt)
            } else {
                (mir::Value::const_unit(), None)
            }
        } else {
            (mir::Value::const_unit(), block)
        }
    }
}