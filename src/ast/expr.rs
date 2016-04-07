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
    Plus(Box<Expr>), // unary plus
    Minus(Box<Expr>), // unary minus
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
            kind: ExprKind::Minus(Box::new(inner)),
            ty: ty.unwrap_or(Ty::Infer(None)),
        }
    }

    pub fn pos(inner: Expr, ty: Option<Ty>) -> Expr {
        Expr {
            kind: ExprKind::Plus(Box::new(inner)),
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
            ExprKind::Call {..} | ExprKind::Binop {..} | ExprKind::Plus(_)
            | ExprKind::Minus(_) | ExprKind::Not(_) | ExprKind::Variable(_)
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
            ExprKind::Plus(ref mut inner) | ExprKind::Minus(ref mut inner)
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
            ExprKind::Plus(ref mut inner) => {
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
            ExprKind::Minus(ref mut inner) => {
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

impl Expr {
    pub fn translate_block(body: Block, _function: &mut mir::Function,
            _block: &mut mir::Block) -> mir::Value {
        if body.stmts.len() != 0 {
            unimplemented!()
        }
        if let Some(e) = body.expr {
            assert!(e.ty.is_final_type());
            match e.kind {
                ExprKind::IntLiteral(n) => {
                    mir::Value::const_int(n, e.ty)
                }
                _ => unimplemented!()
            }
        }
        else {
            unimplemented!()
        }
    }
}


/*
// translation
impl Expr {
    pub fn translate_out<'a>(self, out: Option<&Lvalue>,
            function: &'a Function,
            locals: &mut HashMap<String, Lvalue<'a>>,
            block: &mut mir::Block<'a>, ast: &Ast) {
        assert!(self.ty.is_final_type(), "{:?}", self.ty);
        match self.kind {
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
                }.translate_out(out, function, locals, block, ast)
            }
            ExprKind::Binop {
                op: Operand::AndAnd,
                lhs,
                rhs,
            } => {
                Expr {
                    kind: ExprKind::If {
                        condition:
                            Box::new(Expr::not(*lhs, Some(Ty::Bool))),
                        then_value:
                            Box::new(Block::expr(Expr::bool_lit(false))),
                        else_value: Box::new(Block::expr(*rhs)),
                    },
                    ty: self.ty,
                }.translate_out(out, function, locals, block, ast)
            }
            ExprKind::If {
                condition,
                then_value,
                else_value,
            } => {
                let _cond = if condition.requires_out_ptr() {
                    let cond_ptr = Lvalue::new(block, Ty::Bool, None);
                    condition.translate_out(Some(&cond_ptr),
                        function, locals, block, ast);
                    cond_ptr.read(block)
                } else {
                    condition.translate_value(function, locals, block, ast)
                };
                let mut then_blk = mir::Block::new(&function.raw);
                let mut else_blk = mir::Block::new(&function.raw);
                let join_blk = mir::Block::new(&function.raw);
                //block.conditional_branch(cond, &then_blk, &else_blk);

                let value = Self::translate_block(*then_value, self.ty,
                    function, locals, &mut then_blk, ast);
                if let Some(ptr) = out {
                    ptr.write(value, &then_blk);
                }
                //then_blk.branch(&join_blk);

                let value = Self::translate_block(*else_value, self.ty,
                    function, locals, &mut else_blk, ast);
                if let Some(ptr) = out {
                    ptr.write(value, &else_blk);
                }
                //else_blk.branch(&join_blk);

                *block = join_blk;
            }
            _ => {
                let value = self.translate_value(function, locals, block, ast);
                if let Some(ptr) = out {
                    ptr.write(value, block);
                }
            }
        }
    }

    fn translate_value<'a>(self, function: &'a Function,
            locals: &mut HashMap<String, Lvalue<'a>>,
            block: &mut mir::Block<'a>, ast: &Ast) -> Value {
        match self.kind {
            k @ ExprKind::Binop { op: Operand::AndAnd, .. }
            | k @ ExprKind::Binop { op: Operand::OrOr, .. }
            | k @ ExprKind::If { .. } => {
                panic!("ICE: this expr should be passed to \
                    translate_out: {:?}", k)
            }
            ExprKind::IntLiteral(value) => {
                Value::int_literal(self.ty, value)
            }
            ExprKind::BoolLiteral(b) => {
                Value::bool_literal(self.ty, b)
            }
            ExprKind::UnitLiteral => {
                Value::unit_literal(self.ty)
            }
            ExprKind::Variable(ref name) => {
                if let Some(val) = locals.get(name) {
                    assert!(val.ty == self.ty);
                    val.read(block)
                } else {
                    Value::parameter(self.ty, function, name)
                }
            }
            ExprKind::Block(blk) => {
                Self::translate_block(*blk, self.ty,
                    function, locals, block, ast)
            }
            ExprKind::Binop {
                op,
                lhs,
                rhs,
            } => {
                let lhs = if lhs.requires_out_ptr() {
                    let lhs_ptr = Lvalue::new(block, lhs.ty, None);
                    lhs.translate_out(Some(&lhs_ptr),
                        function, locals, block, ast);
                    lhs_ptr.read(block)
                } else {
                    lhs.translate_value(function, locals, block, ast)
                };

                let rhs = if rhs.requires_out_ptr() {
                    let rhs_ptr = Lvalue::new(block, rhs.ty, None);
                    rhs.translate_out(Some(&rhs_ptr),
                        function, locals, block, ast);
                    rhs_ptr.read(block)
                } else {
                    rhs.translate_value(function, locals, block, ast)
                };

                Value::binop(&op, lhs, rhs, block)
            }
            ExprKind::Plus(inner) => {
                if inner.requires_out_ptr() {
                    let ptr = Lvalue::new(block, inner.ty, None);
                    inner.translate_out(Some(&ptr),
                        function, locals, block, ast);
                    ptr.read(block)
                } else {
                    inner.translate_value(function, locals, block, ast)
                }
            }
            ExprKind::Minus(inner) => {
                if inner.requires_out_ptr() {
                    let ptr = Lvalue::new(block, inner.ty, None);
                    inner.translate_out(Some(&ptr),
                        function, locals, block, ast);
                    ptr.read(block).neg(block)
                } else {
                    inner.translate_value(function, locals, block, ast)
                        .neg(block)
                }
            }
            ExprKind::Not(inner) => {
                if inner.requires_out_ptr() {
                    let ptr = Lvalue::new(block, inner.ty, None);
                    inner.translate_out(Some(&ptr),
                        function, locals, block, ast);
                    ptr.read(block).not(block)
                } else {
                    inner.translate_value(function, locals, block, ast)
                        .not(block)
                }
            }
            ExprKind::Call {
                callee,
                args,
            } => {
                let mut llvm_args = Vec::new();
                for arg in args.into_iter() {
                    llvm_args.push(
                    if arg.requires_out_ptr() {
                        let ptr = Lvalue::new(block, arg.ty, None);
                        arg.translate_out(Some(&ptr),
                            function, locals, block, ast);
                        ptr.read(block)
                    } else {
                        arg.translate_value(function, locals, block, ast)
                    })
                }
                ast.call(&callee, block, llvm_args)
            }
            ExprKind::Return(expr) => {
                let ret = if expr.requires_out_ptr() {
                    let ret_ptr = Lvalue::new(block, expr.ty, Some("ret"));
                    expr.translate_out(Some(&ret_ptr),
                        function, locals, block, ast);
                    ret_ptr.read(block)
                } else {
                    expr.translate_value(function, locals, block, ast)
                };
                block.ret(ret.raw);
                Value::unit_literal(Ty::Unit) // unimportant what this is
            }
            ExprKind::Assign {
                dst,
                src,
            } => {
                let lvalue = dst.lvalue(function, locals)
                    .expect("ICE: non-lvalue expression lhs of assignment");
                src.translate_out(Some(&lvalue),
                    function, locals, block, ast);
                Value::unit_literal(Ty::Unit)
            }
        }
    }

    fn lvalue<'a>(self, _function: &Function,
            locals: &HashMap<String, Lvalue<'a>>)
            -> Option<Lvalue<'a>> {
        match self.kind {
            ExprKind::Variable(s) => {
                if let Some(lv) = locals.get(&s) {
                    Some(*lv)
                } else {
                    None
                    //lvalue::parameter(function, &s)
                }
            }
            _ => None
        }
    }

    pub fn translate_block<'a>(body: Block, _blk_ty: Ty,
            function: &'a Function, locals: &mut HashMap<String, Lvalue<'a>>,
            block: &mut mir::Block<'a>, ast: &Ast) -> Value {
        let _locals_at_start = locals.clone();
        for st in body.stmts {
            match st {
                Stmt::Let {
                    name,
                    ty,
                    value,
                } => {
                    let local = Lvalue::new(block, ty, Some(&name));
                    if let Some(v) = value {
                        v.translate_out(Some(&local),
                            function, locals, block, ast);
                    }
                    locals.insert(name, local);
                }
                Stmt::Expr(e) => {
                    e.translate_out(None, function, locals, block, ast);
                }
            }
        }
        Value::unit_literal(Ty::Unit)

        /*
        if block.is_live() {
            if let Some(e) = body.1 {
                let ret = if e.requires_out_ptr() {
                    let ret_ptr = lvalue::new(&block, blk_ty, Some("ret"));
                    e.translate_out(Some(&ret_ptr),
                        function, locals, block, ast);
                    ret_ptr.read(&block)
                } else {
                    e.translate_value(function, locals, block, ast)
                };
                ret
            } else {
                *locals = locals_at_start;
                value::undef(blk_ty)
            }
        } else {
            *locals = locals_at_start;
            value::unit_literal(ty::Unit)
        }
        */
    }

    fn requires_out_ptr(&self) -> bool {
        match self.kind {
            ExprKind::Binop { op: Operand::OrOr, .. }
            | ExprKind::Binop { op: Operand::AndAnd, .. }
            | ExprKind::If { .. } => {
                true
            }
            _ => false
        }
    }
}
*/


