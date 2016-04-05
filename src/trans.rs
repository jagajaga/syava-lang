use std;
use std::collections::HashMap;
use std::ffi::{CString, CStr};
use parse::{lexer, operand, parser, parser_error};
use ty::{ty, int, union_find};

use llvm_sys::LLVMIntPredicate;
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
        then_value: (Vec<stmt>, Option<Box<expr>>),
        else_value: (Vec<stmt>, Option<Box<expr>>),
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
    fn translate_out<'a>(self, out: Option<&lvalue>, function: &'a function,
            locals: &mut HashMap<String, lvalue<'a>>, block: &mut block<'a>, ast: &ast) {
        assert!(self.ty.is_final_type(), "{:?}", self.ty);
        match self.kind {
            expr_kind::Binop {
                op: operand::OrOr,
                lhs,
                rhs,
            } => {
                expr {
                    kind: expr_kind::If {
                        condition: lhs,
                        then_value: (vec![], Some(Box::new(expr::bool_lit(true)))),
                        else_value: (vec![], Some(rhs)),
                    },
                    ty: self.ty,
                }.translate_out(out, function, locals, block, ast)
            }
            expr_kind::Binop {
                op: operand::AndAnd,
                lhs,
                rhs,
            } => {
                expr {
                    kind: expr_kind::If {
                        condition: Box::new(expr::not(*lhs, Some(ty::Bool))),
                        then_value: (vec![], Some(Box::new(expr::bool_lit(false)))),
                        else_value: (vec![], Some(rhs)),
                    },
                    ty: self.ty,
                }.translate_out(out, function, locals, block, ast)
            }
            expr_kind::If {
                condition,
                then_value,
                else_value,
            } => {
                let cond = if condition.requires_out_ptr() {
                    let cond_ptr = lvalue::new(block, ty::Bool, None);
                    condition.translate_out(Some(&cond_ptr), function, locals, block, ast);
                    cond_ptr.read(block)
                } else {
                    condition.translate_value(function, locals, block, ast)
                };
                if block.is_live() {
                    let mut then_blk = block::new(function, "then");
                    let mut else_blk = block::new(function, "else");
                    let join_blk = block::new(function, "join");
                    block.conditional_branch(cond, &then_blk, &else_blk);

                    let value = Self::translate_block(then_value, self.ty, function,
                        locals, &mut then_blk, ast);
                    if let Some(ptr) = out {
                        ptr.write(value, &then_blk);
                    }
                    then_blk.branch(&join_blk);

                    let value = Self::translate_block(else_value, self.ty, function,
                        locals, &mut else_blk, ast);
                    if let Some(ptr) = out {
                        ptr.write(value, &else_blk);
                    }
                    else_blk.branch(&join_blk);

                    *block = join_blk;
                }
            }
            _ => {
                let value = self.translate_value(function, locals, block, ast);
                if let Some(ptr) = out {
                    ptr.write(value, block);
                }
            }
        }
    }

    fn translate_value<'a>(self, function: &'a function,
            locals: &mut HashMap<String, lvalue<'a>>, block: &mut block<'a>, ast: &ast) -> value {
        match self.kind {
            k @ expr_kind::Binop { op: operand::AndAnd, .. }
            | k @ expr_kind::Binop { op: operand::OrOr, .. }
            | k @ expr_kind::If { .. } => {
                panic!("ICE: this expr should be passed to translate_out: {:?}", k)
            }
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
                    val.read(block)
                } else {
                    value::parameter(self.ty, function, name)
                }
            }
            expr_kind::Binop {
                op,
                lhs,
                rhs,
            } => {
                let lhs = if lhs.requires_out_ptr() {
                    let lhs_ptr = lvalue::new(block, lhs.ty, None);
                    lhs.translate_out(Some(&lhs_ptr), function, locals, block, ast);
                    lhs_ptr.read(block)
                } else {
                    lhs.translate_value(function, locals, block, ast)
                };

                let rhs = if rhs.requires_out_ptr() {
                    let rhs_ptr = lvalue::new(block, rhs.ty, None);
                    rhs.translate_out(Some(&rhs_ptr), function, locals, block, ast);
                    rhs_ptr.read(block)
                } else {
                    rhs.translate_value(function, locals, block, ast)
                };

                value::binop(&op, lhs, rhs, block)
            }
            expr_kind::Plus(inner) => {
                if inner.requires_out_ptr() {
                    let ptr = lvalue::new(block, inner.ty, None);
                    inner.translate_out(Some(&ptr), function, locals, block, ast);
                    ptr.read(block)
                } else {
                    inner.translate_value(function, locals, block, ast)
                }
            }
            expr_kind::Minus(inner) => {
                if inner.requires_out_ptr() {
                    let ptr = lvalue::new(block, inner.ty, None);
                    inner.translate_out(Some(&ptr), function, locals, block, ast);
                    ptr.read(block).neg(block)
                } else {
                    inner.translate_value(function, locals, block, ast).neg(block)
                }
            }
            expr_kind::Not(inner) => {
                if inner.requires_out_ptr() {
                    let ptr = lvalue::new(block, inner.ty, None);
                    inner.translate_out(Some(&ptr), function, locals, block, ast);
                    ptr.read(block).not(block)
                } else {
                    inner.translate_value(function, locals, block, ast).not(block)
                }
            }
            expr_kind::Call {
                callee,
                args,
            } => {
                let mut llvm_args = Vec::new();
                for arg in args.into_iter() {
                    llvm_args.push(
                    if arg.requires_out_ptr() {
                        let ptr = lvalue::new(block, arg.ty, None);
                        arg.translate_out(Some(&ptr), function, locals, block, ast);
                        ptr.read(block)
                    } else {
                        arg.translate_value(function, locals, block, ast)
                    })
                }
                ast.call(&callee, block, llvm_args)
            }
            expr_kind::Return(expr) => {
                let ret = if expr.requires_out_ptr() {
                    let ret_ptr = lvalue::new(block, expr.ty, Some("ret"));
                    expr.translate_out(Some(&ret_ptr), function, locals, block, ast);
                    ret_ptr.read(block)
                } else {
                    expr.translate_value(function, locals, block, ast)
                };
                if block.is_live() {
                    block.ret(ret);
                }
                value::unit_literal(ty::Unit) // unimportant what this is
            }
        }
    }

    fn translate_block<'a>(body: (Vec<stmt>, Option<Box<expr>>), blk_ty: ty,
            function: &'a function, locals: &mut HashMap<String, lvalue<'a>>, block: &mut block<'a>,
            ast: &ast) -> value {
        let locals_at_start = locals.clone();
        for st in body.0 {
            match st {
                stmt::Let {
                    name,
                    ty,
                    value,
                } => {
                    let local = lvalue::new(block, ty, Some(&name));
                    value.translate_out(Some(&local), function, locals, block, ast);
                    locals.insert(name, local);
                }
                stmt::Expr(e) => {
                    e.translate_out(None, function, locals, block, ast);
                    if !block.is_live() {
                        break;
                    }
                }
            }
        }

        if block.is_live() {
            if let Some(e) = body.1 {
                let ret = if e.requires_out_ptr() {
                    let ret_ptr = lvalue::new(&block, blk_ty, Some("ret"));
                    e.translate_out(Some(&ret_ptr), function, locals, block, ast);
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
    }

    fn requires_out_ptr(&self) -> bool {
        match self.kind {
            expr_kind::Binop { op: operand::OrOr, .. }
            | expr_kind::Binop { op: operand::AndAnd, .. }
            | expr_kind::If { .. } => {
                true
            }
            _ => false
        }
    }

    fn typeck_block(block: (&mut Vec<stmt>, &mut Option<Box<expr>>), to_unify: ty,
            uf: &mut union_find, variables: &mut HashMap<String, ty>,
            function: &function, functions: &HashMap<String, function>)
            -> Result<(), ast_error> {
        let mut live_blk = true;
        for stmt in block.0.iter_mut() {
            match *stmt {
                stmt::Let {
                    ref name,
                    ref mut ty,
                    ref mut value,
                } => {
                    ty.generate_inference_id(uf);
                    try!(value.unify_type(*ty, uf, variables, function, functions));
                    variables.insert(name.to_owned(), *ty);
                }
                stmt::Expr(ref mut e @ expr {
                    kind: expr_kind::Return(_),
                    ..
                }) => {
                    try!(e.unify_type(ty::Diverging, uf, variables, function, functions));
                    live_blk = false;
                    break;
                }
                stmt::Expr(ref mut e) => {
                    let mut ty = ty::Infer(None);
                    ty.generate_inference_id(uf);
                    try!(e.unify_type(ty, uf, variables, function, functions));
                }
            }
        }
        if live_blk {
            match *block.1 {
                Some(ref mut expr) => {
                    try!(expr.unify_type(to_unify, uf, variables, function, functions));
                },
                None => {
                    if to_unify != ty::Unit {
                        return Err(ast_error::CouldNotUnify {
                            first: ty::Unit,
                            second: to_unify,
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    }
                },
            }
        }
        Ok(())
    }

    fn finalize_block_ty(block: (&mut Vec<stmt>, &mut Option<Box<expr>>), uf: &mut union_find,
            function: &function) -> Result<(), ast_error> {
        let mut live_blk = true;

        for stmt in block.0.iter_mut() {
            if !live_blk {
                return Err(ast_error::StatementsAfterReturn {
                    function: function.name.clone(),
                    compiler: fl!(),
                });
            }
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
                    try!(value.finalize_type(uf, function));
                }
                stmt::Expr(ref mut e @ expr {
                    kind: expr_kind::Return(_),
                    ..
                }) => {
                    try!(e.finalize_type(uf, function));
                    live_blk = false;
                }
                stmt::Expr(ref mut e) => {
                    try!(e.finalize_type(uf, function));
                }
            }
        }

        if let Some(ref mut expr) = *block.1 {
            if !live_blk {
                return Err(ast_error::StatementsAfterReturn {
                    function: function.name.clone(),
                    compiler: fl!(),
                });
            }
            try!(expr.finalize_type(uf, function));
        }
        Ok(())
    }

    fn unify_type(&mut self, to_unify: ty, uf: &mut union_find, variables: &mut HashMap<String, ty>,
            function: &function, functions: &HashMap<String, function>) -> Result<(), ast_error> {
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
            expr_kind::Plus(ref mut inner) | expr_kind::Minus(ref mut inner)
            | expr_kind::Not(ref mut inner) => {
                try!(inner.unify_type(to_unify, uf, variables, function, functions));
                let ty = self.ty;
                uf.unify(self.ty, inner.ty).map_err(|()|
                    ast_error::CouldNotUnify {
                        first: ty,
                        second: inner.ty,
                        function: function.name.clone(),
                        compiler: fl!(),
                    }
                )
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
                        try!(lhs.unify_type(self.ty, uf, variables, function, functions));
                        try!(rhs.unify_type(lhs.ty, uf, variables, function, functions));
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
                        try!(lhs.unify_type(rhs.ty, uf, variables, function, functions));
                        try!(rhs.unify_type(lhs.ty, uf, variables, function, functions));
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
                        try!(lhs.unify_type(ty::Bool, uf, variables, function, functions));
                        try!(rhs.unify_type(ty::Bool, uf, variables, function, functions));

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
                                caller: function.name.clone(),
                            })
                        }

                        for (arg_ty, expr) in f.input.iter().zip(args) {
                           try!(expr.unify_type(*arg_ty, uf, variables, function, functions));
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
                try!(condition.unify_type(ty::Bool, uf, variables, function, functions));
                try!(Self::typeck_block((&mut then_value.0, &mut then_value.1), to_unify,
                    uf, variables, function, functions));
                try!(Self::typeck_block((&mut else_value.0, &mut else_value.1), to_unify,
                    uf, variables, function, functions));
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
                ret.unify_type(function.output, uf, variables, function, functions)
            }
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
            expr_kind::Plus(ref mut inner) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(ast_error::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(inner.finalize_type(uf, function));
                assert!(self.ty == inner.ty);
                match self.ty {
                    ty::SInt(_) | ty::UInt(_) => Ok(()),
                    ty => {
                        Err(ast_error::UnopUnsupported {
                            op: operand::Plus,
                            inner: ty,
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    }
                }
            }
            expr_kind::Minus(ref mut inner) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(ast_error::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(inner.finalize_type(uf, function));
                assert!(self.ty == inner.ty);
                match self.ty {
                    ty::SInt(_) => Ok(()),
                    ty => {
                        Err(ast_error::UnopUnsupported {
                            op: operand::Minus,
                            inner: ty,
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    }
                }
            }
            expr_kind::Not(ref mut inner) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t) => t,
                    None => return Err(ast_error::NoActualType {
                        compiler: fl!(),
                        function: function.name.clone(),
                    })
                };
                try!(inner.finalize_type(uf, function));
                assert!(self.ty == inner.ty);
                match self.ty {
                    ty::SInt(_) | ty::UInt(_) | ty::Bool => Ok(()),
                    ty => {
                        Err(ast_error::UnopUnsupported {
                            op: operand::Not,
                            inner: ty,
                            function: function.name.clone(),
                            compiler: fl!(),
                        })
                    }
                }
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
                try!(Self::finalize_block_ty((&mut then_value.0, &mut then_value.1), uf, function));
                Self::finalize_block_ty((&mut else_value.0, &mut else_value.1), uf, function)
            }
            expr_kind::Return(ref mut ret) => {
                self.ty = match uf.actual_ty(self.ty) {
                    Some(t @ ty::Diverging) => t,
                    Some(t) => panic!("ICE: return without Diverging type: {:#?}", t),
                    None => panic!("ICE: return with no type (should be Diverging)")
                };
                ret.finalize_type(uf, function)
            }
        }
    }

    pub fn is_block(&self) -> bool {
        match self.kind {
            expr_kind::If {..} => true,
            expr_kind::Call {..} | expr_kind::Binop {..} | expr_kind::Plus(_)
            | expr_kind::Minus(_) | expr_kind::Not(_) | expr_kind::Variable(_)
            | expr_kind::IntLiteral(_) | expr_kind::BoolLiteral(_) | expr_kind::UnitLiteral
            | expr_kind::Return(_) => false,
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

    pub fn if_else(cond: expr, then: (Vec<stmt>, Option<expr>),
            else_: (Vec<stmt>, Option<expr>), ty: Option<ty>) -> expr {
        expr {
            kind: expr_kind::If {
                condition: Box::new(cond),
                then_value: (then.0, then.1.map(|e| Box::new(e))),
                else_value: (else_.0, else_.1.map(|e| Box::new(e))),
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
        body: (Vec<stmt>, Option<Box<expr>>),
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

    fn add_body(&self, body: (Vec<stmt>, Option<Box<expr>>), ast: &ast) {
        let mut block = block::new(self, "entry");
        let mut locals = HashMap::new();

        let ret = expr::translate_block(body, self.output.clone(), self, &mut locals, &mut block, ast);

        if block.is_live() {
            if self.output == ret.ty {
                block.ret(ret)
            } else {
                block.terminate();
                panic!("ICE: typeck passed through non-void void function: {}", self.name)
            }
        }

        ast.module.optimize_function(self);
    }
}

#[derive(Debug)]
pub enum ast_error {
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
        op: operand,
        inner: ty,
        function: String,
        compiler: (&'static str, u32),
    },
    CouldNotUnify {
        first: ty,
        second: ty,
        function: String,
        compiler: (&'static str, u32),
    },
    NoActualType {
        function: String,
        compiler: (&'static str, u32),
    },
    UnknownType(&'static str),
    StatementsAfterReturn {
        function: String,
        compiler: (&'static str, u32),
    },
    /*
    BinopUnsupported {
        op: operand,
        lhs: ty,
        rhs: ty,
    },
    */
}

#[derive(Debug)]
pub struct ast {
    functions: HashMap<String, function>,
    function_blocks: HashMap<String, (Vec<stmt>, Option<Box<expr>>)>,
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
            let function = match self.functions.get(name) {
                Some(f) => f,
                None => panic!("ICE: block without an associated function: {}", name),
            };
            try!(expr::typeck_block((&mut block.0, &mut block.1), function.output.clone(),
                &mut uf, &mut vars, function, &self.functions));
            try!(expr::finalize_block_ty((&mut block.0, &mut block.1), &mut uf, function));
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
            LLVMDumpModule(self.module.raw);

            println!("--- RUNNING ---");
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

    fn call(&self, callee: &str, block: &block, args: Vec<value>)
            -> value {
        match self.functions.get(callee) {
            Some(f) => {
                value {
                    raw: block.build_call(f, args.into_iter().map(|arg| arg.raw).collect()),
                    ty: f.output.clone(),
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

    unsafe fn add_func(&self, name: &str, ret_ty: &ty, args: &[LLVMTypeRef]) -> LLVMValueRef {
        let ty = LLVMFunctionType(ret_ty.to_llvm_ret(), args.as_ptr() as *mut _,
            args.len() as u32, false as LLVMBool);
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

    fn binop(op: &operand, lhs: value, rhs: value, block: &block)
            -> value {
        match *op {
            operand::Mul => lhs.mul(rhs, block),
            operand::Div => lhs.div(rhs, block),
            operand::Rem => lhs.rem(rhs, block),
            operand::Plus => lhs.add(rhs, block),
            operand::Minus => lhs.sub(rhs, block),

            operand::Shl => lhs.shl(rhs, block),
            operand::Shr => lhs.shr(rhs, block),

            operand::And => lhs.and(rhs, block),
            operand::Xor => lhs.xor(rhs, block),
            operand::Or => lhs.or(rhs, block),

            operand::EqualsEquals => lhs.eq(rhs, block),
            operand::NotEquals => lhs.neq(rhs, block),
            operand::LessThan => lhs.le(rhs, block),
            operand::LessThanEquals => lhs.lte(rhs, block),
            operand::GreaterThan => lhs.gt(rhs, block),
            operand::GreaterThanEquals => lhs.gte(rhs, block),

            operand::AndAnd => unreachable!("should be an if statement"),
            operand::OrOr => unreachable!("should be an if statement"),
            operand::Not => unreachable!("Not (`!`) is not a binop"),
        }
    }

    fn mul(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) => {
                value {
                    raw: block.build_mul(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn div(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: block.build_sdiv(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            ty::UInt(_) => {
                value {
                    raw: block.build_udiv(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn rem(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: block.build_srem(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            ty::UInt(_) => {
                value {
                    raw: block.build_urem(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn add(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) => {
                value {
                    raw: block.build_add(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn sub(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) => {
                value {
                    raw: block.build_sub(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn shl(self, rhs: value, block: &block) -> value {
        match rhs.ty {
            ty::SInt(_) | ty::UInt(_) => {
                match self.ty {
                    ty::SInt(ref lt) | ty::UInt(ref lt) => {
                        let shift_mask = lt.shift_mask();
                        let safe_rhs = block.build_and(rhs.raw,
                            unsafe {LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool)});
                        return value {
                            raw: block.build_shl(self.raw, safe_rhs),
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
    fn shr(self, rhs: value, block: &block) -> value {
        match rhs.ty {
            ty::SInt(_) | ty::UInt(_) => {
                match self.ty {
                    ty::SInt(ref lt) => {
                        let shift_mask = lt.shift_mask();
                        let safe_rhs = block.build_and(rhs.raw,
                            unsafe {LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool)});
                        return value {
                            raw: block.build_ashr(self.raw, safe_rhs),
                            ty: self.ty.clone(),
                        };
                    },
                    ty::UInt(ref lt) => {
                        let shift_mask = lt.shift_mask();
                        let safe_rhs = block.build_and(rhs.raw,
                            unsafe {LLVMConstInt(rhs.ty.to_llvm(), shift_mask, false as LLVMBool)});
                        return value {
                            raw: block.build_lshr(self.raw, safe_rhs),
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
    fn and(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                value {
                    raw: block.build_and(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn xor(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                value {
                    raw: block.build_xor(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn or(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                value {
                    raw: block.build_or(self.raw, rhs.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }

    fn eq(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                value {
                    raw: block.build_cmp(LLVMIntEQ, self.raw, rhs.raw),
                    ty: ty::Bool,
                },
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn neq(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool =>
                value {
                    raw: block.build_cmp(LLVMIntNE, self.raw, rhs.raw),
                    ty: ty::Bool,
                },
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn le(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: block.build_cmp(LLVMIntSLT, self.raw, rhs.raw),
                    ty: ty::Bool,
                }
            }
            ty::UInt(_) | ty::Bool => {
                value {
                    raw: block.build_cmp(LLVMIntULT, self.raw, rhs.raw),
                    ty: ty::Bool,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn lte(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: block.build_cmp(LLVMIntSLE, self.raw, rhs.raw),
                    ty: ty::Bool,
                }
            }
            ty::UInt(_) | ty::Bool => {
                value {
                    raw: block.build_cmp(LLVMIntULE, self.raw, rhs.raw),
                    ty: ty::Bool,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn gt(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: block.build_cmp(LLVMIntSLT, self.raw, rhs.raw),
                    ty: ty::Bool,
                }
            }
            ty::UInt(_) | ty::Bool => {
                value {
                    raw: block.build_cmp(LLVMIntULT, self.raw, rhs.raw),
                    ty: ty::Bool,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
    fn gte(self, rhs: value, block: &block) -> value {
        assert!(self.ty == rhs.ty);
        match self.ty {
            ty::SInt(_) => {
                value {
                    raw: block.build_cmp(LLVMIntSGE, self.raw, rhs.raw),
                    ty: ty::Bool,
                }
            }
            ty::UInt(_) | ty::Bool => {
                value {
                    raw: block.build_cmp(LLVMIntUGE, self.raw, rhs.raw),
                    ty: ty::Bool,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }


    fn neg(self, block: &block) -> value {
        if let ty::SInt(_) = self.ty {
            value {
                raw: block.build_neg(self.raw),
                ty: self.ty,
            }
        } else {
            panic!("ICE: unsupported operation")
        }
    }
    fn not(self, block: &block) -> value {
        match self.ty {
            ty::SInt(_) | ty::UInt(_) | ty::Bool => {
                value {
                    raw: block.build_not(self.raw),
                    ty: self.ty,
                }
            }
            _ => panic!("ICE: unsupported operation")
        }
    }
}

#[derive(Clone, Debug)]
struct lvalue<'a> {
    ty: ty,
    raw: LLVMValueRef,
    lifetime: std::marker::PhantomData<block<'a>>,
}

impl<'a> lvalue<'a> {
    fn new(block: &block<'a>, ty: ty, name: Option<&str>) -> lvalue<'a> {
        let name = CString::new(name.unwrap_or("").to_owned()).expect("Null in a variable name");
        lvalue {
            raw: block.build_alloca(ty.to_llvm(), name.as_ptr()),
            ty: ty,
            lifetime: std::marker::PhantomData,
        }
    }

    fn write(&self, value: value, block: &block) {
        if block.is_live() {
            assert!(self.ty == value.ty);
        }
        block.build_store(value.raw, self.raw);
    }

    fn read(&self, block: &block) -> value {
        value {
            raw: block.build_load(self.raw),
            ty: self.ty,
        }
    }
}

struct block<'a> {
    raw: LLVMBasicBlockRef,
    builder: LLVMBuilderRef,
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
                builder: builder,
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

    pub fn builder(&self) -> Option<LLVMBuilderRef> {
        if self.is_live() {
            Some(self.builder)
        } else {
            None
        }
    }

    /// terminator
    fn terminate(&mut self) {
        self.live = false;
    }

    /// terminator
    fn ret(&mut self, ret: value) {
        if self.live {
            self.live = false;
            if ret.ty == ty::Unit {
                unsafe { LLVMBuildRetVoid(self.builder); }
            } else {
                unsafe { LLVMBuildRet(self.builder, ret.raw); }
            }
        }
    }

    /// terminator
    fn conditional_branch(&mut self, cond: value, then_blk: &block, else_blk: &block) {
        if self.live {
            self.live = false;
            unsafe {
                assert!(cond.ty == ty::Bool, "ICE: condition is not a boolean");
                LLVMBuildCondBr(self.builder, cond.raw, then_blk.raw, else_blk.raw);
            }
        }
    }

    /// terminator
    fn branch(&mut self, block: &block) {
        if self.live {
            self.live = false;
            unsafe {
                LLVMBuildBr(self.builder, block.raw);
            }
        }
    }

    fn build_call(&self, func: &function, mut args: Vec<LLVMValueRef>) -> LLVMValueRef {
        assert!(func.args.len() == args.len());
        match self.builder() {
            Some(builder) => {
                unsafe {
                    LLVMBuildCall(builder, func.raw, args.as_mut_ptr(), args.len() as u32, cstr!(""))
                }
            }
            None => Self::none_value()
        }
    }

    fn build_mul(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildMul(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }

    fn build_sdiv(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildSDiv(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_udiv(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildUDiv(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_srem(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildSRem(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_urem(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildSRem(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_add(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildAdd(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_sub(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildSub(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_shl(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildShl(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_ashr(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildAShr(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_lshr(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildLShr(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_and(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildAnd(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_xor(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildXor(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_or(&self, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildOr(builder, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_cmp(&self, cmp: LLVMIntPredicate, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) =>
                unsafe { LLVMBuildICmp(builder, cmp, lhs, rhs, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_neg(&self, inner: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildNeg(builder, inner, cstr!("")) },
            None => Self::none_value()
        }
    }
    fn build_not(&self, inner: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildNot(builder, inner, cstr!("")) },
            None => Self::none_value()
        }
    }

    fn build_alloca(&self, ty: LLVMTypeRef, name: *const i8) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildAlloca(builder, ty, name) },
            None => Self::none_value()
        }
    }
    fn build_store(&self, value: LLVMValueRef, ptr: LLVMValueRef) {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildStore(builder, value, ptr); },
            None => {}
        }
    }
    fn build_load(&self, ptr: LLVMValueRef) -> LLVMValueRef {
        match self.builder() {
            Some(builder) => unsafe { LLVMBuildLoad(builder, ptr, cstr!("")) },
            None => Self::none_value()
        }
    }


    fn none_value() -> LLVMValueRef {
        unsafe {
            LLVMGetUndef(ty::Unit.to_llvm())
        }
    }
}

impl<'a> std::ops::Drop for block<'a> {
    fn drop(&mut self) {
        if self.live {
            println!("dropped live block: {}", self.dbg_name)
        }
        unsafe {
            LLVMDisposeBuilder(self.builder);
        }
    }
}
