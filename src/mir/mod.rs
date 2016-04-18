use std;
use std::collections::HashMap;
use ty::{self, Type, TypeVariant, TypeContext};

mod llvm;

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

    fn new_block(&mut self, expr: Lvalue<'t>, term: Terminator<'t>) -> Block {
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

    fn get_leaf(&mut self, mir: &Mir<'t>, value: Value<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> ValueLeaf<'t> {
        if let ValueKind::Leaf(leaf) = value.0 {
            leaf
        } else {
            let ty = value.ty(mir, self, fn_types);
            let tmp = self.new_tmp(ty);
            block.add_stmt(Lvalue::Temporary(tmp), value, self);
            ValueLeaf::Temporary(tmp)
        }
    }

    fn build(self, mir: &Mir<'t>, llfunc: llvm::Value,
             funcs: &HashMap<String, (llvm::Value, Type<'t>)>) {
        LlFunction::build(mir, self, llfunc, funcs)
    }
}

struct LlFunction<'t> {
    mir: Function<'t>,
    raw: llvm::Value,
    builder: llvm::Builder,
    ret_ptr: llvm::Value,
    temporaries: Vec<llvm::Value>,
    locals: Vec<llvm::Value>,
    blocks: Vec<llvm::BasicBlock>,
}

impl<'t> LlFunction<'t> {
    fn build(mir: &Mir<'t>, mirfunc: Function<'t>, llfunc: llvm::Value,
            funcs: &HashMap<String, (llvm::Value, Type<'t>)>) {
        unsafe {
            let builder = llvm::Builder::new();
            let mut blocks = Vec::new();
            for i in 0..mirfunc.blocks.len() {
                blocks.push(llvm::BasicBlock::append(llfunc, i as u32));
            }

            builder.position_at_end(blocks[0]);

            let mut tmps = Vec::new();
            for mir_tmp in &mirfunc.temporaries {
                tmps.push(
                    builder.build_alloca(
                        llvm::get_type(&mir.target_data, *mir_tmp), "tmp"));
            }
            let mut locals = Vec::new();
            for mir_local in &mirfunc.locals {
                locals.push(
                    builder.build_alloca(
                        llvm::get_type(&mir.target_data, *mir_local), "var"));
            }

            let ret_ptr = builder.build_alloca(
                llvm::get_type(&mir.target_data, mirfunc.ty.output()), "ret");

            let mut self_ = LlFunction {
                mir: mirfunc,
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
                self_.builder.position_at_end(self_.blocks[i]);
                for stmt in blk.statements {
                    stmt.to_llvm(mir, &mut self_, funcs);
                }
                blk.terminator.to_llvm(mir, &self_);
            }
        }
    }


    fn get_tmp_ptr(&self, tmp: &Temporary) -> llvm::Value {
        self.temporaries[tmp.0 as usize]
    }
    fn get_tmp_value(&self, tmp: &Temporary) -> llvm::Value {
        self.builder.build_load(self.temporaries[tmp.0 as usize])
    }
    fn get_local_ptr(&self, var: &Variable) -> llvm::Value {
        self.locals[var.0 as usize]
    }
    fn get_local_value(&self, var: &Variable) -> llvm::Value {
        self.builder.build_load(self.locals[var.0 as usize])
    }

    fn get_block(&self, blk: &Block) -> llvm::BasicBlock {
        self.blocks[blk.0]
    }
}

#[derive(Copy, Clone, Debug)]
enum Const<'t> {
    Int {
        value: u64,
        ty: Type<'t>,
    },
    Bool(bool),
    Unit,
}

impl<'t> Const<'t> {
    unsafe fn to_llvm(self, mir: &Mir<'t>) -> llvm::Value {
        match self {
            Const::Int {
                value,
                ty,
            } => {
                llvm::Value::const_int(
                    llvm::get_type(&mir.target_data, ty), value)
            }
            Const::Bool(value) => {
                llvm::Value::const_bool(value)
            }
            Const::Unit => {
                llvm::Value::const_struct(&[])
            }
        }
    }

    fn ty(&self, mir: &Mir<'t>) -> Type<'t> {
        match *self {
            Const::Int {
                ty,
                ..
            } => ty,
            Const::Bool(_) => Type::bool(mir.ctxt),
            Const::Unit => Type::unit(mir.ctxt),
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum ValueLeaf<'t> {
    Const(Const<'t>),
    Parameter(Parameter),
    Variable(Variable),
    Temporary(Temporary),
}

impl<'t> ValueLeaf<'t> {
    fn ty(&self, mir: &Mir<'t>, function: &Function<'t>) -> Type<'t> {
        match *self {
            ValueLeaf::Const(ref inner) => inner.ty(mir),
            ValueLeaf::Temporary(ref tmp) => function.get_tmp_ty(tmp),
            ValueLeaf::Parameter(ref par) => function.get_par_ty(par),
            ValueLeaf::Variable(ref var) => function.get_local_ty(var),
        }
    }

    unsafe fn to_llvm(self, mir: &Mir<'t>, function: &LlFunction<'t>)
            -> llvm::Value {
        match self {
            ValueLeaf::Const(inner) => {
                inner.to_llvm(mir)
            }
            ValueLeaf::Temporary(tmp) => {
                function.get_tmp_value(&tmp)
            }
            ValueLeaf::Parameter(par) => {
                llvm::Value::get_param(function.raw, par.0)
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
    Deref(ValueLeaf<'t>),

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
            ValueLeaf::Const(Const::Int {
                value: value,
                ty: ty,
            }
        ))
    }
    #[inline(always)]
    pub fn const_bool(value: bool) -> Self {
        Value::leaf(ValueLeaf::Const(Const::Bool(value)))
    }
    #[inline(always)]
    pub fn const_unit() -> Value<'t> {
        Value::leaf(ValueLeaf::Const(Const::Unit))
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
    pub fn pos(inner: Self, mir: &Mir<'t>, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>)
            -> Self {
        Value(ValueKind::Pos(function.get_leaf(mir, inner, block, fn_types)))
    }
    pub fn neg(inner: Self, mir: &Mir<'t>, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>)
            -> Self {
        Value(ValueKind::Neg(function.get_leaf(mir, inner, block, fn_types)))
    }
    pub fn not(inner: Self, mir: &Mir<'t>, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>)
            -> Self {
        Value(ValueKind::Not(function.get_leaf(mir, inner, block, fn_types)))
    }
    pub fn ref_(inner: Self, mir: &Mir<'t>, function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>)
            -> Self {
        let inner_ty = inner.ty(mir, function, fn_types);
        let ptr = function.new_tmp(Type::ref_(inner_ty, mir.ctxt));
        block.write_ref(Lvalue::Temporary(ptr),
            inner, mir, function, fn_types);
        Value::leaf(ValueLeaf::Temporary(ptr))
    }

    pub fn deref(inner: Self, mir: &Mir<'t>, function: &mut Function<'t>,
            block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>)
            -> Self {
        Value(ValueKind::Deref(function.get_leaf(mir, inner, block, fn_types)))
    }

    // -- binops --
    pub fn add(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Add(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn sub(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Sub(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn mul(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Mul(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn div(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Div(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn rem(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Rem(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn and(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::And(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn xor(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Xor(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn or(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Or(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn shl(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Shl(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn shr(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Shr(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }

    // -- comparisons --
    pub fn eq(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Eq(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn neq(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Neq(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn lt(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Lt(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn lte(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Lte(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn gt(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>)
            -> Self {
        Value(ValueKind::Gt(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }
    pub fn gte(lhs: Self, rhs: Self, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        Value(ValueKind::Gte(
            function.get_leaf(mir, lhs, block, fn_types),
            function.get_leaf(mir, rhs, block, fn_types)))
    }

    // -- misc --
    pub fn call(callee: String, args: Vec<Self>, mir: &Mir<'t>,
            function: &mut Function<'t>, block: &mut Block,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Self {
        let args = args.into_iter().map(|v|
            function.get_leaf(mir, v, block, fn_types)).collect();
        Value(ValueKind::Call {
            callee: callee,
            args: args,
        })
    }
}

impl<'t> Value<'t> {
    fn ty(&self, mir: &Mir<'t>, function: &Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Type<'t> {
        match self.0 {
            ValueKind::Leaf(ref v) => v.ty(mir, function),

            ValueKind::Pos(ref inner) | ValueKind::Neg(ref inner)
            | ValueKind::Not(ref inner) => inner.ty(mir, function),

            ValueKind::Ref(ref inner) =>
                Type::ref_(inner.ty(mir, function), mir.ctxt),
            ValueKind::Deref(ref inner) => {
                if let TypeVariant::Reference(inner) =
                        *inner.ty(mir, function).0 {
                    inner
                } else {
                    panic!("Deref of a non-ref type: {:?}", inner)
                }
            }

            ValueKind::Add(ref lhs, ref rhs)
            | ValueKind::Sub(ref lhs, ref rhs)
            | ValueKind::Mul(ref lhs, ref rhs)
            | ValueKind::Div(ref lhs, ref rhs)
            | ValueKind::Rem(ref lhs, ref rhs)
            | ValueKind::And(ref lhs, ref rhs)
            | ValueKind::Xor(ref lhs, ref rhs)
            | ValueKind::Or(ref lhs, ref rhs)
            => {
                let lhs_ty = lhs.ty(mir, function);
                assert_eq!(lhs_ty, rhs.ty(mir, function));
                lhs_ty
            }

            ValueKind::Shl(ref lhs, _)
            | ValueKind::Shr(ref lhs, _)
            => {
                lhs.ty(mir, function)
            }

            ValueKind::Eq(_, _) | ValueKind::Neq(_, _) | ValueKind::Lt(_, _)
            | ValueKind::Lte(_, _) | ValueKind::Gt(_, _) | ValueKind::Gte(_, _)
                => Type::bool(mir.ctxt),

            ValueKind::Call {
                ref callee,
                ..
            } =>  {
                fn_types.get(callee).expect("ICE: no function prototype")
                    .output()
            }
        }
    }

    unsafe fn to_llvm(self, mir: &Mir<'t>, function: &mut LlFunction<'t>,
            funcs: &HashMap<String, (llvm::Value, Type<'t>)>)
            -> llvm::Value {
        use llvm_sys::LLVMIntPredicate::*;
        match self.0 {
            ValueKind::Leaf(v) => {
                v.to_llvm(mir, function)
            }
            ValueKind::Pos(inner) => {
                let ty = inner.ty(mir, &function.mir);
                let llinner = inner.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) => llinner,
                    _ => panic!("ICE: {} can't be used in unary +", ty),
                }
            }
            ValueKind::Neg(inner) => {
                // TODO: check types
                let ty = inner.ty(mir, &function.mir);
                let llinner = inner.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) =>
                        function.builder.build_neg(llinner),
                    _ => panic!("ICE: {} can't be used in unary -", ty),
                }
            }
            ValueKind::Not(inner) => {
                let ty = inner.ty(mir, &function.mir);
                let llinner = inner.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        function.builder.build_not(llinner),
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
            ValueKind::Deref(inner) => {
                let llinner = inner.to_llvm(mir, function);
                function.builder.build_load(llinner)
            }
            ValueKind::Add(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) =>
                        function.builder.build_add(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary +", ty),
                }
            }
            ValueKind::Sub(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) =>
                        function.builder.build_sub(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary -", ty),
                }
            }
            ValueKind::Mul(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) =>
                        function.builder.build_mul(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary *", ty),
                }
            }
            ValueKind::Div(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) =>
                        function.builder.build_sdiv(lhs, rhs),
                    TypeVariant::UInt(_) =>
                        function.builder.build_udiv(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary /", ty),
                }
            }
            ValueKind::Rem(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) =>
                        function.builder.build_srem(lhs, rhs),
                    TypeVariant::UInt(_) =>
                        function.builder.build_urem(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::And(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        function.builder.build_and(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Xor(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        function.builder.build_xor(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Or(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        function.builder.build_or(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Shl(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_) =>
                        function.builder.build_shl(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Shr(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) =>
                        function.builder.build_ashr(lhs, rhs),
                    TypeVariant::UInt(_) =>
                        function.builder.build_lshr(lhs, rhs),
                    _ => panic!("ICE: {} can't be used in binary %", ty),
                }
            }
            ValueKind::Eq(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        function.builder.build_icmp(llvm::IntEQ, lhs, rhs),
                    _ =>  panic!("ICE: {} can't be used in ==", ty),
                }
            }
            ValueKind::Neq(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) | TypeVariant::UInt(_)
                    | TypeVariant::Bool =>
                        function.builder.build_icmp(llvm::IntNE, lhs, rhs),
                    _ =>  panic!("ICE: {} can't be used in !=", ty),
                }
            }
            ValueKind::Lt(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) =>
                        function.builder.build_icmp(LLVMIntSLT, lhs, rhs),
                    TypeVariant::UInt(_) | TypeVariant::Bool =>
                        function.builder.build_icmp(LLVMIntULT, lhs, rhs),
                    _ =>  panic!("ICE: {} can't be used in <", ty),
                }
            }
            ValueKind::Lte(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) =>
                        function.builder.build_icmp(LLVMIntSLE, lhs, rhs),
                    TypeVariant::UInt(_) | TypeVariant::Bool =>
                        function.builder.build_icmp(LLVMIntULE, lhs, rhs),
                    _ =>  panic!("ICE: {} can't be used in <=", ty),
                }
            }
            ValueKind::Gt(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) =>
                        function.builder.build_icmp(LLVMIntSGT,
                            lhs, rhs),
                    TypeVariant::UInt(_) | TypeVariant::Bool =>
                        function.builder.build_icmp(LLVMIntUGT,
                            lhs, rhs),
                    _ =>  panic!("ICE: {} can't be used in >", ty),
                }
            }
            ValueKind::Gte(lhs, rhs) => {
                let ty = lhs.ty(mir, &function.mir);
                let lhs = lhs.to_llvm(mir, function);
                let rhs = rhs.to_llvm(mir, function);
                match *ty.0 {
                    TypeVariant::SInt(_) =>
                        function.builder.build_icmp(LLVMIntSGE,
                            lhs, rhs),
                    TypeVariant::UInt(_) | TypeVariant::Bool =>
                        function.builder.build_icmp(LLVMIntUGE,
                            lhs, rhs),
                    _ =>  panic!("ICE: {} can't be used in >=", ty),
                }
            }
            ValueKind::Call {
                callee,
                args,
            } => {
                let args = args.into_iter().map(|a|
                    a.to_llvm(mir, function)).collect::<Vec<_>>();
                let (callee, output) = *funcs.get(&callee).unwrap();
                let llret = function.builder.build_call(callee, &args);

                if llvm::size_of_type(&mir.target_data, output) == 0 {
                    llvm::Value::const_struct(&mut [])
                } else {
                    llret
                }
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum Lvalue<'t> {
    Variable(Variable),
    Temporary(Temporary),
    Deref(ValueLeaf<'t>),
    Return,
}

#[derive(Debug)]
struct Statement<'t>(Lvalue<'t>, Value<'t>);

impl<'t> Statement<'t> {
    unsafe fn to_llvm(self, mir: &Mir<'t>, function: &mut LlFunction<'t>,
            funcs: &HashMap<String, (llvm::Value, Type<'t>)>) {
        let dst = match self.0 {
            Lvalue::Return => function.ret_ptr,
            Lvalue::Temporary(tmp) => function.get_tmp_ptr(&tmp),
            Lvalue::Variable(var) => function.get_local_ptr(&var),
            Lvalue::Deref(ptr) => ptr.to_llvm(mir, function),
        };
        let src = (self.1).to_llvm(mir, function, funcs);
        function.builder.build_store(dst, src);
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
    unsafe fn to_llvm(self, mir: &Mir<'t>, function: &LlFunction<'t>) {
        match self {
            Terminator::Goto(mut b) => {
                function.builder.build_br(function.get_block(&mut b));
            },
            Terminator::If {
                cond,
                mut then_blk,
                mut else_blk,
            } => {
                let cond = cond.to_llvm(mir, function);
                function.builder.build_cond_br(cond,
                    function.get_block(&mut then_blk),
                    function.get_block(&mut else_blk));
            }
            Terminator::Return => {
                if llvm::size_of_type(&mir.target_data,
                        function.mir.ty.output()) == 0 {
                    function.builder.build_void_ret();
                } else {
                    let value = function.builder.build_load(function.ret_ptr);
                    function.builder.build_ret(value);
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
            mir: &Mir<'t>, function: &mut Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>) -> Value<'t> {
        let ty = val.ty(mir, function, fn_types);
        let tmp = function.new_tmp(ty);
        self.add_stmt(Lvalue::Temporary(tmp), val, function);
        Value::leaf(ValueLeaf::Temporary(tmp))
    }

    pub fn write_to_ptr<'t>(&mut self, ptr: Value<'t>, val: Value<'t>,
            mir: &Mir<'t>, function: &mut Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>) {
        let leaf = function.get_leaf(mir, ptr, self, fn_types);
        if let TypeVariant::Reference(_) = *leaf.ty(mir, function).0 {
        } else {
            panic!("writing to a not-pointer: {}", leaf.ty(mir, function))
        }
        self.add_stmt(Lvalue::Deref(leaf), val, function)
    }

    fn write_ref<'t>(&mut self, ptr: Lvalue<'t>, val: Value<'t>,
            mir: &Mir<'t>, function: &mut Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>) {
        let leaf = function.get_leaf(mir, val, self, fn_types);
        let leaf = match leaf {
            l @ ValueLeaf::Const(_) => {
                let ty = l.ty(mir, function);
                let tmp = function.new_tmp(ty);
                self.add_stmt(Lvalue::Temporary(tmp), Value::leaf(l),
                    function);
                ValueLeaf::Temporary(tmp)
            }
            ValueLeaf::Parameter(_) => {
                panic!("ICE: Attempted to write_ref a parameter");
            }
            l @ ValueLeaf::Temporary(_) | l @ ValueLeaf::Variable(_) => l,
        };
        self.add_stmt(ptr, Value(ValueKind::Ref(leaf)), function);
    }

    fn add_stmt<'t>(&mut self, lvalue: Lvalue<'t>, value: Value<'t>,
            function: &mut Function<'t>) {
        let blk = function.get_block(self);
        blk.statements.push(Statement(lvalue, value))
    }
}
// terminators
impl Block {
    pub fn if_else<'t>(mut self, ty: Type<'t>, cond: Value<'t>,
            mir: &Mir<'t>, function: &mut Function<'t>,
            fn_types: &HashMap<String, ty::Function<'t>>)
            -> (Block, Block, Block, Value<'t>) {
        let cond = function.get_leaf(mir, cond, &mut self, fn_types);
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
    expr: Lvalue<'t>,
    statements: Vec<Statement<'t>>,
    terminator: Terminator<'t>,
}

impl<'t> BlockData<'t> {
    fn new(expr: Lvalue<'t>, term: Terminator<'t>) -> BlockData<'t> {
        BlockData {
            expr: expr,
            statements: Vec::new(),
            terminator: term,
        }
    }
}

pub struct Mir<'t> {
    functions: HashMap<String, Function<'t>>,
    ctxt: &'t TypeContext<'t>,

    optimize: bool,

    target_machine: llvm::TargetMachine,
    target_data: llvm::TargetData,
}

impl<'t> Mir<'t> {
    pub fn new(ctxt: &'t TypeContext<'t>, opt: bool) -> Mir<'t> {
        let opt_level = if opt {
            llvm::NoOptimization
        } else {
            llvm::DefaultOptimization
        };
        let target_machine = llvm::TargetMachine::new(opt_level).unwrap();
        let target_data =
            llvm::TargetData::from_target_machine(&target_machine);

        Mir {
            functions: HashMap::new(),
            ctxt: ctxt,
            optimize: opt,
            target_machine: target_machine,
            target_data: target_data,
        }
    }

    pub fn add_function(&mut self, name: String, func: Function<'t>) {
        self.functions.insert(name, func);
    }

    pub fn build_and_write(mut self, output: &str, print_llir: bool) {
        let mut llvm_functions = HashMap::new();
        let module = llvm::Module::new();

        let optimizer = llvm::FnOptimizer::for_module(&module);

        for (name, function) in &self.functions {
            let llfunc = module.add_function(&name,
                llvm::get_function_type(&self.target_data, &function.ty));
            llvm_functions.insert(name.clone(),
                (llfunc, function.ty.output()));
        }

        let functions =
            std::mem::replace(&mut self.functions, HashMap::new());
        for (name, function) in functions {
            let llfunc = llvm_functions.get(&name).unwrap().0;
            function.build(&self, llfunc, &llvm_functions);
            if self.optimize {
                optimizer.optimize(llfunc);
            }
        }

        if print_llir {
            module.dump();
        }

        module.verify();

        match self.target_machine.emit_to_file(&module, output) {
            Ok(()) => {},
            Err(e) => panic!("Failed to write to output file: {:?}", e),
        }
    }

    #[inline(always)]
    pub fn ty_ctxt(&self) -> &'t TypeContext<'t> {
        self.ctxt
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

impl<'t> std::fmt::Display for Lvalue<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Lvalue::Return => write!(f, "return"),
            Lvalue::Temporary(ref tmp) => write!(f, "tmp{}", tmp.0),
            Lvalue::Variable(ref var) => write!(f, "var{}", var.0),
            Lvalue::Deref(ref ptr) => write!(f, "(*{})", ptr),
        }
    }
}

impl<'t> std::fmt::Display for Const<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Const::Int {
                ref ty,
                ref value,
            } => {
                match *ty.0 {
                    TypeVariant::SInt(_) => write!(f, "{}", *value as i64),
                    TypeVariant::UInt(_) => write!(f, "{}", *value as u64),
                    _ => panic!("Non-integer int"),
                }
            }
            Const::Bool(ref value) => write!(f, "{}", value),
            Const::Unit => write!(f, "()"),
        }
    }
}

impl<'t> std::fmt::Display for ValueLeaf<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            ValueLeaf::Const(ref inner) => write!(f, "const {}", inner),
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
            ValueKind::Deref(ref inner) => write!(f, "*{}", inner),
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
