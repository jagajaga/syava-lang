use std;
use std::collections::HashMap;
use std::cell::RefCell;
use typed_arena::Arena;
use llvm_sys::prelude::*;
use llvm_sys::core::*;

pub struct TypeContext<'t> {
    backing_store: Arena<TypeVariant<'t>>,
    type_references: RefCell<HashMap<TypeVariant<'t>, &'t TypeVariant<'t>>>,
}

impl<'t> TypeContext<'t> {
    pub fn new() -> Self {
        TypeContext {
            backing_store: Arena::new(),
            type_references: RefCell::new(HashMap::new()),
        }
    }

    fn get(&'t self, variant: TypeVariant<'t>) -> &'t TypeVariant<'t> {
        if let Some(var) = self.type_references.borrow().get(&variant) {
            return var;
        }

        let var = self.backing_store.alloc(variant);
        self.type_references.borrow_mut().insert(variant, var);
        var
    }
}

#[derive(Copy, Clone)]
pub struct Type<'t> {
    pub context: &'t TypeContext<'t>,
    pub variant: &'t TypeVariant<'t>,
}

impl<'t> PartialEq for Type<'t> {
    fn eq(&self, rhs: &Self) -> bool {
        self.context as *const TypeContext<'t> ==
            rhs.context as *const TypeContext<'t> &&
            self.variant == rhs.variant
    }
}

impl<'t> Eq for Type<'t> { }

impl<'t> std::hash::Hash for Type<'t> {
    fn hash<H>(&self, state: &mut H) where H: std::hash::Hasher {
        (self.context as *const _).hash(state);
        (self.variant as *const _).hash(state);
    }
}

impl<'t> std::fmt::Debug for Type<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self.variant {
            TypeVariant::SInt(size) => write!(f, "SInt({:?})", size),
            TypeVariant::UInt(size) => write!(f, "SInt({:?})", size),
            TypeVariant::Bool => write!(f, "Bool"),
            TypeVariant::Unit => write!(f, "Unit"),
            TypeVariant::Diverging => write!(f, "Diverging"),
            TypeVariant::Reference(inner) =>
                write!(f, "Ref({:?})", inner),
            TypeVariant::Infer(i) => write!(f, "Infer({:?})", i),
            TypeVariant::InferInt(i) => write!(f, "InferInt({:?})", i),
        }
    }
}

// -- constructors --
impl<'t> Type<'t> {
    pub fn infer(ctxt: &'t TypeContext<'t>) -> Self {
        Type {
            context: ctxt,
            variant: ctxt.get(TypeVariant::Infer(None)),
        }
    }

    pub fn infer_int(ctxt: &'t TypeContext<'t>) -> Self {
        Type {
            context: ctxt,
            variant: ctxt.get(TypeVariant::InferInt(None)),
        }
    }

    pub fn sint(int: Int, ctxt: &'t TypeContext<'t>) -> Self {
        Type {
            context: ctxt,
            variant: ctxt.get(TypeVariant::SInt(int)),
        }
    }
    pub fn uint(int: Int, ctxt: &'t TypeContext<'t>) -> Self {
        Type {
            context: ctxt,
            variant: ctxt.get(TypeVariant::UInt(int)),
        }
    }
    pub fn bool(ctxt: &'t TypeContext<'t>) -> Self {
        Type {
            context: ctxt,
            variant: ctxt.get(TypeVariant::Bool),
        }
    }
    pub fn unit(ctxt: &'t TypeContext<'t>) -> Self {
        Type {
            context: ctxt,
            variant: ctxt.get(TypeVariant::Unit),
        }
    }
    pub fn diverging(ctxt: &'t TypeContext<'t>) -> Self {
        Type {
            context: ctxt,
            variant: ctxt.get(TypeVariant::Diverging),
        }
    }

    pub fn ref_(ty: Type<'t>) -> Self {
        Type {
            context: ty.context,
            variant: ty.context.get(TypeVariant::Reference(ty))
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeVariant<'t> {
    SInt(Int),
    UInt(Int),
    Bool,
    Unit,

    Diverging,

    Reference(Type<'t>),

    Infer(Option<u32>),
    InferInt(Option<u32>),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Int {
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Function<'t> {
    input: Vec<Type<'t>>,
    output: Type<'t>,
}

impl<'t> Function<'t> {
    pub fn new(input: Vec<Type<'t>>, output: Type<'t>) -> Self {
        Function {
            input: input,
            output: output,
        }
    }

    pub fn input(&self) -> &[Type<'t>] {
        &self.input
    }

    pub fn output(&self) -> Type<'t> {
        self.output
    }

    pub fn to_llvm(&self) -> LLVMTypeRef {
        unsafe {
            let mut args = self.input.iter().map(|a| a.to_llvm())
                .collect::<Vec<_>>();
            LLVMFunctionType(self.output.to_llvm_ret(), args.as_mut_ptr(),
                args.len() as u32, false as LLVMBool)
        }
    }
}

impl<'t> Type<'t> {
    pub fn to_llvm(&self) -> LLVMTypeRef {
        unsafe {
            match *self.variant {
                TypeVariant::SInt(ref size) | TypeVariant::UInt(ref size)
                    => LLVMIntType(size.size()),
                TypeVariant::Bool => LLVMInt1Type(),
                TypeVariant::Unit => LLVMStructType(std::ptr::null_mut(), 0,
                        false as LLVMBool),
                TypeVariant::Reference(inner) =>
                    LLVMPointerType(inner.to_llvm(), 0),
                TypeVariant::Diverging
                    => panic!("ICE: Attempted to get the LLVM type of \
                        Diverging"),
                TypeVariant::Infer(_) | TypeVariant::InferInt(_) =>
                    panic!("ICE: Attempted to get the LLVM type of an \
                        inference variable: {:?}", self),
            }
        }
    }

    pub fn to_llvm_ret(&self) -> LLVMTypeRef {
        unsafe {
            match *self.variant {
                TypeVariant::SInt(ref size) | TypeVariant::UInt(ref size) =>
                    LLVMIntType(size.size()),
                TypeVariant::Bool => LLVMInt1Type(),
                TypeVariant::Unit => LLVMVoidType(),
                TypeVariant::Reference(inner) =>
                    LLVMPointerType(inner.to_llvm(), 0),
                TypeVariant::Diverging => LLVMVoidType(),
                TypeVariant::Infer(_) | TypeVariant::InferInt(_) =>
                    panic!("ICE: Attempted to get the LLVM return type of an \
                        inference variable"),
            }
        }
    }

    pub fn is_final_type(&self) -> bool {
        match *self.variant {
            TypeVariant::SInt(_) | TypeVariant::UInt(_) | TypeVariant::Bool
            | TypeVariant::Unit | TypeVariant::Diverging
                => true,
            TypeVariant::Reference(inner) => inner.is_final_type(),
            TypeVariant::Infer(_) | TypeVariant::InferInt(_) => false,
        }
    }

    pub fn generate_inference_id(&mut self, uf: &mut UnionFind<'t>) {
        self.variant = self.get_inference_type(uf);
    }

    fn get_inference_type(&self, uf: &mut UnionFind<'t>)
            -> &'t TypeVariant<'t> {
        match *self.variant {
            TypeVariant::Infer(None) => {
                self.context.get(TypeVariant::Infer(Some(uf.next_id())))
            }
            TypeVariant::InferInt(None) => {
                self.context.get(TypeVariant::InferInt(Some(uf.next_id())))
            }
            TypeVariant::Reference(inner) => {
                self.context.get(TypeVariant::Reference(
                    Type {
                        context: inner.context,
                        variant: inner.get_inference_type(uf),
                    }
                ))
            }
            ref t @ TypeVariant::SInt(_) | ref t @ TypeVariant::UInt(_)
            | ref t @ TypeVariant::Bool | ref t @ TypeVariant::Diverging
            | ref t @ TypeVariant::Unit | ref t @ TypeVariant::Infer(Some(_))
            | ref t @ TypeVariant::InferInt(Some(_)) => t,
        }
    }

    pub fn finalize(&mut self, uf: &mut UnionFind<'t>) -> Result<(), ()> {
        *self = match self.get_final_ty(uf) {
            Some(t) => t,
            None => return Err(())
        };
        Ok(())
    }

    fn get_final_ty(&self, uf: &mut UnionFind<'t>)
            -> Option<Type<'t>> {
        match *self.variant {
            TypeVariant::SInt(_) | TypeVariant::UInt(_) | TypeVariant::Bool
            | TypeVariant::Unit | TypeVariant::Diverging => {
                Some(*self)
            }
            TypeVariant::Reference(inner) => {
                match inner.get_final_ty(uf) {
                    Some(inner) => Some(Type::ref_(inner)),
                    None => None,
                }
            }
            TypeVariant::Infer(_) | TypeVariant::InferInt(_) => {
                match uf.actual_ty(*self) {
                    Some(t) => t.get_final_ty(uf),
                    None => return None,
                }
            }
        }
    }
}

impl<'t> std::fmt::Display for Type<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let s = match *self.variant {
            TypeVariant::SInt(Int::I8) => "s8",
            TypeVariant::SInt(Int::I16) => "s16",
            TypeVariant::SInt(Int::I32) => "s32",
            TypeVariant::SInt(Int::I64) => "s64",
            TypeVariant::UInt(Int::I8) => "u8",
            TypeVariant::UInt(Int::I16) => "u16",
            TypeVariant::UInt(Int::I32) => "u32",
            TypeVariant::UInt(Int::I64) => "u64",
            TypeVariant::Bool => "bool",
            TypeVariant::Unit => "()",
            TypeVariant::Diverging => "!",
            TypeVariant::Reference(inner) => return write!(f, "&{}", inner),
            TypeVariant::Infer(_) | TypeVariant::InferInt(_) => "_",
        };
        write!(f, "{}", s)
    }
}

impl Int {
    #[allow(dead_code)]
    pub fn shift_mask(&self) -> u64 {
        match *self {
            Int::I8 => (1 << 3) - 1,
            Int::I16 => (1 << 4) - 1,
            Int::I32 => (1 << 5) - 1,
            Int::I64 => (1 << 6) - 1,
        }
    }

    pub fn size(&self) -> u32 {
        match *self {
            Int::I8 => 8,
            Int::I16 => 16,
            Int::I32 => 32,
            Int::I64 => 64,
        }
    }
}

pub struct UnionFind<'t> {
    current_id: u32,
    group_parents: Vec<u32>,
    parents_ty: Vec<Option<Type<'t>>>,
}

impl<'t> UnionFind<'t> {
    pub fn new() -> Self {
        UnionFind {
            current_id: 0,
            group_parents: Vec::new(),
            parents_ty: Vec::new(),
        }
    }

    fn union(&mut self, a: u32, b: u32) {
        let b = self.find(b) as usize;
        self.group_parents[b] = self.find(a);
    }

    fn find(&self, mut n: u32) -> u32 {
        while self.group_parents[n as usize] != n {
            n = self.group_parents[n as usize];
        }
        n
    }

    pub fn unify(&mut self, a: Type<'t>, b: Type<'t>) -> Result<(), ()> {
        let a_actual = self.actual_ty(a);
        let b_actual = self.actual_ty(b);
        match (a_actual, b_actual) {
            (Some(a), Some(b)) => {
                if a.is_final_type() && b.is_final_type() && a == b {
                    Ok(())
                } else {
                    match (*a.variant, *b.variant) {
                        (TypeVariant::Reference(lhs),
                                TypeVariant::Reference(rhs)) => {
                            self.unify(lhs, rhs)
                        }
                        _ => Err(())
                    }
                }
            }
            (None, None) => {
                match (*a.variant, *b.variant) {
                    (TypeVariant::Infer(Some(lid)),
                            TypeVariant::Infer(Some(rid)))
                    | (TypeVariant::Infer(Some(lid)),
                            TypeVariant::InferInt(Some(rid)))
                    | (TypeVariant::InferInt(Some(lid)),
                            TypeVariant::Infer(Some(rid)))
                    | (TypeVariant::InferInt(Some(lid)),
                            TypeVariant::InferInt(Some(rid))) => {
                        self.union(lid, rid);
                        Ok(())
                    }
                    (l, r)
                        => panic!("actual ty isn't working: {:?}, {:?}", l, r)
                }
            }
            (Some(ty), None) => {
                match *b.variant {
                    TypeVariant::Infer(Some(id)) => {
                        let id = self.find(id) as usize;
                        self.parents_ty[id] = Some(ty);
                        Ok(())
                    }
                    TypeVariant::InferInt(Some(id)) => {
                        match *ty.variant {
                            TypeVariant::UInt(_) | TypeVariant::SInt(_) => {
                                let id = self.find(id) as usize;
                                self.parents_ty[id] = Some(ty);
                                Ok(())
                            }
                            _ => {
                                Err(())
                            }
                        }
                    }
                    t => panic!("actual ty isn't working: {:?}", t)
                }
            }
            (None, Some(ty)) => {
                match *a.variant {
                    TypeVariant::Infer(Some(id)) => {
                        let id = self.find(id) as usize;
                        self.parents_ty[id] = Some(ty);
                        Ok(())
                    }
                    TypeVariant::InferInt(Some(id)) => {
                        match *ty.variant {
                            TypeVariant::UInt(_) | TypeVariant::SInt(_) => {
                                let id = self.find(id) as usize;
                                self.parents_ty[id] = Some(ty);
                                Ok(())
                            }
                            _ => {
                                Err(())
                            }
                        }
                    }
                    t => panic!("actual ty isn't working: {:?}", t)
                }
            }
        }
    }

    pub fn actual_ty(&self, ty: Type<'t>) -> Option<Type<'t>> {
        match *ty.variant {
            TypeVariant::Infer(Some(id)) | TypeVariant::InferInt(Some(id)) => {
                self.parents_ty[self.find(id) as usize]
            }

            TypeVariant::Infer(None) | TypeVariant::InferInt(None) => {
                None
            }

            _ => Some(ty)
        }
    }

    fn next_id(&mut self) -> u32 {
        if self.current_id == u32::max_value() {
            panic!()
        } else {
            self.group_parents.push(self.current_id);
            self.parents_ty.push(None);
            self.current_id += 1;
            self.current_id - 1
        }
    }
}
