use std;
use llvm_sys::prelude::*;
use llvm_sys::core::*;

use parse;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    SInt(Int),
    UInt(Int),
    Bool,
    Unit,

    Diverging,

    Infer(Option<u32>),
    InferInt(Option<u32>),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Int {
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Function {
    input: Vec<Ty>,
    output: Ty,
}

impl Function {
    pub fn new(input: Vec<Ty>, output: Ty) -> Function {
        Function {
            input: input,
            output: output,
        }
    }

    pub fn input(&self) -> &[Ty] {
        &self.input
    }

    pub fn output(&self) -> Ty {
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

impl Ty {
    pub fn from_str(s: &str, line: u32) -> Result<Ty, parse::ParserError> {
        match s {
            "s8" => Ok(Ty::SInt(Int::I8)),
            "s16" => Ok(Ty::SInt(Int::I16)),
            "s32" => Ok(Ty::SInt(Int::I32)),
            "s64" => Ok(Ty::SInt(Int::I64)),
            "u8" => Ok(Ty::UInt(Int::I8)),
            "u16" => Ok(Ty::UInt(Int::I16)),
            "u32" => Ok(Ty::UInt(Int::I32)),
            "u64" => Ok(Ty::UInt(Int::I64)),
            "bool" => Ok(Ty::Bool),
            "()" => Ok(Ty::Unit),
            "!" => Ok(Ty::Diverging),
            s => Err(parse::ParserError::UnknownType {
                found: s.to_owned(),
                line: line,
                compiler: fl!(),
            }),
        }
    }

    // TODO: we need to convert zero sized return types into void
    pub fn to_llvm(&self) -> LLVMTypeRef {
        unsafe {
            match *self {
                Ty::SInt(ref size) | Ty::UInt(ref size)
                    => LLVMIntType(size.size()),
                Ty::Bool => LLVMInt1Type(),
                Ty::Unit => LLVMStructType(std::ptr::null_mut(), 0,
                        false as LLVMBool),
                Ty::Diverging
                    => panic!("ICE: Attempted to get the LLVM type of \
                        Diverging"),
                Ty::Infer(_) | Ty::InferInt(_) =>
                    panic!("ICE: Attempted to get the LLVM type of an \
                        inference variable"),
            }
        }
    }

    pub fn to_llvm_ret(&self) -> LLVMTypeRef {
        unsafe {
            match *self {
                Ty::SInt(ref size) | Ty::UInt(ref size) =>
                    LLVMIntType(size.size()),
                Ty::Bool => LLVMInt1Type(),
                Ty::Unit => LLVMVoidType(),
                Ty::Diverging => LLVMVoidType(),
                Ty::Infer(_) | Ty::InferInt(_) =>
                    panic!("ICE: Attempted to get the LLVM return type of an \
                        inference variable"),
            }
        }
    }

    pub fn is_final_type(&self) -> bool {
        match *self {
            Ty::SInt(_) | Ty::UInt(_) | Ty::Bool | Ty::Unit | Ty::Diverging
                => true,
            Ty::Infer(_) | Ty::InferInt(_) => false,
        }
    }

    pub fn generate_inference_id(&mut self, uf: &mut UnionFind) {
        match *self {
            Ty::Infer(ref mut inner @ None)
            | Ty::InferInt(ref mut inner @ None) => {
                *inner = Some(uf.next_id());
            }
            _ => {}
        }
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let s = match *self {
            Ty::SInt(Int::I8) => "s8",
            Ty::SInt(Int::I16) => "s16",
            Ty::SInt(Int::I32) => "s32",
            Ty::SInt(Int::I64) => "s64",
            Ty::UInt(Int::I8) => "u8",
            Ty::UInt(Int::I16) => "u16",
            Ty::UInt(Int::I32) => "u32",
            Ty::UInt(Int::I64) => "u64",
            Ty::Bool => "bool",
            Ty::Unit => "()",
            Ty::Diverging => "!",
            Ty::Infer(_) | Ty::InferInt(_) => "_",
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

pub struct UnionFind {
    current_id: u32,
    group_parents: Vec<u32>,
    parents_ty: Vec<Option<Ty>>,
}

impl UnionFind {
    pub fn new() -> UnionFind {
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

    pub fn unify(&mut self, a: Ty, b: Ty) -> Result<(), ()> {
        let a_actual = self.actual_ty(a);
        let b_actual = self.actual_ty(b);
        match (a_actual, b_actual) {
            (Some(a), Some(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err(())
                }
            }
            (None, None) => {
                match (a, b) {
                    (Ty::Infer(Some(lid)), Ty::Infer(Some(rid)))
                    | (Ty::Infer(Some(lid)), Ty::InferInt(Some(rid)))
                    | (Ty::InferInt(Some(lid)), Ty::Infer(Some(rid)))
                    | (Ty::InferInt(Some(lid)), Ty::InferInt(Some(rid))) => {
                        self.union(lid, rid);
                        Ok(())
                    }
                    (l, r)
                        => panic!("actual ty isn't working: {:?}, {:?}", l, r)
                }
            }
            (Some(ty), None) => {
                match b {
                    Ty::Infer(Some(id)) => {
                        let id = self.find(id) as usize;
                        self.parents_ty[id] = Some(ty);
                        Ok(())
                    }
                    Ty::InferInt(Some(id)) => {
                        match ty {
                            Ty::UInt(_) | Ty::SInt(_) => {
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
                match a {
                    Ty::Infer(Some(id)) => {
                        let id = self.find(id) as usize;
                        self.parents_ty[id] = Some(ty);
                        Ok(())
                    }
                    Ty::InferInt(Some(id)) => {
                        match ty {
                            Ty::UInt(_) | Ty::SInt(_) => {
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

    pub fn actual_ty(&self, ty: Ty) -> Option<Ty> {
        match ty {
            ty @ Ty::SInt(_) | ty @ Ty::UInt(_) | ty @ Ty::Bool |
                    ty @ Ty::Unit | ty @ Ty::Diverging => {
                Some(ty)
            }

            Ty::Infer(Some(id)) | Ty::InferInt(Some(id)) => {
                self.parents_ty[self.find(id) as usize]
            }

            Ty::Infer(None) | Ty::InferInt(None) => {
                None
            }
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
