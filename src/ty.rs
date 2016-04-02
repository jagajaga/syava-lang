use std;
use llvm_sys::prelude::*;
use llvm_sys::core::*;

use parse::{parser_error};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ty {
    SInt(int),
    UInt(int),
    Bool,
    Unit,

    Diverging,

    Infer(Option<u32>),
    InferInt(Option<u32>),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum int {
    I32,
}

impl ty {
    pub fn from_str(s: &str, line: u32) -> Result<ty, parser_error> {
        match s {
            "s32" => Ok(ty::SInt(int::I32)),
            "u32" => Ok(ty::UInt(int::I32)),
            "bool" => Ok(ty::Bool),
            "()" => Ok(ty::Unit),
            "!" => Ok(ty::Diverging),
            s => Err(parser_error::UnknownType {
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
                ty::SInt(ref size) | ty::UInt(ref size) => LLVMIntType(size.size()),
                ty::Bool => LLVMInt1Type(),
                ty::Unit => LLVMStructType(std::ptr::null_mut(), 0, false as LLVMBool),
                ty::Diverging => unreachable!("Diverging is not a real type"),
                ty::Infer(_) | ty::InferInt(_) =>
                    unreachable!("You can't get the llvm type of an inference variable"),
            }
        }
    }

    pub fn to_llvm_ret(&self) -> LLVMTypeRef {
        unsafe {
            match *self {
                ty::SInt(ref size) | ty::UInt(ref size) => LLVMIntType(size.size()),
                ty::Bool => LLVMInt1Type(),
                ty::Unit => LLVMVoidType(),
                ty::Diverging => LLVMVoidType(),
                ty::Infer(_) | ty::InferInt(_) =>
                    unreachable!("You can't get the llvm type of an inference variable"),
            }
        }
    }

    pub fn is_final_type(&self) -> bool {
        match *self {
            ty::SInt(_) | ty::UInt(_) | ty::Bool | ty::Unit | ty::Diverging => true,
            ty::Infer(_) | ty::InferInt(_) => false,
        }
    }

    pub fn generate_inference_id(&mut self, uf: &mut union_find) {
        match *self {
            ty::Infer(ref mut inner @ None) | ty::InferInt(ref mut inner @ None) => {
                *inner = Some(uf.next_id());
            }
            _ => {}
        }
    }
}

impl int {
    pub fn shift_mask(&self) -> u64 {
        match *self {
            // int::I8 => (1 << 3) - 1,
            // int::I16 => (1 << 4) - 1,
            int::I32 => (1 << 5) - 1,
            // int::I64 => (1 << 6) - 1,
        }
    }

    pub fn size(&self) -> u32 {
        match *self {
            // int::I8 => 8,
            // int::I16 => 16,
            int::I32 => 32,
            // int::I64 => 64,
        }
    }
}

pub struct union_find {
    current_id: u32,
    group_parents: Vec<u32>,
    parents_ty: Vec<Option<ty>>,
}

impl union_find {
    pub fn new() -> union_find {
        union_find {
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

    pub fn unify(&mut self, a: ty, b: ty) -> Result<(), ()> {
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
                    (ty::Infer(Some(lid)), ty::Infer(Some(rid)))
                            | (ty::Infer(Some(lid)), ty::InferInt(Some(rid)))
                            | (ty::InferInt(Some(lid)), ty::Infer(Some(rid)))
                            | (ty::InferInt(Some(lid)), ty::InferInt(Some(rid))) => {
                        self.union(lid, rid);
                        Ok(())
                    }
                    (l, r) => panic!("actual ty isn't working: {:?}, {:?}", l, r)
                }
            }
            (Some(ty), None) => {
                match b {
                    ty::Infer(Some(id)) => {
                        let id = self.find(id) as usize;
                        self.parents_ty[id] = Some(ty);
                        Ok(())
                    }
                    ty::InferInt(Some(id)) => {
                        match ty {
                            ty::UInt(_) | ty::SInt(_) => {
                                let id = self.find(id) as usize;
                                self.parents_ty[id] = Some(ty);
                                Ok(())
                            }
                            _ty => {
                                Err(())
                            }
                        }
                    }
                    t => panic!("actual ty isn't working: {:?}", t)
                }
            }
            (None, Some(ty)) => {
                match a {
                    ty::Infer(Some(id)) => {
                        let id = self.find(id) as usize;
                        self.parents_ty[id] = Some(ty);
                        Ok(())
                    }
                    ty::InferInt(Some(id)) => {
                        match ty {
                            ty::UInt(_) | ty::SInt(_) => {
                                let id = self.find(id) as usize;
                                self.parents_ty[id] = Some(ty);
                                Ok(())
                            }
                            _ty => {
                                Err(())
                            }
                        }
                    }
                    t => panic!("actual ty isn't working: {:?}", t)
                }
            }
        }
    }

    pub fn actual_ty(&self, ty: ty) -> Option<ty> {
        match ty {
            ty @ ty::SInt(_) | ty @ ty::UInt(_) | ty @ ty::Bool |
                    ty @ ty::Unit | ty @ ty::Diverging => {
                Some(ty)
            }

            ty::Infer(Some(id)) | ty::InferInt(Some(id)) => {
                self.parents_ty[self.find(id) as usize]
            }

            ty::Infer(None) | ty::InferInt(None) => {
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
