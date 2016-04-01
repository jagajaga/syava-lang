use std;
use llvm_sys::prelude::*;
use llvm_sys::core::*;

use parse::{parser_error};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ty {
    SInt(int),
    UInt(int),
    Bool,
    Unit,
    Diverging,

    Infer(Option<u32>),
    InferInt(Option<u32>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
            ty::SInt(_) | ty::UInt(_) | ty::Bool | ty::Unit => true,
            ty::Diverging | ty::Infer(_) | ty::InferInt(_) => false,
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
}

impl union_find {
    pub fn new() -> union_find {
        union_find {
            current_id: 0,
        }
    }

    // very C++ right now
    pub fn unify(&mut self, a: &ty, b: &ty) -> Result<ty, ()> {
        if a == b {
            return Ok(a.clone());
        }

        if a.is_final_type() {
            match *b {
                ty::Diverging => {
                    return Ok(a.clone()) // not sure about this
                }
                ty::Infer(_id) => {
                    return Ok(a.clone())
                }
                ty::InferInt(_id) => {
                    match *a {
                        ty::SInt(_) | ty::UInt(_) => return Ok(a.clone()),
                        _ => return Err(()),
                    }
                }
                ref b if b.is_final_type() => {
                    return Err(())
                }
                _ => unreachable!(),
            }
        }

        if b.is_final_type() {
            match *a {
                ty::Diverging => {
                    return Ok(b.clone()) // not sure about this
                }
                ty::Infer(_id) => {
                    return Ok(b.clone())
                }
                ty::InferInt(_id) => {
                    match *b {
                        ty::SInt(_) | ty::UInt(_) => return Ok(b.clone()),
                        _ => return Err(()),
                    }
                }
                ref a if a.is_final_type() => {
                    return Err(())
                }
                _ => unreachable!(),
            }
        }

        Err(())
    }

    fn next_id(&mut self) -> u32 {
        if self.current_id == u32::max_value() {
            panic!()
        } else {
            self.current_id += 1;
            self.current_id - 1
        }
    }
}
