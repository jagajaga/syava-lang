use std;
use llvm_sys::prelude::*;
use llvm_sys::core::*;

use parse::parser_error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ty {
    Int(int),
    Bool,
    UInt(int),
    Unit,
    Generic,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum int {
    I32,
}

impl ty {
    pub fn from_str(s: &str, line: u32) -> Result<ty, parser_error> {
        match s {
            "s32" => Ok(ty::Int(int::I32)),
            "u32" => Ok(ty::UInt(int::I32)),
            "bool" => Ok(ty::Bool),
            "()" => Ok(ty::Unit),
            s => {
                Err(parser_error::UnknownType {
                    found: s.to_owned(),
                    line: line,
                    compiler: fl!(),
                })
            }
        }
    }

    pub fn to_llvm(&self) -> LLVMTypeRef {
        unsafe {
            match *self {
                ty::Int(ref size) | ty::UInt(ref size) => LLVMIntType(size.size()),
                ty::Bool => LLVMInt1Type(),
                ty::Unit => LLVMStructType(std::ptr::null_mut(), 0, false as LLVMBool),
                ty::Generic => unreachable!("Generic is not a real type"),
            }
        }
    }

    pub fn to_llvm_ret(&self) -> LLVMTypeRef {
        unsafe {
            match *self {
                ty::Int(ref size) | ty::UInt(ref size) => LLVMIntType(size.size()),
                ty::Bool => LLVMInt1Type(),
                ty::Unit => LLVMVoidType(),
                ty::Generic => unreachable!("Generic is not a real type"),
            }
        }
    }
}

impl int {
    pub fn size(&self) -> u32 {
        match *self {
            int::I32 => 32,
        }
    }
}
