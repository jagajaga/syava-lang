#![allow(non_camel_case_types)]

extern crate llvm_sys;

macro_rules! cstr {
    ($s:expr) => (
        concat!($s, "\0").as_ptr() as *const i8
    )
}

macro_rules! fl {
    () => ((file!(), line!()))
}

enum either<L, R> {
    Left(L),
    Right(R),
}

mod parse;
mod trans;
mod ty;
use parse::lexer;
use trans::ast;

fn main() {
    use std::env;
    use std::io::Read;
    let mut file = Vec::new();
    let input = env::args().nth(1).expect("Provide a path to the source");
    std::fs::File::open(input)
        .unwrap()
        .read_to_end(&mut file)
        .unwrap();
    let file = String::from_utf8(file).unwrap();
    let lexer = lexer::new(&file);

    let ast = match ast::create(lexer) {
        Ok(ast) => ast,
        Err(e) => panic!("\n{:#?}", e),
    };
    println!("{}", ast.build().unwrap());
}

mod tests;
