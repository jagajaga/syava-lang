use trans::{ast, ast_error};
use parse::{lexer, parser_error, token_type};

#[derive(Debug)]
#[derive(PartialEq)]
enum errors {
    Ast(ast_error),
    Parser(parser_error),
}

fn test(s: &'static str) -> Result<String, errors> {
    let lexer = lexer::new(&s.clone());
    let ast = match ast::create(lexer) {
        Ok(ast) => ast,
        Err(e) => return Err(errors::Parser(e)),
    };
    match ast.build() {
        Ok(a) => Ok(a),
        Err(e) => Err(errors::Ast(e)),
    }
}

#[test]
fn no_main() {
    assert_eq!(test(""),
               Err(errors::Ast(ast_error::FunctionDoesntExist("main".to_string()))))
}

#[test]
fn fib_10() {
    let test_program1 = r#"
        fn main() -> s32 {
            return fib(10);
        }

        fn fib(n: s32) -> s32 {
            let ret: s32 = if fib_invalid(n) {
                -1
            } else if fib_base(n) {
                1
            } else {
                fib(n - 1) + fib(n - 2)
            };

            return ret;
        }

        fn fib_invalid(n: s32) -> bool {
            return n < 0;
        }

        fn fib_base(n: s32) -> bool {
            return n == 0 || n == 1;
        }
    "#;
    assert_eq!(test(test_program1), Ok("89".to_string()))
}

#[test]
fn simple_function() {
    assert_eq!(test("fn main() -> s32 { return 42; }"),
               Ok("42".to_string()));
}

#[test]
fn wrong_return_main_type() {
    match test("fn main() { return true; }") {
        Err(errors::Ast(ast_error::IncorrectType { expected: a, found: b, .. })) => assert!(a != b),
        _ => panic!("Error in compiler because test is passing or there is an parsing error"),
    }
}

#[test]
fn simple_add_2_to_1_plus_1() {
    assert_eq!(test("fn main() -> s32 { return add2 (1+1); } fn add2 (a: s32) -> s32 { return a \
                     + 2;}"),
               Ok("4".to_string()))
}

#[test]
fn simple_mul_2_to_1_plus_1() {
    assert_eq!(test("fn main() -> s32 { return mul2 (1+1); } fn mul2 (a: s32) -> s32 { return a \
                     * 2;}"),
               Ok("4".to_string()))
}

#[test]
fn function_doesnt_exist() {
    assert_eq!(test("fn main() -> s32 { return add2 (1+1); } fn mul2 (a: s32) -> s32 { return a \
                     * 2;}"),
               Err(errors::Ast(ast_error::FunctionDoesntExist("add2".to_string()))))
}

#[test]
fn simple_div_2_to_1_plus_1() {
    assert_eq!(test("fn main() -> s32 { return div2 (1+1); } fn div2 (a: s32) -> s32 { return a \
                     / 2;}"),
               Ok("1".to_string()))
}

#[test]
fn simple_return_if() {
    assert_eq!(test("fn main() -> s32 { return if 1 > 2 {1} else {2}; }"),
               Ok("2".to_string()))
}

#[test]
fn function_without_statement() {
    match test("fn main() -> s32 { if 1 > 2 {return 1} else {return 2}; }") {
        Err(errors::Parser(parser_error::UnexpectedToken { expected: a, .. })) => {
            assert!(a == token_type::Statement)
        }
        _ => panic!("Error in compiler because test is passing or there is an parsing error"),
    }
}
