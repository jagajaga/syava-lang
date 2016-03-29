#![allow(match_of_unit_variant_via_paren_dotdot)]
#![feature(box_syntax)]

#![feature(plugin)]
#![plugin(plex)]

use std::io::Read;

mod lexer {
    use std::fmt::Display;
    use std::fmt::Formatter;
    use std::fmt;

    #[derive(PartialEq, Clone, Debug)]
    pub enum Token {
        Def,
        Extern,
        Delimiter, // ';' character
        OpeningParenthesis,
        ClosingParenthesis,
        Comma,
        Identifier(String),
        Number(f64),
        Operator(String),

        Whitespace,
        Comment,
    }

    // ► The Specials - Too Much Too Young

    lexer! {
        fn take_token(text: 'a) -> (Token, &'a str); // Token and the rest

        r#"[ \t\r\n]+"# => (Token::Whitespace, text),
        // "C-style" comments (/* .. */) - can't contain "*/"
        r#"/[*](~(.*[*]/.*))[*]/"# => (Token::Comment, text),
        // "C++-style" comments (// ...)
        r#"//[^\n]*"# => (Token::Comment, text),
        r#"def"# => (Token::Def, text),
        r#"extern"# => (Token::Extern, text),
        r#"[a-zA-Z_][a-zA-Z0-9_]*"# => (Token::Identifier(text.to_owned()), text),
        r#"[0-9.]+"# => {
            (if let Ok(i) = text.parse() {
                Token::Number(i)
            } else {
                panic!("float {} is out of range", text)
            }, text)
        },
        r#"\("# => (Token::OpeningParenthesis, text),
        r#"\)"# => (Token::ClosingParenthesis, text),
        r#";"# => (Token::Delimiter, text),
        r#","# => (Token::Comma, text),
        r#"[\+\-\*\/^:<>]+"# => (Token::Operator(text.to_owned()), text),
    }

    /// The Lexer
    #[derive(PartialEq, Clone, Debug, Copy)]
    pub struct Lexer<'a> {
        source: &'a str,
        remaining: &'a str,
    }

    impl<'a> Lexer<'a> {
        /// Create a new Lexer
        pub fn new(src: &'a str) -> Self {
            Lexer {
                source: src,
                remaining: src,
            }
        }
    }

    impl<'a> Iterator for Lexer<'a> {
        type Item = (Token, TextSpan);

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some(token) = take_token(&mut self.remaining) {
                    if let (Token::Whitespace, _) = token {
                        continue;
                    } else {
                        let (token, span) = token;
                        let text_span = TextSpan::from(self.source, self.remaining, span);
                        return Some((token, text_span));
                    }
                } else {
                    return None;
                }
            }
        }
    }

    /// A structure for grouping byte offset of text spans.
    #[derive(Debug)]
    #[derive(Copy, Clone)]
    #[derive(Eq, PartialEq)]
    pub struct TextSpan {
        pub low: usize,
        pub high: usize,
    }

    impl TextSpan {
        /// Create a text span from a string and a slice of it.
        pub fn from(source: &str, remaining: &str, token: &str) -> TextSpan {
            let high = source.len() - remaining.len();
            let low = high - token.len();
            TextSpan {
                low: low,
                high: high,
            }
        }

        pub fn merge(a: TextSpan, b: TextSpan) -> TextSpan {
            let low = if a.low < b.low {
                a.low
            } else {
                b.low
            };
            let high = if a.high > b.high {
                a.high
            } else {
                b.high
            };
            TextSpan {
                low: low,
                high: high,
            }
        }
    }

    impl Display for TextSpan {
        fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
            write!(f, "[{}, {})", self.low, self.high)
        }
    }
}

mod ast {
    pub use self::ASTNode::{ExternNode, FunctionNode};
    pub use self::Expression::{LiteralExpr, VariableExpr, BinaryExpr, CallExpr, UnprocessedExpr,
                               BinaryOperator};

    #[derive(PartialEq, Clone, Debug)]
    pub enum ASTNode {
        ExternNode(Prototype),
        FunctionNode(Function),
    }

    #[derive(PartialEq, Clone, Debug)]
    pub struct Function {
        pub prototype: Prototype,
        pub body: Expression,
    }

    #[derive(PartialEq, Clone, Debug)]
    pub struct Prototype {
        pub name: String,
        pub args: Vec<String>,
    }

    #[derive(PartialEq, Clone, Debug)]
    pub enum Expression {
        LiteralExpr(f64),
        VariableExpr(String),
        BinaryExpr(String, Box<Expression>, Box<Expression>),
        CallExpr(String, Vec<Expression>),
        UnprocessedExpr(Vec<Expression>),
        BinaryOperator(String),
    }
}

mod parser {
    // Grammar:
    //
    // program : [[statement | expression] Delimiter ?]*;
    // statement : [declaration | definition];
    // declaration : Extern prototype;
    // definition : Def prototype expression;
    // prototype : Identifier OpeningParenthesis [Identifier Comma ?]* ClosingParenthesis;
    // expression : [primary_expr (Operator primary_expr)*];
    // primary_expr : [Identifier | Number | call_expr | parenthesis_expr];
    // call_expr : Identifier OpeningParenthesis [expression Comma ?]* ClosingParenthesis;
    // parenthesis_expr: OpeningParenthesis expression ClosingParenthesis;
    //

    use std::collections::HashMap;

    use ast::*;
    use lexer::*;

    use lexer::Token::*;

    pub struct ParserSettings {
        operator_precedence: HashMap<String, i32>,
    }

    pub fn default_parser_settings() -> ParserSettings {
        let mut operator_precedence = HashMap::new();
        operator_precedence.insert("<".to_string(), 10);
        operator_precedence.insert("+".to_string(), 20);
        operator_precedence.insert("-".to_string(), 20);
        operator_precedence.insert("*".to_string(), 40);

        ParserSettings { operator_precedence: operator_precedence }
    }

    parser! {
        fn parse_(Token, TextSpan);

        // Ignore spans
        (a, b) {
            TextSpan::merge(a, b)
        }

        program: Vec<ASTNode> {
            => vec![],
            stex[e] rest[mut p] => {
                p.insert(0, e);
                p
            },
        }

        stex: ASTNode {
            statement[e] => e,
            expression[e] => e
        }
        
        rest: Vec<ASTNode> {
            program[p] => {
                p
            },
            Delimiter program[p] => {
                p
            },
        }
        
        statement: ASTNode {
            declaration[e] => {
                e
            },
            definition[e] => {
                e
            }
        }
        
        declaration: ASTNode {
            Extern prototype[p] => {
                ExternNode(p)
            },
        }

        definition: ASTNode {
            Def prototype[p] expr[e] => {
                FunctionNode(Function {
                    prototype: p,
                    body: e,
                })
            }
        }

        prototype: Prototype {
            Identifier(id) OpeningParenthesis arguments[a] ClosingParenthesis => Prototype {
                name: id,
                args: a,
            }
        }

        arguments: Vec<String> {
            => vec![],
            Identifier(id) extra_args[mut a] => {
                a.insert(0, id);
                a
            }
        }

        extra_args: Vec<String> {
            Comma arguments[a] => {
                a
            },
            arguments[a] => {
                a
            }
        }

        expression: ASTNode {
            expr[e] => {
                let prototype = Prototype {name: "".to_string(), args: vec![]};
                FunctionNode (Function {
                    prototype: prototype,
                    body: e
                })
            }
        }

        primary_expression: Expression {
            #[no_reduce(OpeningParenthesis)]
            Identifier(id) => VariableExpr(id),
            Number(val) => LiteralExpr(val),
            Identifier(id) OpeningParenthesis many_exprs[args] ClosingParenthesis => {
                CallExpr(id, args)
            },
            parenthesis_expr[e] => e,
        }

        many_exprs: Vec<Expression> {
            => vec![],
            expr[e] extra_exprs[mut exprs] => {
                exprs.insert(0, e);
                exprs
            }
        }

        extra_exprs: Vec<Expression> {
            Comma many_exprs[a] => {
                a
            },
            many_exprs[a] => {
                a
            }
        }

        parenthesis_expr: Expression {
            OpeningParenthesis expr[e] ClosingParenthesis => e
        }
        
        expr: Expression {
           primary_expression[e] => e,
           primary_expression[e] binary_expr[mut st] => {
               st.insert(0, e);
               UnprocessedExpr(st)
           }
        }

        binary_expr: Vec<Expression> {
            Operator(op) primary_expression[e] extra_binary_exprs[mut ebe] => {
                ebe.insert(0, e);
                ebe.insert(0, BinaryOperator(op));
                ebe
            },
        }

        extra_binary_exprs: Vec<Expression> {
            => vec![],
            Operator(op) primary_expression[e] extra_binary_exprs[mut ebe] => {
                ebe.insert(0, e);
                ebe.insert(0, BinaryOperator(op));
                ebe
            },
        }
    }

    fn sh_yard(ast: &Vec<Expression>, operator_precedence: &ParserSettings) -> Expression {
//TODO
        BinaryExpr("+".to_string(), box LiteralExpr(1.0), box LiteralExpr(1.0))
    }

    fn shunting_yard(ast: &Vec<ASTNode>, operator_precedence: &ParserSettings) -> Vec<ASTNode> {
        ast.iter()
           .map(|x| {
               match *x {
                   FunctionNode(ref f) => {
                       FunctionNode(Function {
                           prototype: f.prototype.clone(),
                           body: match f.body {
                               UnprocessedExpr(ref ue) => sh_yard(ue, operator_precedence),
                               _ => f.body.clone(),
                           },
                       })
                   }
                   ref e => e.clone(),
               }
           })
           .collect()
    }

    pub fn parse<I: Iterator<Item = (Token, TextSpan)>>
        (i: I,
         operator_precedence: &ParserSettings)
         -> Result<Vec<ASTNode>, (Option<(Token, TextSpan)>, &'static str)> {
        match parse_(i) {
            Ok(a) => Ok(shunting_yard(&a, operator_precedence)),
            e => e,
        }
    }
}

fn main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    let lexer = lexer::Lexer::new(&s);
    for i in lexer {
        println!("{:?}", i);
    }
    let mut parser_settings = parser::default_parser_settings();
    let parse_result: Vec<ast::ASTNode> = parser::parse(lexer, &parser_settings).unwrap();
    println!("{:?}", parse_result);
}

#[test]
fn test_parser() {
    use parser::*;
    use ast::*;
    use lexer::*;
    let tests = vec![
        ("extern sin();", vec![ExternNode(Prototype{name:"sin".to_string(), args:vec![]})]),
        ("", vec![]),
        ("def foo(x y x);", vec![FunctionNode(Function { prototype: Prototype { name: "foo".to_string(), args: vec!["x".to_string(), "y".to_string(), "x".to_string()] }, body: LiteralExpr(0.0) })]),
    ];

    for tc in tests {
        let parsed = lexer::Lexer::new(tc.0);
        let r = parser::parse(parsed).unwrap();
        assert_eq!(tc.1, r);
    }
}
