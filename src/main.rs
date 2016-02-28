#![allow(match_of_unit_variant_via_paren_dotdot)]

#![feature(plugin)]
#![plugin(plex)]

use std::io::Read;

mod lexer {
    use std::fmt::Display;
    use std::fmt::Formatter;
    use std::fmt;

    #[derive(Debug, Clone)]
    #[derive(PartialEq)]
    pub enum Token {
        EOF,
        Def,
        Extern,
        Identifier(String),
        Number(f32),

        Whitespace,
        Comment,
    }

    impl Token {
        pub fn contents(&self) -> Option<&str> {
            let s = match *self {
                Token::Identifier(ref s) => s,
                _ => return None,
            };
            Some(s)
        }
    }

    /// The Lexer
    #[derive(Debug)]
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

fn main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    let mut result = lexer::Lexer::new(&s);
    for i in result {
        println!("{:?}", i);
    }
}
