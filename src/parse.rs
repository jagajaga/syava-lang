use std::str;
use ast;
use ast::expr::{Stmt, Expr, ExprKind};
use ty::{self, Type, TypeContext};
use Either::{self, Left, Right};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    // Item
    KeywordFn,

    // Statement
    KeywordLet,
    KeywordReturn,
    CloseBrace,

    // Expression
    KeywordTrue,
    KeywordFalse,
    KeywordIf,
    KeywordElse,
    Ident(String),
    Integer {
        value: u64,
        suffix: String,
    },

    Operand(Operand),

    // Misc
    OpenParen,
    CloseParen,
    OpenBrace,
    Semicolon,
    Colon,
    Comma,
    SkinnyArrow,
    Equals,
    Eof,
}

impl Token {
    pub fn ty(&self) -> TokenType {
        match *self {
            Token::KeywordFn => TokenType::Item,

            Token::KeywordLet | Token::CloseBrace => TokenType::Statement,

            Token::KeywordReturn |
            Token::KeywordTrue |
            Token::KeywordFalse |
            Token::KeywordIf |
            Token::Ident(_) |
            Token::Integer { .. } => TokenType::Expression,

            Token::Operand(_) => TokenType::Operand,

            Token::KeywordElse |
            Token::OpenParen |
            Token::CloseParen |
            Token::OpenBrace |
            Token::Semicolon |
            Token::Colon |
            Token::SkinnyArrow |
            Token::Comma |
            Token::Equals |
            Token::Eof => TokenType::Misc,
        }
    }
}

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Mul,
    Div,
    Rem,

    Plus,
    Minus,

    Shl,
    Shr,

    And,
    Xor,
    Or,

    EqualsEquals,
    NotEquals,
    LessThan,
    LessThanEquals,
    GreaterThan,
    GreaterThanEquals,

    AndAnd,
    OrOr,

    Not,
}

impl Operand {
    pub fn precedence(&self) -> u8 {
        match *self {
            Operand::Mul | Operand::Div | Operand::Rem => 9,
            Operand::Plus | Operand::Minus => 8,
            Operand::Shl | Operand::Shr => 7,
            Operand::And => 6,
            Operand::Xor => 5,
            Operand::Or => 4,
            Operand::EqualsEquals |
            Operand::NotEquals |
            Operand::LessThan |
            Operand::LessThanEquals |
            Operand::GreaterThan |
            Operand::GreaterThanEquals => 3,
            Operand::AndAnd => 2,
            Operand::OrOr => 1,
            Operand::Not => unreachable!("Not (`!`) is not a binop"),
        }
    }

    // simply a convenience function
    pub fn expr<'t>(&self, lhs: Expr<'t>, rhs: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Expr<'t> {
        self.precedence(); // makes certain that self is a binop
        Expr {
            kind: ExprKind::Binop {
                op: *self,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty: Type::infer(ctxt),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenType {
    Item,
    Statement,
    Expression,
    Operand,
    Misc,

    Specific(Token),
    AnyOf(Vec<Token>),
}

pub struct Lexer<'src> {
    src: str::Chars<'src>,
    readahead: Vec<char>,
    line: u32,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &str) -> Lexer {
        Lexer {
            src: src.chars(),
            readahead: Vec::with_capacity(1),
            line: 1,
        }
    }

    fn ident(&mut self, first: char) -> String {
        let mut ret = String::new();
        ret.push(first);
        loop {
            match self.getc() {
                Some(c) if Self::is_ident(c) => ret.push(c),
                Some(c) => {
                    self.ungetc(c);
                    break;
                }
                None => break,
            }
        }

        ret
    }

    #[inline(always)]
    fn is_start_of_ident(c: char) -> bool {
        (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
    }

    #[inline(always)]
    fn is_ident(c: char) -> bool {
        Self::is_start_of_ident(c) || Self::is_integer(c)
    }

    #[inline(always)]
    fn is_integer(c: char) -> bool {
        c >= '0' && c <= '9'
    }

    fn block_comment(&mut self) -> Result<(), ParserError> {
        loop {
            let c = self.getc();
            if c == Some('*') {
                let c = self.getc();
                if c == Some('/') {
                    return Ok(());
                } else if c == Some('\n') {
                    self.line += 1;
                } else if c == None {
                    return Err(ParserError::UnclosedComment);
                }
            } else if c == Some('/') {
                let c = self.getc();
                if c == Some('*') {
                    try!(self.block_comment())
                } else if c == Some('\n') {
                    self.line += 1;
                } else if c == None {
                    return Err(ParserError::UnclosedComment);
                }
            } else if c == Some('\n') {
                self.line += 1;
            } else if c == None {
                return Err(ParserError::UnclosedComment);
            }
        }
    }

    fn line_comment(&mut self) {
        loop {
            match self.getc() {
                Some('\n') => {
                    self.line += 1;
                    break;
                }
                None => break,
                Some(_) => {}
            }
        }
    }

    fn getc(&mut self) -> Option<char> {
        if let Some(c) = self.readahead.pop() {
            Some(c)
        } else if let Some(c) = self.src.next() {
            Some(c)
        } else {
            None
        }
    }
    fn ungetc(&mut self, c: char) {
        // make sure that readahead is only 1
        assert!(self.readahead.len() == 0);
        self.readahead.push(c)
    }

    fn eat_whitespace(&mut self) -> Option<()> {
        loop {
            let c = match self.getc() {
                Some(c) => c,
                None => return None,
            };
            if !Self::is_whitespace(c) {
                self.ungetc(c);
                break;
            } else if c == '\n' {
                self.line += 1;
            }
        }

        Some(())
    }

    fn is_whitespace(c: char) -> bool {
        c == '\t' || c == '\n' || c == '\r' || c == ' '
    }

    pub fn next_token(&mut self) -> Result<Token, ParserError> {
        self.eat_whitespace();
        let first = match self.getc() {
            Some(c) => c,
            None => return Ok(Token::Eof),
        };
        match first {
            '(' => Ok(Token::OpenParen),
            ')' => Ok(Token::CloseParen),
            '{' => Ok(Token::OpenBrace),
            '}' => Ok(Token::CloseBrace),
            ';' => Ok(Token::Semicolon),
            ':' => Ok(Token::Colon),
            ',' => Ok(Token::Comma),
            '*' => Ok(Token::Operand(Operand::Mul)),
            '%' => Ok(Token::Operand(Operand::Rem)),
            '+' => Ok(Token::Operand(Operand::Plus)),
            '-' => {
                match self.getc() {
                    Some('>') => {
                        return Ok(Token::SkinnyArrow);
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(Token::Operand(Operand::Minus))
            }
            '/' => {
                match self.getc() {
                    Some('*') => {
                        try!(self.block_comment());
                        return self.next_token();
                    }
                    Some('/') => {
                        self.line_comment();
                        return self.next_token();
                    }
                    Some(c) => {
                        self.ungetc(c);
                    }
                    None => {}
                }
                Ok(Token::Operand(Operand::Div))
            }

            '!' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(Token::Operand(Operand::NotEquals));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(Token::Operand(Operand::Not))
            }
            '<' => {
                match self.getc() {
                    Some('<') => {
                        return Ok(Token::Operand(Operand::Shl));
                    }
                    Some('=') => {
                        return Ok(Token::Operand(Operand::LessThanEquals));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(Token::Operand(Operand::LessThan))
            }
            '>' => {
                match self.getc() {
                    Some('>') => {
                        return Ok(Token::Operand(Operand::Shr));
                    }
                    Some('=') => {
                        return Ok(Token::Operand(Operand::GreaterThanEquals));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(Token::Operand(Operand::GreaterThan))
            }
            '=' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(Token::Operand(Operand::EqualsEquals));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(Token::Equals)
            }
            '&' => {
                match self.getc() {
                    Some('&') => {
                        return Ok(Token::Operand(Operand::AndAnd));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(Token::Operand(Operand::And))
            }
            '|' => {
                match self.getc() {
                    Some('|') => {
                        return Ok(Token::Operand(Operand::OrOr));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(Token::Operand(Operand::Or))
            }
            '^' => Ok(Token::Operand(Operand::Xor)),

            c if Self::is_start_of_ident(c) => {
                let ident = self.ident(c);
                match &ident[..] {
                    "fn" => return Ok(Token::KeywordFn),
                    "return" => return Ok(Token::KeywordReturn),
                    "let" => return Ok(Token::KeywordLet),
                    "if" => return Ok(Token::KeywordIf),
                    "else" => return Ok(Token::KeywordElse),
                    "true" => return Ok(Token::KeywordTrue),
                    "false" => return Ok(Token::KeywordFalse),
                    _ => {}
                }

                Ok(Token::Ident(ident))
            }
            c if Self::is_integer(c) => {
                let mut string = String::new();
                string.push(c);
                let mut suffix = String::new();
                loop {
                    match self.getc() {
                        Some(c @ '0'...'9') => string.push(c),
                        Some(c) => {
                            self.ungetc(c);
                            break;
                        }
                        None => break,
                    }
                }
                loop {
                    match self.getc() {
                        Some(c) if Self::is_ident(c) => suffix.push(c),
                        Some(c) => {
                            self.ungetc(c);
                            break;
                        }
                        None => break,
                    }
                }

                let value = string.parse::<u64>()
                                  .expect("we pushed something which wasn't 0...9 onto a string");

                Ok(Token::Integer {
                    value: value,
                    suffix: suffix,
                })
            }

            i => {
                Err(ParserError::InvalidToken {
                    token: i,
                    line: self.line,
                    compiler: fl!(),
                })
            }
        }
    }
}

#[derive(Debug)]
pub enum ParserError {
    ExpectedEof,

    UnclosedComment,
    UnknownType {
        found: String,
        line: u32,
        compiler: (&'static str, u32),
    },
    InvalidToken {
        token: char,
        line: u32,
        compiler: (&'static str, u32),
    },
    DuplicatedFunctionArgument {
        argument: String,
        function: String,
        compiler: (&'static str, u32),
    },
    DuplicatedFunction {
        function: String,
        compiler: (&'static str, u32),
    },
    UnexpectedToken {
        found: Token,
        expected: TokenType,
        line: u32,
        compiler: (&'static str, u32),
    },
    ExpectedSemicolon {
        line: u32,
        compiler: (&'static str, u32),
    },
    InvalidSuffix {
        suffix: String,
        line: u32,
        compiler: (&'static str, u32),
    },
}

pub struct Parser<'src> {
    lexer: Lexer<'src>,
    peekahead: Option<Token>,
}

impl<'src> Parser<'src> {
    pub fn new(lexer: Lexer<'src>) -> Self {
        Parser {
            lexer: lexer,
            peekahead: None,
        }
    }

    #[inline(always)]
    pub fn line(&self) -> u32 {
        self.lexer.line
    }

    fn get_token(&mut self) -> Result<Token, ParserError> {
        match self.peekahead.take() {
            Some(tok) => Ok(tok),
            None => self.lexer.next_token(),
        }
    }
    fn peek_token(&mut self) -> Result<Token, ParserError> {
        let tok = match self.peekahead {
            Some(ref tok) => return Ok(tok.clone()),
            None => try!(self.lexer.next_token()),
        };
        self.peekahead = Some(tok.clone());
        Ok(tok)
    }
    fn unget_token(&mut self, token: Token) {
        assert!(self.peekahead.is_none(),
                "current: {:?}, attempted to unget: {:?}, line: {}",
                self.peekahead,
                token,
                self.line());
        self.peekahead = Some(token);
    }

    pub fn item<'t>(&mut self, ctxt: &'t TypeContext<'t>) -> Result<ast::Item<'t>, ParserError> {
        match try!(self.get_token()) {
            Token::KeywordFn => self.function(ctxt),
            Token::Eof => Err(ParserError::ExpectedEof),
            tok => {
                Err(ParserError::UnexpectedToken {
                    found: tok,
                    expected: TokenType::Item,
                    line: self.line(),
                    compiler: fl!(),
                })
            }
        }
    }

    fn maybe_peek_ty(&mut self, expected: &TokenType) -> Result<Option<Token>, ParserError> {
        let token = try!(self.peek_token());
        match *expected {
            TokenType::Specific(ref t) => {
                if &token == t {
                    return Ok(Some(token));
                }
            }
            TokenType::AnyOf(ref t) => {
                if t.contains(&token) {
                    return Ok(Some(token));
                }
            }
            ref tt => {
                if &token.ty() == tt {
                    return Ok(Some(token));
                }
            }
        }
        Ok(None)
    }

    fn peek_ty(&mut self, expected: TokenType, line: u32) -> Result<Token, ParserError> {
        match self.maybe_peek_ty(&expected) {
            Ok(Some(t)) => return Ok(t),
            Err(e) => return Err(e),
            _ => {}
        }
        Err(ParserError::UnexpectedToken {
            found: try!(self.get_token()),
            expected: expected,
            line: self.line(),
            compiler: (file!(), line),
        })
    }

    fn maybe_eat_ty(&mut self, expected: &TokenType) -> Result<Option<Token>, ParserError> {
        match try!(self.maybe_peek_ty(expected)) {
            Some(_) => self.get_token().map(|t| Some(t)),
            None => Ok(None),
        }
    }

    fn eat_ty(&mut self, expected: TokenType, compiler_line: u32) -> Result<Token, ParserError> {
        match self.maybe_eat_ty(&expected) {
            Ok(Some(t)) => return Ok(t),
            Err(e) => return Err(e),
            _ => {}
        }
        Err(ParserError::UnexpectedToken {
            found: try!(self.get_token()),
            expected: expected,
            line: self.line(),
            compiler: (file!(), compiler_line),
        })
    }


    fn maybe_eat(&mut self, expected: Token) -> Result<Option<Token>, ParserError> {
        self.maybe_eat_ty(&TokenType::Specific(expected))
    }

    fn eat(&mut self, expected: Token, line: u32) -> Result<Token, ParserError> {
        self.eat_ty(TokenType::Specific(expected), line)
    }

    fn maybe_peek(&mut self, expected: Token) -> Result<Option<Token>, ParserError> {
        self.maybe_peek_ty(&TokenType::Specific(expected))
    }

    #[allow(dead_code)]
    fn peek(&mut self, expected: Token, line: u32) -> Result<Token, ParserError> {
        self.peek_ty(TokenType::Specific(expected), line)
    }

    fn parse_ident(&mut self, line: u32) -> Result<String, ParserError> {
        match try!(self.get_token()) {
            Token::Ident(s) => Ok(s),
            tok => {
                Err(ParserError::UnexpectedToken {
                    found: tok,
                    expected: TokenType::Specific(Token::Ident(String::new())),
                    line: self.line(),
                    compiler: (file!(), line),
                })
            }
        }
    }

    fn parse_ty<'t>(&mut self,
                    ctxt: &'t TypeContext<'t>,
                    line: u32)
                    -> Result<Type<'t>, ParserError> {
        match try!(self.get_token()) {
            Token::Ident(s) => {
                match &*s {
                    "s8" => Ok(Type::sint(ty::Int::I8, ctxt)),
                    "s16" => Ok(Type::sint(ty::Int::I16, ctxt)),
                    "s32" => Ok(Type::sint(ty::Int::I32, ctxt)),
                    "s64" => Ok(Type::sint(ty::Int::I64, ctxt)),
                    "u8" => Ok(Type::uint(ty::Int::I8, ctxt)),
                    "u16" => Ok(Type::uint(ty::Int::I16, ctxt)),
                    "u32" => Ok(Type::uint(ty::Int::I32, ctxt)),
                    "u64" => Ok(Type::uint(ty::Int::I64, ctxt)),
                    "bool" => Ok(Type::bool(ctxt)),
                    s => {
                        Err(ParserError::UnknownType {
                            found: s.to_owned(),
                            line: line,
                            compiler: fl!(),
                        })
                    }
                }
            }
            Token::OpenParen => {
                try!(self.eat(Token::CloseParen, line!()));
                Ok(Type::unit(ctxt))
            }
            Token::Operand(Operand::And) => {
                let inner = try!(self.parse_ty(ctxt, line));
                Ok(Type::ref_(inner, ctxt))
            }
            Token::Operand(Operand::AndAnd) => {
                let inner = try!(self.parse_ty(ctxt, line));
                Ok(Type::ref_(Type::ref_(inner, ctxt), ctxt))
            }
            tok => {
                Err(ParserError::UnexpectedToken {
                    found: tok,
                    expected: TokenType::AnyOf(vec![Token::Ident(String::new()), Token::OpenParen]),
                    line: self.line(),
                    compiler: (file!(), line),
                })
            }
        }
    }

    fn maybe_parse_single_expr<'t>(&mut self,
                                   ctxt: &'t TypeContext<'t>)
                                   -> Result<Option<Expr<'t>>, ParserError> {
        match try!(self.get_token()) {
            Token::Ident(name) => {
                if let Some(_) = try!(self.maybe_eat(Token::OpenParen)) {
                    let mut args = Vec::new();
                    if let Some(e) = try!(self.maybe_parse_expr(ctxt)) {
                        args.push(e);
                        while let Some(_) = try!(self.maybe_eat(Token::Comma)) {
                            args.push(try!(self.parse_expr(ctxt, line!())));
                        }
                    }
                    try!(self.eat(Token::CloseParen, line!()));
                    Ok(Some(Expr::call(name, args, ctxt)))
                } else {
                    Ok(Some(Expr::var(name, ctxt)))
                }
            }
            Token::KeywordIf => {
                let condition = try!(self.parse_expr(ctxt, line!()));
                let if_value = try!(self.parse_block(ctxt));
                let else_value = if let Some(_) = try!(self.maybe_eat(Token::KeywordElse)) {
                    match try!(self.peek_ty(TokenType::AnyOf(vec![Token::OpenBrace,
                                                                  Token::KeywordIf]),
                                            line!())) {
                        Token::OpenBrace => try!(self.parse_block(ctxt)),
                        Token::KeywordIf => try!(self.parse_block(ctxt)),
                        tok => unreachable!("{:?}", tok),
                    }
                } else {
                    ast::Block::expr(Expr::unit_lit(ctxt))
                };
                Ok(Some(Expr::if_else(condition, if_value, else_value, ctxt)))
            }
            Token::OpenBrace => {
                self.unget_token(Token::OpenBrace);
                Ok(Some(Expr::block(try!(self.parse_block(ctxt)), ctxt)))
            }

            Token::Integer { value, suffix } => {
                if suffix == "" {
                    return Ok(Some(Expr::int_lit(value, ctxt)));
                }
                let ty = match &*suffix {
                    "" => return Ok(Some(Expr::int_lit(value, ctxt))),
                    "s8" => Type::sint(ty::Int::I8, ctxt),
                    "s16" => Type::sint(ty::Int::I16, ctxt),
                    "s32" => Type::sint(ty::Int::I32, ctxt),
                    "s64" => Type::sint(ty::Int::I64, ctxt),
                    "u8" => Type::uint(ty::Int::I8, ctxt),
                    "u16" => Type::uint(ty::Int::I16, ctxt),
                    "u32" => Type::uint(ty::Int::I32, ctxt),
                    "u64" => Type::uint(ty::Int::I64, ctxt),
                    _ => {
                        return Err(ParserError::InvalidSuffix {
                            suffix: suffix.clone(),
                            line: self.line(),
                            compiler: fl!(),
                        })
                    }
                };
                Ok(Some(Expr::int_lit_with_ty(value, ty)))
            }
            Token::OpenParen => {
                if let Some(_) = try!(self.maybe_eat(Token::CloseParen)) {
                    Ok(Some(Expr::unit_lit(ctxt)))
                } else {
                    let expr = try!(self.parse_expr(ctxt, line!()));
                    try!(self.eat(Token::CloseParen, line!()));
                    Ok(Some(expr))
                }
            }
            Token::Operand(Operand::Minus) => {
                let inner = try!(self.parse_single_expr(ctxt, line!()));
                Ok(Some(Expr::neg(inner, ctxt)))
            }
            Token::Operand(Operand::Plus) => {
                let inner = try!(self.parse_single_expr(ctxt, line!()));
                Ok(Some(Expr::pos(inner, ctxt)))
            }
            Token::Operand(Operand::Not) => {
                let inner = try!(self.parse_single_expr(ctxt, line!()));
                Ok(Some(Expr::not(inner, ctxt)))
            }
            Token::Operand(Operand::And) => {
                let inner = try!(self.parse_single_expr(ctxt, line!()));
                Ok(Some(Expr::ref_(inner, ctxt)))
            }
            Token::Operand(Operand::AndAnd) => {
                let inner = try!(self.parse_single_expr(ctxt, line!()));
                Ok(Some(Expr::ref_(Expr::ref_(inner, ctxt), ctxt)))
            }
            Token::Operand(Operand::Mul) => {
                let inner = try!(self.parse_single_expr(ctxt, line!()));
                Ok(Some(Expr::deref(inner, ctxt)))
            }
            Token::KeywordTrue => Ok(Some(Expr::bool_lit(true, ctxt))),
            Token::KeywordFalse => Ok(Some(Expr::bool_lit(false, ctxt))),
            Token::KeywordReturn => {
                Ok(Some(Expr::ret(if let Some(e) = try!(self.maybe_parse_expr(ctxt)) {
                                      e
                                  } else {
                                      Expr::unit_lit(ctxt)
                                  },
                                  ctxt)))
            }
            tok => {
                self.unget_token(tok);
                Ok(None)
            }
        }
    }

    fn parse_single_expr<'t>(&mut self,
                             ctxt: &'t TypeContext<'t>,
                             line: u32)
                             -> Result<Expr<'t>, ParserError> {
        match self.maybe_parse_single_expr(ctxt) {
            Ok(Some(e)) => Ok(e),
            Ok(None) => {
                Err(ParserError::UnexpectedToken {
                    found: try!(self.get_token()),
                    expected: TokenType::Expression,
                    line: self.line(),
                    compiler: (file!(), line),
                })
            }
            Err(e) => Err(e),
        }
    }

    fn maybe_parse_expr<'t>(&mut self,
                            ctxt: &'t TypeContext<'t>)
                            -> Result<Option<Expr<'t>>, ParserError> {
        let lhs = match try!(self.maybe_parse_single_expr(ctxt)) {
            Some(l) => l,
            None => return Ok(None),
        };
        match try!(self.maybe_eat_ty(&TokenType::Operand)) {
            Some(Token::Operand(ref op)) => self.parse_binop(lhs, op, ctxt).map(|e| Some(e)),
            Some(tok) => unreachable!("{:?}", tok),
            None => {
                if let Some(_) = try!(self.maybe_eat(Token::Equals)) {
                    let assign = Expr::assign(lhs, try!(self.parse_expr(ctxt, line!())), ctxt);
                    Ok(Some(assign))
                } else {
                    Ok(Some(lhs))
                }
            }
        }
    }

    fn parse_expr<'t>(&mut self,
                      ctxt: &'t TypeContext<'t>,
                      line: u32)
                      -> Result<Expr<'t>, ParserError> {
        let lhs = try!(self.parse_single_expr(ctxt, line));
        match try!(self.maybe_eat_ty(&TokenType::Operand)) {
            Some(Token::Operand(ref op)) => self.parse_binop(lhs, op, ctxt),
            Some(tok) => unreachable!("{:?}", tok),
            None => Ok(lhs),
        }
    }

    fn parse_stmt<'t>(&mut self,
                      ctxt: &'t TypeContext<'t>)
                      -> Result<Option<Either<Stmt<'t>, Expr<'t>>>, ParserError> {
        match try!(self.maybe_parse_expr(ctxt)) {
            Some(e) => {
                if let Some(_) = try!(self.maybe_eat(Token::Semicolon)) {
                    Ok(Some(Left(Stmt::Expr(e))))
                } else if e.is_block() {
                    // if the expression is a block, treat it as an expression
                    // *unless* it's the last expression in the outer block
                    match try!(self.maybe_peek(Token::CloseBrace)) {
                        Some(_) => Ok(Some(Right(e))),
                        None => Ok(Some(Left(Stmt::Expr(e)))),
                    }
                } else {
                    Ok(Some(Right(e)))
                }
            }
            None => {
                match try!(self.eat_ty(TokenType::Statement, line!())) {
                    Token::KeywordLet => {
                        let name = try!(self.parse_ident(line!()));
                        let ty = if let Some(_) = try!(self.maybe_eat(Token::Colon)) {
                            try!(self.parse_ty(ctxt, line!()))
                        } else {
                            Type::infer(ctxt)
                        };
                        let expr = if let Some(_) = try!(self.maybe_eat(Token::Equals)) {
                            Some(Box::new(try!(self.parse_expr(ctxt, line!()))))
                        } else {
                            None
                        };
                        try!(self.eat(Token::Semicolon, line!()));
                        Ok(Some(Left(Stmt::Let {
                            name: name,
                            ty: ty,
                            value: expr,
                        })))
                    }
                    Token::CloseBrace => {
                        self.unget_token(Token::CloseBrace);
                        Ok(None)
                    }
                    tok => unreachable!("{:?}", tok),
                }
            }
        }
    }

    fn parse_binop<'t>(&mut self,
                       lhs: Expr<'t>,
                       left_op: &Operand,
                       ctxt: &'t TypeContext<'t>)
                       -> Result<Expr<'t>, ParserError> {
        let rhs = try!(self.parse_single_expr(ctxt, line!()));
        match try!(self.maybe_eat_ty(&TokenType::Operand)) {
            Some(Token::Operand(ref right_op)) => {
                if left_op.precedence() >= right_op.precedence() {
                    let new_lhs = left_op.expr(lhs, rhs, ctxt);
                    self.parse_binop(new_lhs, right_op, ctxt)
                } else {
                    let new_rhs = try!(self.parse_binop(rhs, right_op, ctxt));
                    Ok(left_op.expr(lhs, new_rhs, ctxt))
                }
            }
            Some(tok) => unreachable!("{:?}", tok),
            None => Ok(left_op.expr(lhs, rhs, ctxt)),
        }
    }

    fn parse_block<'t>(&mut self,
                       ctxt: &'t TypeContext<'t>)
                       -> Result<ast::Block<'t>, ParserError> {
        try!(self.eat(Token::OpenBrace, line!()));
        let mut body = Vec::new();
        let mut expr = None;
        while let Some(st) = try!(self.parse_stmt(ctxt)) {
            match st {
                Left(st) => body.push(st),
                Right(e) => {
                    expr = Some(e);
                    if let Some(_) = try!(self.parse_stmt(ctxt)) {
                        println!("{:#?}", expr.unwrap());
                        return Err(ParserError::ExpectedSemicolon {
                            line: self.line(),
                            compiler: fl!(),
                        });
                    } else {
                        break;
                    }
                }
            }
        }
        try!(self.eat(Token::CloseBrace, line!()));
        Ok(ast::Block::new(body, expr))
    }

    fn function<'t>(&mut self, ctxt: &'t TypeContext<'t>) -> Result<ast::Item<'t>, ParserError> {
        let name = try!(self.parse_ident(line!()));

        try!(self.eat(Token::OpenParen, line!()));

        let mut args = Vec::new();
        match try!(self.get_token()) {
            Token::Ident(arg) => {
                try!(self.eat(Token::Colon, line!()));
                args.push((arg, try!(self.parse_ty(ctxt, line!()))));
                loop {
                    let comma_or_close_paren = try!(self.get_token());
                    if let Token::Comma = comma_or_close_paren {
                        let name = try!(self.parse_ident(line!()));
                        try!(self.eat(Token::Colon, line!()));
                        args.push((name, try!(self.parse_ty(ctxt, line!()))));
                    } else if let Token::CloseParen = comma_or_close_paren {
                        break;
                    } else {
                        return Err(ParserError::UnexpectedToken {
                            found: comma_or_close_paren,
                            expected: TokenType::AnyOf(vec![Token::Comma, Token::CloseParen]),
                            line: self.line(),
                            compiler: fl!(),
                        });
                    }
                }
            }
            Token::CloseParen => {}
            tok => {
                return Err(ParserError::UnexpectedToken {
                    found: tok,
                    expected: TokenType::AnyOf(vec![Token::Ident(String::new()),
                                                    Token::CloseParen]),
                    line: self.line(),
                    compiler: fl!(),
                });
            }
        }

        let ret_ty = match try!(self.maybe_eat(Token::SkinnyArrow)) {
            Some(_) => try!(self.parse_ty(ctxt, line!())),
            None => Type::unit(ctxt),
        };


        Ok(ast::Item::Function {
            name: name,
            ret: ret_ty,
            args: args,
            body: try!(self.parse_block(ctxt)),
        })
    }
}
