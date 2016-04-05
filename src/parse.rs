use std::str;
use trans::{expr, stmt, item};
use ty::ty;
use either::{self, Left, Right};

#[derive(Debug, PartialEq, Eq)]
pub enum token {
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

    Operand(operand),

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

impl token {
    pub fn ty(&self) -> token_type {
        match *self {
            token::KeywordFn => token_type::Item,

            token::KeywordLet | token::CloseBrace
                => token_type::Statement,

            token::KeywordReturn | token::KeywordTrue | token::KeywordFalse |
            token::KeywordIf | token::Ident(_) | token::Integer {..}
                => token_type::Expression,

            token::Operand(_) => token_type::Operand,

            token::KeywordElse | token::OpenParen | token::CloseParen |
            token::OpenBrace |  token::Semicolon | token::Colon | token::SkinnyArrow |
            token::Comma | token::Equals | token::Eof => token_type::Misc,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum operand {
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

    Not,

    EqualsEquals,
    NotEquals,
    LessThan,
    LessThanEquals,
    GreaterThan,
    GreaterThanEquals,

    AndAnd,
    OrOr,
}

impl operand {
    pub fn precedence(&self) -> u8 {
        match *self {
            operand::Mul | operand::Div | operand::Rem => 9,
            operand::Plus | operand::Minus => 8,
            operand::Shl | operand::Shr => 7,
            operand::And => 6,
            operand::Xor => 5,
            operand::Or => 4,
            operand::EqualsEquals | operand::NotEquals | operand::LessThan |
            operand::LessThanEquals | operand::GreaterThan | operand::GreaterThanEquals => 3,
            operand::AndAnd => 2,
            operand::OrOr => 1,
            operand::Not => unreachable!("Not (`!`) is not a binop")
        }
    }

    // simply a convenience function
    pub fn expr(&self, lhs: expr, rhs: expr) -> expr {
        self.precedence(); // makes certain that self is a binop
        expr {
            kind: ::trans::expr_kind::Binop {
                op: *self,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty: ty::Infer(None),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum token_type {
    Item,
    Statement,
    Expression,
    Operand,
    Misc,

    Specific(token),
    AnyOf(Vec<token>),
}

pub struct lexer<'src> {
    src: str::Chars<'src>,
    readahead: Vec<char>,
    line: u32,
}

impl<'src> lexer<'src> {
    pub fn new(src: &str) -> lexer {
        lexer {
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
                Some(c) if Self::is_ident(c) => {
                    ret.push(c)
                }
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

    fn block_comment(&mut self) -> Result<(), parser_error> {
        loop {
            let c = self.getc();
            if c == Some('*') {
                let c = self.getc();
                if c == Some('/') {
                    return Ok(());
                } else if c == Some('\n') {
                    self.line += 1;
                } else if c == None {
                    return Err(parser_error::UnclosedComment);
                }
            } else if c == Some('/') {
                let c = self.getc();
                if c == Some('*') {
                    try!(self.block_comment())
                } else if c == Some('\n') {
                    self.line += 1;
                } else if c == None {
                    return Err(parser_error::UnclosedComment);
                }
            } else if c == Some('\n') {
                self.line += 1;
            } else if c == None {
                return Err(parser_error::UnclosedComment);
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
        assert!(self.readahead.len() == 0); // make sure that readahead is only 1
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

    pub fn next_token(&mut self) -> Result<token, parser_error> {
        self.eat_whitespace();
        let first = match self.getc() {
            Some(c) => c,
            None => return Ok(token::Eof),
        };
        match first {
            '(' => Ok(token::OpenParen),
            ')' => Ok(token::CloseParen),
            '{' => Ok(token::OpenBrace),
            '}' => Ok(token::CloseBrace),
            ';' => Ok(token::Semicolon),
            ':' => Ok(token::Colon),
            ',' => Ok(token::Comma),
            '*' => Ok(token::Operand(operand::Mul)),
            '%' => Ok(token::Operand(operand::Rem)),
            '+' => Ok(token::Operand(operand::Plus)),
            '-' => {
                match self.getc() {
                    Some('>') => {
                        return Ok(token::SkinnyArrow);
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => { }
                }
                Ok(token::Operand(operand::Minus))
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
                    None => { }
                }
                Ok(token::Operand(operand::Div))
            }

            '!' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(token::Operand(operand::NotEquals));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::Not))
            }
            '<' => {
                match self.getc() {
                    Some('<') => {
                        return Ok(token::Operand(operand::Shl));
                    }
                    Some('=') => {
                        return Ok(token::Operand(operand::LessThanEquals));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::LessThan))
            }
            '>' => {
                match self.getc() {
                    Some('>') => {
                        return Ok(token::Operand(operand::Shr));
                    }
                    Some('=') => {
                        return Ok(token::Operand(operand::GreaterThanEquals));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::GreaterThan))
            }
            '=' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(token::Operand(operand::EqualsEquals));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Equals)
            }
            '&' => {
                match self.getc() {
                    Some('&') => {
                        return Ok(token::Operand(operand::AndAnd));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::And))
            }
            '|' => {
                match self.getc() {
                    Some('|') => {
                        return Ok(token::Operand(operand::OrOr));
                    }
                    Some(c) => {
                        self.ungetc(c)
                    }
                    None => {}
                }
                Ok(token::Operand(operand::Or))
            }

            c if Self::is_start_of_ident(c) => {
                let ident = self.ident(c);
                match &ident[..] {
                    "fn" => return Ok(token::KeywordFn),
                    "return" => return Ok(token::KeywordReturn),
                    "let" => return Ok(token::KeywordLet),
                    "if" => return Ok(token::KeywordIf),
                    "else" => return Ok(token::KeywordElse),
                    "true" => return Ok(token::KeywordTrue),
                    "false" => return Ok(token::KeywordFalse),
                    _ => {},
                }

                Ok(token::Ident(ident))
            }
            c if Self::is_integer(c) => {
                let mut string = String::new();
                string.push(c);
                let mut suffix = String::new();
                loop {
                    match self.getc() {
                        Some(c @ '0'...'9') => {
                            string.push(c)
                        }
                        Some(c) => {
                            self.ungetc(c);
                            break;
                        }
                        None => break,
                    }
                }
                loop {
                    match self.getc() {
                        Some(c) if Self::is_ident(c) => {
                            suffix.push(c)
                        }
                        Some(c) => {
                            self.ungetc(c);
                            break;
                        }
                        None => break,
                    }
                }

                let value = string.parse::<u64>()
                    .expect("we pushed something which wasn't 0...9 onto a string");

                Ok(token::Integer {
                    value: value,
                    suffix: suffix,
                })
            }

            i => {
                Err(parser_error::InvalidToken {
                    token: i,
                    line: self.line,
                    compiler: fl!(),
                })
            }
        }
    }
}

#[derive(Debug)]
pub enum parser_error {
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
        found: token,
        expected: token_type,
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

pub struct parser<'src> {
    lexer: lexer<'src>,
    peekahead: Option<token>,
}

impl<'src> parser<'src> {
    pub fn new(lexer: lexer<'src>) -> Self {
        parser {
            lexer: lexer,
            peekahead: None,
        }
    }

    #[inline(always)]
    pub fn line(&self) -> u32 {
        self.lexer.line
    }

    fn get_token(&mut self) -> Result<token, parser_error> {
        match self.peekahead.take() {
            Some(tok) => Ok(tok),
            None => self.lexer.next_token(),
        }
    }
    fn unget_token(&mut self, token: token) {
        assert!(self.peekahead.is_none(), "current: {:?}, attempted: {:?}, line: {}",
            self.peekahead, token, self.line());
        self.peekahead = Some(token);
    }

    pub fn item(&mut self) -> Result<item, parser_error> {
        match try!(self.get_token()) {
            token::KeywordFn => self.function(),
            token::Eof => Err(parser_error::ExpectedEof),
            tok => Err(parser_error::UnexpectedToken {
                found: tok,
                expected: token_type::Item,
                line: self.line(),
                compiler: fl!(),
            }),
        }
    }

    fn maybe_eat_ty(&mut self, expected: &token_type, _: u32) -> Result<Option<token>, parser_error> {
        let token = try!(self.get_token());
        match *expected {
            token_type::Specific(ref t) => {
                if &token == t {
                    return Ok(Some(token));
                }
            }
            token_type::AnyOf(ref t) => {
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
        self.unget_token(token);
        Ok(None)
    }

    fn eat_ty(&mut self, expected: token_type, compiler_line: u32) -> Result<token, parser_error> {
        match self.maybe_eat_ty(&expected, compiler_line) {
            Ok(Some(t)) => return Ok(t),
            Err(e) => return Err(e),
            _ => {},
        }
        Err(parser_error::UnexpectedToken {
            found: try!(self.get_token()),
            expected: expected,
            line: self.line(),
            compiler: (file!(), compiler_line),
        })
    }

    fn maybe_eat(&mut self, expected: token, line: u32) -> Result<Option<token>, parser_error> {
        self.maybe_eat_ty(&token_type::Specific(expected), line)
    }

    fn eat(&mut self, expected: token, line: u32) -> Result<token, parser_error> {
        self.eat_ty(token_type::Specific(expected), line)
    }

    fn parse_ident(&mut self, line: u32) -> Result<String, parser_error> {
        match try!(self.get_token()) {
            token::Ident(s) => Ok(s),
            tok => {
                Err(parser_error::UnexpectedToken {
                    found: tok,
                    expected: token_type::Specific(token::Ident(String::new())),
                    line: self.line(),
                    compiler: (file!(), line),
                })
            }
        }
    }

    fn parse_ty(&mut self, line: u32) -> Result<ty, parser_error> {
        match try!(self.get_token()) {
            token::Ident(s) => ty::from_str(&s, line!()),
            token::OpenParen => {
                try!(self.eat(token::CloseParen, line!()));
                Ok(ty::Unit)
            }
            tok => Err(parser_error::UnexpectedToken {
                found: tok,
                expected: token_type::AnyOf(vec![token::Ident(String::new()),
                    token::OpenParen]),
                line: self.line(),
                compiler: (file!(), line),
            })
        }
    }

    fn maybe_parse_single_expr(&mut self) -> Result<Option<expr>, parser_error> {
        match try!(self.get_token()) {
            token::Ident(name) => {
                if let Some(_) = try!(self.maybe_eat(token::OpenParen, line!())) {
                    let mut args = Vec::new();
                    if let Some(e) = try!(self.maybe_parse_expr()) {
                        args.push(e);
                        while let Some(_) = try!(self.maybe_eat(token::Comma, line!())) {
                            args.push(try!(self.parse_expr(line!())));
                        }
                    }
                    try!(self.eat(token::CloseParen, line!()));
                    Ok(Some(expr::call(name, args, None)))
                } else {
                    Ok(Some(expr::var(name, None)))
                }
            }
            token::KeywordIf => {
                let condition = try!(self.parse_expr(line!()));
                let if_value = try!(self.parse_block());
                let else_value =
                if let Some(_) = try!(self.maybe_eat(token::KeywordElse, line!())) {
                    match try!(self.eat_ty(token_type::AnyOf(
                            vec![token::OpenBrace, token::KeywordIf]), line!())) {
                        token::OpenBrace => {
                            self.unget_token(token::OpenBrace);
                            try!(self.parse_block())
                        }
                        token::KeywordIf => {
                            self.unget_token(token::KeywordIf);
                            try!(self.parse_block())
                        }
                        tok => unreachable!("{:?}", tok),
                    }
                } else {
                    (Vec::new(), Some(expr::unit_lit()))
                };
                Ok(Some(expr::if_else(condition, if_value, else_value, None)))
            },

            token::Integer {value, suffix} => {
                if suffix == "" {
                    return Ok(Some(expr::int_lit(value, None)));
                }
                match ty::from_str(&suffix, self.line()) {
                    Ok(ty @ ty::SInt(_)) | Ok(ty @ ty::UInt(_)) => {
                        return Ok(Some(expr::int_lit(value, Some(ty))))
                    }
                    _ => {}
                }
                Err(parser_error::InvalidSuffix {
                    suffix: suffix,
                    line: self.line(),
                    compiler: fl!(),
                })
            }
            token::OpenParen => {
                if let Some(_) = try!(self.maybe_eat(token::CloseParen, line!())) {
                    Ok(Some(expr::unit_lit()))
                } else {
                    let expr = try!(self.parse_expr(line!()));
                    try!(self.eat(token::CloseParen, line!()));
                    Ok(Some(expr))
                }
            }
            token::Operand(operand::Minus) => {
                let inner = try!(self.parse_single_expr(line!()));
                Ok(Some(expr::neg(inner, None)))
            }
            token::Operand(operand::Plus) => {
                let inner = try!(self.parse_single_expr(line!()));
                Ok(Some(expr::pos(inner, None)))
            }
            token::Operand(operand::Not) => {
                let inner = try!(self.parse_single_expr(line!()));
                Ok(Some(expr::not(inner, None)))
            }
            token::KeywordTrue => Ok(Some(expr::bool_lit(true))),
            token::KeywordFalse => Ok(Some(expr::bool_lit(false))),
            token::KeywordReturn => {
                Ok(Some(expr::ret(
                if let Some(e) = try!(self.maybe_parse_expr()) {
                    e
                } else {
                    expr::unit_lit()
                })))
            },
            tok => {
                self.unget_token(tok);
                Ok(None)
            }
        }
    }

    fn parse_single_expr(&mut self, line: u32) -> Result<expr, parser_error> {
        match self.maybe_parse_single_expr() {
            Ok(Some(e)) => Ok(e),
            Ok(None) => Err(parser_error::UnexpectedToken {
                found: try!(self.get_token()),
                expected: token_type::Expression,
                line: self.line(),
                compiler: (file!(), line),
            }),
            Err(e) => Err(e),
        }
    }

    fn maybe_parse_expr(&mut self) -> Result<Option<expr>, parser_error> {
        let lhs = match try!(self.maybe_parse_single_expr()) {
            Some(l) => l,
            None => return Ok(None),
        };
        match try!(self.maybe_eat_ty(&token_type::Operand, line!())) {
            Some(token::Operand(ref op)) => {
                self.parse_binop(lhs, op).map(|e| Some(e))
            }
            Some(tok) => unreachable!("{:?}", tok),
            None => {
                Ok(Some(lhs))
            }
        }
    }

    fn parse_expr(&mut self, line: u32) -> Result<expr, parser_error> {
        let lhs = try!(self.parse_single_expr(line));
        match try!(self.maybe_eat_ty(&token_type::Operand, line!())) {
            Some(token::Operand(ref op)) => {
                self.parse_binop(lhs, op)
            }
            Some(tok) => unreachable!("{:?}", tok),
            None => {
                Ok(lhs)
            }
        }
    }

    fn parse_stmt(&mut self) -> Result<Option<either<stmt, expr>>, parser_error> {
        match try!(self.maybe_parse_expr()) {
            Some(e) => {
                if let Some(_) = try!(self.maybe_eat(token::Semicolon, line!())) {
                    Ok(Some(Left(stmt::Expr(e))))
                } else if e.is_block() {
                    // if the expression is a block, treat it as an expression
                    // *unless* it's the last expression in the outer block
                    match try!(self.maybe_eat(token::CloseBrace, line!())) {
                        Some(_) => {
                            self.unget_token(token::CloseBrace);
                            Ok(Some(Right(e)))
                        }
                        None => {
                            Ok(Some(Left(stmt::Expr(e))))
                        }
                    }
                } else {
                    Ok(Some(Right(e)))
                }
            }
            None => {
                match try!(self.eat_ty(token_type::Statement, line!())) {
                    token::KeywordLet => {
                        let name = try!(self.parse_ident(line!()));
                        let ty = if let Some(_) = try!(self.maybe_eat(token::Colon, line!())) {
                            try!(self.parse_ty(line!()))
                        } else {
                            ty::Infer(None)
                        };
                        try!(self.eat(token::Equals, line!()));
                        let expr = try!(self.parse_expr(line!()));
                        try!(self.eat(token::Semicolon, line!()));
                        Ok(Some(Left(stmt::Let {
                            name: name,
                            ty: ty,
                            value: Box::new(expr),
                        })))
                    }
                    token::CloseBrace => {
                        self.unget_token(token::CloseBrace);
                        Ok(None)
                    }
                    tok => unreachable!("{:?}", tok),
                }
            }
        }
    }

    fn parse_binop(&mut self, lhs: expr, left_op: &operand) -> Result<expr, parser_error> {
        let rhs = try!(self.parse_single_expr(line!()));
        match try!(self.maybe_eat_ty(&token_type::Operand, line!())) {
            Some(token::Operand(ref right_op)) => {
                if left_op.precedence() >= right_op.precedence() {
                    let new_lhs = left_op.expr(lhs, rhs);
                    self.parse_binop(new_lhs, right_op)
                } else {
                    let new_rhs = try!(self.parse_binop(rhs, right_op));
                    Ok(left_op.expr(lhs, new_rhs))
                }
            }
            Some(tok) => unreachable!("{:?}", tok),
            None => Ok(left_op.expr(lhs, rhs)),
        }
    }

    fn parse_block(&mut self) -> Result<(Vec<stmt>, Option<expr>), parser_error> {
        try!(self.eat(token::OpenBrace, line!()));
        let mut body = Vec::new();
        let mut expr = None;
        while let Some(st) = try!(self.parse_stmt()) {
            match st {
                Left(st) => body.push(st),
                Right(e) => {
                    expr = Some(e);
                    if let Some(_) = try!(self.parse_stmt()) {
                        println!("{:#?}", expr.unwrap());
                        return Err(parser_error::ExpectedSemicolon {
                            line: self.line(),
                            compiler: fl!(),
                        })
                    } else {
                        break;
                    }
                }
            }
        }
        try!(self.eat(token::CloseBrace, line!()));
        Ok((body, expr))
    }

    fn function(&mut self) -> Result<item, parser_error> {
        let name = try!(self.parse_ident(line!()));

        try!(self.eat(token::OpenParen, line!()));

        let mut args = Vec::new();
        match try!(self.get_token()) {
            token::Ident(arg) => {
                try!(self.eat(token::Colon, line!()));
                let ty = try!(self.parse_ident(line!()));
                args.push((arg, try!(ty::from_str(&ty, self.line()))));
                loop {
                    let comma_or_close_paren = try!(self.get_token());
                    if let token::Comma = comma_or_close_paren {
                        let name = try!(self.parse_ident(line!()));
                        try!(self.eat(token::Colon, line!()));
                        let ty = try!(self.parse_ident(line!()));
                        args.push((name, try!(ty::from_str(&ty, self.line()))));
                    } else if let token::CloseParen = comma_or_close_paren {
                        break;
                    } else {
                        return Err(parser_error::UnexpectedToken {
                            found: comma_or_close_paren,
                            expected: token_type::AnyOf(vec![token::Comma, token::CloseParen]),
                            line: self.line(),
                            compiler: fl!(),
                        });
                    }
                }
            }
            token::CloseParen => {}
            tok => {
                return Err(parser_error::UnexpectedToken {
                    found: tok,
                    expected: token_type::AnyOf(vec![token::Ident(String::new()),
                        token::CloseParen]),
                    line: self.line(),
                    compiler: fl!(),
                });
            }
        }

        let ret_ty = match try!(self.maybe_eat(token::SkinnyArrow, line!())) {
            Some(_) => {
                try!(self.parse_ty(line!()))
            }
            None => ty::Unit,
        };

        let (stmts, expr) = try!(self.parse_block());
        let expr = expr.map(|e| Box::new(e));

        Ok(item::Function { name: name, ret: ret_ty, args: args, body: (stmts, expr) })
    }
}
