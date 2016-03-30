use std::str;
use trans::{expr, stmt, item};
use ty::ty;

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
    Integer(u64),

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

            token::KeywordLet | token::KeywordReturn | token::CloseBrace => token_type::Statement,

            token::KeywordTrue |
            token::KeywordFalse |
            token::KeywordIf |
            token::Ident(_) |
            token::Integer(_) => token_type::Expression,

            token::Operand(_) => token_type::Operand,

            token::KeywordElse |
            token::OpenParen |
            token::CloseParen |
            token::OpenBrace |
            token::Semicolon |
            token::Colon |
            token::SkinnyArrow |
            token::Comma |
            token::Equals |
            token::Eof => token_type::Misc,
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
            operand::Mul | operand::Div | operand::Rem => 8,
            operand::Plus | operand::Minus => 7,
            operand::And => 6,
            operand::Xor => 5,
            operand::Or => 4,
            operand::EqualsEquals |
            operand::NotEquals |
            operand::LessThan |
            operand::LessThanEquals |
            operand::GreaterThan |
            operand::GreaterThanEquals => 3,
            operand::AndAnd => 2,
            operand::OrOr => 1,
            operand::Not => unreachable!("Not (`!`) is not a binop"),
        }
    }

    // simply a convenience function
    pub fn expr(&self, lhs: expr, rhs: expr) -> expr {
        expr::Binop {
            op: *self,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
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
                Some(c @ 'a'...'z') | Some(c @ 'A'...'Z') | Some(c @ '0'...'9') | Some(c @ '_') => {
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
                    Some(c) => self.ungetc(c),
                    None => {}
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
                    None => {}
                }
                Ok(token::Operand(operand::Div))
            }

            '!' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(token::Operand(operand::NotEquals));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(token::Operand(operand::Not))
            }
            '<' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(token::Operand(operand::LessThanEquals));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(token::Operand(operand::LessThan))
            }
            '>' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(token::Operand(operand::GreaterThanEquals));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(token::Operand(operand::GreaterThan))
            }
            '=' => {
                match self.getc() {
                    Some('=') => {
                        return Ok(token::Operand(operand::EqualsEquals));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(token::Equals)
            }
            '&' => {
                match self.getc() {
                    Some('&') => {
                        return Ok(token::Operand(operand::AndAnd));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(token::Operand(operand::And))
            }
            '|' => {
                match self.getc() {
                    Some('|') => {
                        return Ok(token::Operand(operand::OrOr));
                    }
                    Some(c) => self.ungetc(c),
                    None => {}
                }
                Ok(token::Operand(operand::Or))
            }

            'a'...'z' | 'A'...'Z' | '_' => {
                let ident = self.ident(first);
                match &ident[..] {
                    "fn" => return Ok(token::KeywordFn),
                    "return" => return Ok(token::KeywordReturn),
                    "let" => return Ok(token::KeywordLet),
                    "if" => return Ok(token::KeywordIf),
                    "else" => return Ok(token::KeywordElse),
                    "true" => return Ok(token::KeywordTrue),
                    "false" => return Ok(token::KeywordFalse),
                    _ => {}
                }

                Ok(token::Ident(ident))
            }
            '0'...'9' => {
                let mut string = String::new();
                if first != '-' {
                    string.push(first);
                }
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

                let value = string.parse::<u64>()
                                  .expect("we pushed something which wasn't 0...9 onto a string");

                Ok(token::Integer(value))
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
}

pub struct parser<'src> {
    lexer: lexer<'src>,
    token_buffer: Vec<token>,
}

impl<'src> parser<'src> {
    pub fn new(lexer: lexer<'src>) -> Self {
        parser {
            lexer: lexer,
            token_buffer: Vec::new(),
        }
    }

    #[inline(always)]
    pub fn line(&self) -> u32 {
        self.lexer.line
    }

    fn get_token(&mut self) -> Result<token, parser_error> {
        match self.token_buffer.pop() {
            Some(tok) => Ok(tok),
            None => self.lexer.next_token(),
        }
    }
    fn unget_token(&mut self, token: token) {
        self.token_buffer.push(token)
    }

    pub fn item(&mut self) -> Result<item, parser_error> {
        match try!(self.get_token()) {
            token::KeywordFn => self.function(),
            token::Eof => Err(parser_error::ExpectedEof),
            tok => {
                Err(parser_error::UnexpectedToken {
                    found: tok,
                    expected: token_type::Item,
                    line: self.line(),
                    compiler: fl!(),
                })
            }
        }
    }

    fn maybe_eat_ty(&mut self,
                    expected: &token_type,
                    _: u32)
                    -> Result<Option<token>, parser_error> {
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
            _ => {}
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
            tok => {
                Err(parser_error::UnexpectedToken {
                    found: tok,
                    expected: token_type::AnyOf(vec![token::Ident(String::new()),
                                                     token::OpenParen]),
                    line: self.line(),
                    compiler: (file!(), line),
                })
            }
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
                    Ok(Some(expr::Call {
                        name: name,
                        args: args,
                    }))
                } else {
                    Ok(Some(expr::Variable(name)))
                }
            }
            token::KeywordIf => {
                let condition = try!(self.parse_expr(line!()));
                try!(self.eat(token::OpenBrace, line!()));
                let if_value = try!(self.parse_expr(line!()));
                try!(self.eat(token::CloseBrace, line!()));
                try!(self.eat(token::KeywordElse, line!()));

                let else_value = match try!(self.eat_ty(token_type::AnyOf(
                        vec![token::OpenBrace, token::KeywordIf]), line!())) {
                    token::OpenBrace => {
                        let expr = try!(self.parse_expr(line!()));
                        try!(self.eat(token::CloseBrace, line!()));
                        expr
                    }
                    token::KeywordIf => {
                        self.unget_token(token::KeywordIf);
                        try!(self.parse_expr(line!()))
                    }
                    tok => unreachable!("{:?}", tok),
                };
                Ok(Some(expr::If {
                    condition: Box::new(condition),
                    then_value: Box::new(if_value),
                    else_value: Box::new(else_value),
                }))
            }
            token::Integer(value) => Ok(Some(expr::IntLiteral(value))),
            token::OpenParen => {
                let expr = try!(self.parse_expr(line!()));
                try!(self.eat(token::CloseParen, line!()));
                Ok(Some(expr))
            }
            token::Operand(operand::Minus) => {
                Ok(Some(expr::Minus(Box::new(try!(self.parse_single_expr(line!()))))))
            }
            token::Operand(operand::Plus) => {
                Ok(Some(expr::Plus(Box::new(try!(self.parse_single_expr(line!()))))))
            }
            token::Operand(operand::Not) => {
                Ok(Some(expr::Not(Box::new(try!(self.parse_single_expr(line!()))))))
            }
            token::KeywordTrue => Ok(Some(expr::BoolLiteral(true))),
            token::KeywordFalse => Ok(Some(expr::BoolLiteral(false))),
            tok => {
                self.unget_token(tok);
                Ok(None)
            }
        }
    }

    fn parse_single_expr(&mut self, line: u32) -> Result<expr, parser_error> {
        match self.maybe_parse_single_expr() {
            Ok(Some(e)) => Ok(e),
            Ok(None) => {
                Err(parser_error::UnexpectedToken {
                    found: try!(self.get_token()),
                    expected: token_type::Expression,
                    line: self.line(),
                    compiler: (file!(), line),
                })
            }
            Err(e) => Err(e),
        }
    }

    fn maybe_parse_expr(&mut self) -> Result<Option<expr>, parser_error> {
        let lhs = match try!(self.maybe_parse_single_expr()) {
            Some(l) => l,
            None => return Ok(None),
        };
        match try!(self.maybe_eat_ty(&token_type::Operand, line!())) {
            Some(token::Operand(ref op)) => self.parse_binop(lhs, op).map(|e| Some(e)),
            Some(tok) => unreachable!("{:?}", tok),
            None => Ok(Some(lhs)),
        }
    }

    fn parse_expr(&mut self, line: u32) -> Result<expr, parser_error> {
        let lhs = try!(self.parse_single_expr(line));
        match try!(self.maybe_eat_ty(&token_type::Operand, line!())) {
            Some(token::Operand(ref op)) => self.parse_binop(lhs, op),
            Some(tok) => unreachable!("{:?}", tok),
            None => Ok(lhs),
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
            Some(_) => try!(self.parse_ty(line!())),
            None => ty::Unit,
        };
        try!(self.eat(token::OpenBrace, line!()));

        let mut body = Vec::new();
        loop {
            match try!(self.eat_ty(token_type::Statement, line!())) {
                token::KeywordReturn => {
                    body.push(stmt::Return(try!(self.maybe_parse_expr())));
                    try!(self.eat(token::Semicolon, line!()));
                }
                token::KeywordLet => {
                    let name = try!(self.parse_ident(line!()));
                    try!(self.eat(token::Colon, line!()));
                    let ty = try!(self.parse_ty(line!()));
                    try!(self.eat(token::Equals, line!()));
                    let expr = try!(self.parse_expr(line!()));
                    body.push(stmt::Let {
                        name: name,
                        ty: ty,
                        value: expr,
                    });
                    try!(self.eat(token::Semicolon, line!()));
                }
                token::CloseBrace => break,
                tok => unreachable!("{:?}", tok),
            }
        }

        Ok(item::Function {
            name: name,
            ret: ret_ty,
            args: args,
            body: body,
        })
    }
}
