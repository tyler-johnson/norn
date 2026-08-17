//! Tokenizer.
//!
//! The grammar is newline-sensitive in two narrow places (statement separation, and postfix chains
//! that must not silently continue across a line break), so every token records whether a line
//! break preceded it. Nothing else in the language depends on layout.

use crate::diag::Diagnostic;
use crate::span::Span;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kw {
    Module,
    Use,
    Record,
    Enum,
    Fn,
    Task,
    Uses,
    Let,
    Mut,
    Return,
    Match,
    If,
    Else,
    Await,
    Scope,
    Spawn,
    True,
    False,
}

impl Kw {
    pub fn text(self) -> &'static str {
        match self {
            Kw::Module => "module",
            Kw::Use => "use",
            Kw::Record => "record",
            Kw::Enum => "enum",
            Kw::Fn => "fn",
            Kw::Task => "task",
            Kw::Uses => "uses",
            Kw::Let => "let",
            Kw::Mut => "mut",
            Kw::Return => "return",
            Kw::Match => "match",
            Kw::If => "if",
            Kw::Else => "else",
            Kw::Await => "await",
            Kw::Scope => "scope",
            Kw::Spawn => "spawn",
            Kw::True => "true",
            Kw::False => "false",
        }
    }
}

/// Words the language will need in a later milestone. They are rejected as identifiers now so that
/// M0 programs do not have to be rewritten when reactors and structured concurrency land.
pub const RESERVED: &[&str] = &[
    "after_commit",
    "as",
    "blocking",
    "break",
    "const",
    "continue",
    "delay",
    "event",
    "export",
    "for",
    "impl",
    "in",
    "input",
    "interface",
    "loop",
    "macro",
    "on",
    "pub",
    "reactor",
    "signal",
    "source",
    "state",
    "static",
    "trait",
    "type",
    "where",
    "while",
];

#[derive(Clone, PartialEq, Debug)]
pub enum TokenKind {
    Int(i64),
    Float(f64),
    Str(String),
    Ident(String),
    /// A word reserved for a later milestone, kept as a token so the parser can explain itself.
    Reserved(String),
    Kw(Kw),

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Dot,
    DotDot,
    Colon,
    Question,
    FatArrow,
    ThinArrow,
    Underscore,
    At,
    /// Marks a data constructor: `#User(id: 7)`, `#LoadError.NotFound`.
    Hash,

    Eq,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    AndAnd,
    OrOr,
    Bang,
    Amp,
    Pipe,

    Eof,
}

impl TokenKind {
    /// How this token is named in a diagnostic.
    pub fn describe(&self) -> String {
        match self {
            TokenKind::Int(_) => "an integer literal".into(),
            TokenKind::Float(_) => "a float literal".into(),
            TokenKind::Str(_) => "a string literal".into(),
            TokenKind::Ident(name) => format!("`{name}`"),
            TokenKind::Reserved(name) => format!("`{name}`"),
            TokenKind::Kw(kw) => format!("`{}`", kw.text()),
            TokenKind::Eof => "end of file".into(),
            other => format!("`{}`", other.punct_text()),
        }
    }

    fn punct_text(&self) -> &'static str {
        match self {
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::LBrace => "{",
            TokenKind::RBrace => "}",
            TokenKind::LBracket => "[",
            TokenKind::RBracket => "]",
            TokenKind::Comma => ",",
            TokenKind::Dot => ".",
            TokenKind::DotDot => "..",
            TokenKind::Colon => ":",
            TokenKind::Question => "?",
            TokenKind::FatArrow => "=>",
            TokenKind::ThinArrow => "->",
            TokenKind::Underscore => "_",
            TokenKind::At => "@",
            TokenKind::Hash => "#",
            TokenKind::Eq => "=",
            TokenKind::EqEq => "==",
            TokenKind::Ne => "!=",
            TokenKind::Lt => "<",
            TokenKind::Le => "<=",
            TokenKind::Gt => ">",
            TokenKind::Ge => ">=",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Star => "*",
            TokenKind::Slash => "/",
            TokenKind::Percent => "%",
            TokenKind::AndAnd => "&&",
            TokenKind::OrOr => "||",
            TokenKind::Bang => "!",
            TokenKind::Amp => "&",
            TokenKind::Pipe => "|",
            _ => "?",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    /// True when at least one line break separates this token from the previous one.
    pub nl_before: bool,
}

pub struct Lexed {
    pub tokens: Vec<Token>,
    pub errors: Vec<Diagnostic>,
}

pub fn lex(text: &str) -> Lexed {
    Lexer {
        bytes: text.as_bytes(),
        text,
        pos: 0,
        tokens: Vec::new(),
        errors: Vec::new(),
    }
    .run()
}

struct Lexer<'a> {
    bytes: &'a [u8],
    text: &'a str,
    pos: usize,
    tokens: Vec<Token>,
    errors: Vec<Diagnostic>,
}

impl<'a> Lexer<'a> {
    fn run(mut self) -> Lexed {
        loop {
            let nl = self.skip_trivia();
            let start = self.pos;
            if self.pos >= self.bytes.len() {
                self.tokens.push(Token {
                    kind: TokenKind::Eof,
                    span: Span::new(start as u32, start as u32),
                    nl_before: nl,
                });
                break;
            }
            match self.token() {
                Some(kind) => {
                    let span = Span::new(start as u32, self.pos as u32);
                    self.tokens.push(Token {
                        kind,
                        span,
                        nl_before: nl,
                    });
                }
                None => {
                    // `token` already recorded a diagnostic and consumed at least one byte.
                }
            }
        }
        Lexed {
            tokens: self.tokens,
            errors: self.errors,
        }
    }

    /// Consume whitespace and comments; report whether a line break was crossed.
    fn skip_trivia(&mut self) -> bool {
        let mut nl = false;
        loop {
            match self.peek() {
                Some(b'\n') => {
                    nl = true;
                    self.pos += 1;
                }
                Some(b' ' | b'\t' | b'\r') => self.pos += 1,
                Some(b'/') if self.peek_at(1) == Some(b'/') => {
                    while !matches!(self.peek(), None | Some(b'\n')) {
                        self.pos += 1;
                    }
                }
                Some(b'/') if self.peek_at(1) == Some(b'*') => {
                    let start = self.pos;
                    self.pos += 2;
                    let mut depth = 1usize;
                    while depth > 0 {
                        match (self.peek(), self.peek_at(1)) {
                            (None, _) => {
                                self.error(
                                    Span::new(start as u32, self.pos as u32),
                                    "unterminated block comment",
                                );
                                break;
                            }
                            (Some(b'/'), Some(b'*')) => {
                                depth += 1;
                                self.pos += 2;
                            }
                            (Some(b'*'), Some(b'/')) => {
                                depth -= 1;
                                self.pos += 2;
                            }
                            (Some(b'\n'), _) => {
                                nl = true;
                                self.pos += 1;
                            }
                            _ => self.pos += 1,
                        }
                    }
                }
                _ => return nl,
            }
        }
    }

    fn token(&mut self) -> Option<TokenKind> {
        let c = self.peek()?;
        match c {
            b'0'..=b'9' => Some(self.number()),
            b'"' => Some(self.string()),
            c if is_ident_start(c) => Some(self.word()),
            _ => self.punct(),
        }
    }

    fn word(&mut self) -> TokenKind {
        let start = self.pos;
        while self.peek().is_some_and(is_ident_continue) {
            self.pos += 1;
        }
        let word = &self.text[start..self.pos];
        if word == "_" {
            return TokenKind::Underscore;
        }
        let kw = match word {
            "module" => Some(Kw::Module),
            "use" => Some(Kw::Use),
            "record" => Some(Kw::Record),
            "enum" => Some(Kw::Enum),
            "fn" => Some(Kw::Fn),
            "task" => Some(Kw::Task),
            "uses" => Some(Kw::Uses),
            "let" => Some(Kw::Let),
            "mut" => Some(Kw::Mut),
            "return" => Some(Kw::Return),
            "match" => Some(Kw::Match),
            "if" => Some(Kw::If),
            "else" => Some(Kw::Else),
            "await" => Some(Kw::Await),
            "scope" => Some(Kw::Scope),
            "spawn" => Some(Kw::Spawn),
            "true" => Some(Kw::True),
            "false" => Some(Kw::False),
            _ => None,
        };
        match kw {
            Some(kw) => TokenKind::Kw(kw),
            None if RESERVED.contains(&word) => TokenKind::Reserved(word.to_string()),
            None => TokenKind::Ident(word.to_string()),
        }
    }

    fn number(&mut self) -> TokenKind {
        let start = self.pos;
        if self.peek() == Some(b'0') && matches!(self.peek_at(1), Some(b'x' | b'X' | b'b' | b'B')) {
            let radix = if matches!(self.peek_at(1), Some(b'x' | b'X')) {
                16
            } else {
                2
            };
            self.pos += 2;
            let digits_start = self.pos;
            while self
                .peek()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_')
            {
                self.pos += 1;
            }
            let digits: String = self.text[digits_start..self.pos]
                .chars()
                .filter(|c| *c != '_')
                .collect();
            return match i64::from_str_radix(&digits, radix) {
                Ok(v) => TokenKind::Int(v),
                Err(_) => {
                    self.error(
                        Span::new(start as u32, self.pos as u32),
                        format!("invalid base-{radix} integer literal"),
                    );
                    TokenKind::Int(0)
                }
            };
        }

        while self.peek().is_some_and(|c| c.is_ascii_digit() || c == b'_') {
            self.pos += 1;
        }

        // A dot begins a fraction only when a digit follows it; `2.seconds` stays a method call.
        let mut is_float = false;
        if self.peek() == Some(b'.') && self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
            is_float = true;
            self.pos += 1;
            while self.peek().is_some_and(|c| c.is_ascii_digit() || c == b'_') {
                self.pos += 1;
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E'))
            && (self.peek_at(1).is_some_and(|c| c.is_ascii_digit())
                || (matches!(self.peek_at(1), Some(b'+' | b'-'))
                    && self.peek_at(2).is_some_and(|c| c.is_ascii_digit())))
        {
            is_float = true;
            self.pos += 2;
            while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                self.pos += 1;
            }
        }

        let span = Span::new(start as u32, self.pos as u32);
        let digits: String = self.text[start..self.pos]
            .chars()
            .filter(|c| *c != '_')
            .collect();
        if is_float {
            match digits.parse::<f64>() {
                Ok(v) => TokenKind::Float(v),
                Err(_) => {
                    self.error(span, "invalid float literal");
                    TokenKind::Float(0.0)
                }
            }
        } else {
            match digits.parse::<i64>() {
                Ok(v) => TokenKind::Int(v),
                Err(_) => {
                    self.error(span, "integer literal does not fit in `I64`");
                    TokenKind::Int(0)
                }
            }
        }
    }

    fn string(&mut self) -> TokenKind {
        let start = self.pos;
        self.pos += 1;
        let mut out = String::new();
        loop {
            match self.peek() {
                None | Some(b'\n') => {
                    self.error(
                        Span::new(start as u32, self.pos as u32),
                        "unterminated string literal",
                    );
                    break;
                }
                Some(b'"') => {
                    self.pos += 1;
                    break;
                }
                Some(b'\\') => {
                    let esc_start = self.pos;
                    self.pos += 1;
                    let escaped = match self.peek() {
                        Some(b'n') => Some('\n'),
                        Some(b't') => Some('\t'),
                        Some(b'r') => Some('\r'),
                        Some(b'0') => Some('\0'),
                        Some(b'\\') => Some('\\'),
                        Some(b'"') => Some('"'),
                        _ => None,
                    };
                    match escaped {
                        Some(c) => {
                            out.push(c);
                            self.pos += 1;
                        }
                        None => {
                            self.pos += 1;
                            self.error(
                                Span::new(esc_start as u32, self.pos as u32),
                                "unknown escape sequence",
                            );
                        }
                    }
                }
                Some(_) => {
                    let c = self.text[self.pos..].chars().next().unwrap();
                    out.push(c);
                    self.pos += c.len_utf8();
                }
            }
        }
        TokenKind::Str(out)
    }

    fn punct(&mut self) -> Option<TokenKind> {
        let start = self.pos;
        let two = |l: &mut Self, kind: TokenKind| {
            l.pos += 2;
            Some(kind)
        };
        let one = |l: &mut Self, kind: TokenKind| {
            l.pos += 1;
            Some(kind)
        };
        let (c, next) = (self.peek()?, self.peek_at(1));
        match (c, next) {
            (b'=', Some(b'=')) => two(self, TokenKind::EqEq),
            (b'=', Some(b'>')) => two(self, TokenKind::FatArrow),
            (b'!', Some(b'=')) => two(self, TokenKind::Ne),
            (b'<', Some(b'=')) => two(self, TokenKind::Le),
            (b'>', Some(b'=')) => two(self, TokenKind::Ge),
            (b'-', Some(b'>')) => two(self, TokenKind::ThinArrow),
            (b'&', Some(b'&')) => two(self, TokenKind::AndAnd),
            (b'|', Some(b'|')) => two(self, TokenKind::OrOr),
            (b'.', Some(b'.')) => two(self, TokenKind::DotDot),
            (b'(', _) => one(self, TokenKind::LParen),
            (b')', _) => one(self, TokenKind::RParen),
            (b'{', _) => one(self, TokenKind::LBrace),
            (b'}', _) => one(self, TokenKind::RBrace),
            (b'[', _) => one(self, TokenKind::LBracket),
            (b']', _) => one(self, TokenKind::RBracket),
            (b',', _) => one(self, TokenKind::Comma),
            (b'.', _) => one(self, TokenKind::Dot),
            (b':', _) => one(self, TokenKind::Colon),
            (b'?', _) => one(self, TokenKind::Question),
            (b'@', _) => one(self, TokenKind::At),
            (b'#', _) => one(self, TokenKind::Hash),
            (b'=', _) => one(self, TokenKind::Eq),
            (b'<', _) => one(self, TokenKind::Lt),
            (b'>', _) => one(self, TokenKind::Gt),
            (b'+', _) => one(self, TokenKind::Plus),
            (b'-', _) => one(self, TokenKind::Minus),
            (b'*', _) => one(self, TokenKind::Star),
            (b'/', _) => one(self, TokenKind::Slash),
            (b'%', _) => one(self, TokenKind::Percent),
            (b'!', _) => one(self, TokenKind::Bang),
            (b'&', _) => one(self, TokenKind::Amp),
            (b'|', _) => one(self, TokenKind::Pipe),
            (b';', _) => {
                self.pos += 1;
                self.error(
                    Span::new(start as u32, self.pos as u32),
                    "statements are separated by line breaks, not `;`",
                );
                None
            }
            _ => {
                let c = self.text[self.pos..].chars().next().unwrap();
                self.pos += c.len_utf8();
                self.error(
                    Span::new(start as u32, self.pos as u32),
                    format!("unexpected character `{c}`"),
                );
                None
            }
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn peek_at(&self, n: usize) -> Option<u8> {
        self.bytes.get(self.pos + n).copied()
    }

    fn error(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(Diagnostic::new(span, message));
    }
}

fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}

fn is_ident_continue(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}
