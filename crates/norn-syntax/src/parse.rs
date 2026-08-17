//! Recursive-descent parser with precedence climbing for binary operators.
//!
//! Two layout rules keep the grammar semicolon-free:
//!
//! 1. Statements within a block are separated by line breaks.
//! 2. A postfix chain continues across a line break only for `.`; a `(`, `[`, or `?` on a fresh
//!    line starts something new rather than silently extending the previous expression.
//!
//! Two more rules keep spelling out of the grammar. A `#` marks a data constructor — `#User(id: 7)`
//! builds a value, `user(id: 7)` calls a function — so a brace is always a block and never a
//! literal. In a pattern, a bare name always binds and only a marked path matches. Nothing anywhere
//! depends on whether a name is capitalised.
//!
//! Errors are recorded per item and the parser resynchronises at the next top-level declaration,
//! so one malformed function does not hide the rest of the file.

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::lex::{Kw, Lexed, Token, TokenKind, lex};
use crate::span::Span;

pub struct Parsed {
    pub module: Module,
    pub errors: Vec<Diagnostic>,
}

impl Parsed {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
}

pub fn parse(text: &str) -> Parsed {
    let Lexed { tokens, errors } = lex(text);
    let mut parser = Parser {
        tokens,
        pos: 0,
        errors,
    };
    let module = parser.module();
    let mut errors = parser.errors;
    // Lexer diagnostics are produced up front, so report in source order rather than stage order.
    errors.sort_by_key(|d| d.span.start);
    Parsed { module, errors }
}

/// Signals that the current item could not be parsed. The diagnostic is already recorded.
struct Bail;

type PResult<T> = Result<T, Bail>;

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    errors: Vec<Diagnostic>,
}

impl Parser {
    // ---------------------------------------------------------------- token access

    fn peek(&self) -> &Token {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn peek_kind(&self) -> &TokenKind {
        &self.peek().kind
    }

    fn peek_at(&self, n: usize) -> &Token {
        &self.tokens[(self.pos + n).min(self.tokens.len() - 1)]
    }

    /// Compare by variant, except for keywords, which must match exactly — every keyword shares
    /// one `TokenKind` discriminant.
    fn at(&self, kind: &TokenKind) -> bool {
        match (self.peek_kind(), kind) {
            (TokenKind::Kw(found), TokenKind::Kw(want)) => found == want,
            (found, want) => std::mem::discriminant(found) == std::mem::discriminant(want),
        }
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek_kind(), TokenKind::Eof)
    }

    fn advance(&mut self) -> Token {
        let token = self.tokens[self.pos.min(self.tokens.len() - 1)].clone();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        token
    }

    fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.at(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: TokenKind) -> PResult<Token> {
        if self.at(&kind) {
            Ok(self.advance())
        } else {
            let found = self.peek_kind().describe();
            Err(self.error(format!("expected {}, found {found}", kind.describe())))
        }
    }

    fn error(&mut self, message: impl Into<String>) -> Bail {
        let span = self.peek().span;
        self.errors.push(Diagnostic::new(span, message));
        Bail
    }

    fn push(&mut self, diagnostic: Diagnostic) -> Bail {
        self.errors.push(diagnostic);
        Bail
    }

    // ---------------------------------------------------------------- module

    fn module(&mut self) -> Module {
        let start = self.peek().span;
        let mut name = None;
        let mut uses = Vec::new();
        let mut items = Vec::new();

        if self.at(&TokenKind::Kw(Kw::Module)) {
            self.advance();
            match self.path() {
                Ok(path) => name = Some(path),
                Err(Bail) => self.recover(),
            }
        }

        while !self.at_eof() {
            let before = self.pos;
            match self.top_level(&mut uses, &mut items) {
                Ok(()) => {}
                Err(Bail) => self.recover(),
            }
            if self.pos == before {
                // Nothing consumed: force progress so a bad token cannot loop forever.
                self.advance();
            }
        }

        let end = self.peek().span;
        Module {
            name,
            uses,
            items,
            span: start.to(end),
        }
    }

    fn top_level(&mut self, uses: &mut Vec<UseDecl>, items: &mut Vec<Item>) -> PResult<()> {
        if !self.at_eof() && !self.peek().nl_before && (!uses.is_empty() || !items.is_empty()) {
            let found = self.peek_kind().describe();
            return Err(self.error(format!(
                "expected a line break before {found}, found it on the same line as the previous declaration"
            )));
        }
        match self.peek_kind().clone() {
            TokenKind::Kw(Kw::Use) => {
                let start = self.advance().span;
                let path = self.path()?;
                let span = start.to(path.span);
                uses.push(UseDecl { path, span });
            }
            TokenKind::Kw(Kw::Record) => items.push(Item::Record(self.record_decl()?)),
            TokenKind::Kw(Kw::Enum) => items.push(Item::Enum(self.enum_decl()?)),
            TokenKind::Kw(Kw::Fn) | TokenKind::Kw(Kw::Task) => {
                items.push(Item::Fn(self.fn_decl()?))
            }
            TokenKind::Kw(Kw::Module) => {
                let span = self.peek().span;
                return Err(self.push(
                    Diagnostic::new(span, "`module` must be the first declaration in a file")
                        .label("second module declaration"),
                ));
            }
            TokenKind::At => {
                let span = self.peek().span;
                return Err(self.push(
                    Diagnostic::new(span, "attributes are not available yet")
                        .label("`@` attribute")
                        .note("derives and declaration attributes arrive with metaprogramming; see BOOTSTRAP.md §8"),
                ));
            }
            TokenKind::Reserved(word) => {
                let span = self.peek().span;
                return Err(self.push(reserved_diagnostic(span, &word)));
            }
            other => {
                let span = self.peek().span;
                return Err(self.push(
                    Diagnostic::new(
                        span,
                        format!("expected a declaration, found {}", other.describe()),
                    )
                    .note(
                        "a file contains `use`, `record`, `enum`, `fn`, and `task fn` declarations",
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Skip forward to the next plausible top-level declaration.
    fn recover(&mut self) {
        loop {
            if self.at_eof() {
                return;
            }
            let token = self.peek();
            let starts_decl = matches!(
                token.kind,
                TokenKind::Kw(Kw::Use)
                    | TokenKind::Kw(Kw::Record)
                    | TokenKind::Kw(Kw::Enum)
                    | TokenKind::Kw(Kw::Fn)
                    | TokenKind::Kw(Kw::Task)
            );
            if starts_decl && token.nl_before {
                return;
            }
            self.advance();
        }
    }

    // ---------------------------------------------------------------- declarations

    fn record_decl(&mut self) -> PResult<RecordDecl> {
        let start = self.advance().span;
        let name = self.ident()?;
        self.expect(TokenKind::LBrace)?;
        let mut fields = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at_eof() {
            fields.push(self.field_decl()?);
            self.separator(&TokenKind::RBrace, "field")?;
        }
        let end = self.expect(TokenKind::RBrace)?.span;
        Ok(RecordDecl {
            name,
            fields,
            span: start.to(end),
        })
    }

    fn field_decl(&mut self) -> PResult<FieldDecl> {
        let name = self.ident()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.ty()?;
        let span = name.span.to(ty.span);
        Ok(FieldDecl { name, ty, span })
    }

    fn enum_decl(&mut self) -> PResult<EnumDecl> {
        let start = self.advance().span;
        let name = self.ident()?;
        self.expect(TokenKind::LBrace)?;
        let mut variants = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at_eof() {
            let vname = self.ident()?;
            let mut span = vname.span;
            let payload = if self.at(&TokenKind::LParen) && !self.peek().nl_before {
                self.advance();
                let mut types = Vec::new();
                while !self.at(&TokenKind::RParen) && !self.at_eof() {
                    types.push(self.ty()?);
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                span = span.to(self.expect(TokenKind::RParen)?.span);
                VariantPayload::Tuple(types)
            } else if self.at(&TokenKind::LBrace) && !self.peek().nl_before {
                self.advance();
                let mut fields = Vec::new();
                while !self.at(&TokenKind::RBrace) && !self.at_eof() {
                    fields.push(self.field_decl()?);
                    self.separator(&TokenKind::RBrace, "field")?;
                }
                span = span.to(self.expect(TokenKind::RBrace)?.span);
                VariantPayload::Record(fields)
            } else {
                VariantPayload::Unit
            };
            variants.push(Variant {
                name: vname,
                payload,
                span,
            });
            self.separator(&TokenKind::RBrace, "variant")?;
        }
        let end = self.expect(TokenKind::RBrace)?.span;
        Ok(EnumDecl {
            name,
            variants,
            span: start.to(end),
        })
    }

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        let start = self.peek().span;
        let is_task = self.eat(&TokenKind::Kw(Kw::Task));
        self.expect(TokenKind::Kw(Kw::Fn))?;
        let name = self.ident()?;

        self.expect(TokenKind::LParen)?;
        let mut params = Vec::new();
        while !self.at(&TokenKind::RParen) && !self.at_eof() {
            let pname = self.ident()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.ty()?;
            let span = pname.span.to(ty.span);
            params.push(Param {
                name: pname,
                ty,
                span,
            });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RParen)?;

        let ret = if self.eat(&TokenKind::ThinArrow) {
            Some(self.ty()?)
        } else {
            None
        };

        let mut uses = Vec::new();
        if self.at(&TokenKind::Kw(Kw::Uses)) {
            let uses_span = self.advance().span;
            if !is_task {
                self.errors.push(
                    Diagnostic::new(uses_span, "only a `task fn` may declare capabilities")
                        .label("`uses` on an ordinary function")
                        .note(
                            "ordinary functions are pure; move the effectful work into a `task fn`",
                        ),
                );
            }
            self.expect(TokenKind::LBrace)?;
            while !self.at(&TokenKind::RBrace) && !self.at_eof() {
                uses.push(self.path()?);
                self.separator(&TokenKind::RBrace, "capability")?;
            }
            self.expect(TokenKind::RBrace)?;
        }

        let body = self.block()?;
        let span = start.to(body.span);
        Ok(FnDecl {
            is_task,
            name,
            params,
            ret,
            uses,
            body,
            span,
        })
    }

    /// Accept a comma, a line break, or the closing token as an item separator.
    fn separator(&mut self, close: &TokenKind, what: &str) -> PResult<()> {
        if self.eat(&TokenKind::Comma) || self.at(close) || self.at_eof() {
            return Ok(());
        }
        if self.peek().nl_before {
            return Ok(());
        }
        let found = self.peek_kind().describe();
        Err(self.error(format!(
            "expected a line break or `,` between {what}s, found {found}"
        )))
    }

    // ---------------------------------------------------------------- names and types

    fn ident(&mut self) -> PResult<Ident> {
        match self.peek_kind().clone() {
            TokenKind::Ident(name) => {
                let span = self.advance().span;
                Ok(Ident { name, span })
            }
            TokenKind::Reserved(word) => {
                let span = self.peek().span;
                Err(self.push(reserved_diagnostic(span, &word)))
            }
            other => Err(self.error(format!("expected a name, found {}", other.describe()))),
        }
    }

    fn path(&mut self) -> PResult<Path> {
        let first = self.ident()?;
        let mut span = first.span;
        let mut segments = vec![first];
        while self.at(&TokenKind::Dot) && matches!(self.peek_at(1).kind, TokenKind::Ident(_)) {
            self.advance();
            let seg = self.ident()?;
            span = span.to(seg.span);
            segments.push(seg);
        }
        Ok(Path { segments, span })
    }

    fn ty(&mut self) -> PResult<Type> {
        let start = self.peek().span;
        if self.at(&TokenKind::LParen) {
            self.advance();
            let end = self.expect(TokenKind::RParen)?.span;
            return Ok(Type {
                kind: TypeKind::Unit,
                span: start.to(end),
            });
        }
        if self.at(&TokenKind::Amp) {
            self.advance();
            let mutable = self.eat(&TokenKind::Kw(Kw::Mut));
            let inner = self.ty()?;
            let span = start.to(inner.span);
            return Ok(Type {
                kind: TypeKind::Ref {
                    mutable,
                    inner: Box::new(inner),
                },
                span,
            });
        }
        let path = self.path()?;
        let mut span = path.span;
        let mut args = Vec::new();
        if self.at(&TokenKind::Lt) {
            self.advance();
            while !self.at(&TokenKind::Gt) && !self.at_eof() {
                args.push(self.ty()?);
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            span = span.to(self.expect(TokenKind::Gt)?.span);
        }
        Ok(Type {
            kind: TypeKind::Path { path, args },
            span,
        })
    }

    // ---------------------------------------------------------------- statements

    fn block(&mut self) -> PResult<Block> {
        let start = self.expect(TokenKind::LBrace)?.span;
        let mut stmts = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at_eof() {
            stmts.push(self.stmt()?);
            if !self.at(&TokenKind::RBrace) && !self.at_eof() && !self.peek().nl_before {
                let found = self.peek_kind().describe();
                let span = self.peek().span;
                let mut diagnostic = Diagnostic::new(
                    span,
                    format!("expected a line break between statements, found {found}"),
                );
                if self.at(&TokenKind::LBrace) {
                    // The mistake a Rust or Go reader makes first.
                    diagnostic = diagnostic
                        .label("this brace opens a block")
                        .note("a brace always opens a block; a record is built with `#Name(field: value)`");
                }
                return Err(self.push(diagnostic));
            }
        }
        let end = self.expect(TokenKind::RBrace)?.span;
        Ok(Block {
            stmts,
            span: start.to(end),
        })
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let start = self.peek().span;
        match self.peek_kind().clone() {
            TokenKind::Kw(Kw::Let) => {
                self.advance();
                let mutable = self.eat(&TokenKind::Kw(Kw::Mut));
                let name = self.ident()?;
                let ty = if self.eat(&TokenKind::Colon) {
                    Some(self.ty()?)
                } else {
                    None
                };
                self.expect(TokenKind::Eq)?;
                let value = self.expr()?;
                let span = start.to(value.span);
                Ok(Stmt {
                    kind: StmtKind::Let {
                        mutable,
                        name,
                        ty,
                        value,
                    },
                    span,
                })
            }
            TokenKind::Kw(Kw::Return) => {
                self.advance();
                let has_value =
                    !self.at(&TokenKind::RBrace) && !self.at_eof() && !self.peek().nl_before;
                let value = if has_value { Some(self.expr()?) } else { None };
                let span = value.as_ref().map_or(start, |v| start.to(v.span));
                Ok(Stmt {
                    kind: StmtKind::Return(value),
                    span,
                })
            }
            TokenKind::Reserved(word) => {
                let span = self.peek().span;
                Err(self.push(reserved_diagnostic(span, &word)))
            }
            _ => {
                let expr = self.expr()?;
                if self.at(&TokenKind::Eq) {
                    self.advance();
                    let value = self.expr()?;
                    let span = expr.span.to(value.span);
                    return Ok(Stmt {
                        kind: StmtKind::Assign {
                            target: expr,
                            value,
                        },
                        span,
                    });
                }
                let span = expr.span;
                Ok(Stmt {
                    kind: StmtKind::Expr(expr),
                    span,
                })
            }
        }
    }

    // ---------------------------------------------------------------- expressions

    fn expr(&mut self) -> PResult<Expr> {
        self.expr_bp(0)
    }

    fn expr_bp(&mut self, min_bp: u8) -> PResult<Expr> {
        let mut lhs = self.unary()?;
        loop {
            let Some(op) = bin_op(self.peek_kind()) else {
                break;
            };
            let bp = binding_power(op);
            if bp < min_bp {
                break;
            }
            self.advance();
            let rhs = self.expr_bp(bp + 1)?;
            let span = lhs.span.to(rhs.span);
            lhs = Expr {
                kind: ExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let op = match self.peek_kind() {
            TokenKind::Minus => Some(UnOp::Neg),
            TokenKind::Bang => Some(UnOp::Not),
            TokenKind::Amp => {
                if matches!(self.peek_at(1).kind, TokenKind::Kw(Kw::Mut)) {
                    Some(UnOp::RefMut)
                } else {
                    Some(UnOp::Ref)
                }
            }
            _ => None,
        };
        if let Some(op) = op {
            self.advance();
            if op == UnOp::RefMut {
                self.advance();
            }
            let expr = self.unary()?;
            let span = start.to(expr.span);
            return Ok(Expr {
                kind: ExprKind::Unary {
                    op,
                    expr: Box::new(expr),
                },
                span,
            });
        }

        if self.at(&TokenKind::Kw(Kw::Await)) {
            self.advance();
            // `await foo()?` reads as `(await foo())?`: the task is awaited first, and `?`
            // propagates the failure of its result. So the operand stops short of the `?`.
            let inner = self.primary()?;
            let inner = self.postfix_with(inner, false)?;
            let span = start.to(inner.span);
            let awaited = Expr {
                kind: ExprKind::Await(Box::new(inner)),
                span,
            };
            return self.postfix(awaited);
        }

        let primary = self.primary()?;
        self.postfix(primary)
    }

    fn postfix(&mut self, expr: Expr) -> PResult<Expr> {
        self.postfix_with(expr, true)
    }

    fn postfix_with(&mut self, mut expr: Expr, allow_try: bool) -> PResult<Expr> {
        loop {
            let nl = self.peek().nl_before;
            match self.peek_kind() {
                // A `.` may begin a fresh line: chained operator pipelines are written that way.
                TokenKind::Dot => {
                    self.advance();
                    let name = self.ident()?;
                    let span = expr.span.to(name.span);
                    expr = Expr {
                        kind: ExprKind::Field {
                            base: Box::new(expr),
                            name,
                        },
                        span,
                    };
                }
                TokenKind::LParen if !nl => {
                    expr = self.call(expr, Vec::new())?;
                }
                // Explicit type arguments, as in `response.json<Profile>(limit: 2.mebibytes)`.
                // Speculative: `a < b` must still read as a comparison, so the attempt is only
                // accepted when a call follows.
                TokenKind::Lt if !nl => {
                    let save = self.pos;
                    let saved_errors = self.errors.len();
                    match self.try_type_args() {
                        Some(args) => expr = self.call(expr, args)?,
                        None => {
                            self.pos = save;
                            self.errors.truncate(saved_errors);
                            return Ok(expr);
                        }
                    }
                }
                TokenKind::LBracket if !nl => {
                    self.advance();
                    let index = self.expr()?;
                    let end = self.expect(TokenKind::RBracket)?.span;
                    let span = expr.span.to(end);
                    expr = Expr {
                        kind: ExprKind::Index {
                            base: Box::new(expr),
                            index: Box::new(index),
                        },
                        span,
                    };
                }
                TokenKind::Question if !nl && allow_try => {
                    let end = self.advance().span;
                    let span = expr.span.to(end);
                    expr = Expr {
                        kind: ExprKind::Try(Box::new(expr)),
                        span,
                    };
                }
                _ => return Ok(expr),
            }
        }
    }

    fn try_type_args(&mut self) -> Option<Vec<Type>> {
        self.advance(); // `<`
        let mut args = Vec::new();
        loop {
            if self.at(&TokenKind::Gt) {
                break;
            }
            let ty = self.ty().ok()?;
            args.push(ty);
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        if !self.eat(&TokenKind::Gt) {
            return None;
        }
        // Only a call may carry type arguments, so a `(` must follow for this reading to hold.
        if !self.at(&TokenKind::LParen) || self.peek().nl_before {
            return None;
        }
        Some(args)
    }

    fn call(&mut self, callee: Expr, type_args: Vec<Type>) -> PResult<Expr> {
        self.expect(TokenKind::LParen)?;
        let mut args = Vec::new();
        while !self.at(&TokenKind::RParen) && !self.at_eof() {
            let arg_start = self.peek().span;
            // `status: 200` — a named argument, distinguished from a bare expression by the colon.
            let name = match (self.peek_kind().clone(), &self.peek_at(1).kind) {
                (TokenKind::Ident(name), TokenKind::Colon) => {
                    let span = self.advance().span;
                    self.advance();
                    Some(Ident { name, span })
                }
                _ => None,
            };
            let value = self.expr()?;
            let span = arg_start.to(value.span);
            args.push(Arg { name, value, span });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let end = self.expect(TokenKind::RParen)?.span;
        let span = callee.span.to(end);
        Ok(Expr {
            kind: ExprKind::Call {
                callee: Box::new(callee),
                type_args,
                args,
            },
            span,
        })
    }

    fn primary(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        match self.peek_kind().clone() {
            TokenKind::Int(v) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Int(v),
                    span: start,
                })
            }
            TokenKind::Float(v) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Float(v),
                    span: start,
                })
            }
            TokenKind::Str(v) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Str(v),
                    span: start,
                })
            }
            TokenKind::Kw(Kw::True) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Bool(true),
                    span: start,
                })
            }
            TokenKind::Kw(Kw::False) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Bool(false),
                    span: start,
                })
            }
            TokenKind::Kw(Kw::Match) => self.match_expr(),
            TokenKind::Kw(Kw::If) => self.if_expr(),
            TokenKind::LBrace => {
                let block = self.block()?;
                let span = block.span;
                Ok(Expr {
                    kind: ExprKind::Block(block),
                    span,
                })
            }
            TokenKind::Kw(Kw::Task) => {
                // `task request => handle(request)` — a task-valued lambda.
                self.advance();
                let params = self.lambda_params()?;
                self.expect(TokenKind::FatArrow)?;
                let body = self.expr()?;
                let span = start.to(body.span);
                Ok(Expr {
                    kind: ExprKind::Lambda {
                        is_task: true,
                        params,
                        body: Box::new(body),
                    },
                    span,
                })
            }
            TokenKind::Underscore if matches!(self.peek_at(1).kind, TokenKind::FatArrow) => {
                let params = self.lambda_params()?;
                self.expect(TokenKind::FatArrow)?;
                let body = self.expr()?;
                let span = start.to(body.span);
                Ok(Expr {
                    kind: ExprKind::Lambda {
                        is_task: false,
                        params,
                        body: Box::new(body),
                    },
                    span,
                })
            }
            TokenKind::LParen => self.paren_or_lambda(),
            TokenKind::Ident(_) => {
                if matches!(self.peek_at(1).kind, TokenKind::FatArrow) {
                    let params = self.lambda_params()?;
                    self.expect(TokenKind::FatArrow)?;
                    let body = self.expr()?;
                    let span = start.to(body.span);
                    return Ok(Expr {
                        kind: ExprKind::Lambda {
                            is_task: false,
                            params,
                            body: Box::new(body),
                        },
                        span,
                    });
                }
                let path = self.path()?;
                let span = path.span;
                Ok(Expr {
                    kind: ExprKind::Path(path),
                    span,
                })
            }
            TokenKind::Hash => {
                self.advance();
                let path = self.path()?;
                let (args, end) = self.construct_args()?;
                let span = start.to(end.unwrap_or(path.span));
                Ok(Expr {
                    kind: ExprKind::Construct { path, args },
                    span,
                })
            }
            TokenKind::Reserved(word) => Err(self.push(reserved_diagnostic(start, &word))),
            other => Err(self.error(format!(
                "expected an expression, found {}",
                other.describe()
            ))),
        }
    }

    /// The argument list of a data constructor, which a unit variant omits entirely: `#NotFound`
    /// and `#NotFound()` mean the same thing.
    fn construct_args(&mut self) -> PResult<(Vec<Arg>, Option<Span>)> {
        if !self.at(&TokenKind::LParen) || self.peek().nl_before {
            return Ok((Vec::new(), None));
        }
        self.advance();
        let mut args = Vec::new();
        while !self.at(&TokenKind::RParen) && !self.at_eof() {
            let start = self.peek().span;
            let name = match (self.peek_kind().clone(), &self.peek_at(1).kind) {
                (TokenKind::Ident(name), TokenKind::Colon) => {
                    let span = self.advance().span;
                    self.advance();
                    Some(Ident { name, span })
                }
                _ => None,
            };
            let value = self.expr()?;
            let span = start.to(value.span);
            args.push(Arg { name, value, span });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let end = self.expect(TokenKind::RParen)?.span;
        Ok((args, Some(end)))
    }

    /// `()`, `(expr)`, `() => e`, or `(a, b) => e`. The lambda readings are tried first and the
    /// parser rewinds if the `=>` does not appear.
    fn paren_or_lambda(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let save = self.pos;
        let saved_errors = self.errors.len();

        if let Ok(params) = self.lambda_params()
            && self.at(&TokenKind::FatArrow)
        {
            self.advance();
            let body = self.expr()?;
            let span = start.to(body.span);
            return Ok(Expr {
                kind: ExprKind::Lambda {
                    is_task: false,
                    params,
                    body: Box::new(body),
                },
                span,
            });
        }
        self.pos = save;
        self.errors.truncate(saved_errors);

        self.advance(); // `(`
        if self.at(&TokenKind::RParen) {
            let end = self.advance().span;
            return Ok(Expr {
                kind: ExprKind::Unit,
                span: start.to(end),
            });
        }
        let mut inner = self.expr()?;
        let end = self.expect(TokenKind::RParen)?.span;
        inner.span = start.to(end);
        Ok(inner)
    }

    fn lambda_params(&mut self) -> PResult<Vec<Pat>> {
        if self.at(&TokenKind::LParen) {
            self.advance();
            let mut params = Vec::new();
            while !self.at(&TokenKind::RParen) && !self.at_eof() {
                params.push(self.pat_single()?);
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(TokenKind::RParen)?;
            Ok(params)
        } else {
            Ok(vec![self.pat_single()?])
        }
    }

    fn if_expr(&mut self) -> PResult<Expr> {
        let start = self.advance().span;
        let cond = self.expr()?;
        let then = self.block()?;
        let mut span = start.to(then.span);
        let els = if self.at(&TokenKind::Kw(Kw::Else)) {
            self.advance();
            let expr = if self.at(&TokenKind::Kw(Kw::If)) {
                self.if_expr()?
            } else {
                let block = self.block()?;
                let span = block.span;
                Expr {
                    kind: ExprKind::Block(block),
                    span,
                }
            };
            span = span.to(expr.span);
            Some(Box::new(expr))
        } else {
            None
        };
        Ok(Expr {
            kind: ExprKind::If {
                cond: Box::new(cond),
                then,
                els,
            },
            span,
        })
    }

    fn match_expr(&mut self) -> PResult<Expr> {
        let start = self.advance().span;
        let scrutinee = self.expr()?;
        self.expect(TokenKind::LBrace)?;
        let mut arms = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at_eof() {
            let arm_start = self.peek().span;
            let pat = self.pat()?;
            let guard = if self.eat(&TokenKind::Kw(Kw::If)) {
                Some(self.expr()?)
            } else {
                None
            };
            self.expect(TokenKind::FatArrow)?;
            let body = self.expr()?;
            let span = arm_start.to(body.span);
            arms.push(Arm {
                pat,
                guard,
                body,
                span,
            });
            self.separator(&TokenKind::RBrace, "arm")?;
        }
        let end = self.expect(TokenKind::RBrace)?.span;
        let span = start.to(end);
        Ok(Expr {
            kind: ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms,
            },
            span,
        })
    }

    // ---------------------------------------------------------------- patterns

    fn pat(&mut self) -> PResult<Pat> {
        let first = self.pat_single()?;
        if !self.at(&TokenKind::Pipe) {
            return Ok(first);
        }
        let mut span = first.span;
        let mut alts = vec![first];
        while self.eat(&TokenKind::Pipe) {
            let alt = self.pat_single()?;
            span = span.to(alt.span);
            alts.push(alt);
        }
        Ok(Pat {
            kind: PatKind::Or(alts),
            span,
        })
    }

    fn pat_single(&mut self) -> PResult<Pat> {
        let start = self.peek().span;
        match self.peek_kind().clone() {
            TokenKind::Underscore => {
                self.advance();
                Ok(Pat {
                    kind: PatKind::Wild,
                    span: start,
                })
            }
            TokenKind::Int(v) => {
                self.advance();
                Ok(Pat {
                    kind: PatKind::Int(v),
                    span: start,
                })
            }
            TokenKind::Minus if matches!(self.peek_at(1).kind, TokenKind::Int(_)) => {
                self.advance();
                let TokenKind::Int(v) = self.peek_kind().clone() else {
                    unreachable!()
                };
                let end = self.advance().span;
                Ok(Pat {
                    kind: PatKind::Int(-v),
                    span: start.to(end),
                })
            }
            TokenKind::Str(v) => {
                self.advance();
                Ok(Pat {
                    kind: PatKind::Str(v),
                    span: start,
                })
            }
            TokenKind::Kw(Kw::True) => {
                self.advance();
                Ok(Pat {
                    kind: PatKind::Bool(true),
                    span: start,
                })
            }
            TokenKind::Kw(Kw::False) => {
                self.advance();
                Ok(Pat {
                    kind: PatKind::Bool(false),
                    span: start,
                })
            }
            // A bare name always binds. Nothing about how it is spelled changes that.
            TokenKind::Ident(name) => {
                let span = self.advance().span;
                if self.at(&TokenKind::Dot) {
                    return Err(self.push(
                        Diagnostic::new(
                            span.to(self.peek().span),
                            "a bare name in a pattern binds",
                        )
                        .label("this is a binding, not a constructor")
                        .note("to match a constructor, mark it: `#LoadError.NotFound`"),
                    ));
                }
                Ok(Pat {
                    kind: PatKind::Binding(Ident { name, span }),
                    span,
                })
            }
            TokenKind::Hash => {
                self.advance();
                let path = self.path()?;
                let mut span = start.to(path.span);
                let mut args = Vec::new();
                let mut rest = false;
                if self.at(&TokenKind::LParen) && !self.peek().nl_before {
                    self.advance();
                    while !self.at(&TokenKind::RParen) && !self.at_eof() {
                        if self.at(&TokenKind::DotDot) {
                            self.advance();
                            rest = true;
                            if !self.eat(&TokenKind::Comma) {
                                break;
                            }
                            continue;
                        }
                        let arg_start = self.peek().span;
                        let name = match (self.peek_kind().clone(), &self.peek_at(1).kind) {
                            (TokenKind::Ident(name), TokenKind::Colon) => {
                                let span = self.advance().span;
                                self.advance();
                                Some(Ident { name, span })
                            }
                            _ => None,
                        };
                        let pat = self.pat()?;
                        let arg_span = arg_start.to(pat.span);
                        args.push(PatArg {
                            name,
                            pat,
                            span: arg_span,
                        });
                        if !self.eat(&TokenKind::Comma) {
                            break;
                        }
                    }
                    span = span.to(self.expect(TokenKind::RParen)?.span);
                }
                Ok(Pat {
                    kind: PatKind::Construct { path, args, rest },
                    span,
                })
            }
            TokenKind::Reserved(word) => Err(self.push(reserved_diagnostic(start, &word))),
            other => Err(self.error(format!("expected a pattern, found {}", other.describe()))),
        }
    }
}

fn reserved_diagnostic(span: Span, word: &str) -> Diagnostic {
    Diagnostic::new(span, format!("`{word}` is reserved for a later milestone"))
        .label("reserved word")
        .note("it cannot be used as a name yet; see BOOTSTRAP.md §5 for when it becomes available")
}

fn bin_op(kind: &TokenKind) -> Option<BinOp> {
    Some(match kind {
        TokenKind::OrOr => BinOp::Or,
        TokenKind::AndAnd => BinOp::And,
        TokenKind::EqEq => BinOp::Eq,
        TokenKind::Ne => BinOp::Ne,
        TokenKind::Lt => BinOp::Lt,
        TokenKind::Le => BinOp::Le,
        TokenKind::Gt => BinOp::Gt,
        TokenKind::Ge => BinOp::Ge,
        TokenKind::Plus => BinOp::Add,
        TokenKind::Minus => BinOp::Sub,
        TokenKind::Star => BinOp::Mul,
        TokenKind::Slash => BinOp::Div,
        TokenKind::Percent => BinOp::Rem,
        _ => return None,
    })
}

/// Higher binds tighter. Comparisons sit between the logical and arithmetic operators, so
/// `a + 1 < b && c` groups the way it reads.
fn binding_power(op: BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 3,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 5,
        BinOp::Add | BinOp::Sub => 7,
        BinOp::Mul | BinOp::Div | BinOp::Rem => 9,
    }
}
