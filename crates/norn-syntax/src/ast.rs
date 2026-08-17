//! The spanned abstract syntax tree.
//!
//! Every node carries the span it was parsed from. The tree is not lossless — comments and
//! original layout are discarded — so `print` produces a canonical rendering rather than the
//! original bytes. Round-tripping is therefore defined as idempotence of print∘parse, which is
//! what the snapshot corpus checks.

use crate::span::Span;

#[derive(Clone, Debug)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

/// A dotted name: `fs`, `std.fs`, `LoadError.NotFound`.
#[derive(Clone, Debug)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub span: Span,
}

impl Path {
    pub fn last(&self) -> &Ident {
        self.segments.last().expect("a path has at least one segment")
    }

    pub fn text(&self) -> String {
        self.segments.iter().map(|s| s.name.as_str()).collect::<Vec<_>>().join(".")
    }
}

#[derive(Debug)]
pub struct Module {
    pub name: Option<Path>,
    pub uses: Vec<UseDecl>,
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Debug)]
pub struct UseDecl {
    pub path: Path,
    pub span: Span,
}

#[derive(Debug)]
pub enum Item {
    Record(RecordDecl),
    Enum(EnumDecl),
    Fn(FnDecl),
}

#[derive(Debug)]
pub struct RecordDecl {
    pub name: Ident,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}

#[derive(Debug)]
pub struct FieldDecl {
    pub name: Ident,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug)]
pub struct EnumDecl {
    pub name: Ident,
    pub variants: Vec<Variant>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Variant {
    pub name: Ident,
    pub payload: VariantPayload,
    pub span: Span,
}

#[derive(Debug)]
pub enum VariantPayload {
    Unit,
    Tuple(Vec<Type>),
    Record(Vec<FieldDecl>),
}

#[derive(Debug)]
pub struct FnDecl {
    pub is_task: bool,
    pub name: Ident,
    pub params: Vec<Param>,
    pub ret: Option<Type>,
    /// The declared capability set. Checked, not inferred; empty until M4 gives it meaning.
    pub uses: Vec<Path>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug)]
pub struct Param {
    pub name: Ident,
    pub ty: Type,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TypeKind {
    /// `()`
    Unit,
    /// `Result<T, E>`, `I64`, `http.Request`
    Path { path: Path, args: Vec<Type> },
    /// `&T`, `&mut T`
    Ref { mutable: bool, inner: Box<Type> },
}

#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum StmtKind {
    Let { mutable: bool, name: Ident, ty: Option<Type>, value: Expr },
    Assign { target: Expr, value: Expr },
    Return(Option<Expr>),
    Expr(Expr),
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExprKind {
    Unit,
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    Path(Path),
    Unary { op: UnOp, expr: Box<Expr> },
    Binary { op: BinOp, lhs: Box<Expr>, rhs: Box<Expr> },
    Field { base: Box<Expr>, name: Ident },
    Index { base: Box<Expr>, index: Box<Expr> },
    Call { callee: Box<Expr>, type_args: Vec<Type>, args: Vec<Arg> },
    Record { path: Path, fields: Vec<FieldInit> },
    Await(Box<Expr>),
    /// Postfix `?`: propagate the error case outward.
    Try(Box<Expr>),
    Match { scrutinee: Box<Expr>, arms: Vec<Arm> },
    If { cond: Box<Expr>, then: Block, els: Option<Box<Expr>> },
    Block(Block),
    Lambda { is_task: bool, params: Vec<Pat>, body: Box<Expr> },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnOp {
    Neg,
    Not,
    Ref,
    RefMut,
}

impl UnOp {
    pub fn text(self) -> &'static str {
        match self {
            UnOp::Neg => "-",
            UnOp::Not => "!",
            UnOp::Ref => "&",
            UnOp::RefMut => "&mut ",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl BinOp {
    pub fn text(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "&&",
            BinOp::Or => "||",
        }
    }
}

/// A call argument, optionally named: `http.text(status: 200, body: greeting)`.
#[derive(Debug)]
pub struct Arg {
    pub name: Option<Ident>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct FieldInit {
    pub name: Ident,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct Arm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum PatKind {
    Wild,
    /// A lowercase single-segment name binds; anything else is a path pattern.
    Binding(Ident),
    Int(i64),
    Str(String),
    Bool(bool),
    Path(Path),
    Tuple { path: Path, elems: Vec<Pat> },
    Record { path: Path, fields: Vec<FieldPat>, rest: bool },
    Or(Vec<Pat>),
}

#[derive(Debug)]
pub struct FieldPat {
    pub name: Ident,
    /// `None` is shorthand: `Io { code }` binds `code` to the field of the same name.
    pub pat: Option<Pat>,
    pub span: Span,
}
