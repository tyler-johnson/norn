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
        self.segments
            .last()
            .expect("a path has at least one segment")
    }

    pub fn text(&self) -> String {
        self.segments
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>()
            .join(".")
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
    Reactor(ReactorDecl),
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

/// An owner of state and a dependency graph over it. Its members are declarations, not statements:
/// nothing here runs in order, and the order it does run in is computed rather than written.
#[derive(Debug)]
pub struct ReactorDecl {
    pub name: Ident,
    pub params: Vec<Param>,
    /// The capability set of the effects this reactor launches. Its spawner's set must cover it.
    pub uses: Vec<Path>,
    pub members: Vec<Member>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Member {
    pub kind: MemberKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum MemberKind {
    /// `input opened: () [capacity: 64, overflow: reject]`
    Input { name: Ident, ty: Type, queue: Queue },
    /// `state accepted: I64 = 0`
    State { name: Ident, ty: Type, init: Expr },
    /// `signal open = accepted - released`, optionally `export`ed and optionally annotated. The
    /// annotation is the *element* type: a signal's own type cannot be written down.
    Signal {
        exported: bool,
        name: Ident,
        ty: Option<Type>,
        body: Expr,
    },
    /// `on opened() { … }` — the only place state is assigned and the only place an effect is
    /// requested.
    On {
        input: Ident,
        params: Vec<Ident>,
        body: Block,
    },
}

/// `[capacity: 64, overflow: reject]`. There is no default: an unbounded queue is the one thing
/// the runtime must never create implicitly, and a default capacity is a number nobody chose.
#[derive(Debug)]
pub struct Queue {
    pub capacity: Expr,
    pub overflow: Ident,
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
    Let {
        mutable: bool,
        name: Ident,
        ty: Option<Type>,
        value: Expr,
    },
    Assign {
        target: Expr,
        value: Expr,
    },
    Return(Option<Expr>),
    /// `after deliver(message) -> delivery_finished` — request an effect, and optionally name the
    /// input its result comes back on. Legal only inside an `on` handler.
    ///
    /// After *what* is not spelled, because within a turn there is only one boundary to be after:
    /// the commit that publishes the snapshot. `await` names what it waits for no more than this
    /// names what it follows.
    After {
        task: Expr,
        returns: Option<Ident>,
    },
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
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Field {
        base: Box<Expr>,
        name: Ident,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        type_args: Vec<Type>,
        args: Vec<Arg>,
    },
    /// A data constructor: `#User(id: 7)`, `#LoadError.Invalid("bad")`, `#LoadError.NotFound`.
    /// The `#` is what separates building a value from calling a function; without it the two
    /// forms would be spelled identically and told apart only by the case of a name.
    Construct {
        path: Path,
        args: Vec<Arg>,
    },
    Await(Box<Expr>),
    /// `scope { … }` — structured concurrency. Valued as its body, and the point at which every
    /// task spawned inside is cancelled and joined.
    Scope(Block),
    /// `spawn e` — start a task in the enclosing scope. It cannot outlive that scope.
    Spawn(Box<Expr>),
    /// `spawn reactor Gate(limit: 8)` — create a reactor and hand back a handle to it. Spelled as
    /// a form of `spawn` because it is one: the reactor is owned by the scope that started it.
    SpawnReactor {
        path: Path,
        args: Vec<Arg>,
    },
    /// Postfix `?`: propagate the error case outward.
    Try(Box<Expr>),
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<Arm>,
    },
    If {
        cond: Box<Expr>,
        then: Block,
        els: Option<Box<Expr>>,
    },
    Block(Block),
    Lambda {
        is_task: bool,
        params: Vec<Pat>,
        body: Box<Expr>,
    },
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
    /// Any bare name binds. What a name looks like never decides this — only its shape does, and
    /// a bare name has no `#` and no dots.
    Binding(Ident),
    Int(i64),
    Str(String),
    Bool(bool),
    /// The mirror of `ExprKind::Construct`: `#LoadError.Io(code, message)`, `#LoadError.NotFound`.
    /// Arguments may be positional or named, and `..` ignores the rest.
    Construct {
        path: Path,
        args: Vec<PatArg>,
        rest: bool,
    },
    Or(Vec<Pat>),
}

/// A constructor argument in a pattern, optionally named: `#LoadError.Io(code: 404, message: m)`.
#[derive(Debug)]
pub struct PatArg {
    pub name: Option<Ident>,
    pub pat: Pat,
    pub span: Span,
}
