//! The typed high-level IR.
//!
//! HIR is the AST after every name has been resolved to an index and every expression has been
//! given a type. It keeps the shape of the source — blocks, `match`, `if`, `?` — because that is
//! what diagnostics and, later, reactive analysis need to talk about. Flattening happens in NIR.

use norn_syntax::Span;

macro_rules! id {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub struct $name(pub u32);

        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(RecordId, "Index into `Program::records`.");
id!(EnumId, "Index into `Program::enums`.");
id!(FnId, "Index into `Program::fns`.");
id!(LocalId, "Index into the enclosing function's `locals`.");

impl EnumId {
    /// `Option`, `Result`, and `IoError` occupy the first three slots of the enum table. They are
    /// ordinary enums at runtime; only the type checker knows that the first two take arguments.
    pub const OPTION: EnumId = EnumId(0);
    pub const RESULT: EnumId = EnumId(1);
    pub const IO_ERROR: EnumId = EnumId(2);

    pub const NONE: usize = 0;
    pub const SOME: usize = 1;
    pub const OK: usize = 0;
    pub const ERR: usize = 1;
}

/// The built-in `IoError`. The tag order lives here because the checker seeds the enum from it and
/// the runtime constructs values against it; two lists would drift.
pub mod io_error {
    pub const NOT_FOUND: usize = 0;
    pub const DENIED: usize = 1;
    pub const IN_USE: usize = 2;
    pub const REFUSED: usize = 3;
    pub const CLOSED: usize = 4;
    pub const OTHER: usize = 5;

    /// Each variant and how many fields it carries.
    pub const VARIANTS: &[(&str, usize)] = &[
        ("NotFound", 0),
        ("Denied", 0),
        ("InUse", 0),
        ("Refused", 0),
        ("Closed", 0),
        ("Other", 1),
    ];
}

/// An operating-system resource. Non-copyable from M4; owned dynamically until then.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Resource {
    Listener,
    Connection,
}

impl Resource {
    pub fn name(self) -> &'static str {
        match self {
            Resource::Listener => "Listener",
            Resource::Connection => "Connection",
        }
    }
}

/// Authority a task needs in order to touch the world. The v0 vocabulary is fixed and closed: an
/// unknown name is an error rather than an extension point, because `uses` is checked and not
/// inferred, and a typo that quietly widened authority would defeat the point of declaring it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Capability {
    Clock,
    NetListen,
    NetIo,
}

impl Capability {
    pub const ALL: &'static [Capability] =
        &[Capability::Clock, Capability::NetListen, Capability::NetIo];

    pub fn from_name(name: &str) -> Option<Capability> {
        match name {
            "clock" => Some(Capability::Clock),
            "net.listen" => Some(Capability::NetListen),
            "net.io" => Some(Capability::NetIo),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Capability::Clock => "clock",
            Capability::NetListen => "net.listen",
            Capability::NetIo => "net.io",
        }
    }
}

/// A monomorphic type. `Option` and `Result` are the only generic constructors in v0, and neither
/// is user-definable.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Unit,
    I64,
    F64,
    Bool,
    Str,
    Record(RecordId),
    Enum(EnumId),
    Option(Box<Ty>),
    Result(Box<Ty>, Box<Ty>),
    /// A computation that has not run. Calling a `task fn` builds one; `await` and `spawn` are what
    /// start it. Laziness is what lets a policy cancel obsolete work in M3 — it cannot cancel work
    /// it did not control the starting of.
    Task(Box<Ty>),
    Resource(Resource),
    /// The type of an expression that never produces a value: `return`, or a block that always
    /// leaves early. Compatible with every expected type.
    Never,
    /// A type that could not be determined. Already reported; suppresses cascading errors.
    Error,
}

impl Ty {
    /// Whether a value of type `self` may be used where `expected` is wanted.
    pub fn fits(&self, expected: &Ty) -> bool {
        match (self, expected) {
            (Ty::Never, _) | (_, Ty::Never) => true,
            (Ty::Error, _) | (_, Ty::Error) => true,
            (a, b) => a == b,
        }
    }

    pub fn is_error(&self) -> bool {
        matches!(self, Ty::Error)
    }
}

pub struct Program {
    pub records: Vec<RecordDef>,
    pub enums: Vec<EnumDef>,
    pub fns: Vec<FnDef>,
    pub main: Option<FnId>,
}

impl Program {
    /// How a type is spelled in a diagnostic.
    pub fn ty_name(&self, ty: &Ty) -> String {
        match ty {
            Ty::Unit => "()".into(),
            Ty::I64 => "I64".into(),
            Ty::F64 => "F64".into(),
            Ty::Bool => "Bool".into(),
            Ty::Str => "String".into(),
            Ty::Record(id) => self.records[id.index()].name.clone(),
            Ty::Enum(id) => self.enums[id.index()].name.clone(),
            Ty::Option(inner) => format!("Option<{}>", self.ty_name(inner)),
            Ty::Result(ok, err) => {
                format!("Result<{}, {}>", self.ty_name(ok), self.ty_name(err))
            }
            Ty::Task(inner) => format!("Task<{}>", self.ty_name(inner)),
            Ty::Resource(resource) => resource.name().into(),
            Ty::Never => "!".into(),
            Ty::Error => "?".into(),
        }
    }
}

pub struct RecordDef {
    pub name: String,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

impl RecordDef {
    pub fn field(&self, name: &str) -> Option<(usize, &FieldDef)> {
        self.fields.iter().enumerate().find(|(_, f)| f.name == name)
    }
}

pub struct FieldDef {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
}

pub struct EnumDef {
    pub name: String,
    pub variants: Vec<VariantDef>,
    pub span: Span,
}

impl EnumDef {
    pub fn variant(&self, name: &str) -> Option<(usize, &VariantDef)> {
        self.variants
            .iter()
            .enumerate()
            .find(|(_, v)| v.name == name)
    }
}

pub struct VariantDef {
    pub name: String,
    /// A tuple payload is stored as fields named `0`, `1`, … so one representation serves both.
    pub fields: Vec<FieldDef>,
    pub positional: bool,
    pub span: Span,
}

pub struct FnDef {
    pub name: String,
    /// Whether calling this function builds a `Task<ret>` instead of running it.
    pub is_task: bool,
    /// The declared capability set, sorted and deduplicated. Checked, not inferred.
    pub uses: Vec<Capability>,
    /// Parameters occupy the first `params` slots of `locals`.
    pub params: usize,
    pub locals: Vec<LocalDef>,
    pub ret: Ty,
    pub body: Expr,
    pub span: Span,
}

pub struct LocalDef {
    pub name: String,
    pub ty: Ty,
    pub mutable: bool,
    pub span: Span,
}

/// Which aggregate a `#`-marked constructor builds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ctor {
    Record(RecordId),
    Variant(EnumId, usize),
}

pub struct Expr {
    pub kind: ExprKind,
    pub ty: Ty,
    pub span: Span,
}

pub enum ExprKind {
    Unit,
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    Local(LocalId),
    /// Field access, resolved to an index into the record's fields.
    Field {
        base: Box<Expr>,
        index: usize,
    },
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// `&&` and `||`, kept apart from `Binary` because they do not evaluate both sides.
    ShortCircuit {
        and: bool,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Call {
        callee: FnId,
        args: Vec<Expr>,
    },
    Builtin {
        builtin: Builtin,
        args: Vec<Expr>,
    },
    /// Arguments are in declaration order and complete: named and defaulted forms are expanded
    /// during checking so that nothing downstream has to reorder anything.
    Construct {
        ctor: Ctor,
        args: Vec<Expr>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<Arm>,
    },
    If {
        cond: Box<Expr>,
        then: Box<Expr>,
        els: Option<Box<Expr>>,
    },
    Block {
        stmts: Vec<Stmt>,
        tail: Option<Box<Expr>>,
    },
    /// Run a task and take its value. Legal only inside a `task fn`, and a suspension point: NIR
    /// turns it into a terminator, which is what makes block ids state numbers.
    Await {
        expr: Box<Expr>,
    },
    /// `scope { … }`. Valued as its body; leaving it cancels and joins everything spawned inside.
    Scope {
        body: Box<Expr>,
    },
    /// `spawn e`, where `e: Task<()>`. Requiring `()` forces a spawned task to say what happens to
    /// its own failures rather than having them silently dropped.
    Spawn {
        expr: Box<Expr>,
    },
    /// Postfix `?`. `ok_variant` distinguishes unwrapping a `Result` from an `Option`.
    Try {
        expr: Box<Expr>,
        enum_id: EnumId,
    },
    Return {
        value: Option<Box<Expr>>,
    },
    /// Stands in for an expression that failed to check.
    Error,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    AddInt,
    SubInt,
    MulInt,
    DivInt,
    RemInt,
    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,
    RemFloat,
    Concat,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Functions the compiler knows about directly. There is no standard library yet, so the set is
/// exactly what a milestone needs to be observable: `print` to say something, and the timer and
/// socket primitives M2 is about.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Builtin {
    Print,
    ListenerPort,
    Sleep,
    TcpListen,
    TcpAccept,
    TcpRead,
    TcpWrite,
    TcpClose,
}

impl Builtin {
    /// Every builtin, for consumers that need the list rather than one entry — the editor grammar
    /// test is the first. It sits beside the exhaustive matches below so that adding a variant puts
    /// the compiler's finger next to the line that also needs the new name.
    pub const ALL: &'static [Builtin] = &[
        Builtin::Print,
        Builtin::ListenerPort,
        Builtin::Sleep,
        Builtin::TcpListen,
        Builtin::TcpAccept,
        Builtin::TcpRead,
        Builtin::TcpWrite,
        Builtin::TcpClose,
    ];

    pub fn from_name(name: &str) -> Option<Builtin> {
        match name {
            "print" => Some(Builtin::Print),
            "listener_port" => Some(Builtin::ListenerPort),
            "sleep" => Some(Builtin::Sleep),
            "tcp_listen" => Some(Builtin::TcpListen),
            "tcp_accept" => Some(Builtin::TcpAccept),
            "tcp_read" => Some(Builtin::TcpRead),
            "tcp_write" => Some(Builtin::TcpWrite),
            "tcp_close" => Some(Builtin::TcpClose),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Builtin::Print => "print",
            Builtin::ListenerPort => "listener_port",
            Builtin::Sleep => "sleep",
            Builtin::TcpListen => "tcp_listen",
            Builtin::TcpAccept => "tcp_accept",
            Builtin::TcpRead => "tcp_read",
            Builtin::TcpWrite => "tcp_write",
            Builtin::TcpClose => "tcp_close",
        }
    }

    /// Whether calling it builds a task rather than producing a value on the spot.
    pub fn is_task(self) -> bool {
        matches!(self.signature().1, Ty::Task(_))
    }

    pub fn capabilities(self) -> &'static [Capability] {
        match self {
            Builtin::Print | Builtin::ListenerPort => &[],
            Builtin::Sleep => &[Capability::Clock],
            Builtin::TcpListen => &[Capability::NetListen],
            Builtin::TcpAccept | Builtin::TcpRead | Builtin::TcpWrite | Builtin::TcpClose => {
                &[Capability::NetIo]
            }
        }
    }

    /// Parameter types and result type. `print` is the one builtin whose parameter is any type at
    /// all, and the checker special-cases it rather than pretending there is a type for that.
    pub fn signature(self) -> (Vec<Ty>, Ty) {
        let listener = Ty::Resource(Resource::Listener);
        let connection = Ty::Resource(Resource::Connection);
        let io_error = || Ty::Enum(EnumId::IO_ERROR);
        let task = |ty: Ty| Ty::Task(Box::new(ty));
        let fallible = |ok: Ty| Ty::Result(Box::new(ok), Box::new(io_error()));
        match self {
            Builtin::Print => (vec![Ty::Error], Ty::Unit),
            Builtin::ListenerPort => (vec![listener], Ty::I64),
            Builtin::Sleep => (vec![Ty::I64], task(Ty::Unit)),
            Builtin::TcpListen => (vec![Ty::I64], task(fallible(listener))),
            Builtin::TcpAccept => (vec![listener], task(fallible(connection))),
            Builtin::TcpRead => (vec![connection], task(fallible(Ty::Str))),
            Builtin::TcpWrite => (vec![connection, Ty::Str], task(fallible(Ty::Unit))),
            Builtin::TcpClose => (vec![connection], task(Ty::Unit)),
        }
    }
}

pub struct Arm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

pub enum PatKind {
    Wild,
    Bind(LocalId),
    Int(i64),
    Str(String),
    Bool(bool),
    /// Sub-patterns are full arity and in declaration order; `..` and named arguments are expanded
    /// to `Wild` during checking.
    Variant {
        enum_id: EnumId,
        variant: usize,
        args: Vec<Pat>,
    },
    Record {
        record: RecordId,
        args: Vec<Pat>,
    },
    Or(Vec<Pat>),
    Error,
}

impl Pat {
    /// Whether this pattern matches every value of its type, which is what lets a `match` be
    /// considered exhaustive without a wildcard arm.
    pub fn is_irrefutable(&self) -> bool {
        matches!(self.kind, PatKind::Wild | PatKind::Bind(_))
    }
}

pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

pub enum StmtKind {
    Let { local: LocalId, value: Expr },
    Assign { place: Expr, value: Expr },
    Expr(Expr),
}
