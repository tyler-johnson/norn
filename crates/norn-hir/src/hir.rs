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
    /// `Option` and `Result` occupy the first two slots of the enum table. They are ordinary
    /// enums at runtime; only the type checker knows their arguments vary.
    pub const OPTION: EnumId = EnumId(0);
    pub const RESULT: EnumId = EnumId(1);

    pub const NONE: usize = 0;
    pub const SOME: usize = 1;
    pub const OK: usize = 0;
    pub const ERR: usize = 1;
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

/// Functions the compiler knows about directly. `print` is deliberately the only one: it is what
/// makes `norn run` observable, and everything else can wait for a standard library.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Builtin {
    Print,
}

impl Builtin {
    pub fn from_name(name: &str) -> Option<Builtin> {
        match name {
            "print" => Some(Builtin::Print),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Builtin::Print => "print",
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
