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

id!(StructId, "Index into `Program::structs`.");
id!(EnumId, "Index into `Program::enums`.");
id!(FnId, "Index into `Program::fns`.");
id!(LocalId, "Index into the enclosing function's `locals`.");
id!(ReactorId, "Index into `Program::reactors`.");
id!(NodeId, "Index into a reactor's `nodes`.");

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

/// An operating-system resource: affine, so using one as a value moves it and using it twice is an
/// error rather than a runtime shrug.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Resource {
    Listener,
    Connection,
    /// A write-only sink on the filesystem, from `file_create`.
    File,
    /// A finite stream of bytes with demand-driven transfer. Its type is spelled `Flow<Bytes>` —
    /// the only element type in v0 — and it is consumed from Norn through the flow intrinsics;
    /// `std/flow`'s `pipe` is the canonical consumer.
    Flow,
}

impl Resource {
    pub fn name(self) -> &'static str {
        match self {
            Resource::Listener => "Listener",
            Resource::Connection => "Connection",
            Resource::File => "File",
            Resource::Flow => "Flow<Bytes>",
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
    FsRead,
    FsWrite,
}

impl Capability {
    pub const ALL: &'static [Capability] = &[
        Capability::Clock,
        Capability::NetListen,
        Capability::NetIo,
        Capability::FsRead,
        Capability::FsWrite,
    ];

    pub fn from_name(name: &str) -> Option<Capability> {
        match name {
            "clock" => Some(Capability::Clock),
            "net.listen" => Some(Capability::NetListen),
            "net.io" => Some(Capability::NetIo),
            "fs.read" => Some(Capability::FsRead),
            "fs.write" => Some(Capability::FsWrite),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Capability::Clock => "clock",
            Capability::NetListen => "net.listen",
            Capability::NetIo => "net.io",
            Capability::FsRead => "fs.read",
            Capability::FsWrite => "fs.write",
        }
    }
}

/// A type. Everything an executable body carries is monomorphic — generic declarations are
/// templates the checker instantiates, and only `Ty::Param` names a hole, opaque inside the one
/// template body that declares it. `Option` and `Result` keep their own spellings: they are the
/// seeded generic constructors, and instantiation composes through them structurally.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Unit,
    I64,
    F64,
    Bool,
    Str,
    /// A sequence of raw octets. What the wire carries and a file holds; `String` is for text that
    /// is known to be text. There is no literal — bytes come from I/O and from `bytes(s)`.
    Bytes,
    Struct(StructId),
    Enum(EnumId),
    Option(Box<Ty>),
    Result(Box<Ty>, Box<Ty>),
    /// A computation that has not run. Calling a `task fn` builds one; `await` and `spawn` are what
    /// start it. Laziness is what lets a policy cancel obsolete work in M3 — it cannot cancel work
    /// it did not control the starting of.
    Task(Box<Ty>),
    Resource(Resource),
    /// `&T`. A value the callee may look at but does not own, so passing one does not move it.
    ///
    /// Producible only in parameter position: `resolve_ty` refuses it everywhere else, which is
    /// what makes "a reference may not escape" a fact about where it can be written down rather
    /// than an analysis. The one place it could still escape is a task, which outlives the call
    /// that built it — so `spawn` and `after` operands may not borrow, and `await f(&x)` is safe
    /// because the awaiting task is parked and ownership is unique.
    Ref(Box<Ty>),
    /// A handle to a running reactor. Spelled by its own name, exactly like a `Listener`.
    ///
    /// Not affine: a handle names something a scope owns, and neither `send` nor `latest` consumes
    /// it — `examples/reactors/server.norn` hands the same `gate` to a spawn and to a recursive
    /// call in consecutive lines.
    Reactor(ReactorId),
    /// One input of a running reactor, as a value `send` can be handed. The argument is the
    /// message type.
    ///
    /// Unspellable: `resolve_ty` never produces it, so no field, parameter, return, or payload can
    /// have this type, and the only way to obtain one is `reactor.input` at the point of use.
    Input(Box<Ty>),
    /// One exported signal of a running reactor, as a value `latest` can read. The argument is the
    /// *element* type — the type of the value the signal currently holds.
    ///
    /// Unspellable for the same reason, which is what makes "a signal cannot escape its reactor" a
    /// fact about the grammar rather than a check somebody has to write. `signal count: I64`
    /// annotates the element type; there is nowhere to write `Signal<I64>` at all.
    Signal(Box<Ty>),
    /// Registered, never produced. v0 has no `event` nodes and no way to read one — the read side
    /// still waits on subscriptions and `for await`. It exists so that writing `Event<T>` is
    /// answered with the milestone rather than "unknown type".
    Event(Box<Ty>),
    /// A declared type parameter, meaningful only inside the template that declares it. Equal to
    /// itself and to nothing else — the derived equality is what makes a bare `T` opaque: without
    /// a bound it can only be moved, stored, matched by binding, or passed on.
    Param {
        index: u32,
        name: String,
    },
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

    /// What this type is when the borrow is stripped. `&T` and `T` are the same values, so every
    /// question except "does using it move it" is asked of the pointee.
    pub fn owned(&self) -> &Ty {
        match self {
            Ty::Ref(inner) => inner,
            other => other,
        }
    }

    pub fn is_ref(&self) -> bool {
        matches!(self, Ty::Ref(_))
    }
}

pub struct Program {
    pub structs: Vec<StructDef>,
    pub enums: Vec<EnumDef>,
    pub fns: Vec<FnDef>,
    pub reactors: Vec<ReactorDef>,
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
            Ty::Bytes => "Bytes".into(),
            Ty::Struct(id) => self.structs[id.index()].name.clone(),
            Ty::Enum(id) => self.enums[id.index()].name.clone(),
            Ty::Option(inner) => format!("Option<{}>", self.ty_name(inner)),
            Ty::Result(ok, err) => {
                format!("Result<{}, {}>", self.ty_name(ok), self.ty_name(err))
            }
            Ty::Task(inner) => format!("Task<{}>", self.ty_name(inner)),
            Ty::Resource(resource) => resource.name().into(),
            Ty::Ref(inner) => format!("&{}", self.ty_name(inner)),
            Ty::Reactor(id) => self.reactors[id.index()].name.clone(),
            Ty::Input(inner) => format!("an input taking {}", self.ty_name(inner)),
            Ty::Signal(inner) => format!("a signal of {}", self.ty_name(inner)),
            Ty::Event(inner) => format!("an event of {}", self.ty_name(inner)),
            Ty::Param { name, .. } => name.clone(),
            Ty::Never => "!".into(),
            Ty::Error => "?".into(),
        }
    }

    /// Whether a value of this type is moved by being used, rather than copied.
    ///
    /// The affine set in v0 is deliberately small: operating-system resources, because a descriptor
    /// has exactly one closer; a built-but-unstarted `Task<T>`, because starting one twice would run
    /// its effects twice and because it may be carrying a resource; and any aggregate holding one of
    /// those, because a struct is no less an owner than a variable. Everything else is copied, which
    /// is what an interpreter that clones values already does and what keeps `print(p); print(p)`
    /// legal. Ordinary values become move-checked when M5 makes the copy cost something.
    ///
    /// A borrow is never affine: not owning it is the whole point.
    pub fn affine(&self, ty: &Ty) -> bool {
        self.affine_seen(ty, &mut Vec::new())
    }

    /// `visiting` guards against a struct that reaches itself — `struct Node { next: Option<Node> }`
    /// is writable, and asking whether it is affine would otherwise not terminate.
    fn affine_seen(&self, ty: &Ty, visiting: &mut Vec<Ty>) -> bool {
        if visiting.contains(ty) {
            return false;
        }
        match ty {
            Ty::Resource(_) | Ty::Task(_) => true,
            Ty::Ref(_) => false,
            Ty::Option(inner) => self.affine_seen(inner, visiting),
            Ty::Result(ok, err) => {
                self.affine_seen(ok, visiting) || self.affine_seen(err, visiting)
            }
            Ty::Struct(id) => {
                visiting.push(ty.clone());
                let found = self.structs[id.index()]
                    .fields
                    .iter()
                    .any(|field| self.affine_seen(&field.ty, visiting));
                visiting.pop();
                found
            }
            Ty::Enum(id) => {
                visiting.push(ty.clone());
                let found = self.enums[id.index()].variants.iter().any(|variant| {
                    variant
                        .fields
                        .iter()
                        .any(|field| self.affine_seen(&field.ty, visiting))
                });
                visiting.pop();
                found
            }
            _ => false,
        }
    }
}

/// What to do with a message that arrives at a full mailbox. There is no default: an unbounded
/// queue is the one thing the runtime must never create implicitly, and a default capacity would be
/// a number nobody chose.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Overflow {
    /// Drop the arriving message.
    Reject,
    /// Make room by dropping the oldest message still queued.
    DropOldest,
    /// Make room by dropping the newest message still queued.
    DropNewest,
    /// Suspend the sender until there is room.
    Wait,
}

impl Overflow {
    pub const ALL: &'static [Overflow] = &[
        Overflow::Reject,
        Overflow::DropOldest,
        Overflow::DropNewest,
        Overflow::Wait,
    ];

    pub fn from_name(name: &str) -> Option<Overflow> {
        match name {
            "reject" => Some(Overflow::Reject),
            "drop_oldest" => Some(Overflow::DropOldest),
            "drop_newest" => Some(Overflow::DropNewest),
            "wait" => Some(Overflow::Wait),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Overflow::Reject => "reject",
            Overflow::DropOldest => "drop_oldest",
            Overflow::DropNewest => "drop_newest",
            Overflow::Wait => "wait",
        }
    }
}

/// An owner of state and a static dependency graph over it.
///
/// After checking there are no expressions left here: every node body and every handler has been
/// lifted to an ordinary top-level function, and what remains is indices — dependency edges, slot
/// numbers, and the order to walk them in. That is the whole point of the milestone. The graph is a
/// compile-time artifact, and the runtime is a loop over it.
pub struct ReactorDef {
    pub name: String,
    /// Constructor parameters, in declaration order. Each is also a node, and a slot: a parameter
    /// is state that is written once and never again.
    pub params: Vec<(String, Ty)>,
    /// The capability set of the effects this reactor launches. Checked against its spawner's.
    pub uses: Vec<Capability>,
    pub inputs: Vec<InputDef>,
    pub nodes: Vec<Node>,
    /// Node indices holding a value that survives between turns, in **source order**.
    ///
    /// Source order and not topological order, deliberately: a slot index is the shape of the
    /// durable state projection `DESIGN.md` §14 asks for, and adding a derived signal must not
    /// renumber persisted state.
    pub slots: Vec<NodeId>,
    /// A topological order over the whole graph: every node appears after its dependencies. One
    /// pass over it *is* the fixed point, which is what acyclicity buys.
    pub order: Vec<NodeId>,
    /// Exported nodes, in source order. A published snapshot is exactly these values.
    pub exports: Vec<NodeId>,
    pub span: Span,
}

impl ReactorDef {
    pub fn node(&self, name: &str) -> Option<NodeId> {
        self.nodes
            .iter()
            .position(|node| node.name == name)
            .map(|index| NodeId(index as u32))
    }

    pub fn input(&self, name: &str) -> Option<usize> {
        self.inputs.iter().position(|input| input.name == name)
    }
}

pub struct InputDef {
    pub name: String,
    /// The message type. `()` means the occurrence itself is the message.
    pub ty: Ty,
    pub capacity: usize,
    pub overflow: Overflow,
    /// The lifted `on` handler: `(message, every slot in slot order) -> ()`, writing slots and
    /// requesting effects as it goes.
    pub handler: FnId,
    /// The subsequence of `order` this input can reach — its propagation plan. Everything else in
    /// the graph is provably unaffected by a message on this input, so a turn does not touch it.
    pub plan: Vec<NodeId>,
    pub span: Span,
}

pub struct Node {
    pub name: String,
    pub kind: NodeKind,
    /// The type of the value the node holds.
    pub ty: Ty,
    /// The nodes whose values this one is computed from, in the order the lifted function takes
    /// them as parameters.
    pub deps: Vec<NodeId>,
    pub exported: bool,
    pub span: Span,
}

pub enum NodeKind {
    /// A constructor parameter: a slot written once, when the reactor is created.
    Param { slot: usize, index: usize },
    /// A state cell: a slot, plus the pure function computing its initial value from the
    /// constructor parameters it mentions.
    ///
    /// State is where a feedback loop crosses a temporal boundary, which is why the cycle check is
    /// a property of signals alone.
    State { slot: usize, init: FnId },
    /// A pure derived view of its dependencies: `deps` in, one value out.
    Signal { body: FnId },
}

impl NodeKind {
    pub fn slot(&self) -> Option<usize> {
        match self {
            NodeKind::Param { slot, .. } | NodeKind::State { slot, .. } => Some(*slot),
            NodeKind::Signal { .. } => None,
        }
    }

    /// Whether the node's value is recomputed during propagation rather than committed by a
    /// handler.
    pub fn is_signal(&self) -> bool {
        matches!(self, NodeKind::Signal { .. })
    }
}

pub struct StructDef {
    pub name: String,
    /// Non-empty marks a template: a declaration the checker instantiates rather than a type a
    /// value can have. Instances are appended to the same table as ordinary monomorphic defs.
    pub type_params: Vec<String>,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

impl StructDef {
    pub fn field(&self, name: &str) -> Option<(usize, &FieldDef)> {
        self.fields.iter().enumerate().find(|(_, f)| f.name == name)
    }
}

#[derive(Clone)]
pub struct FieldDef {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
}

pub struct EnumDef {
    pub name: String,
    /// Non-empty marks a template, exactly as on `StructDef`.
    pub type_params: Vec<String>,
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

#[derive(Clone)]
pub struct VariantDef {
    pub name: String,
    /// A tuple payload is stored as fields named `0`, `1`, … so one representation serves both.
    pub fields: Vec<FieldDef>,
    pub positional: bool,
    pub span: Span,
}

pub struct FnDef {
    pub name: String,
    /// Non-empty marks a template, exactly as on `StructDef`: the body is checked once with the
    /// parameters opaque, and only instances of it are ever executed.
    pub type_params: Vec<String>,
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
    pub role: LocalRole,
    pub span: Span,
}

/// Where a local came from. Ordinary code only ever produces `Ordinary`; the rest exist because a
/// lifted node body or handler binds the reactor's members as parameters, and a diagnostic about
/// one should say what it actually is rather than "not declared `mut`".
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LocalRole {
    Ordinary,
    /// A reactor constructor parameter.
    Param,
    /// A state cell backed by this slot. Assigning to it inside a handler is a commit, which is
    /// what makes lowering emit `SetSlot` here and nowhere else.
    State(usize),
    /// Another node's current value, read-only.
    Signal,
    /// The message an `on` handler was invoked with.
    Message,
}

/// Which aggregate a constructor expression builds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ctor {
    Struct(StructId),
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
    /// Field access, resolved to an index into the struct's fields.
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
    /// `spawn reactor Gate(limit: 8)`. Creates the reactor, runs it to its first stable state,
    /// publishes version 0, and yields a handle.
    SpawnReactor {
        reactor: ReactorId,
        args: Vec<Expr>,
    },
    /// `gate.opened` — one input of a running reactor, as a value `send` can be handed.
    ReactorInput {
        reactor: Box<Expr>,
        index: usize,
    },
    /// `gate.snapshot` — one exported signal, as a value `latest` can read. An unexported signal is
    /// reactor-private and has no spelling from outside at all.
    ReactorExport {
        reactor: Box<Expr>,
        index: usize,
    },
    /// Postfix `?`. `ok_variant` distinguishes unwrapping a `Result` from an `Option`.
    Try {
        expr: Box<Expr>,
        enum_id: EnumId,
    },
    Return {
        value: Option<Box<Expr>>,
    },
    /// `while cond { … }`. The condition re-evaluates before every iteration; the whole expression
    /// is `()`.
    While {
        cond: Box<Expr>,
        body: Box<Expr>,
    },
    /// `loop { … }`. Typed by its `break value`s: their unified type, `()` if only bare breaks,
    /// `Never` if no break at all.
    Loop {
        body: Box<Expr>,
    },
    /// Leave the innermost loop. `value` is only ever `Some` inside a `loop`.
    Break {
        value: Option<Box<Expr>>,
    },
    /// Jump to the innermost loop's next iteration.
    Continue,
    /// Stands in for an expression that failed to check.
    Error,
}

// `UnOp`, `BinOp`, and `Builtin` are mirrored in `norn-codegen/src/prelude.rs`, variant names
// included: the interpreter's trap messages interpolate `{:?}` of them, and both engines must
// word a trap identically.
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
    Send,
    Latest,
    Bytes,
    BytesLen,
    BytesSlice,
    /// The trusting half of bytes→text: traps on invalid UTF-8 rather than returning `Option`.
    /// The checked half is `std/bytes`'s `to_string`, a validator written in Norn — this is the
    /// intrinsic it stands on, the first `_unchecked` name in the table.
    TextUnchecked,
    Byte,
    BytesConcat,
    /// `data[i]`. Carried by syntax alone: not in `ALL` and not in `from_name`, so `bytes_at`
    /// stays a name users may define, and the checker's desugar of an index expression is the
    /// only way to spell it.
    BytesAt,
    FileCreate,
    /// The write half of the file seam: `file_create` opens with authority, and these two drive
    /// the open handle — which is why neither needs a capability of its own.
    FileWrite,
    FileClose,
    FlowOfFile,
    /// One chunk of a flow, empty when the flow is exhausted. With `flow_len` and `flow_close`
    /// this is what lets a flow be consumed from Norn — `std/flow`'s `pipe` is the first taker.
    FlowNext,
    FlowLen,
    FlowClose,
}

impl Builtin {
    /// Every nameable builtin, for consumers that need the list rather than one entry — the editor
    /// grammar test is the first. It sits beside the exhaustive matches below so that adding a
    /// variant puts the compiler's finger next to the line that also needs the new name.
    /// `BytesAt` is absent on purpose: its only spelling is `data[i]`.
    pub const ALL: &'static [Builtin] = &[
        Builtin::Print,
        Builtin::ListenerPort,
        Builtin::Sleep,
        Builtin::TcpListen,
        Builtin::TcpAccept,
        Builtin::TcpRead,
        Builtin::TcpWrite,
        Builtin::TcpClose,
        Builtin::Send,
        Builtin::Latest,
        Builtin::Bytes,
        Builtin::BytesLen,
        Builtin::BytesSlice,
        Builtin::TextUnchecked,
        Builtin::Byte,
        Builtin::BytesConcat,
        Builtin::FileCreate,
        Builtin::FileWrite,
        Builtin::FileClose,
        Builtin::FlowOfFile,
        Builtin::FlowNext,
        Builtin::FlowLen,
        Builtin::FlowClose,
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
            "send" => Some(Builtin::Send),
            "latest" => Some(Builtin::Latest),
            "bytes" => Some(Builtin::Bytes),
            "bytes_len" => Some(Builtin::BytesLen),
            "bytes_slice" => Some(Builtin::BytesSlice),
            "text_unchecked" => Some(Builtin::TextUnchecked),
            "byte" => Some(Builtin::Byte),
            "bytes_concat" => Some(Builtin::BytesConcat),
            "file_create" => Some(Builtin::FileCreate),
            "file_write" => Some(Builtin::FileWrite),
            "file_close" => Some(Builtin::FileClose),
            "flow_of_file" => Some(Builtin::FlowOfFile),
            "flow_next" => Some(Builtin::FlowNext),
            "flow_len" => Some(Builtin::FlowLen),
            "flow_close" => Some(Builtin::FlowClose),
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
            Builtin::Send => "send",
            Builtin::Latest => "latest",
            Builtin::Bytes => "bytes",
            Builtin::BytesLen => "bytes_len",
            Builtin::BytesSlice => "bytes_slice",
            Builtin::TextUnchecked => "text_unchecked",
            Builtin::Byte => "byte",
            Builtin::BytesConcat => "bytes_concat",
            Builtin::BytesAt => "bytes_at",
            Builtin::FileCreate => "file_create",
            Builtin::FileWrite => "file_write",
            Builtin::FileClose => "file_close",
            Builtin::FlowOfFile => "flow_of_file",
            Builtin::FlowNext => "flow_next",
            Builtin::FlowLen => "flow_len",
            Builtin::FlowClose => "flow_close",
        }
    }

    /// Whether it may run inside a turn.
    ///
    /// A separate question from `capabilities`, and the plainest illustration of why: `print` needs
    /// no capability and is still something the world can see happen. Observing the graph part-way
    /// through propagation is exactly what a turn promises never to allow, so the criterion is
    /// "could anything outside tell that this ran", not "did it need authority".
    pub fn is_pure(self) -> bool {
        match self {
            Builtin::ListenerPort
            | Builtin::Bytes
            | Builtin::BytesLen
            | Builtin::BytesSlice
            | Builtin::TextUnchecked
            | Builtin::Byte
            | Builtin::BytesConcat
            | Builtin::BytesAt
            | Builtin::FlowLen => true,
            Builtin::Print
            | Builtin::Sleep
            | Builtin::TcpListen
            | Builtin::TcpAccept
            | Builtin::TcpRead
            | Builtin::TcpWrite
            | Builtin::TcpClose
            | Builtin::FileCreate
            | Builtin::FileWrite
            | Builtin::FileClose
            | Builtin::FlowOfFile
            | Builtin::FlowNext
            | Builtin::FlowClose
            | Builtin::Send
            | Builtin::Latest => false,
        }
    }

    /// Whether calling it builds a task rather than producing a value on the spot.
    pub fn is_task(self) -> bool {
        matches!(self.signature().1, Ty::Task(_))
    }

    pub fn capabilities(self) -> &'static [Capability] {
        match self {
            Builtin::Print
            | Builtin::ListenerPort
            | Builtin::Send
            | Builtin::Latest
            | Builtin::Bytes
            | Builtin::BytesLen
            | Builtin::BytesSlice
            | Builtin::TextUnchecked
            | Builtin::Byte
            | Builtin::BytesConcat
            | Builtin::BytesAt
            // The open handle is the authority: `file_create` and `flow_of_file` checked a
            // capability when they opened it, and driving or closing what is already open asks
            // for nothing more — the `pipe_to` precedent.
            | Builtin::FileWrite
            | Builtin::FileClose
            | Builtin::FlowNext
            | Builtin::FlowLen
            | Builtin::FlowClose => &[],
            Builtin::FileCreate => &[Capability::FsWrite],
            Builtin::FlowOfFile => &[Capability::FsRead],
            Builtin::Sleep => &[Capability::Clock],
            Builtin::TcpListen => &[Capability::NetListen],
            Builtin::TcpAccept | Builtin::TcpRead | Builtin::TcpWrite | Builtin::TcpClose => {
                &[Capability::NetIo]
            }
        }
    }

    /// Parameter types and result type. `print`, `send`, and `latest` are the builtins whose types
    /// depend on what they are handed, spelled here as `Ty::Error` — which every type fits — and
    /// checked properly at the call site rather than pretended to have a type they do not.
    ///
    /// The socket builtins are where borrowing earns its keep: reading and writing look at a
    /// descriptor, `tcp_close` takes it away, and the difference is spelled `&`. That is what makes
    /// closing a connection and then reading from it the same error as any other use after a move.
    pub fn signature(self) -> (Vec<Ty>, Ty) {
        let listener = || Ty::Resource(Resource::Listener);
        let connection = || Ty::Resource(Resource::Connection);
        let file = || Ty::Resource(Resource::File);
        let flow = || Ty::Resource(Resource::Flow);
        let borrowed = |ty: Ty| Ty::Ref(Box::new(ty));
        let io_error = || Ty::Enum(EnumId::IO_ERROR);
        let task = |ty: Ty| Ty::Task(Box::new(ty));
        let fallible = |ok: Ty| Ty::Result(Box::new(ok), Box::new(io_error()));
        match self {
            Builtin::Print => (vec![Ty::Error], Ty::Unit),
            Builtin::ListenerPort => (vec![borrowed(listener())], Ty::I64),
            Builtin::Sleep => (vec![Ty::I64], task(Ty::Unit)),
            Builtin::TcpListen => (vec![Ty::I64], task(fallible(listener()))),
            Builtin::TcpAccept => (vec![borrowed(listener())], task(fallible(connection()))),
            Builtin::TcpRead => (vec![borrowed(connection())], task(fallible(Ty::Bytes))),
            Builtin::TcpWrite => (
                vec![borrowed(connection()), Ty::Bytes],
                task(fallible(Ty::Unit)),
            ),
            Builtin::TcpClose => (vec![connection()], task(Ty::Unit)),
            Builtin::Send => (vec![Ty::Error, Ty::Error], task(Ty::Unit)),
            Builtin::Latest => (vec![Ty::Error], Ty::Error),
            Builtin::Bytes => (vec![Ty::Str], Ty::Bytes),
            Builtin::BytesLen => (vec![Ty::Bytes], Ty::I64),
            Builtin::BytesSlice => (vec![Ty::Bytes, Ty::I64, Ty::I64], Ty::Bytes),
            Builtin::TextUnchecked => (vec![Ty::Bytes], Ty::Str),
            Builtin::Byte => (vec![Ty::I64], Ty::Bytes),
            Builtin::BytesConcat => (vec![Ty::Bytes, Ty::Bytes], Ty::Bytes),
            Builtin::BytesAt => (vec![Ty::Bytes, Ty::I64], Ty::I64),
            Builtin::FileCreate => (vec![Ty::Str], task(fallible(file()))),
            Builtin::FileWrite => (vec![borrowed(file()), Ty::Bytes], task(fallible(Ty::Unit))),
            Builtin::FileClose => (vec![file()], task(Ty::Unit)),
            Builtin::FlowOfFile => (vec![Ty::Str], task(fallible(flow()))),
            // An empty chunk means the flow is exhausted — a mid-stream end of input is already
            // `UnexpectedEof` in the runtime, so empty is unambiguous.
            Builtin::FlowNext => (vec![borrowed(flow())], task(fallible(Ty::Bytes))),
            Builtin::FlowLen => (vec![borrowed(flow())], Ty::I64),
            Builtin::FlowClose => (vec![flow()], task(Ty::Unit)),
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
    Struct {
        strukt: StructId,
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
    Let {
        local: LocalId,
        value: Expr,
    },
    Assign {
        place: Expr,
        value: Expr,
    },
    /// `after deliver(m) -> delivered`. The operand is *built* here and started only after the
    /// snapshot is published — which is what M2's laziness was for. `returns` is the index of the
    /// input the effect's value comes back on, making a completion a later input.
    After {
        task: Expr,
        returns: Option<usize>,
    },
    Expr(Expr),
}
