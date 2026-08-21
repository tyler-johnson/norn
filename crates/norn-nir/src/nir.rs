//! The lowered IR.
//!
//! NIR is flat: each function is a list of basic blocks, each block a straight run of assignments
//! ending in one terminator. Nothing nests, nothing is implicit — `match` has become switches and
//! branches, `&&` has become control flow, `?` has become an early return.
//!
//! Flatness is the point. When tasks arrive in M2, a suspension point splits a block and the
//! function becomes a state machine over the same representation; when native code arrives in M5,
//! the backend walks these blocks and prints. Neither step should have to understand `match`.

use std::rc::Rc;

use norn_hir::hir::{BinOp, Builtin, EnumId, Mode, Overflow, Ty, UnOp};

pub type BlockId = usize;
pub type LocalId = usize;
pub type FnId = usize;

pub struct Program {
    pub structs: Vec<StructLayout>,
    pub enums: Vec<EnumLayout>,
    pub fns: Vec<Function>,
    pub reactors: Vec<Reactor>,
    pub main: Option<FnId>,
}

impl Program {
    /// The type of a projected place in `function`, walking the path one step at a time.
    pub fn ty_of_place(&self, function: &Function, place: &Place) -> Ty {
        let mut ty = function.tys[place.local].clone();
        for proj in &place.proj {
            ty = self.ty_of_proj(&ty, proj);
        }
        ty
    }

    /// One projection step. `Field` walks a struct's layout; `Downcast` walks into a variant's
    /// payload — a table lookup for a user enum, structural for `Option` and `Result`, whose
    /// instantiations never appear in the enum table.
    pub fn ty_of_proj(&self, ty: &Ty, proj: &Proj) -> Ty {
        match (ty, proj) {
            (Ty::Struct(id), Proj::Field(field)) => {
                self.structs[id.index()].fields[*field].ty.clone()
            }
            (Ty::Enum(id), Proj::Downcast { variant, field }) => {
                self.enums[id.index()].variants[*variant].fields[*field]
                    .ty
                    .clone()
            }
            (Ty::Option(inner), Proj::Downcast { variant, field: 0 })
                if *variant == EnumId::SOME =>
            {
                (**inner).clone()
            }
            (Ty::Result(ok, _), Proj::Downcast { variant, field: 0 }) if *variant == EnumId::OK => {
                (**ok).clone()
            }
            (Ty::Result(_, err), Proj::Downcast { variant, field: 0 })
                if *variant == EnumId::ERR =>
            {
                (**err).clone()
            }
            (Ty::Shared(inner), Proj::Deref) => (**inner).clone(),
            (ty, proj) => panic!("cannot project {proj:?} out of {ty:?}"),
        }
    }

    /// How the variant a `Downcast` names is spelled, given the type it downcasts.
    pub fn variant_name(&self, ty: &Ty, variant: usize) -> String {
        match ty {
            Ty::Enum(id) => self.enums[id.index()].variants[variant].name.clone(),
            Ty::Option(_) if variant == EnumId::SOME => "Some".into(),
            Ty::Option(_) => "None".into(),
            Ty::Result(..) if variant == EnumId::OK => "Ok".into(),
            Ty::Result(..) => "Err".into(),
            other => panic!("no variant {variant} on {other:?}"),
        }
    }
}

/// A reactor as the runtime consumes it: a table, not an evaluator.
///
/// Every body has been lifted to an ordinary function in `fns`, so what remains is indices — which
/// nodes feed which, where their values live, and what order to walk them in. That is the artifact
/// the milestone exists to produce, and `norn graph` prints exactly this.
pub struct Reactor {
    pub name: String,
    /// Constructor parameter types, in declaration order.
    pub params: Vec<Ty>,
    pub nodes: Vec<Node>,
    /// The node holding each slot, in slot (source) order.
    pub slots: Vec<usize>,
    pub inputs: Vec<Input>,
    pub order: Vec<usize>,
    pub exports: Vec<usize>,
}

pub struct Node {
    pub name: String,
    /// The type of the value the node holds.
    pub ty: Ty,
    pub deps: Vec<usize>,
    pub kind: NodeKind,
}

pub enum NodeKind {
    /// A constructor parameter: slot, and which argument fills it.
    Param { slot: usize, index: usize },
    /// A state cell: slot, and the function computing its initial value.
    State { slot: usize, init: FnId },
    /// A derived view: the function computing it from `deps`.
    Signal { body: FnId },
}

impl NodeKind {
    pub fn slot(&self) -> Option<usize> {
        match self {
            NodeKind::Param { slot, .. } | NodeKind::State { slot, .. } => Some(*slot),
            NodeKind::Signal { .. } => None,
        }
    }
}

pub struct Input {
    pub name: String,
    /// The message type. `()` means the occurrence itself is the message.
    pub ty: Ty,
    pub capacity: usize,
    pub overflow: Overflow,
    /// `(message, every slot in slot order) -> ()`, writing slots and requesting effects as it goes.
    pub handler: FnId,
    pub plan: Vec<usize>,
}

/// Names are kept so that a value can be rendered in the surface syntax that built it.
pub struct StructLayout {
    pub name: String,
    pub fields: Vec<FieldLayout>,
}

pub struct EnumLayout {
    pub name: String,
    pub variants: Vec<VariantLayout>,
}

pub struct VariantLayout {
    pub name: String,
    pub fields: Vec<FieldLayout>,
    /// Whether the payload was declared positionally, which decides how it is printed.
    pub positional: bool,
}

pub struct FieldLayout {
    pub name: String,
    pub ty: Ty,
}

/// Whether calling this function runs it or builds a task. The distinction is all that separates
/// the two in NIR: a task's body is ordinary blocks, and the suspension points in it are terminators
/// like any other.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FnKind {
    Plain,
    Task,
}

pub struct Function {
    pub name: String,
    pub kind: FnKind,
    pub params: usize,
    /// The mode of each parameter, in lockstep with `locals[..params]` — the checker's settled
    /// column, copied so both engines can pair a `Mut` argument's place with the writeback the
    /// call's return performs. `Read` and `Sink` change nothing at run time.
    pub modes: Vec<Mode>,
    pub locals: Vec<String>,
    /// The type of each local, in lockstep with `locals` — temporaries append to both.
    pub tys: Vec<Ty>,
    pub ret: Ty,
    /// A neutered generic template, symbolic instance, or trait-call stub. Its signature may
    /// still carry `Ty::Param` against a `()` body; nothing executable references it, and it
    /// survives only because ids are positional. Typed consumers must skip it, not type it.
    pub inert: bool,
    pub blocks: Vec<Block>,
}

#[derive(Default)]
pub struct Block {
    pub instrs: Vec<Instr>,
    pub term: Term,
}

pub enum Instr {
    Assign(Place, Rvalue),
    /// Open a scope. Everything spawned until the matching `Term::ScopeExit` belongs to it.
    ScopeEnter,
    /// Start a task in the innermost open scope. The operand is a `Task<()>`.
    Spawn(Operand),
    /// Create a reactor and bind a handle to it.
    SpawnReactor {
        dest: Place,
        reactor: usize,
        args: Vec<Operand>,
    },
    /// Commit a state cell. Emitted only in a handler, and in place: the value the turn commits is
    /// wherever the handler left it.
    SetSlot(usize, Operand),
    /// Request an effect. Emitted only in a handler, and in place, so that an `after` in a
    /// branch that was not taken does not fire. The operand is a task that has been built and not
    /// started; the runtime starts it once the snapshot is published.
    Emit {
        task: Operand,
        returns: Option<usize>,
    },
}

/// One step of a projection path.
///
/// `Field` indexes a struct's payload. `Downcast` indexes an enum variant's payload, and carries
/// the variant because field 0 of an enum has a different type per variant — the surrounding
/// control flow (a `SwitchTag`, a `?`) has always proved which variant the value is at every
/// site that projects into one, so lowering records it (MIR's `PlaceElem::Downcast`, for the
/// same reason). Downcasts appear on read paths only: an assignment left-hand side is
/// checker-restricted to struct-field chains.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Proj {
    Field(usize),
    Downcast {
        variant: usize,
        field: usize,
    },
    /// Reads through a `Shared`. Read paths only, like `Downcast`: an assignment left-hand side
    /// is checker-restricted to struct-field chains, and a shared value is immutable.
    Deref,
}

impl Proj {
    /// The payload index, however the step is typed. Consumers whose values store fields as one
    /// flat vec regardless of variant — the interpreter — index by this alone; they match a
    /// `Deref` step before asking.
    pub fn index(&self) -> usize {
        match self {
            Proj::Field(index) | Proj::Downcast { field: index, .. } => *index,
            Proj::Deref => panic!("a deref has no payload index"),
        }
    }
}

/// A local, optionally projected into: `x`, `x.2`, `x.0.1`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Place {
    pub local: LocalId,
    pub proj: Vec<Proj>,
}

impl Place {
    pub fn local(local: LocalId) -> Place {
        Place {
            local,
            proj: Vec::new(),
        }
    }

    pub fn field(&self, index: usize) -> Place {
        let mut proj = self.proj.clone();
        proj.push(Proj::Field(index));
        Place {
            local: self.local,
            proj,
        }
    }

    pub fn downcast(&self, variant: usize, field: usize) -> Place {
        let mut proj = self.proj.clone();
        proj.push(Proj::Downcast { variant, field });
        Place {
            local: self.local,
            proj,
        }
    }

    pub fn deref(&self) -> Place {
        let mut proj = self.proj.clone();
        proj.push(Proj::Deref);
        Place {
            local: self.local,
            proj,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Operand {
    Const(Const),
    Copy(Place),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Const {
    Unit,
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Rc<str>),
}

pub enum Rvalue {
    Use(Operand),
    Unary(UnOp, Operand),
    Binary(BinOp, Operand, Operand),
    Call(FnId, Vec<Operand>),
    Builtin(Builtin, Vec<Operand>),
    /// Build a task from a `task fn` and its arguments. Nothing runs: the arguments are evaluated
    /// now, and the body only when something awaits or spawns it.
    Task(FnId, Vec<Operand>),
    BuiltinTask(Builtin, Vec<Operand>),
    Struct(usize, Vec<Operand>),
    Variant(usize, usize, Vec<Operand>),
    /// `gate.opened` — one input of a running reactor, as a value `send` can be handed.
    ReactorInput(Operand, usize),
    /// `gate.snapshot` — one exported signal, as a value `latest` can read.
    ReactorExport(Operand, usize),
}

pub enum Term {
    Goto(BlockId),
    Branch {
        cond: Operand,
        then: BlockId,
        els: BlockId,
    },
    /// Dispatch on the variant tag of an enum value.
    SwitchTag {
        scrutinee: Place,
        cases: Vec<(usize, BlockId)>,
        default: BlockId,
    },
    Return(Operand),
    /// Run a task and resume with its value.
    ///
    /// A suspension point is a terminator, which is the load-bearing decision of M2: block ids
    /// therefore *are* the state numbers, and the state machine `BOOTSTRAP.md` §1 promised is
    /// explicit here rather than discovered by the backend. M5 emits `loop { match frame.state { … } }`
    /// straight from the block list.
    Await {
        task: Operand,
        dest: Place,
        resume: BlockId,
    },
    /// Leave the innermost open scope: cancel and join its children, then resume.
    ScopeExit {
        resume: BlockId,
    },
    /// A state the checker could not rule out and the program must not reach.
    Trap(&'static str),
}

impl Default for Term {
    fn default() -> Term {
        Term::Trap("block was never terminated")
    }
}

impl Term {
    /// Every block this one can transfer control to. Passes that walk the block graph ask here
    /// rather than matching, so a new terminator joins them by answering this.
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Term::Goto(target) => vec![*target],
            Term::Branch { then, els, .. } => vec![*then, *els],
            Term::SwitchTag { cases, default, .. } => cases
                .iter()
                .map(|(_, block)| *block)
                .chain([*default])
                .collect(),
            Term::Await { resume, .. } | Term::ScopeExit { resume } => vec![*resume],
            Term::Return(_) | Term::Trap(_) => Vec::new(),
        }
    }

    /// Rewrite the block ids this terminator names, given a map from old id to new.
    pub fn retarget(&mut self, map: &[BlockId]) {
        match self {
            Term::Goto(target) => *target = map[*target],
            Term::Branch { then, els, .. } => {
                *then = map[*then];
                *els = map[*els];
            }
            Term::SwitchTag { cases, default, .. } => {
                for (_, block) in cases.iter_mut() {
                    *block = map[*block];
                }
                *default = map[*default];
            }
            Term::Await { resume, .. } | Term::ScopeExit { resume } => *resume = map[*resume],
            Term::Return(_) | Term::Trap(_) => {}
        }
    }
}

/// Render a program in the textual form `norn nir` prints. This is a debugging surface and the
/// artifact M5 will diff the native backend against, so it is deliberately explicit.
pub fn print(program: &Program) -> String {
    let mut out = String::new();
    for (id, strukt) in program.structs.iter().enumerate() {
        let fields: Vec<String> = strukt
            .fields
            .iter()
            .map(|f| format!("{}: {}", f.name, print_ty(program, &f.ty)))
            .collect();
        out.push_str(&format!(
            "struct {} #{id} ({})\n",
            strukt.name,
            fields.join(", ")
        ));
    }
    for (id, def) in program.enums.iter().enumerate() {
        let variants: Vec<String> = def
            .variants
            .iter()
            .map(|v| {
                if v.fields.is_empty() {
                    return v.name.clone();
                }
                let fields: Vec<String> = v
                    .fields
                    .iter()
                    .map(|f| {
                        if v.positional {
                            print_ty(program, &f.ty)
                        } else {
                            format!("{}: {}", f.name, print_ty(program, &f.ty))
                        }
                    })
                    .collect();
                format!("{}({})", v.name, fields.join(", "))
            })
            .collect();
        out.push_str(&format!(
            "enum {} #{id} ({})\n",
            def.name,
            variants.join(", ")
        ));
    }
    if !program.structs.is_empty() || !program.enums.is_empty() {
        out.push('\n');
    }
    out.push_str(&print_reactors(program));

    for (id, function) in program.fns.iter().enumerate() {
        let params: Vec<String> = (0..function.params)
            .map(|i| {
                format!(
                    "{}: {}",
                    local_name(function, i),
                    local_ty(program, function, i)
                )
            })
            .collect();
        let inert = if function.inert { "inert " } else { "" };
        let task = match function.kind {
            FnKind::Plain => "",
            FnKind::Task => "task ",
        };
        out.push_str(&format!(
            "{inert}{task}fn {} #{id}({}) -> {}\n",
            function.name,
            params.join(", "),
            print_ty(program, &function.ret)
        ));
        for index in function.params..function.locals.len() {
            out.push_str(&format!(
                "    local {}: {}\n",
                local_name(function, index),
                local_ty(program, function, index)
            ));
        }
        for (index, block) in function.blocks.iter().enumerate() {
            out.push_str(&format!("  b{index}:\n"));
            for instr in &block.instrs {
                let text = match instr {
                    Instr::Assign(place, rvalue) => format!(
                        "{} = {}",
                        print_place(program, function, place),
                        print_rvalue(program, function, rvalue)
                    ),
                    Instr::ScopeEnter => "scope enter".into(),
                    Instr::Spawn(operand) => {
                        format!("spawn {}", print_operand(program, function, operand))
                    }
                    Instr::SpawnReactor {
                        dest,
                        reactor,
                        args,
                    } => {
                        let args: Vec<String> = args
                            .iter()
                            .map(|a| print_operand(program, function, a))
                            .collect();
                        format!(
                            "{} = spawn reactor {}#{reactor}({})",
                            print_place(program, function, dest),
                            program.reactors[*reactor].name,
                            args.join(", ")
                        )
                    }
                    Instr::SetSlot(slot, operand) => {
                        format!(
                            "set slot {slot} = {}",
                            print_operand(program, function, operand)
                        )
                    }
                    Instr::Emit { task, returns } => match returns {
                        Some(input) => {
                            format!(
                                "emit {} -> input {input}",
                                print_operand(program, function, task)
                            )
                        }
                        None => format!("emit {}", print_operand(program, function, task)),
                    },
                };
                out.push_str(&format!("    {text}\n"));
            }
            out.push_str(&format!(
                "    {}\n",
                print_term(program, function, &block.term)
            ));
        }
        out.push('\n');
    }
    out
}

fn local_name(function: &Function, index: usize) -> String {
    match function.locals.get(index) {
        Some(name) if !name.is_empty() => format!("_{index}/{name}"),
        _ => format!("_{index}"),
    }
}

fn local_ty(program: &Program, function: &Function, index: usize) -> String {
    // A trait-call stub declares `params > 0` over an empty locals vec, so a parameter can have
    // no entry to name — the header still prints, with the type unknown.
    match function.tys.get(index) {
        Some(ty) => print_ty(program, ty),
        None => "?".into(),
    }
}

/// How a type is spelled in printed NIR. Aggregates spell by their table name — an instance's
/// name carries its arguments, `List<I64>` — and the unspellable reactor types get the bracketed
/// spellings `Input<T>`/`Signal<T>` rather than HIR's diagnostic prose.
pub fn print_ty(program: &Program, ty: &Ty) -> String {
    match ty {
        Ty::Unit => "()".into(),
        Ty::I64 => "I64".into(),
        Ty::F64 => "F64".into(),
        Ty::Bool => "Bool".into(),
        Ty::Str => "String".into(),
        Ty::Bytes => "Bytes".into(),
        Ty::Struct(id) => program.structs[id.index()].name.clone(),
        Ty::Enum(id) => program.enums[id.index()].name.clone(),
        Ty::Option(inner) => format!("Option<{}>", print_ty(program, inner)),
        Ty::Result(ok, err) => format!(
            "Result<{}, {}>",
            print_ty(program, ok),
            print_ty(program, err)
        ),
        Ty::Task(inner) => format!("Task<{}>", print_ty(program, inner)),
        Ty::Shared(inner) => format!("Shared<{}>", print_ty(program, inner)),
        Ty::Slots(inner) => format!("Slots<{}>", print_ty(program, inner)),
        Ty::Resource(resource) => resource.name().into(),
        Ty::Reactor(id) => program.reactors[id.index()].name.clone(),
        Ty::Input(inner) => format!("Input<{}>", print_ty(program, inner)),
        Ty::Signal(inner) => format!("Signal<{}>", print_ty(program, inner)),
        Ty::Event(inner) => format!("Event<{}>", print_ty(program, inner)),
        Ty::Param { name, .. } => name.clone(),
        Ty::Never => "!".into(),
        Ty::Error => "?".into(),
    }
}

fn print_place(program: &Program, function: &Function, place: &Place) -> String {
    let mut out = local_name(function, place.local);
    let mut ty = function.tys[place.local].clone();
    for proj in &place.proj {
        match proj {
            Proj::Field(index) => out.push_str(&format!(".{index}")),
            // A downcast spells the variant it committed to: `_3.0@Some`.
            Proj::Downcast { variant, field } => {
                out.push_str(&format!(".{field}@{}", program.variant_name(&ty, *variant)))
            }
            // A read through a `Shared`: `_3.*.0`.
            Proj::Deref => out.push_str(".*"),
        }
        ty = program.ty_of_proj(&ty, proj);
    }
    out
}

fn print_operand(program: &Program, function: &Function, operand: &Operand) -> String {
    match operand {
        Operand::Const(c) => print_const(c),
        Operand::Copy(place) => print_place(program, function, place),
    }
}

fn print_const(value: &Const) -> String {
    match value {
        Const::Unit => "()".into(),
        Const::Int(v) => v.to_string(),
        Const::Float(v) => format!("{v:?}"),
        Const::Bool(v) => v.to_string(),
        Const::Str(v) => format!("{:?}", &**v),
    }
}

fn print_rvalue(program: &Program, function: &Function, rvalue: &Rvalue) -> String {
    let args = |operands: &[Operand]| {
        operands
            .iter()
            .map(|o| print_operand(program, function, o))
            .collect::<Vec<_>>()
            .join(", ")
    };
    match rvalue {
        Rvalue::Use(operand) => print_operand(program, function, operand),
        Rvalue::Unary(op, operand) => {
            format!(
                "{} {}",
                unary_name(*op),
                print_operand(program, function, operand)
            )
        }
        Rvalue::Binary(op, lhs, rhs) => format!(
            "{} {} {}",
            print_operand(program, function, lhs),
            binary_name(*op),
            print_operand(program, function, rhs)
        ),
        // A `Mut` position prints its operand behind `mut`: the writeback pair is derived, and
        // the text should show where the call writes.
        Rvalue::Call(id, operands) => {
            let callee = &program.fns[*id];
            let printed = operands
                .iter()
                .enumerate()
                .map(|(index, o)| {
                    let arg = print_operand(program, function, o);
                    match callee.modes.get(index) {
                        Some(Mode::Mut) => format!("mut {arg}"),
                        _ => arg,
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("call {}#{id}({printed})", callee.name)
        }
        Rvalue::Builtin(builtin, operands) => {
            format!("builtin {}({})", builtin.name(), args(operands))
        }
        Rvalue::Task(id, operands) => {
            format!("task {}#{id}({})", program.fns[*id].name, args(operands))
        }
        Rvalue::BuiltinTask(builtin, operands) => {
            format!("task builtin {}({})", builtin.name(), args(operands))
        }
        Rvalue::Struct(id, operands) => {
            format!("{}({})", program.structs[*id].name, args(operands))
        }
        Rvalue::Variant(enum_id, variant, operands) => {
            let def = &program.enums[*enum_id];
            format!(
                "{}.{}({})",
                def.name,
                def.variants[*variant].name,
                args(operands)
            )
        }
        Rvalue::ReactorInput(operand, index) => {
            format!(
                "input {index} of {}",
                print_operand(program, function, operand)
            )
        }
        Rvalue::ReactorExport(operand, index) => {
            format!(
                "export {index} of {}",
                print_operand(program, function, operand)
            )
        }
    }
}

/// The reactor stanza: the dependency graph, the slot map, the topological order, and each input's
/// propagation plan.
///
/// These lines are the compile-time artifact the milestone exists to produce, so they are printed
/// rather than left to be reconstructed from the function table. `norn graph` prints them alone.
pub fn print_reactors(program: &Program) -> String {
    print_graph(program, None)
}

/// The same stanza, optionally narrowed to one reactor. `norn graph <file> [Name]` prints this.
pub fn print_graph(program: &Program, wanted: Option<&str>) -> String {
    let mut out = String::new();
    for (id, reactor) in program.reactors.iter().enumerate() {
        if wanted.is_some_and(|wanted| wanted != reactor.name) {
            continue;
        }
        let params: Vec<String> = reactor
            .params
            .iter()
            .map(|ty| print_ty(program, ty))
            .collect();
        out.push_str(&format!(
            "reactor {} #{id}({})\n",
            reactor.name,
            params.join(", ")
        ));
        for (index, node) in reactor.nodes.iter().enumerate() {
            let kind = match &node.kind {
                NodeKind::Param { slot, index } => format!("param slot {slot} arg {index}"),
                NodeKind::State { slot, init } => {
                    format!("state slot {slot} init {}#{init}", program.fns[*init].name)
                }
                NodeKind::Signal { body } => {
                    format!("signal {}#{body}", program.fns[*body].name)
                }
            };
            let deps: Vec<String> = node
                .deps
                .iter()
                .map(|dep| reactor.nodes[*dep].name.clone())
                .collect();
            let exported = if reactor.exports.contains(&index) {
                " export"
            } else {
                ""
            };
            out.push_str(&format!(
                "    node {index} {}: {} {kind}{exported} <- [{}]\n",
                node.name,
                print_ty(program, &node.ty),
                deps.join(", ")
            ));
        }
        out.push_str(&format!("    order [{}]\n", names(reactor, &reactor.order)));
        for (index, input) in reactor.inputs.iter().enumerate() {
            out.push_str(&format!(
                "    input {index} {}: {} capacity {} overflow {} handler {}#{}\n",
                input.name,
                print_ty(program, &input.ty),
                input.capacity,
                input.overflow.name(),
                program.fns[input.handler].name,
                input.handler
            ));
            out.push_str(&format!("        plan [{}]\n", names(reactor, &input.plan)));
        }
        out.push_str(&format!(
            "    exports [{}]\n",
            names(reactor, &reactor.exports)
        ));
        out.push('\n');
    }
    out
}

fn names(reactor: &Reactor, nodes: &[usize]) -> String {
    nodes
        .iter()
        .map(|node| reactor.nodes[*node].name.clone())
        .collect::<Vec<_>>()
        .join(", ")
}

fn print_term(program: &Program, function: &Function, term: &Term) -> String {
    match term {
        Term::Goto(target) => format!("goto b{target}"),
        Term::Branch { cond, then, els } => {
            format!(
                "branch {} ? b{then} : b{els}",
                print_operand(program, function, cond)
            )
        }
        Term::SwitchTag {
            scrutinee,
            cases,
            default,
        } => {
            let cases: Vec<String> = cases
                .iter()
                .map(|(tag, block)| format!("{tag} => b{block}"))
                .collect();
            format!(
                "switch tag {} [{}] else b{default}",
                print_place(program, function, scrutinee),
                cases.join(", ")
            )
        }
        Term::Return(operand) => format!("return {}", print_operand(program, function, operand)),
        Term::Await { task, dest, resume } => format!(
            "await {} -> {}, resume b{resume}",
            print_operand(program, function, task),
            print_place(program, function, dest)
        ),
        Term::ScopeExit { resume } => format!("scope exit, resume b{resume}"),
        Term::Trap(message) => format!("trap {message:?}"),
    }
}

fn unary_name(op: UnOp) -> &'static str {
    match op {
        UnOp::Neg => "neg",
        UnOp::Not => "not",
    }
}

fn binary_name(op: BinOp) -> &'static str {
    match op {
        BinOp::AddInt => "add.i",
        BinOp::SubInt => "sub.i",
        BinOp::MulInt => "mul.i",
        BinOp::DivInt => "div.i",
        BinOp::RemInt => "rem.i",
        BinOp::AddFloat => "add.f",
        BinOp::SubFloat => "sub.f",
        BinOp::MulFloat => "mul.f",
        BinOp::DivFloat => "div.f",
        BinOp::RemFloat => "rem.f",
        BinOp::Concat => "concat",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
    }
}
