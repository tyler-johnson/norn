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

use norn_hir::hir::{BinOp, Builtin, Overflow, UnOp};

pub type BlockId = usize;
pub type LocalId = usize;
pub type FnId = usize;

pub struct Program {
    pub records: Vec<RecordLayout>,
    pub enums: Vec<EnumLayout>,
    pub fns: Vec<Function>,
    pub reactors: Vec<Reactor>,
    pub main: Option<FnId>,
}

/// A reactor as the runtime consumes it: a table, not an evaluator.
///
/// Every body has been lifted to an ordinary function in `fns`, so what remains is indices — which
/// nodes feed which, where their values live, and what order to walk them in. That is the artifact
/// the milestone exists to produce, and `norn graph` prints exactly this.
pub struct Reactor {
    pub name: String,
    pub nodes: Vec<Node>,
    /// The node holding each slot, in slot (source) order.
    pub slots: Vec<usize>,
    pub inputs: Vec<Input>,
    pub order: Vec<usize>,
    pub exports: Vec<usize>,
}

pub struct Node {
    pub name: String,
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
    pub capacity: usize,
    pub overflow: Overflow,
    /// `(message, every slot in slot order) -> ()`, writing slots and requesting effects as it goes.
    pub handler: FnId,
    pub plan: Vec<usize>,
}

/// Names are kept so that a value can be rendered in the surface syntax that built it.
pub struct RecordLayout {
    pub name: String,
    pub fields: Vec<String>,
}

pub struct EnumLayout {
    pub name: String,
    pub variants: Vec<VariantLayout>,
}

pub struct VariantLayout {
    pub name: String,
    pub fields: Vec<String>,
    /// Whether the payload was declared positionally, which decides how it is printed.
    pub positional: bool,
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
    pub locals: Vec<String>,
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

/// A local, optionally projected into: `x`, `x.2`, `x.0.1`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Place {
    pub local: LocalId,
    pub proj: Vec<usize>,
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
        proj.push(index);
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
    Record(usize, Vec<Operand>),
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
    for (id, record) in program.records.iter().enumerate() {
        out.push_str(&format!(
            "record {} #{id} ({})\n",
            record.name,
            record.fields.join(", ")
        ));
    }
    for (id, def) in program.enums.iter().enumerate() {
        let variants: Vec<String> = def
            .variants
            .iter()
            .map(|v| format!("{}/{}", v.name, v.fields.len()))
            .collect();
        out.push_str(&format!(
            "enum {} #{id} ({})\n",
            def.name,
            variants.join(", ")
        ));
    }
    if !program.records.is_empty() || !program.enums.is_empty() {
        out.push('\n');
    }
    out.push_str(&print_reactors(program));

    for (id, function) in program.fns.iter().enumerate() {
        let params: Vec<String> = (0..function.params)
            .map(|i| local_name(function, i))
            .collect();
        let task = match function.kind {
            FnKind::Plain => "",
            FnKind::Task => "task ",
        };
        out.push_str(&format!(
            "{task}fn {} #{id}({})\n",
            function.name,
            params.join(", ")
        ));
        for index in function.params..function.locals.len() {
            out.push_str(&format!("    local {}\n", local_name(function, index)));
        }
        for (index, block) in function.blocks.iter().enumerate() {
            out.push_str(&format!("  b{index}:\n"));
            for instr in &block.instrs {
                let text = match instr {
                    Instr::Assign(place, rvalue) => format!(
                        "{} = {}",
                        print_place(function, place),
                        print_rvalue(program, function, rvalue)
                    ),
                    Instr::ScopeEnter => "scope enter".into(),
                    Instr::Spawn(operand) => {
                        format!("spawn {}", print_operand(function, operand))
                    }
                    Instr::SpawnReactor {
                        dest,
                        reactor,
                        args,
                    } => {
                        let args: Vec<String> =
                            args.iter().map(|a| print_operand(function, a)).collect();
                        format!(
                            "{} = spawn reactor {}#{reactor}({})",
                            print_place(function, dest),
                            program.reactors[*reactor].name,
                            args.join(", ")
                        )
                    }
                    Instr::SetSlot(slot, operand) => {
                        format!("set slot {slot} = {}", print_operand(function, operand))
                    }
                    Instr::Emit { task, returns } => match returns {
                        Some(input) => {
                            format!("emit {} -> input {input}", print_operand(function, task))
                        }
                        None => format!("emit {}", print_operand(function, task)),
                    },
                };
                out.push_str(&format!("    {text}\n"));
            }
            out.push_str(&format!("    {}\n", print_term(function, &block.term)));
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

fn print_place(function: &Function, place: &Place) -> String {
    let mut out = local_name(function, place.local);
    for index in &place.proj {
        out.push_str(&format!(".{index}"));
    }
    out
}

fn print_operand(function: &Function, operand: &Operand) -> String {
    match operand {
        Operand::Const(c) => print_const(c),
        Operand::Copy(place) => print_place(function, place),
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
            .map(|o| print_operand(function, o))
            .collect::<Vec<_>>()
            .join(", ")
    };
    match rvalue {
        Rvalue::Use(operand) => print_operand(function, operand),
        Rvalue::Unary(op, operand) => {
            format!("{} {}", unary_name(*op), print_operand(function, operand))
        }
        Rvalue::Binary(op, lhs, rhs) => format!(
            "{} {} {}",
            print_operand(function, lhs),
            binary_name(*op),
            print_operand(function, rhs)
        ),
        Rvalue::Call(id, operands) => {
            format!("call {}#{id}({})", program.fns[*id].name, args(operands))
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
        Rvalue::Record(id, operands) => {
            format!("{}({})", program.records[*id].name, args(operands))
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
            format!("input {index} of {}", print_operand(function, operand))
        }
        Rvalue::ReactorExport(operand, index) => {
            format!("export {index} of {}", print_operand(function, operand))
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
        out.push_str(&format!("reactor {} #{id}\n", reactor.name));
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
                "    node {index} {} {kind}{exported} <- [{}]\n",
                node.name,
                deps.join(", ")
            ));
        }
        out.push_str(&format!("    order [{}]\n", names(reactor, &reactor.order)));
        for (index, input) in reactor.inputs.iter().enumerate() {
            out.push_str(&format!(
                "    input {index} {} capacity {} overflow {} handler {}#{}\n",
                input.name,
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

fn print_term(function: &Function, term: &Term) -> String {
    match term {
        Term::Goto(target) => format!("goto b{target}"),
        Term::Branch { cond, then, els } => {
            format!(
                "branch {} ? b{then} : b{els}",
                print_operand(function, cond)
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
                print_place(function, scrutinee),
                cases.join(", ")
            )
        }
        Term::Return(operand) => format!("return {}", print_operand(function, operand)),
        Term::Await { task, dest, resume } => format!(
            "await {} -> {}, resume b{resume}",
            print_operand(function, task),
            print_place(function, dest)
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
