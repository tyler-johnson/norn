//! Name resolution and type checking: AST in, typed HIR out.
//!
//! The checker is bidirectional. `check_expr` takes the type its position demands, when there is
//! one, and falls back to synthesising a type when there is not. That is what lets `None` and
//! `Err(e)` work without inference variables: the expectation supplies the argument the
//! expression cannot know on its own, and where no expectation exists the checker says so rather
//! than guessing.
//!
//! Construction is spelled like a call, so name resolution here is what tells `Point(x: 1)` the
//! struct from `point(x: 1)` the function: call position asks the builtins, then the `fn`s, then
//! the type namespace — never the locals, which is why a local sharing a struct's name is legal
//! and invisible to a call.
//!
//! Everything the grammar admits but v0 does not implement — tasks, `await`, methods, generic
//! arguments, first-class functions — is rejected here, by name, with the milestone that will
//! provide it.

use std::collections::HashMap;

use norn_syntax::ast;
use norn_syntax::{Diagnostic, Span};

use crate::hir::*;

mod call;
mod expr;
mod flow;
mod generics;
mod item;
mod moves;
mod ns;
mod reactor;
mod sink;
mod traits;
mod turns;
mod ty;

use generics::Generics;
use traits::{ImplDef, TraitDef, TraitId};

pub struct Checked {
    pub program: Program,
    pub errors: Vec<Diagnostic>,
}

impl Checked {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
}

/// One file handed to `check_modules`. `name` is what diagnostics print; `key` is the
/// lexically-normalized resolution identity import specifiers resolve to.
pub struct ModuleInput<'a> {
    pub name: String,
    pub key: String,
    pub module: &'a ast::Module,
}

/// The checked program, with diagnostics attributed per module — `errors` is parallel to the
/// inputs, because a `Span` carries no file identity and the caller has one `SourceFile` each.
pub struct CheckedModules {
    pub program: Program,
    pub errors: Vec<Vec<Diagnostic>>,
}

impl CheckedModules {
    pub fn ok(&self) -> bool {
        self.errors.iter().all(|errors| errors.is_empty())
    }
}

/// Check a program of one or more files. `inputs[0]` is the entry module: the one whose `main`
/// counts, and the one whose declarations keep their unprefixed display names.
pub fn check_modules(inputs: &[ModuleInput]) -> CheckedModules {
    let mut checker = Checker::new(inputs.len());
    checker.run(inputs);
    let Checker {
        program,
        mut errors,
        ..
    } = checker;
    // Report in source order rather than stage order, as the parser does: signatures are resolved
    // before any body is checked, and what that finds should not float to the top of the list.
    for errors in &mut errors {
        errors.sort_by_key(|diagnostic| diagnostic.span.start);
    }
    CheckedModules { program, errors }
}

/// Check a single module. A thin wrapper over `check_modules`, kept so a one-file program — and
/// every in-memory test — stays a one-line call.
pub fn check(module: &ast::Module) -> Checked {
    let inputs = [ModuleInput {
        name: String::new(),
        key: String::new(),
        module,
    }];
    let mut checked = check_modules(&inputs);
    Checked {
        program: checked.program,
        errors: checked
            .errors
            .pop()
            .expect("one module in, one error list out"),
    }
}

/// The four constructor names that stay bare: resolved by the expected type in expressions and
/// by the scrutinee in patterns. In exchange they are unbindable — no local, parameter, pattern
/// binding, `fn`, or reactor member may take one — which is what keeps `None =>` from quietly
/// becoming a catch-all binding.
fn is_builtin_variant(name: &str) -> bool {
    matches!(name, "None" | "Some" | "Ok" | "Err")
}

/// Why an import specifier could not be resolved to a module key.
pub enum SpecifierError {
    /// No leading `./` or `../`, and not `std/…`: the shape reserved for packages.
    Bare,
    /// The specifier wrote the `.norn`, which is implied.
    Extension,
}

/// Where a specifier resolved to. Provenance is carried rather than re-inferred from the key's
/// shape, because the shapes can coincide: a relative `./std/fs` from a root-level entry
/// legitimately yields the file key `std/fs.norn`. The keys themselves cannot collide — relative
/// resolution always appends `.norn`, and a std key never has it.
pub enum Resolved {
    /// A relative specifier: the key names a file, `.norn` appended.
    File(String),
    /// A `std/…` specifier: the key is the specifier verbatim, extensionless, resolved against
    /// the table in `crate::stdlib` rather than the filesystem.
    Std(String),
}

/// Resolve an import specifier against the key of the importing module: `std/…` is a
/// standard-library key, verbatim; anything else is dirname ⊕ specifier, with `.` and `..` folded
/// lexically and `.norn` appended.
///
/// Shared by the checker and the loader so the two cannot disagree about which module a specifier
/// names. Lexical means `./a/../fmt` and `./fmt` coincide; symlink aliasing is a documented v0 gap.
pub fn resolve_specifier(importer_key: &str, specifier: &str) -> Result<Resolved, SpecifierError> {
    // Ahead of the std branch on purpose: `"std/fmt.norn"` is the extension mistake, not a
    // standard-library module that does not exist.
    if specifier.ends_with(".norn") {
        return Err(SpecifierError::Extension);
    }
    if specifier.starts_with("std/") {
        return Ok(Resolved::Std(specifier.to_string()));
    }
    if !specifier.starts_with("./") && !specifier.starts_with("../") {
        return Err(SpecifierError::Bare);
    }
    let mut parts: Vec<&str> = match importer_key.rsplit_once('/') {
        Some((dir, _)) => dir.split('/').collect(),
        None => Vec::new(),
    };
    for segment in specifier.split('/') {
        match segment {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            segment => parts.push(segment),
        }
    }
    Ok(Resolved::File(format!("{}.norn", parts.join("/"))))
}

/// What kind of thing a file declares under a name, read straight off the AST — the exports view
/// an importing file resolves against, available before any checking has run.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DeclKind {
    Fn,
    Struct,
    Enum,
    Trait,
    Reactor,
}

impl DeclKind {
    fn describe(self) -> &'static str {
        match self {
            DeclKind::Fn => "function",
            DeclKind::Struct => "struct",
            DeclKind::Enum => "enum",
            DeclKind::Trait => "trait",
            DeclKind::Reactor => "reactor",
        }
    }
}

/// What `ns.name` resolved to, for the sites that consult a namespace binding.
#[derive(Clone, Copy)]
enum NsItem {
    Fn(FnId),
    Struct(StructId),
    Enum(EnumId),
    Reactor(ReactorId),
}

/// What a name at the head of a path refers to.
#[derive(Clone)]
enum TypeName {
    Struct(StructId),
    Enum(EnumId),
    Reactor(ReactorId),
    Builtin(Ty),
}

/// What kind of expression is being checked, and therefore what it is allowed to do.
///
/// This was a `bool` while the only question was "are we in a `task fn`". A turn adds a second,
/// stricter answer — a node body may not even build a task — and the `after` operand adds a
/// third that sits between them: it must build a task, and must still not run one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ctx {
    /// An ordinary `fn`.
    Plain,
    /// A `task fn`.
    Task,
    /// A signal body, a state initialiser, or an `on` handler.
    Turn,
    /// The operand of `after`: evaluated during the turn, started after it.
    Effect,
}

impl Ctx {
    /// Whether a task may be *built* here. Building is not running, which is the whole reason
    /// `after` can describe an effect without performing one.
    fn builds_tasks(self) -> bool {
        matches!(self, Ctx::Task | Ctx::Effect)
    }

    /// Whether execution may suspend here.
    fn suspends(self) -> bool {
        matches!(self, Ctx::Task)
    }

    /// Whether this runs inside a turn, and so may not be observable from outside it.
    fn in_turn(self) -> bool {
        matches!(self, Ctx::Turn | Ctx::Effect)
    }
}

/// What a reactor member is, for the sake of a diagnostic about reading it in the wrong place.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sort {
    Param,
    Input,
    State,
    Signal,
}

impl Sort {
    fn describe(self) -> &'static str {
        match self {
            Sort::Param => "parameter",
            Sort::Input => "input",
            Sort::State => "state",
            Sort::Signal => "signal",
        }
    }
}

/// One module's namespaces. Every name a file can mention resolves through its own `ModuleNs`;
/// what another file declared only enters through an import binding.
struct ModuleNs {
    types: HashMap<String, TypeName>,
    fns: HashMap<String, FnId>,
    reactors: HashMap<String, ReactorId>,
    /// Traits are their own namespace: a trait name appears in bounds and `impl` headers, never
    /// in type or value position, so it cannot collide with resolution anywhere else.
    traits: HashMap<String, TraitId>,
    /// `import * as fmt` bindings: local name → module index.
    namespaces: HashMap<String, usize>,
}

impl ModuleNs {
    fn new() -> ModuleNs {
        ModuleNs {
            types: HashMap::new(),
            fns: HashMap::new(),
            reactors: HashMap::new(),
            traits: HashMap::new(),
            namespaces: HashMap::new(),
        }
    }
}

struct Checker {
    program: Program,
    /// Diagnostics per module, indexed the way the inputs were. Attribution matters because a
    /// `Span` has no file identity: whoever renders these pairs each list with its own file.
    errors: Vec<Vec<Diagnostic>>,
    /// Per-module namespaces; `current` says whose file is being looked at.
    ns: Vec<ModuleNs>,
    current: usize,
    /// Which module declared each function and reactor, parallel to `program.fns` and
    /// `program.reactors` — how the global passes put a diagnostic in the right file's list.
    fn_owner: Vec<usize>,
    reactor_owner: Vec<usize>,
    /// Per module, the `FnId` each item declared — `None` where declaration was refused. Bodies
    /// are checked through this table rather than by looking the name back up, so a duplicate or a
    /// display-name prefix can never silently skip (or double-check) a body.
    fn_of_item: Vec<Vec<Option<FnId>>>,
    /// The module identities the inputs arrived with: display names for diagnostics, keys for
    /// specifier resolution, and the file stem each non-entry module prefixes display names with.
    names: Vec<String>,
    keys: Vec<String>,
    stems: Vec<String>,
    key_index: HashMap<String, usize>,
    /// Per module, what it declares: name → (kind, exported). First declaration wins, matching
    /// namespace insertion order.
    decls: Vec<HashMap<String, (DeclKind, bool)>>,
    /// Per module, per import declaration, the module its specifier resolved to.
    import_target: Vec<Vec<Option<usize>>>,
    /// Function imports that passed every check except having an id: bound after every module's
    /// `declare_fns` has run. (module, local name, target module, source name, item span).
    pending_fn_imports: Vec<(usize, String, usize, String, Span)>,
    /// Signatures, resolved before any body is checked so that functions may call one another
    /// regardless of declaration order.
    signatures: Vec<(Vec<(String, Ty)>, Ty)>,
    /// Each function's parameter modes, in lockstep with `signatures` — pushed at every site
    /// that appends one. Until `infer_sinks` runs these are the *written* modes: `sink T` is
    /// `Sink`, everything else `Read`; inference flips a `Read` to `Sink` where a concrete body
    /// consumes the parameter. `check_moves` reads the settled table and nothing downstream
    /// learns modes exist.
    param_modes: Vec<Vec<Mode>>,
    /// Which of `param_modes`' entries are declared rather than inferable, in the same lockstep.
    /// A written `sink` pins `Sink`; a trait's contract pins an impl method's whole row —
    /// bodiless declarations cannot be flipped by a body, so an impl that consumes a read-pinned
    /// parameter is an error at the impl, never a silent flip.
    mode_pinned: Vec<Vec<bool>>,
    locals: Vec<LocalDef>,
    scopes: Vec<Vec<(String, LocalId)>>,
    ret: Ty,
    /// The function being checked: its name for diagnostics, whether it is a `task fn`, and what it
    /// declared it uses. Capability checking happens where a task is *built*, because an awaiting
    /// function cannot see a `Task<T>`'s provenance.
    fn_name: String,
    ctx: Ctx,
    uses: Vec<Capability>,
    /// The member namespace of the reactor whose body is being checked, if any. Consulted only
    /// when a name fails to resolve, so that "you cannot read that here" beats "unknown name".
    members: HashMap<String, Sort>,
    /// The reactor being checked, and whether the member being checked is an `on` handler.
    /// `Ctx::Turn` covers node bodies and handlers alike; these two say which.
    reactor: Option<ReactorId>,
    in_handler: bool,
    /// Whether the expression being checked is an assignment target.
    assigning: bool,
    /// The loops enclosing the expression being checked, innermost last. `break` and `continue`
    /// target the last frame; a `loop`'s frame is also where its `break value`s agree on a type.
    loops: Vec<LoopCtx>,
    /// The generic-instantiation registry: which templates have been instantiated at which
    /// arguments, and the ids the instances were appended under.
    generics: Generics,
    /// The type parameters of the declaration being resolved or checked, in declaration order —
    /// what `resolve_ty` answers a bare `T` from. Set per item, cleared after.
    type_params_in_scope: Vec<String>,
    /// Every trait in the program, in declaration order; ids index this table. Traits are a
    /// checker-only fact: `hir::Program` never grows trait tables, because every method call is
    /// rewritten to a plain call before lowering sees it.
    traits: Vec<TraitDef>,
    /// Every impl in the program, in declaration order — the table method resolution scans.
    /// Methods are receiver-keyed rather than imported, so the scan is global on purpose.
    impls: Vec<ImplDef>,
    /// What `Self` names where the current signature or body sits: the reserved parameter slot
    /// inside a trait declaration, the receiver type inside an impl, nothing anywhere else.
    self_ty: Option<Ty>,
    /// Per function, per type parameter, the bounds it declared — parallel to `program.fns`,
    /// pushed in lockstep at every site that appends a function. Only declared functions carry
    /// any: instances were gated at instantiation, and nothing else can spell a bound.
    fn_bounds: Vec<Vec<Vec<TraitId>>>,
    /// The declared bounds of `type_params_in_scope`, parallel to it — what a bound on a `T`
    /// argument is satisfied *by* inside a template body: propagation by declaration, never
    /// search.
    bounds_in_scope: Vec<Vec<TraitId>>,
    /// The module that declared each struct and enum, parallel to the program tables — what the
    /// orphan rule consults. Seeded enums and instances of another module's template carry their
    /// owner's index; the seeded three have no module and carry `usize::MAX`.
    struct_owner: Vec<usize>,
    enum_owner: Vec<usize>,
}

/// One enclosing loop, as `break` and `continue` see it.
struct LoopCtx {
    /// `loop` rather than `while`. Only a `loop` may be left with a value.
    is_loop: bool,
    /// What a `loop` produces. Seeded from the expectation when there is one, settled by the first
    /// `break value` otherwise, and checked against every later one.
    result: Option<Ty>,
    /// Whether any `break` targeted this frame. A `loop` nothing leaves is `Never`, not `()`.
    saw_break: bool,
    /// The first `break value` site, for the diagnostic when a bare `break` disagrees with it.
    first_value: Option<Span>,
}
