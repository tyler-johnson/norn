//! Name resolution and type checking: AST in, typed HIR out.
//!
//! The checker is bidirectional. `check_expr` takes the type its position demands, when there is
//! one, and falls back to synthesising a type when there is not. That is what lets `#None` and
//! `#Err(e)` work without inference variables: the expectation supplies the argument the
//! expression cannot know on its own, and where no expectation exists the checker says so rather
//! than guessing.
//!
//! Everything the grammar admits but v0 does not implement — tasks, `await`, methods, generic
//! arguments, first-class functions — is rejected here, by name, with the milestone that will
//! provide it.

use std::collections::HashMap;

use norn_syntax::ast;
use norn_syntax::{Diagnostic, Span};

use crate::hir::*;

pub struct Checked {
    pub program: Program,
    pub errors: Vec<Diagnostic>,
}

impl Checked {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
}

pub fn check(module: &ast::Module) -> Checked {
    let mut checker = Checker::new();
    checker.run(module);
    let Checker {
        program,
        mut errors,
        ..
    } = checker;
    // Report in source order rather than stage order, as the parser does: signatures are resolved
    // before any body is checked, and what that finds should not float to the top of the list.
    errors.sort_by_key(|diagnostic| diagnostic.span.start);
    Checked { program, errors }
}

/// What a name at the head of a path refers to.
enum TypeName {
    Record(RecordId),
    Enum(EnumId),
    Reactor(ReactorId),
    Builtin(Ty),
}

/// What kind of expression is being checked, and therefore what it is allowed to do.
///
/// This was a `bool` while the only question was "are we in a `task fn`". A turn adds a second,
/// stricter answer — a node body may not even build a task — and the `after_commit` operand adds a
/// third that sits between them: it must build a task, and must still not run one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ctx {
    /// An ordinary `fn`.
    Plain,
    /// A `task fn`.
    Task,
    /// A signal body, a state initialiser, or an `on` handler.
    Turn,
    /// The operand of `after_commit`: evaluated during the turn, started after it.
    Effect,
}

impl Ctx {
    /// Whether a task may be *built* here. Building is not running, which is the whole reason
    /// `after_commit` can describe an effect without performing one.
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

struct Checker {
    program: Program,
    errors: Vec<Diagnostic>,
    types: HashMap<String, TypeName>,
    fns: HashMap<String, FnId>,
    reactors: HashMap<String, ReactorId>,
    /// Signatures, resolved before any body is checked so that functions may call one another
    /// regardless of declaration order.
    signatures: Vec<(Vec<(String, Ty)>, Ty)>,
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
    /// How many `scope { … }` expressions enclose the expression being checked. Reset per function,
    /// which is what makes "inside a scope in the same function" the rule `spawn` enforces.
    scope_depth: usize,
}

impl Checker {
    fn new() -> Checker {
        // `Option` and `Result` are seeded as ordinary enums so that construction, matching, and
        // lowering treat them exactly like a user enum. Only their type arguments are special.
        let span = Span::new(0, 0);
        let option = EnumDef {
            name: "Option".into(),
            variants: vec![
                VariantDef {
                    name: "None".into(),
                    fields: vec![],
                    positional: true,
                    span,
                },
                VariantDef {
                    name: "Some".into(),
                    fields: vec![FieldDef {
                        name: "0".into(),
                        ty: Ty::Error,
                        span,
                    }],
                    positional: true,
                    span,
                },
            ],
            span,
        };
        let result = EnumDef {
            name: "Result".into(),
            variants: vec![
                VariantDef {
                    name: "Ok".into(),
                    fields: vec![FieldDef {
                        name: "0".into(),
                        ty: Ty::Error,
                        span,
                    }],
                    positional: true,
                    span,
                },
                VariantDef {
                    name: "Err".into(),
                    fields: vec![FieldDef {
                        name: "0".into(),
                        ty: Ty::Error,
                        span,
                    }],
                    positional: true,
                    span,
                },
            ],
            span,
        };
        // `IoError` is seeded beside them: the socket builtins have to fail with something, and a
        // failure type the language cannot name is not a failure type.
        let io_error = EnumDef {
            name: "IoError".into(),
            variants: io_error::VARIANTS
                .iter()
                .map(|(name, fields)| VariantDef {
                    name: (*name).into(),
                    fields: (0..*fields)
                        .map(|index| FieldDef {
                            name: index.to_string(),
                            ty: Ty::Str,
                            span,
                        })
                        .collect(),
                    positional: true,
                    span,
                })
                .collect(),
            span,
        };
        Checker {
            program: Program {
                records: Vec::new(),
                enums: vec![option, result, io_error],
                fns: Vec::new(),
                reactors: Vec::new(),
                main: None,
            },
            errors: Vec::new(),
            types: HashMap::new(),
            fns: HashMap::new(),
            reactors: HashMap::new(),
            signatures: Vec::new(),
            locals: Vec::new(),
            scopes: Vec::new(),
            ret: Ty::Unit,
            fn_name: String::new(),
            ctx: Ctx::Plain,
            uses: Vec::new(),
            members: HashMap::new(),
            reactor: None,
            in_handler: false,
            assigning: false,
            scope_depth: 0,
        }
    }

    fn error(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(Diagnostic::new(span, message));
    }

    fn push(&mut self, diagnostic: Diagnostic) {
        self.errors.push(diagnostic);
    }

    // ---------------------------------------------------------------- program

    fn run(&mut self, module: &ast::Module) {
        if let Some(decl) = module.uses.first() {
            self.push(
                Diagnostic::new(decl.span, "`use` has nothing to import yet")
                    .label("no module system")
                    .note("modules and imports arrive with the standard library; see BOOTSTRAP.md"),
            );
        }

        self.declare_types(module);
        self.define_types(module);
        self.declare_fns(module);
        // Reactors are declared, scanned, and checked between signatures and bodies, because a
        // `task fn` body may mention a reactor and a node body may call any function.
        self.declare_reactors(module);
        let graphs = self.scan_reactors(module);
        self.check_reactors(module, graphs);
        self.check_fns(module);
        self.check_turns();
    }

    /// The one diagnostic every purity rule shares. A turn is not a place where the world can
    /// notice anything happening, and every way to break that says so the same way.
    fn impure(&mut self, what: &str, does: &str, span: Span) {
        self.push(
            Diagnostic::new(
                span,
                format!("`{what}` cannot appear in a reactor, because it {does}"),
            )
            .label("a turn is pure")
            .note(
                "a turn runs to a fixed point with nothing able to observe it part-way; effects leave it through `after_commit`",
            ),
        );
    }

    /// Pass one: every type name exists before any type is resolved, so declarations may refer to
    /// one another in any order.
    fn declare_types(&mut self, module: &ast::Module) {
        self.types.insert("I64".into(), TypeName::Builtin(Ty::I64));
        self.types.insert("F64".into(), TypeName::Builtin(Ty::F64));
        self.types
            .insert("Bool".into(), TypeName::Builtin(Ty::Bool));
        self.types
            .insert("String".into(), TypeName::Builtin(Ty::Str));
        self.types.insert(
            "Listener".into(),
            TypeName::Builtin(Ty::Resource(Resource::Listener)),
        );
        self.types.insert(
            "Connection".into(),
            TypeName::Builtin(Ty::Resource(Resource::Connection)),
        );
        self.types
            .insert("IoError".into(), TypeName::Enum(EnumId::IO_ERROR));

        for item in &module.items {
            let (name, span) = match item {
                ast::Item::Record(decl) => (&decl.name, decl.span),
                ast::Item::Enum(decl) => (&decl.name, decl.span),
                ast::Item::Reactor(decl) => (&decl.name, decl.span),
                ast::Item::Fn(_) => continue,
            };
            if self.types.contains_key(&name.name) {
                self.push(
                    Diagnostic::new(name.span, format!("`{}` is declared twice", name.name))
                        .label("duplicate type"),
                );
                continue;
            }
            let resolved = match item {
                ast::Item::Record(decl) => {
                    let id = RecordId(self.program.records.len() as u32);
                    self.program.records.push(RecordDef {
                        name: decl.name.name.clone(),
                        fields: Vec::new(),
                        span,
                    });
                    TypeName::Record(id)
                }
                ast::Item::Enum(decl) => {
                    let id = EnumId(self.program.enums.len() as u32);
                    self.program.enums.push(EnumDef {
                        name: decl.name.name.clone(),
                        variants: Vec::new(),
                        span,
                    });
                    TypeName::Enum(id)
                }
                // A reactor handle is a type in the same sense a `Listener` is: it is spelled by
                // its own name, and it names the thing rather than describing its shape.
                ast::Item::Reactor(decl) => {
                    let id = ReactorId(self.program.reactors.len() as u32);
                    self.program.reactors.push(ReactorDef {
                        name: decl.name.name.clone(),
                        params: Vec::new(),
                        uses: Vec::new(),
                        inputs: Vec::new(),
                        nodes: Vec::new(),
                        slots: Vec::new(),
                        order: Vec::new(),
                        exports: Vec::new(),
                        span,
                    });
                    self.reactors.insert(decl.name.name.clone(), id);
                    TypeName::Reactor(id)
                }
                ast::Item::Fn(_) => unreachable!(),
            };
            self.types.insert(name.name.clone(), resolved);
        }
    }

    /// Pass two: fill in field and payload types.
    fn define_types(&mut self, module: &ast::Module) {
        for item in &module.items {
            match item {
                ast::Item::Record(decl) => {
                    let Some(TypeName::Record(id)) = self.types.get(&decl.name.name) else {
                        continue;
                    };
                    let id = *id;
                    let mut fields = Vec::new();
                    for field in &decl.fields {
                        if fields.iter().any(|f: &FieldDef| f.name == field.name.name) {
                            self.error(
                                field.name.span,
                                format!("field `{}` is declared twice", field.name.name),
                            );
                            continue;
                        }
                        let ty = self.resolve_ty(&field.ty);
                        fields.push(FieldDef {
                            name: field.name.name.clone(),
                            ty,
                            span: field.span,
                        });
                    }
                    self.program.records[id.index()].fields = fields;
                }
                ast::Item::Enum(decl) => {
                    let Some(TypeName::Enum(id)) = self.types.get(&decl.name.name) else {
                        continue;
                    };
                    let id = *id;
                    let mut variants = Vec::new();
                    for variant in &decl.variants {
                        let (fields, positional) = match &variant.payload {
                            ast::VariantPayload::Unit => (Vec::new(), true),
                            ast::VariantPayload::Tuple(types) => {
                                let fields = types
                                    .iter()
                                    .enumerate()
                                    .map(|(i, ty)| FieldDef {
                                        name: i.to_string(),
                                        ty: self.resolve_ty(ty),
                                        span: ty.span,
                                    })
                                    .collect();
                                (fields, true)
                            }
                            ast::VariantPayload::Record(decls) => {
                                let fields = decls
                                    .iter()
                                    .map(|f| FieldDef {
                                        name: f.name.name.clone(),
                                        ty: self.resolve_ty(&f.ty),
                                        span: f.span,
                                    })
                                    .collect();
                                (fields, false)
                            }
                        };
                        variants.push(VariantDef {
                            name: variant.name.name.clone(),
                            fields,
                            positional,
                            span: variant.span,
                        });
                    }
                    self.program.enums[id.index()].variants = variants;
                }
                ast::Item::Fn(_) | ast::Item::Reactor(_) => {}
            }
        }
    }

    fn declare_fns(&mut self, module: &ast::Module) {
        for item in &module.items {
            let ast::Item::Fn(decl) = item else { continue };
            if Builtin::from_name(&decl.name.name).is_some() {
                self.push(
                    Diagnostic::new(
                        decl.name.span,
                        format!("`{}` is a built-in function", decl.name.name),
                    )
                    .label("cannot be redefined"),
                );
                continue;
            }
            if self.fns.contains_key(&decl.name.name) {
                self.push(
                    Diagnostic::new(
                        decl.name.span,
                        format!("`{}` is declared twice", decl.name.name),
                    )
                    .label("duplicate function"),
                );
                continue;
            }
            let params: Vec<(String, Ty)> = decl
                .params
                .iter()
                .map(|p| (p.name.name.clone(), self.resolve_ty(&p.ty)))
                .collect();
            let ret = decl.ret.as_ref().map_or(Ty::Unit, |ty| self.resolve_ty(ty));
            let uses = self.capabilities(&decl.uses);
            let id = FnId(self.program.fns.len() as u32);
            self.fns.insert(decl.name.name.clone(), id);
            self.signatures.push((params.clone(), ret.clone()));
            self.program.fns.push(FnDef {
                name: decl.name.name.clone(),
                is_task: decl.is_task,
                uses,
                params: params.len(),
                locals: Vec::new(),
                ret,
                body: Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span: decl.span,
                },
                span: decl.span,
            });
            if decl.name.name == "main" {
                self.program.main = Some(id);
            }
        }
    }

    /// Resolve a `uses { … }` list. The vocabulary is closed, so an unknown name is an error that
    /// says what the three are rather than a capability nobody grants.
    fn capabilities(&mut self, uses: &[ast::Path]) -> Vec<Capability> {
        let mut resolved = Vec::new();
        for path in uses {
            let name = path.text();
            match Capability::from_name(&name) {
                Some(capability) => {
                    if !resolved.contains(&capability) {
                        resolved.push(capability);
                    }
                }
                None => {
                    let known: Vec<&str> = Capability::ALL.iter().map(|c| c.name()).collect();
                    self.push(
                        Diagnostic::new(path.span, format!("unknown capability `{name}`"))
                            .label("not a capability v0 knows")
                            .note(format!("the vocabulary is fixed: {}", known.join(", "))),
                    );
                }
            }
        }
        resolved.sort();
        resolved
    }

    fn check_fns(&mut self, module: &ast::Module) {
        for item in &module.items {
            let ast::Item::Fn(decl) = item else { continue };
            let Some(&id) = self.fns.get(&decl.name.name) else {
                continue;
            };
            if self.program.fns[id.index()].name != decl.name.name {
                continue;
            }
            if !decl.is_task && !decl.uses.is_empty() {
                // The parser already rejects `uses` on a non-task function, so this is unreachable
                // in practice; keeping it means the checker never silently ignores a capability.
                self.error(decl.span, "capabilities are only meaningful on a `task fn`");
            }

            let (params, ret) = self.signatures[id.index()].clone();
            self.locals = Vec::new();
            self.scopes = vec![Vec::new()];
            self.ret = ret.clone();
            self.fn_name = decl.name.name.clone();
            self.ctx = if decl.is_task { Ctx::Task } else { Ctx::Plain };
            self.members = HashMap::new();
            self.reactor = None;
            self.in_handler = false;
            self.uses = self.program.fns[id.index()].uses.clone();
            self.scope_depth = 0;
            for ((name, ty), param) in params.iter().zip(&decl.params) {
                self.declare_local(name.clone(), ty.clone(), false, param.name.span);
            }
            let body = self.check_block(&decl.body, Some(&ret), decl.body.span);
            let locals = std::mem::take(&mut self.locals);
            self.program.fns[id.index()].locals = locals;
            self.program.fns[id.index()].body = body;
        }
    }

    // ---------------------------------------------------------------- reactors

    /// Pair each reactor declaration with the id `declare_types` gave it, skipping a redeclaration
    /// so that a duplicate name does not quietly fold two reactors into one.
    fn reactor_items<'m>(&self, module: &'m ast::Module) -> Vec<(ReactorId, &'m ast::ReactorDecl)> {
        let mut seen: Vec<ReactorId> = Vec::new();
        let mut out = Vec::new();
        for item in &module.items {
            let ast::Item::Reactor(decl) = item else {
                continue;
            };
            let Some(&id) = self.reactors.get(&decl.name.name) else {
                continue;
            };
            if seen.contains(&id) {
                continue;
            }
            seen.push(id);
            out.push((id, decl));
        }
        out
    }

    /// Declare a function that was lifted out of a reactor rather than written as one.
    ///
    /// Its name is not a legal identifier, so nothing can call it by name; it exists so that a node
    /// body is an ordinary `FnKind::Plain` function that M1's lowering and M5's backend already
    /// know how to compile. `FnKind` needs no third variant, because a node function is plain
    /// because it *is* plain.
    fn declare_lifted(&mut self, name: String, span: Span) -> FnId {
        let id = FnId(self.program.fns.len() as u32);
        self.signatures.push((Vec::new(), Ty::Error));
        self.program.fns.push(FnDef {
            name,
            is_task: false,
            uses: Vec::new(),
            params: 0,
            locals: Vec::new(),
            ret: Ty::Error,
            body: Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            },
            span,
        });
        id
    }

    /// Pass one: names, parameters, capabilities, input and state *types*, and the member
    /// namespace. No expression is looked at — the scan that decides what order to look at them in
    /// has not run yet.
    fn declare_reactors(&mut self, module: &ast::Module) {
        for (id, decl) in self.reactor_items(module) {
            let uses = self.capabilities(&decl.uses);
            let mut params = Vec::new();
            let mut nodes: Vec<Node> = Vec::new();
            let mut slots: Vec<NodeId> = Vec::new();
            let mut inputs: Vec<InputDef> = Vec::new();
            let mut taken: HashMap<String, Span> = HashMap::new();

            let claim = |checker: &mut Checker,
                         taken: &mut HashMap<String, Span>,
                         name: &ast::Ident|
             -> bool {
                if let Some(first) = taken.get(&name.name) {
                    checker.push(
                        Diagnostic::new(
                            name.span,
                            format!("`{}` is declared twice in `{}`", name.name, decl.name.name),
                        )
                        .label("duplicate member")
                        .secondary(*first, "first declared here"),
                    );
                    return false;
                }
                taken.insert(name.name.clone(), name.span);
                true
            };

            // A parameter is a node and a slot: state written once, when the reactor is created.
            // Making it one costs a variant and removes a special case from every later pass —
            // a node body's arguments are then exactly its dependencies, with nothing threaded
            // alongside them.
            for (index, param) in decl.params.iter().enumerate() {
                if !claim(self, &mut taken, &param.name) {
                    continue;
                }
                let ty = self.resolve_ty(&param.ty);
                let slot = slots.len();
                slots.push(NodeId(nodes.len() as u32));
                nodes.push(Node {
                    name: param.name.name.clone(),
                    kind: NodeKind::Param { slot, index },
                    ty: ty.clone(),
                    deps: Vec::new(),
                    exported: false,
                    span: param.span,
                });
                params.push((param.name.name.clone(), ty));
            }

            for member in &decl.members {
                match &member.kind {
                    ast::MemberKind::Input { name, ty, queue } => {
                        if !claim(self, &mut taken, name) {
                            continue;
                        }
                        let ty = self.resolve_ty(ty);
                        let capacity = self.capacity(&queue.capacity);
                        let overflow = self.overflow(&queue.overflow);
                        let handler = self.declare_lifted(
                            format!("{}.on.{}", decl.name.name, name.name),
                            member.span,
                        );
                        inputs.push(InputDef {
                            name: name.name.clone(),
                            ty,
                            capacity,
                            overflow,
                            handler,
                            plan: Vec::new(),
                            span: member.span,
                        });
                    }
                    ast::MemberKind::State { name, ty, .. } => {
                        if !claim(self, &mut taken, name) {
                            continue;
                        }
                        let ty = self.resolve_ty(ty);
                        let init = self.declare_lifted(
                            format!("{}.{}.init", decl.name.name, name.name),
                            member.span,
                        );
                        let slot = slots.len();
                        slots.push(NodeId(nodes.len() as u32));
                        nodes.push(Node {
                            name: name.name.clone(),
                            kind: NodeKind::State { slot, init },
                            ty,
                            deps: Vec::new(),
                            exported: false,
                            span: member.span,
                        });
                    }
                    ast::MemberKind::Signal { name, exported, .. } => {
                        if !claim(self, &mut taken, name) {
                            continue;
                        }
                        let body = self.declare_lifted(
                            format!("{}.{}", decl.name.name, name.name),
                            member.span,
                        );
                        nodes.push(Node {
                            name: name.name.clone(),
                            kind: NodeKind::Signal { body },
                            // Filled in by `check_reactors`, which types the bodies in the order
                            // the scan worked out.
                            ty: Ty::Error,
                            deps: Vec::new(),
                            exported: *exported,
                            span: member.span,
                        });
                    }
                    ast::MemberKind::On { .. } => {}
                }
            }

            // A handler is matched to its input by name, so both directions have to be checked:
            // an input with no handler can never do anything, and a handler for no input responds
            // to a message that cannot arrive.
            let mut handled: Vec<usize> = Vec::new();
            for member in &decl.members {
                let ast::MemberKind::On { input, .. } = &member.kind else {
                    continue;
                };
                let Some(index) = inputs.iter().position(|i| i.name == input.name) else {
                    let known: Vec<&str> = inputs.iter().map(|i| i.name.as_str()).collect();
                    let mut diagnostic = Diagnostic::new(
                        input.span,
                        format!("`{}` has no input `{}`", decl.name.name, input.name),
                    )
                    .label("nothing would send this");
                    if !known.is_empty() {
                        diagnostic =
                            diagnostic.note(format!("its inputs are: {}", known.join(", ")));
                    }
                    self.push(diagnostic);
                    continue;
                };
                if handled.contains(&index) {
                    self.push(
                        Diagnostic::new(
                            input.span,
                            format!("`{}` already has a handler", input.name),
                        )
                        .label("second `on` for one input")
                        .secondary(inputs[index].span, "the input")
                        .note("one input is one handler: two would need an order between them, and a turn has none"),
                    );
                    continue;
                }
                handled.push(index);
            }
            for (index, input) in inputs.iter().enumerate() {
                if handled.contains(&index) {
                    continue;
                }
                self.push(
                    Diagnostic::new(
                        input.span,
                        format!("`{}` has no `on {}` handler", input.name, input.name),
                    )
                    .label("nothing responds to this")
                    .note("an input is how a message reaches state; with no handler it can only be dropped"),
                );
            }

            let reactor = &mut self.program.reactors[id.index()];
            reactor.params = params;
            reactor.uses = uses;
            reactor.inputs = inputs;
            reactor.slots = slots;
            reactor.exports = nodes
                .iter()
                .enumerate()
                .filter(|(_, node)| node.exported)
                .map(|(index, _)| NodeId(index as u32))
                .collect();
            reactor.nodes = nodes;
        }
    }

    /// Pass two: the dependency edges, the cycle check, and a topological order — all from the
    /// shape of the source, before any body is typed.
    fn scan_reactors(&mut self, module: &ast::Module) -> Vec<Wiring> {
        let mut wirings = Vec::new();
        for (id, decl) in self.reactor_items(module) {
            wirings.push(self.scan_reactor(id, decl));
        }
        wirings
    }

    fn scan_reactor(&mut self, id: ReactorId, decl: &ast::ReactorDecl) -> Wiring {
        let members = self.member_namespace(id);
        let count = self.program.reactors[id.index()].nodes.len();
        let mut deps: Vec<Vec<usize>> = vec![Vec::new(); count];
        let mut writes: Vec<Vec<usize>> =
            vec![Vec::new(); self.program.reactors[id.index()].inputs.len()];
        let mut ok = true;

        for member in &decl.members {
            match &member.kind {
                ast::MemberKind::State { name, init, .. } => {
                    let Some(node) = self.node_index(id, &name.name) else {
                        continue;
                    };
                    let mut scan = Scan::new(&members);
                    scan.expr(init);
                    // An initialiser is not propagation: it runs once, before any turn, so it may
                    // read what is already fixed — the constructor parameters — and nothing else.
                    // Reading another cell's initial value would need an order between them that
                    // the graph deliberately does not have.
                    for (found, span) in &scan.reads {
                        match members.get(found) {
                            Some(Sort::Param) => {
                                let dep =
                                    self.node_index(id, found).expect("a parameter is a node");
                                push_once(&mut deps[node], dep);
                            }
                            Some(sort) => {
                                self.push(
                                    Diagnostic::new(
                                        *span,
                                        format!(
                                            "a `state` initialiser cannot read the {} `{found}`",
                                            sort.describe()
                                        ),
                                    )
                                    .label("initialisers run before the first turn")
                                    .note("read a constructor parameter instead, or derive the value with a signal"),
                                );
                                ok = false;
                            }
                            None => {}
                        }
                    }
                }
                ast::MemberKind::Signal { name, body, .. } => {
                    let Some(node) = self.node_index(id, &name.name) else {
                        continue;
                    };
                    let mut scan = Scan::new(&members);
                    scan.expr(body);
                    for (found, span) in &scan.reads {
                        match members.get(found) {
                            Some(Sort::Input) => {
                                self.unreadable_member(found, Sort::Input, *span);
                                ok = false;
                            }
                            Some(_) => {
                                let dep = self.node_index(id, found).expect("a member with a sort");
                                push_once(&mut deps[node], dep);
                            }
                            None => {}
                        }
                    }
                }
                ast::MemberKind::On {
                    input,
                    params,
                    body,
                } => {
                    let Some(index) = self.program.reactors[id.index()].input(&input.name) else {
                        continue;
                    };
                    // The handler's own message binding shadows any member of the same name.
                    let mut scan = Scan::new(&members);
                    for param in params {
                        scan.bind(&param.name);
                    }
                    scan.block(body);
                    for (found, span) in &scan.writes {
                        match members.get(found) {
                            Some(Sort::State) => {
                                let node = self.node_index(id, found).expect("state is a node");
                                push_once(&mut writes[index], node);
                            }
                            // Assignment to a parameter or a signal is reported when the body is
                            // typed, where the diagnostic can say what the name actually is.
                            Some(_) | None => {
                                let _ = span;
                            }
                        }
                    }
                }
                ast::MemberKind::Input { .. } => {}
            }
        }

        if let Some(cycle) = self.find_cycle(id, &deps) {
            self.report_cycle(id, &cycle);
            ok = false;
        }
        let order = if ok {
            topological(&deps)
        } else {
            (0..count).collect()
        };

        let reactor = &mut self.program.reactors[id.index()];
        for (node, found) in deps.iter().enumerate() {
            reactor.nodes[node].deps = found.iter().map(|d| NodeId(*d as u32)).collect();
        }
        reactor.order = order.iter().map(|n| NodeId(*n as u32)).collect();

        Wiring {
            deps,
            order,
            writes,
            ok,
        }
    }

    /// Pass three: type every body, in the order pass two worked out, and lift each to a function.
    ///
    /// Topological order is what makes forward references work: `signal healthy = open < limit`
    /// can be written above `signal open` because `open` is typed first regardless of where it
    /// appears in the file.
    fn check_reactors(&mut self, module: &ast::Module, wirings: Vec<Wiring>) {
        for ((id, decl), wiring) in self.reactor_items(module).into_iter().zip(wirings) {
            if !wiring.ok {
                continue;
            }
            self.check_reactor(id, decl, &wiring);
        }
    }

    fn check_reactor(&mut self, id: ReactorId, decl: &ast::ReactorDecl, wiring: &Wiring) {
        let members = self.member_namespace(id);
        let uses = self.program.reactors[id.index()].uses.clone();
        let name = self.program.reactors[id.index()].name.clone();

        for &node in &wiring.order {
            let (kind_fn, node_span) = {
                let node_def = &self.program.reactors[id.index()].nodes[node];
                let function = match node_def.kind {
                    NodeKind::Param { .. } => None,
                    NodeKind::State { init, .. } => Some(init),
                    NodeKind::Signal { body, .. } => Some(body),
                };
                (function, node_def.span)
            };
            let Some(function) = kind_fn else {
                continue;
            };
            let Some(member) =
                member_for(decl, &self.program.reactors[id.index()].nodes[node].name)
            else {
                continue;
            };
            let (body, annotation) = match &member.kind {
                ast::MemberKind::State { ty, init, .. } => (init, Some(ty)),
                ast::MemberKind::Signal { ty, body, .. } => (body, ty.as_ref()),
                _ => continue,
            };

            self.begin_member(&name, function, Ctx::Turn, &uses, id, &members, false);
            for &dep in &wiring.deps[node] {
                self.bind_node(id, dep, false);
            }
            let expected = annotation.map(|ty| self.resolve_ty(ty));
            let checked = self.check_expr(body, expected.as_ref());
            let ty = expected.unwrap_or_else(|| match &checked.ty {
                Ty::Never => Ty::Error,
                ty => ty.clone(),
            });
            self.finish_member(function, ty.clone(), checked);
            let _ = node_span;
            self.program.reactors[id.index()].nodes[node].ty = ty;
        }

        // Handlers last: every node type is known by now, so a handler can be checked in one pass
        // whatever order it was written in.
        for member in &decl.members {
            let ast::MemberKind::On {
                input,
                params,
                body,
            } = &member.kind
            else {
                continue;
            };
            let Some(index) = self.program.reactors[id.index()].input(&input.name) else {
                continue;
            };
            let function = self.program.reactors[id.index()].inputs[index].handler;
            if self.program.fns[function.index()].ret != Ty::Error {
                // A second handler for the same input; already reported.
                continue;
            }

            self.begin_member(&name, function, Ctx::Turn, &uses, id, &members, true);
            let message = self.program.reactors[id.index()].inputs[index].ty.clone();
            self.bind_message(&input.name, params, &message, member.span);
            // Every slot, in slot order, so that the runtime's call is one shape rather than one
            // per handler. State is `mut` here and nowhere else: this is the only place a commit
            // can happen.
            let slots = self.program.reactors[id.index()].slots.clone();
            for slot in slots {
                self.bind_node(id, slot.index(), true);
            }
            let checked = self.check_block(body, Some(&Ty::Unit), body.span);
            self.finish_member(function, Ty::Unit, checked);
        }

        self.ctx = Ctx::Plain;
        self.members = HashMap::new();
        self.reactor = None;
        self.in_handler = false;
        self.plans(id, wiring);
    }

    /// Bind the message an `on` handler was invoked with.
    ///
    /// One binding, or none when the message is `()`: an occurrence with no payload has nothing to
    /// name. Destructuring several names out of one message needs patterns in a parameter position,
    /// which nothing else in v0 has.
    fn bind_message(&mut self, input: &str, params: &[ast::Ident], ty: &Ty, span: Span) {
        let wanted = if *ty == Ty::Unit { 0 } else { 1 };
        if params.len() == wanted {
            if let Some(param) = params.first() {
                self.declare_role(
                    param.name.clone(),
                    ty.clone(),
                    false,
                    LocalRole::Message,
                    param.span,
                );
            }
            return;
        }
        let message = if wanted == 0 {
            format!("`{input}` carries no message, so `on {input}()` binds nothing")
        } else {
            format!(
                "`on {input}` binds the message it was sent, so it takes one name, not {}",
                params.len()
            )
        };
        let mut diagnostic = Diagnostic::new(span, message);
        diagnostic = if wanted == 0 {
            diagnostic.label("declared as `()`")
        } else {
            diagnostic.note(format!(
                "write `on {input}(message)`, where `message` is the {} it was sent",
                self.program.ty_name(ty)
            ))
        };
        self.push(diagnostic);
        for param in params {
            self.declare_role(
                param.name.clone(),
                Ty::Error,
                false,
                LocalRole::Message,
                param.span,
            );
        }
    }

    /// Start checking one lifted member: a fresh local frame, and the reactor's namespace in hand
    /// for the sake of diagnostics about names that are members but not readable here.
    #[allow(clippy::too_many_arguments)]
    fn begin_member(
        &mut self,
        reactor_name: &str,
        function: FnId,
        ctx: Ctx,
        uses: &[Capability],
        id: ReactorId,
        members: &HashMap<String, Sort>,
        handler: bool,
    ) {
        self.locals = Vec::new();
        self.scopes = vec![Vec::new()];
        self.ret = Ty::Unit;
        self.fn_name = self.program.fns[function.index()].name.clone();
        self.ctx = ctx;
        self.uses = uses.to_vec();
        self.scope_depth = 0;
        self.reactor = Some(id);
        self.in_handler = handler;
        // A node body sees only what it depends on; a handler sees state but never a signal. Both
        // are expressed by simply not binding the rest, with `members` supplying the diagnostic.
        self.members = members.clone();
        let _ = reactor_name;
    }

    fn bind_node(&mut self, id: ReactorId, node: usize, mutable: bool) {
        let node = &self.program.reactors[id.index()].nodes[node];
        let (name, ty, span) = (node.name.clone(), node.ty.clone(), node.span);
        let role = match node.kind {
            NodeKind::Param { .. } => LocalRole::Param,
            NodeKind::State { slot, .. } => LocalRole::State(slot),
            NodeKind::Signal { .. } => LocalRole::Signal,
        };
        // A parameter is fixed for the reactor's life, so it is never `mut` even in a handler.
        let mutable = mutable && matches!(role, LocalRole::State(_));
        self.declare_role(name, ty, mutable, role, span);
    }

    fn finish_member(&mut self, function: FnId, ret: Ty, body: Expr) {
        let locals = std::mem::take(&mut self.locals);
        let params = locals.len() - count_extra(&locals);
        let def = &mut self.program.fns[function.index()];
        def.params = params;
        def.ret = ret;
        def.locals = locals;
        def.body = body;
    }

    /// Pass four's other half: what each input's turn actually has to touch.
    ///
    /// A plan is the subsequence of `order` reachable from the state cells that input's handler
    /// assigns. Everything outside it is provably unaffected by a message on that input, so a turn
    /// does not walk it — and because it is carved out of `order`, it is a subsequence of `order`
    /// by construction rather than by a check somebody has to remember.
    fn plans(&mut self, id: ReactorId, wiring: &Wiring) {
        let count = self.program.reactors[id.index()].nodes.len();
        // Dependents, from the dependency edges: propagation runs the other way round.
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); count];
        for (node, deps) in wiring.deps.iter().enumerate() {
            for &dep in deps {
                dependents[dep].push(node);
            }
        }

        for index in 0..self.program.reactors[id.index()].inputs.len() {
            let mut reached = vec![false; count];
            let mut stack: Vec<usize> = wiring.writes[index].clone();
            for &node in &stack {
                reached[node] = true;
            }
            while let Some(node) = stack.pop() {
                for &next in &dependents[node] {
                    if !reached[next] {
                        reached[next] = true;
                        stack.push(next);
                    }
                }
            }
            let plan: Vec<NodeId> = wiring
                .order
                .iter()
                .filter(|node| reached[**node])
                .map(|node| NodeId(*node as u32))
                .collect();
            self.program.reactors[id.index()].inputs[index].plan = plan;
        }
    }

    /// Pass five: everything about a turn that is a property of the *call graph* rather than of one
    /// expression — that it terminates, and that nothing it reaches can be observed from outside.
    ///
    /// Both have the same shape and the same reason for living here. `check_reactors` can see that
    /// a node body does not itself call `print`, and cannot see that the ordinary function it calls
    /// does; an ordinary `fn` is allowed to print, because printing needs no authority. So purity
    /// is checked over the functions a turn can reach, which is the same walk termination needs.
    ///
    /// A turn has to terminate, and `DESIGN.md` §14 leaves open how strict that should be — total
    /// functions, cost annotations, cooperative budgets. v0 can answer it with a theorem instead:
    /// there is no `while`, no `for`, and no `loop`, so recursion is the only way a pure function
    /// can fail to return. One pass over the call graph therefore makes every turn provably
    /// terminating, with no annotation burden and no runtime budget.
    ///
    /// This expires the day loops arrive, and should be replaced rather than extended when they do.
    fn check_turns(&mut self) {
        let mut turn_fns: Vec<(FnId, Span)> = Vec::new();
        for reactor in &self.program.reactors {
            for node in &reactor.nodes {
                match node.kind {
                    NodeKind::Param { .. } => {}
                    NodeKind::State { init, .. } => turn_fns.push((init, node.span)),
                    NodeKind::Signal { body, .. } => turn_fns.push((body, node.span)),
                }
            }
            for input in &reactor.inputs {
                turn_fns.push((input.handler, input.span));
            }
        }
        if turn_fns.is_empty() {
            return;
        }

        let calls: Vec<Vec<FnId>> = self
            .program
            .fns
            .iter()
            .map(|def| {
                let mut found = Vec::new();
                collect_calls(&def.body, &mut found);
                found
            })
            .collect();
        let impurities: Vec<Option<(Builtin, Span)>> = self
            .program
            .fns
            .iter()
            .map(|def| impure_builtin(&def.body))
            .collect();

        for (function, span) in turn_fns {
            // Reported once per turn function even when several reachable functions are impure:
            // the first one is what has to change, and listing the rest is noise until it does.
            if let Some((culprit, builtin, at)) = reachable_impurity(&calls, &impurities, function)
                && culprit != function
            {
                let name = self.program.fns[culprit.index()].name.clone();
                self.push(
                    Diagnostic::new(
                        span,
                        format!(
                            "this reaches `{}`, which calls `{}`",
                            name,
                            builtin.name()
                        ),
                    )
                    .label("a turn is pure")
                    .secondary(at, format!("`{}` is something the world can see happen", builtin.name()))
                    .note("purity is not the same question as authority: `print` needs no capability and is still observable")
                    .note("effects leave a turn through `after_commit`, which starts them once the snapshot is published"),
                );
            }

            let Some(cycle) = reachable_cycle(&calls, function) else {
                continue;
            };
            let names: Vec<&str> = cycle
                .iter()
                .map(|id| self.program.fns[id.index()].name.as_str())
                .collect();
            let culprit = cycle[0];
            let message = format!("`{}` is recursive, and a turn must end", names[0]);
            let mut diagnostic = Diagnostic::new(span, message)
                .label("reached from here")
                .secondary(
                    self.program.fns[culprit.index()].span,
                    format!("the cycle is {}", names.join(" → ")),
                );
            diagnostic = diagnostic
                .note("v0 has no loop construct, so recursion is the only way a pure function can fail to return — which is what makes termination provable rather than hoped for")
                .note("compute the value with a bounded expression, or move the work into a `task fn` and request it with `after_commit`");
            self.push(diagnostic);
        }
    }

    fn member_namespace(&self, id: ReactorId) -> HashMap<String, Sort> {
        let reactor = &self.program.reactors[id.index()];
        let mut members = HashMap::new();
        for node in &reactor.nodes {
            let sort = match node.kind {
                NodeKind::Param { .. } => Sort::Param,
                NodeKind::State { .. } => Sort::State,
                NodeKind::Signal { .. } => Sort::Signal,
            };
            members.insert(node.name.clone(), sort);
        }
        for input in &reactor.inputs {
            members.insert(input.name.clone(), Sort::Input);
        }
        members
    }

    fn node_index(&self, id: ReactorId, name: &str) -> Option<usize> {
        self.program.reactors[id.index()]
            .nodes
            .iter()
            .position(|node| node.name == name)
    }

    /// Find one instantaneous cycle, as the path that closes it.
    ///
    /// Only edges *between signals* can close one: a state cell is a temporal boundary, so a
    /// feedback loop that crosses one is exactly the accepted kind. That is also why one pass over
    /// the topological order is the fixed point rather than an iteration to convergence.
    fn find_cycle(&self, id: ReactorId, deps: &[Vec<usize>]) -> Option<Vec<usize>> {
        let reactor = &self.program.reactors[id.index()];
        let instantaneous = |node: usize| reactor.nodes[node].kind.is_signal();

        #[derive(Clone, Copy, PartialEq)]
        enum Mark {
            White,
            Grey,
            Black,
        }
        let mut marks = vec![Mark::White; deps.len()];
        let mut path: Vec<usize> = Vec::new();

        // Iterative rather than recursive, and started from every node in source order, so the
        // cycle reported for a given program is always the same one.
        for start in 0..deps.len() {
            if !instantaneous(start) || marks[start] != Mark::White {
                continue;
            }
            let mut stack = vec![(start, 0usize)];
            marks[start] = Mark::Grey;
            path.push(start);
            while let Some((node, next)) = stack.pop() {
                if next >= deps[node].len() {
                    marks[node] = Mark::Black;
                    path.pop();
                    continue;
                }
                stack.push((node, next + 1));
                let dep = deps[node][next];
                if !instantaneous(dep) {
                    continue;
                }
                match marks[dep] {
                    Mark::Grey => {
                        let at = path.iter().position(|n| *n == dep).unwrap_or(0);
                        let mut cycle = path[at..].to_vec();
                        cycle.push(dep);
                        return Some(cycle);
                    }
                    Mark::Black => {}
                    Mark::White => {
                        marks[dep] = Mark::Grey;
                        path.push(dep);
                        stack.push((dep, 0));
                    }
                }
            }
        }
        None
    }

    /// Report a cycle across every span involved.
    ///
    /// This is what `Diagnostic::secondary` exists for. A causality cycle is inherently
    /// multi-site — `a` depends on `b` and `b` on `a` is a fact about two declarations — and
    /// demoting the second to a note would lose the line and column that make it fixable.
    fn report_cycle(&mut self, id: ReactorId, cycle: &[usize]) {
        let reactor = &self.program.reactors[id.index()];
        let names: Vec<String> = cycle
            .iter()
            .map(|node| reactor.nodes[*node].name.clone())
            .collect();
        let spans: Vec<(Span, String)> = cycle[..cycle.len() - 1]
            .iter()
            .enumerate()
            .map(|(step, node)| {
                let node = &reactor.nodes[*node];
                (
                    node.span,
                    format!("`{}` depends on `{}`", node.name, names[step + 1]),
                )
            })
            .collect();

        let mut spans = spans.into_iter();
        let (head_span, head_label) = spans.next().expect("a cycle has at least one step");
        let mut diagnostic = Diagnostic::new(
            head_span,
            format!("instantaneous causality cycle {}", names.join(" → ")),
        )
        .label(head_label);
        for (span, label) in spans {
            diagnostic = diagnostic.secondary(span, label);
        }
        self.push(diagnostic.note(
            "a signal is its expression, so a cycle among signals has no value to settle on",
        ).note(
            "break it with a `state` cell: state is the temporal boundary a feedback loop has to cross",
        ));
    }

    fn capacity(&mut self, expr: &ast::Expr) -> usize {
        match expr.kind {
            ast::ExprKind::Int(value) if value > 0 => value as usize,
            ast::ExprKind::Int(_) => {
                self.push(
                    Diagnostic::new(expr.span, "a capacity must be positive")
                        .label("nothing could ever be queued")
                        .note("a mailbox that holds nothing is an input nothing can reach"),
                );
                1
            }
            _ => {
                self.push(
                    Diagnostic::new(expr.span, "a capacity must be an integer literal")
                        .label("not a literal")
                        .note("the bound is part of the reactor's shape, so it is known before anything runs"),
                );
                1
            }
        }
    }

    fn overflow(&mut self, name: &ast::Ident) -> Overflow {
        match Overflow::from_name(&name.name) {
            Some(overflow) => overflow,
            None => {
                let known: Vec<&str> = Overflow::ALL.iter().map(|o| o.name()).collect();
                self.push(
                    Diagnostic::new(
                        name.span,
                        format!("unknown overflow policy `{}`", name.name),
                    )
                    .label("not a policy v0 knows")
                    .note(format!("the vocabulary is fixed: {}", known.join(", "))),
                );
                Overflow::Reject
            }
        }
    }

    // ---------------------------------------------------------------- types

    fn resolve_ty(&mut self, ty: &ast::Type) -> Ty {
        match &ty.kind {
            ast::TypeKind::Unit => Ty::Unit,
            // A borrow is transparent in v0. The distinction becomes real in M4, when ownership
            // arrives; until then `&T` and `T` denote the same values.
            ast::TypeKind::Ref { inner, .. } => self.resolve_ty(inner),
            ast::TypeKind::Path { path, args } => {
                if path.segments.len() != 1 {
                    self.error(path.span, format!("unknown type `{}`", path.text()));
                    return Ty::Error;
                }
                let name = &path.last().name;
                match name.as_str() {
                    "Option" => {
                        return match self.type_args(name, args, 1, ty.span) {
                            Some(mut args) => Ty::Option(Box::new(args.remove(0))),
                            None => Ty::Error,
                        };
                    }
                    "Result" => {
                        return match self.type_args(name, args, 2, ty.span) {
                            Some(mut args) => {
                                let ok = args.remove(0);
                                let err = args.remove(0);
                                Ty::Result(Box::new(ok), Box::new(err))
                            }
                            None => Ty::Error,
                        };
                    }
                    "Task" => {
                        return match self.type_args(name, args, 1, ty.span) {
                            Some(mut args) => Ty::Task(Box::new(args.remove(0))),
                            None => Ty::Error,
                        };
                    }
                    // A signal's own type has no spelling. Registering the names here is what
                    // turns the attempt into a teaching diagnostic instead of "unknown type", and
                    // it is also why there is no escape check to write: a signal cannot appear in
                    // a field, a parameter, a return type, or a payload, because there is nowhere
                    // to write it down.
                    "Signal" | "Event" => {
                        self.push(
                            Diagnostic::new(
                                ty.span,
                                format!("`{name}` is not a type that can be written"),
                            )
                            .label(format!(
                                "{} lives inside a reactor",
                                if name == "Event" { "an event" } else { "a signal" }
                            ))
                            .note(
                                "declare it as a member — `signal open = …` — and annotate the element type, as in `signal open: I64 = …`",
                            )
                            .note("outside its reactor it is reached through an `export`, and read with `latest`"),
                        );
                        return Ty::Error;
                    }
                    _ => {}
                }
                if !args.is_empty() {
                    self.push(
                        Diagnostic::new(ty.span, format!("`{name}` takes no type arguments"))
                            .note("user-defined generics arrive after M6; see BOOTSTRAP.md §8"),
                    );
                    return Ty::Error;
                }
                match self.types.get(name) {
                    Some(TypeName::Builtin(ty)) => ty.clone(),
                    Some(TypeName::Record(id)) => Ty::Record(*id),
                    Some(TypeName::Enum(id)) => Ty::Enum(*id),
                    Some(TypeName::Reactor(id)) => Ty::Reactor(*id),
                    None => {
                        self.error(path.span, format!("unknown type `{name}`"));
                        Ty::Error
                    }
                }
            }
        }
    }

    fn type_args(
        &mut self,
        name: &str,
        args: &[ast::Type],
        want: usize,
        span: Span,
    ) -> Option<Vec<Ty>> {
        if args.len() != want {
            let plural = if want == 1 { "argument" } else { "arguments" };
            self.push(
                Diagnostic::new(
                    span,
                    format!("`{name}` takes {want} type {plural}, found {}", args.len()),
                )
                .note(match name {
                    "Result" => {
                        "write both, as in `Result<Config, LoadError>` — there is no default error type"
                    }
                    "Task" => "write the value the task produces, as in `Task<()>`",
                    _ => "write the element type, as in `Option<I64>`",
                }),
            );
            return None;
        }
        Some(args.iter().map(|ty| self.resolve_ty(ty)).collect())
    }

    // ---------------------------------------------------------------- locals

    fn declare_local(&mut self, name: String, ty: Ty, mutable: bool, span: Span) -> LocalId {
        self.declare_role(name, ty, mutable, LocalRole::Ordinary, span)
    }

    fn declare_role(
        &mut self,
        name: String,
        ty: Ty,
        mutable: bool,
        role: LocalRole,
        span: Span,
    ) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalDef {
            name: name.clone(),
            ty,
            mutable,
            role,
            span,
        });
        self.scopes
            .last_mut()
            .expect("a scope is open")
            .push((name, id));
        id
    }

    fn lookup_local(&self, name: &str) -> Option<LocalId> {
        self.scopes.iter().rev().find_map(|scope| {
            scope
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, id)| *id)
        })
    }

    // ---------------------------------------------------------------- expressions

    /// Report a mismatch unless `found` fits `expected`.
    fn expect(&mut self, found: Expr, expected: Option<&Ty>, span: Span) -> Expr {
        if let Some(expected) = expected
            && !found.ty.fits(expected)
        {
            // A task where its own result was wanted is a missing `await`, and saying so is worth
            // more than reporting the shapes that differ.
            if let Ty::Task(produced) = &found.ty
                && produced.fits(expected)
            {
                self.discarded_task(span);
                return self.error_expr(span);
            }
            let message = format!(
                "expected {}, found {}",
                self.program.ty_name(expected),
                self.program.ty_name(&found.ty)
            );
            self.error(span, message);
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        found
    }

    fn check_expr(&mut self, expr: &ast::Expr, expected: Option<&Ty>) -> Expr {
        let span = expr.span;
        let checked = match &expr.kind {
            ast::ExprKind::Unit => Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span,
            },
            ast::ExprKind::Int(v) => Expr {
                kind: ExprKind::Int(*v),
                ty: Ty::I64,
                span,
            },
            ast::ExprKind::Float(v) => Expr {
                kind: ExprKind::Float(*v),
                ty: Ty::F64,
                span,
            },
            ast::ExprKind::Str(v) => Expr {
                kind: ExprKind::Str(v.clone()),
                ty: Ty::Str,
                span,
            },
            ast::ExprKind::Bool(v) => Expr {
                kind: ExprKind::Bool(*v),
                ty: Ty::Bool,
                span,
            },
            ast::ExprKind::Path(path) => self.check_path(path),
            ast::ExprKind::Field { base, name } => {
                let base = self.check_expr(base, None);
                self.field_access(base, name, span)
            }
            ast::ExprKind::Unary { op, expr: inner } => self.check_unary(*op, inner, span),
            ast::ExprKind::Binary { op, lhs, rhs } => self.check_binary(*op, lhs, rhs, span),
            ast::ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.check_call(callee, type_args, args, span),
            ast::ExprKind::Construct { path, args } => {
                self.check_construct(path, args, expected, span)
            }
            ast::ExprKind::Block(block) => self.check_block(block, expected, span),
            ast::ExprKind::If { cond, then, els } => self.check_if(cond, then, els, expected, span),
            ast::ExprKind::Match { scrutinee, arms } => {
                self.check_match(scrutinee, arms, expected, span)
            }
            ast::ExprKind::Try(inner) => self.check_try(inner, span),
            ast::ExprKind::Index { .. } => {
                self.push(
                    Diagnostic::new(span, "indexing is not available yet")
                        .note("collections arrive with the standard library"),
                );
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
            ast::ExprKind::Await(inner) => self.check_await(inner, span),
            ast::ExprKind::Scope(block) => self.check_scope(block, expected, span),
            ast::ExprKind::Spawn(inner) => self.check_spawn(inner, span),
            ast::ExprKind::SpawnReactor { path, args } => {
                self.check_spawn_reactor(path, args, span)
            }
            ast::ExprKind::Lambda { .. } => {
                self.push(
                    Diagnostic::new(span, "functions are not values yet")
                        .label("lambda")
                        .note("nothing in v0 needs one: the reactor surface is `input`, `state`, `signal`, and `on`, and closures arrive with the dynamic subgraphs of M7"),
                );
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
        };
        // A construct that consulted the expectation itself has already reported any mismatch.
        if matches!(checked.kind, ExprKind::Error) {
            return checked;
        }
        self.expect(checked, expected, span)
    }

    // ---------------------------------------------------------------- tasks

    fn error_expr(&self, span: Span) -> Expr {
        Expr {
            kind: ExprKind::Error,
            ty: Ty::Error,
            span,
        }
    }

    /// Whether the running function may create a task at all, and whether it declared the authority
    /// the task it is creating needs. Both questions belong here, at the point of creation: once a
    /// `Task<T>` is a value, nothing downstream can tell what it will do.
    fn require_task_authority(&mut self, what: &str, needs: &[Capability], span: Span) -> bool {
        if !self.ctx.builds_tasks() {
            if self.ctx.in_turn() {
                self.impure(what, "builds a task", span);
                return false;
            }
            let message = format!(
                "only a `task fn` can create a task, and `{}` is not one",
                self.fn_name
            );
            self.push(
                Diagnostic::new(span, message)
                    .label(format!("`{what}` builds a task"))
                    .note("mark the enclosing function `task fn`"),
            );
            return false;
        }
        let mut authorised = true;
        for capability in needs {
            if !self.uses.contains(capability) {
                let message = format!(
                    "`{}` does not declare the capability `{}`",
                    self.fn_name,
                    capability.name()
                );
                self.push(
                    Diagnostic::new(span, message)
                        .label(format!("`{what}` uses it"))
                        .note("a task's `uses { … }` set must cover every task it creates")
                        .note(format!(
                            "add it: `uses {{ {} }}`",
                            self.uses
                                .iter()
                                .chain(std::iter::once(capability))
                                .map(|c| c.name())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )),
                );
                authorised = false;
            }
        }
        authorised
    }

    /// A task that is built and dropped does nothing at all, which is the obvious first bug
    /// laziness invites. It is worth a diagnostic rather than a silent no-op.
    fn discarded_task(&mut self, span: Span) {
        self.push(
            Diagnostic::new(span, "this builds a task and then discards it")
                .label("the task never runs")
                .note("`await` it to run it here, or `spawn` it to run it in a scope"),
        );
    }

    fn check_await(&mut self, inner: &ast::Expr, span: Span) -> Expr {
        if self.ctx.in_turn() {
            self.impure("await", "suspends", span);
            return self.error_expr(span);
        }
        if !self.ctx.suspends() {
            self.push(
                Diagnostic::new(span, "`await` is only available inside a `task fn`")
                    .label("only a task may suspend")
                    .note("mark the enclosing function `task fn`"),
            );
            return self.error_expr(span);
        }
        // The operand synthesises rather than being checked against `Task<expected>`. Every task
        // value in v0 comes from a call, which knows its own type, and synthesising lets `await`
        // report what it was actually handed instead of a shape mismatch two layers down.
        let task = self.check_expr(inner, None);
        if task.ty.is_error() {
            return self.error_expr(span);
        }
        let Ty::Task(produced) = &task.ty else {
            let message = format!(
                "`await` applies to a task, not {}",
                self.program.ty_name(&task.ty)
            );
            self.push(
                Diagnostic::new(span, message)
                    .label("not a task")
                    .note("a task comes from calling a `task fn`, and nothing else in v0"),
            );
            return self.error_expr(span);
        };
        let ty = (**produced).clone();
        Expr {
            kind: ExprKind::Await {
                expr: Box::new(task),
            },
            ty,
            span,
        }
    }

    fn check_scope(&mut self, block: &ast::Block, expected: Option<&Ty>, span: Span) -> Expr {
        if self.ctx.in_turn() {
            self.impure("scope", "starts tasks", span);
            return self.error_expr(span);
        }
        if !self.ctx.suspends() {
            self.push(
                Diagnostic::new(span, "a `scope` is only available inside a `task fn`")
                    .label("only a task may start other tasks")
                    .note("mark the enclosing function `task fn`"),
            );
            return self.error_expr(span);
        }
        self.scope_depth += 1;
        let body = self.check_block(block, expected, block.span);
        self.scope_depth -= 1;
        let ty = body.ty.clone();
        Expr {
            kind: ExprKind::Scope {
                body: Box::new(body),
            },
            ty,
            span,
        }
    }

    fn check_spawn(&mut self, inner: &ast::Expr, span: Span) -> Expr {
        if self.ctx.in_turn() {
            self.impure("spawn", "starts a task", span);
            return self.error_expr(span);
        }
        if !self.ctx.suspends() {
            self.push(
                Diagnostic::new(span, "`spawn` is only available inside a `task fn`")
                    .label("only a task may start other tasks")
                    .note("mark the enclosing function `task fn`"),
            );
            return self.error_expr(span);
        }
        if self.scope_depth == 0 {
            self.push(
                Diagnostic::new(span, "`spawn` must appear inside a `scope`")
                    .label("nothing here would cancel or join it")
                    .note("wrap it in `scope { … }`: a spawned task may not outlive the scope that started it"),
            );
            return self.error_expr(span);
        }
        let task = self.check_expr(inner, None);
        if task.ty.is_error() {
            return self.error_expr(span);
        }
        match &task.ty {
            Ty::Task(produced) if **produced == Ty::Unit => {}
            Ty::Task(produced) => {
                let message = format!(
                    "`spawn` needs a task that produces (), and this one produces {}",
                    self.program.ty_name(produced)
                );
                self.push(
                    Diagnostic::new(span, message)
                        .label("nothing would receive the value")
                        .note("there are no task handles in v0, so a spawned task has to say what happens to its own result"),
                );
                return self.error_expr(span);
            }
            other => {
                let message = format!(
                    "`spawn` applies to a task, not {}",
                    self.program.ty_name(other)
                );
                self.push(Diagnostic::new(span, message).label("not a task"));
                return self.error_expr(span);
            }
        }
        Expr {
            kind: ExprKind::Spawn {
                expr: Box::new(task),
            },
            ty: Ty::Unit,
            span,
        }
    }

    fn check_path(&mut self, path: &ast::Path) -> Expr {
        let span = path.span;
        let head = &path.segments[0];
        let Some(local) = self.lookup_local(&head.name) else {
            // Inside a reactor, a name that does not resolve is very often a member that is real
            // but unreadable *here*, and saying which is the whole difference between a diagnostic
            // that teaches the rule and one that looks like a typo.
            if let Some(sort) = self.members.get(&head.name).copied() {
                self.unreadable_member(&head.name, sort, span);
                return self.error_expr(span);
            }
            if path.segments.len() == 1 && self.fns.contains_key(&head.name) {
                self.push(
                    Diagnostic::new(span, "functions are not values yet")
                        .label(format!("`{}` can only be called", head.name))
                        .note("first-class functions arrive with closures in M7"),
                );
            } else {
                self.error(span, format!("unknown name `{}`", head.name));
            }
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };

        // A dotted expression is a local followed by field projections. Deciding that here is what
        // lets the grammar keep `a.b.c` as one node.
        let mut expr = Expr {
            kind: ExprKind::Local(local),
            ty: self.locals[local.index()].ty.clone(),
            span: head.span,
        };
        for segment in &path.segments[1..] {
            expr = self.field_access(expr, segment, head.span.to(segment.span));
        }
        expr
    }

    /// A reactor member that exists but is not in scope where it was written.
    fn unreadable_member(&mut self, name: &str, sort: Sort, span: Span) {
        if sort == Sort::Signal && self.assigning {
            self.push(
                Diagnostic::new(
                    span,
                    format!("`{name}` is a signal, and a signal is never assigned"),
                )
                .label("derived, not stored")
                .note("a signal *is* its expression; two definitions of one value is what assigning to it would mean")
                .note("to make it settable, declare it as `state` and assign it here instead"),
            );
            return;
        }
        let diagnostic = match sort {
            // The rule that is absolute rather than explained. A handler runs *before*
            // propagation, so a signal read there would quietly mean last turn's value — and a
            // language whose central claim is glitch freedom should not have a way to read a
            // stale value that looks exactly like reading a fresh one.
            Sort::Signal => Diagnostic::new(
                span,
                format!("an `on` handler cannot read the signal `{name}`"),
            )
            .label("signals are recomputed after the handler runs")
            .note("reading it here would mean the previous turn's value, which is never what was meant")
            .note("compute the condition from state, or move the decision into a signal of its own"),
            Sort::Input => Diagnostic::new(span, format!("`{name}` is an input, not a value"))
                .label("an input is a mailbox")
                .note("respond to it with `on {name}(…) {{ … }}`; a node body cannot read one"),
            Sort::Param | Sort::State => {
                Diagnostic::new(span, format!("`{name}` is not in scope here"))
                    .label(format!("a reactor {}", sort.describe()))
            }
        };
        self.push(diagnostic);
    }

    fn field_access(&mut self, base: Expr, name: &ast::Ident, span: Span) -> Expr {
        if base.ty.is_error() {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        // A reactor handle has no fields, but it does have members, and `gate.opened` is how one is
        // named from outside. Inputs and exported signals are the only two that have a spelling
        // there: an unexported signal is reactor-private, which is what `export` is for.
        if let Ty::Reactor(id) = base.ty {
            let reactor = &self.program.reactors[id.index()];
            if let Some(index) = reactor.input(&name.name) {
                let ty = Ty::Input(Box::new(reactor.inputs[index].ty.clone()));
                return Expr {
                    kind: ExprKind::ReactorInput {
                        reactor: Box::new(base),
                        index,
                    },
                    ty,
                    span,
                };
            }
            if let Some(index) = reactor
                .exports
                .iter()
                .position(|node| reactor.nodes[node.index()].name == name.name)
            {
                let ty = Ty::Signal(Box::new(
                    reactor.nodes[reactor.exports[index].index()].ty.clone(),
                ));
                return Expr {
                    kind: ExprKind::ReactorExport {
                        reactor: Box::new(base),
                        index,
                    },
                    ty,
                    span,
                };
            }
            let reactor_name = reactor.name.clone();
            let private = reactor
                .node(&name.name)
                .is_some_and(|node| !reactor.nodes[node.index()].exported);
            let mut diagnostic = Diagnostic::new(
                name.span,
                format!(
                    "`{reactor_name}` has no input or exported signal `{}`",
                    name.name
                ),
            );
            diagnostic = if private {
                diagnostic.label("declared, but not exported").note(format!(
                    "write `export signal {}` to make it readable from outside",
                    name.name
                ))
            } else {
                diagnostic.label("unknown member")
            };
            self.push(diagnostic);
            return self.error_expr(span);
        }

        let Ty::Record(id) = base.ty else {
            let message = format!("{} has no fields", self.program.ty_name(&base.ty));
            self.push(
                Diagnostic::new(span, message).label(format!("`{}` accessed here", name.name)),
            );
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let Some((index, field)) = self.program.records[id.index()].field(&name.name) else {
            let record = self.program.records[id.index()].name.clone();
            self.push(
                Diagnostic::new(
                    name.span,
                    format!("`{record}` has no field `{}`", name.name),
                )
                .label("unknown field"),
            );
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let ty = field.ty.clone();
        Expr {
            kind: ExprKind::Field {
                base: Box::new(base),
                index,
            },
            ty,
            span,
        }
    }

    fn check_unary(&mut self, op: ast::UnOp, inner: &ast::Expr, span: Span) -> Expr {
        // `&` and `&mut` are transparent until M4 introduces ownership.
        if matches!(op, ast::UnOp::Ref | ast::UnOp::RefMut) {
            return self.check_expr(inner, None);
        }
        let inner = self.check_expr(inner, None);
        if inner.ty.is_error() {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let (hir_op, ty) = match (op, &inner.ty) {
            (ast::UnOp::Neg, Ty::I64) => (UnOp::Neg, Ty::I64),
            (ast::UnOp::Neg, Ty::F64) => (UnOp::Neg, Ty::F64),
            (ast::UnOp::Not, Ty::Bool) => (UnOp::Not, Ty::Bool),
            (op, ty) => {
                let message = format!(
                    "`{}` does not apply to {}",
                    op.text().trim(),
                    self.program.ty_name(ty)
                );
                self.error(span, message);
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
        };
        Expr {
            kind: ExprKind::Unary {
                op: hir_op,
                expr: Box::new(inner),
            },
            ty,
            span,
        }
    }

    fn check_binary(
        &mut self,
        op: ast::BinOp,
        lhs: &ast::Expr,
        rhs: &ast::Expr,
        span: Span,
    ) -> Expr {
        if matches!(op, ast::BinOp::And | ast::BinOp::Or) {
            let lhs = self.check_expr(lhs, Some(&Ty::Bool));
            let rhs = self.check_expr(rhs, Some(&Ty::Bool));
            return Expr {
                kind: ExprKind::ShortCircuit {
                    and: op == ast::BinOp::And,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                ty: Ty::Bool,
                span,
            };
        }

        let lhs = self.check_expr(lhs, None);
        let rhs = self.check_expr(rhs, Some(&lhs.ty));
        if lhs.ty.is_error() || rhs.ty.is_error() {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }

        use ast::BinOp as A;
        let operand = &lhs.ty;
        let resolved = match op {
            A::Add => match operand {
                Ty::I64 => Some((BinOp::AddInt, Ty::I64)),
                Ty::F64 => Some((BinOp::AddFloat, Ty::F64)),
                Ty::Str => Some((BinOp::Concat, Ty::Str)),
                _ => None,
            },
            A::Sub => match operand {
                Ty::I64 => Some((BinOp::SubInt, Ty::I64)),
                Ty::F64 => Some((BinOp::SubFloat, Ty::F64)),
                _ => None,
            },
            A::Mul => match operand {
                Ty::I64 => Some((BinOp::MulInt, Ty::I64)),
                Ty::F64 => Some((BinOp::MulFloat, Ty::F64)),
                _ => None,
            },
            A::Div => match operand {
                Ty::I64 => Some((BinOp::DivInt, Ty::I64)),
                Ty::F64 => Some((BinOp::DivFloat, Ty::F64)),
                _ => None,
            },
            A::Rem => match operand {
                Ty::I64 => Some((BinOp::RemInt, Ty::I64)),
                Ty::F64 => Some((BinOp::RemFloat, Ty::F64)),
                _ => None,
            },
            A::Eq | A::Ne => match operand {
                Ty::I64 | Ty::F64 | Ty::Bool | Ty::Str => {
                    Some((if op == A::Eq { BinOp::Eq } else { BinOp::Ne }, Ty::Bool))
                }
                _ => None,
            },
            A::Lt | A::Le | A::Gt | A::Ge => match operand {
                Ty::I64 | Ty::F64 | Ty::Str => {
                    let hir_op = match op {
                        A::Lt => BinOp::Lt,
                        A::Le => BinOp::Le,
                        A::Gt => BinOp::Gt,
                        _ => BinOp::Ge,
                    };
                    Some((hir_op, Ty::Bool))
                }
                _ => None,
            },
            A::And | A::Or => unreachable!("handled above"),
        };

        let Some((hir_op, ty)) = resolved else {
            let message = format!(
                "`{}` does not apply to {}",
                op.text(),
                self.program.ty_name(operand)
            );
            let mut diagnostic = Diagnostic::new(span, message);
            if matches!(op, A::Eq | A::Ne) {
                diagnostic = diagnostic.note(
                    "structural equality on records and enums is not derived yet; match instead",
                );
            }
            self.push(diagnostic);
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        Expr {
            kind: ExprKind::Binary {
                op: hir_op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty,
            span,
        }
    }

    fn check_call(
        &mut self,
        callee: &ast::Expr,
        type_args: &[ast::Type],
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
        if !type_args.is_empty() {
            self.push(
                Diagnostic::new(span, "explicit type arguments are not available yet")
                    .note("generics arrive after M6; see BOOTSTRAP.md §8"),
            );
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let ast::ExprKind::Path(path) = &callee.kind else {
            self.push(
                Diagnostic::new(callee.span, "only a named function can be called")
                    .note("methods and function values arrive with M7; a reactor's members are reached as `handle.member`, and nothing else has any"),
            );
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        if path.segments.len() != 1 {
            self.error(path.span, format!("unknown function `{}`", path.text()));
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let name = &path.last().name;

        if let Some(builtin) = Builtin::from_name(name) {
            return self.check_builtin(builtin, args, span);
        }

        let Some(&id) = self.fns.get(name) else {
            self.error(path.span, format!("unknown function `{name}`"));
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let (params, ret) = self.signatures[id.index()].clone();
        let param_names: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
        let Some(order) = self.argument_order(&param_names, args, name, "parameter", span) else {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };

        let mut checked = Vec::with_capacity(params.len());
        for (index, (_, ty)) in params.iter().enumerate() {
            let arg = &args[order[index]];
            checked.push(self.check_expr(&arg.value, Some(ty)));
        }

        // Calling a `task fn` builds a task; it does not run one. That is why the capability check
        // happens here rather than at the `await`.
        let ty = if self.program.fns[id.index()].is_task {
            let needs = self.program.fns[id.index()].uses.clone();
            self.require_task_authority(name, &needs, span);
            Ty::Task(Box::new(ret))
        } else {
            ret
        };
        Expr {
            kind: ExprKind::Call {
                callee: id,
                args: checked,
            },
            ty,
            span,
        }
    }

    fn check_builtin(&mut self, builtin: Builtin, args: &[ast::Arg], span: Span) -> Expr {
        let (params, ret) = builtin.signature();
        let name = builtin.name();
        // Purity is asked before anything else, because the answer does not depend on the
        // arguments and the diagnostic should be about the call rather than about a type.
        if self.ctx.in_turn() && !builtin.is_pure() {
            self.impure(name, "is something the world can see happen", span);
            return self.error_expr(span);
        }
        if args.len() != params.len() || args.iter().any(|arg| arg.name.is_some()) {
            let message = format!(
                "`{name}` takes {} positional argument{}",
                params.len(),
                if params.len() == 1 { "" } else { "s" }
            );
            self.error(span, message);
            return self.error_expr(span);
        }
        if builtin.is_task() && !self.require_task_authority(name, builtin.capabilities(), span) {
            return self.error_expr(span);
        }
        // `send` and `latest` are typed by what they are handed rather than by a signature, the
        // way `print` is. Both take a member of a running reactor, which is the only way to name
        // one from outside — there is no method resolution in v0, so the handle table is closed
        // and these two are the whole of it.
        match builtin {
            Builtin::Send => return self.check_send(args, span),
            Builtin::Latest => return self.check_latest(args, span),
            _ => {}
        }

        let mut checked = Vec::with_capacity(params.len());
        for (arg, param) in args.iter().zip(&params) {
            // `print` is the one builtin that takes a value of any type at all, spelled as an
            // expectation of `Ty::Error`, which every type fits.
            let wanted = if param.is_error() { None } else { Some(param) };
            checked.push(self.check_expr(&arg.value, wanted));
        }
        Expr {
            kind: ExprKind::Builtin {
                builtin,
                args: checked,
            },
            ty: ret,
            span,
        }
    }

    /// `send(gate.opened, message)` — put a message in a reactor's mailbox.
    ///
    /// It builds a task rather than doing it, because a `wait` mailbox that is full suspends the
    /// sender, and one spelling should not sometimes suspend and sometimes not.
    fn check_send(&mut self, args: &[ast::Arg], span: Span) -> Expr {
        let target = self.check_expr(&args[0].value, None);
        if target.ty.is_error() {
            return self.error_expr(span);
        }
        let Ty::Input(message) = target.ty.clone() else {
            let message = format!(
                "`send` needs an input of a reactor, not {}",
                self.program.ty_name(&target.ty)
            );
            self.push(
                Diagnostic::new(args[0].span, message)
                    .label("not an input")
                    .note("name one on a handle, as in `send(gate.opened, ())`"),
            );
            return self.error_expr(span);
        };
        let value = self.check_expr(&args[1].value, Some(&message));
        Expr {
            kind: ExprKind::Builtin {
                builtin: Builtin::Send,
                args: vec![target, value],
            },
            ty: Ty::Task(Box::new(Ty::Unit)),
            span,
        }
    }

    /// `latest(gate.snapshot)` — the last published value of an exported signal.
    ///
    /// It does not enter the reactor and does not wait for one: what it returns is a version that
    /// was stable when it was published. A read synchronised with the reactor's own turn is a
    /// stronger thing that `DESIGN.md` §14 leaves open.
    fn check_latest(&mut self, args: &[ast::Arg], span: Span) -> Expr {
        let target = self.check_expr(&args[0].value, None);
        if target.ty.is_error() {
            return self.error_expr(span);
        }
        let Ty::Signal(element) = target.ty.clone() else {
            let message = format!(
                "`latest` needs an exported signal, not {}",
                self.program.ty_name(&target.ty)
            );
            self.push(
                Diagnostic::new(args[0].span, message)
                    .label("not a signal")
                    .note("name one on a handle, as in `latest(gate.snapshot)`"),
            );
            return self.error_expr(span);
        };
        Expr {
            kind: ExprKind::Builtin {
                builtin: Builtin::Latest,
                args: vec![target],
            },
            ty: *element,
            span,
        }
    }

    /// `spawn reactor Gate(limit: 8)`.
    ///
    /// The reactor is owned by the scope that started it, exactly as a spawned task is, and the
    /// capability check is the same one a task gets: authority is checked where the thing that
    /// will use it is created, because afterwards nothing can tell what a handle will do.
    fn check_spawn_reactor(&mut self, path: &ast::Path, args: &[ast::Arg], span: Span) -> Expr {
        if self.ctx.in_turn() {
            self.impure("spawn reactor", "creates a reactor", span);
            return self.error_expr(span);
        }
        if !self.ctx.suspends() {
            self.push(
                Diagnostic::new(span, "`spawn reactor` is only available inside a `task fn`")
                    .label("only a task may own a reactor")
                    .note("mark the enclosing function `task fn`"),
            );
            return self.error_expr(span);
        }
        if self.scope_depth == 0 {
            self.push(
                Diagnostic::new(span, "`spawn reactor` must appear inside a `scope`")
                    .label("nothing here would cancel it")
                    .note("wrap it in `scope { … }`: a reactor may not outlive the scope that started it"),
            );
            return self.error_expr(span);
        }
        let name = path.text();
        let Some(&id) = self.reactors.get(&name) else {
            self.push(
                Diagnostic::new(path.span, format!("unknown reactor `{name}`"))
                    .label("not a reactor"),
            );
            return self.error_expr(span);
        };

        let params = self.program.reactors[id.index()].params.clone();
        let names: Vec<String> = params.iter().map(|(name, _)| name.clone()).collect();
        let Some(order) = self.argument_order(&names, args, &name, "parameter", span) else {
            return self.error_expr(span);
        };
        let mut checked = Vec::with_capacity(params.len());
        for (index, (_, ty)) in params.iter().enumerate() {
            checked.push(self.check_expr(&args[order[index]].value, Some(ty)));
        }

        let needs = self.program.reactors[id.index()].uses.clone();
        self.require_task_authority(&name, &needs, span);
        Expr {
            kind: ExprKind::SpawnReactor {
                reactor: id,
                args: checked,
            },
            ty: Ty::Reactor(id),
            span,
        }
    }

    /// Map declaration order onto the order the arguments were written. Arguments are either all
    /// positional or all named; mixing the two is rejected rather than given a precedence rule.
    fn argument_order(
        &mut self,
        names: &[String],
        args: &[ast::Arg],
        subject: &str,
        noun: &str,
        span: Span,
    ) -> Option<Vec<usize>> {
        let named = args.iter().filter(|a| a.name.is_some()).count();
        if named != 0 && named != args.len() {
            self.push(
                Diagnostic::new(span, "arguments are either all named or all positional").note(
                    "mixing the two forms would need a precedence rule nobody should have to learn",
                ),
            );
            return None;
        }

        if named == 0 {
            if args.len() != names.len() {
                let message = format!(
                    "`{subject}` takes {} {noun}{}, found {}",
                    names.len(),
                    if names.len() == 1 { "" } else { "s" },
                    args.len()
                );
                self.error(span, message);
                return None;
            }
            return Some((0..args.len()).collect());
        }

        let mut order = vec![usize::MAX; names.len()];
        let mut failed = false;
        for (position, arg) in args.iter().enumerate() {
            let name = arg.name.as_ref().expect("all arguments are named");
            let Some(index) = names.iter().position(|n| *n == name.name) else {
                self.push(
                    Diagnostic::new(
                        name.span,
                        format!("`{subject}` has no {noun} named `{}`", name.name),
                    )
                    .label(format!("unknown {noun}")),
                );
                failed = true;
                continue;
            };
            if order[index] != usize::MAX {
                self.error(name.span, format!("`{}` is given twice", name.name));
                failed = true;
                continue;
            }
            order[index] = position;
        }
        let missing: Vec<&str> = order
            .iter()
            .enumerate()
            .filter(|(_, p)| **p == usize::MAX)
            .map(|(i, _)| names[i].as_str())
            .collect();
        if !missing.is_empty() {
            let message = format!(
                "missing {noun}{}: {}",
                if missing.len() == 1 { "" } else { "s" },
                missing.join(", ")
            );
            self.error(span, message);
            failed = true;
        }
        if failed { None } else { Some(order) }
    }

    fn check_construct(
        &mut self,
        path: &ast::Path,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        // The built-in constructors need the expectation to supply the argument they cannot see.
        if path.segments.len() == 1 {
            match path.last().name.as_str() {
                "None" | "Some" => return self.check_option(path, args, expected, span),
                "Ok" | "Err" => return self.check_result(path, args, expected, span),
                _ => {}
            }
        }

        match path.segments.len() {
            1 => {
                let name = &path.last().name;
                match self.types.get(name) {
                    Some(TypeName::Record(id)) => {
                        let id = *id;
                        self.construct_record(id, args, span)
                    }
                    Some(TypeName::Enum(_)) => {
                        self.push(
                            Diagnostic::new(span, format!("`{name}` is an enum"))
                                .note("name the variant too, as in `#LoadError.NotFound`"),
                        );
                        Expr {
                            kind: ExprKind::Error,
                            ty: Ty::Error,
                            span,
                        }
                    }
                    _ => {
                        self.error(span, format!("unknown record `{name}`"));
                        Expr {
                            kind: ExprKind::Error,
                            ty: Ty::Error,
                            span,
                        }
                    }
                }
            }
            2 => {
                let enum_name = &path.segments[0].name;
                let variant_name = &path.segments[1].name;
                let Some(TypeName::Enum(id)) = self.types.get(enum_name) else {
                    self.error(path.segments[0].span, format!("unknown enum `{enum_name}`"));
                    return Expr {
                        kind: ExprKind::Error,
                        ty: Ty::Error,
                        span,
                    };
                };
                let id = *id;
                let Some((index, _)) = self.program.enums[id.index()].variant(variant_name) else {
                    let message = format!("`{enum_name}` has no variant `{variant_name}`");
                    self.push(
                        Diagnostic::new(path.segments[1].span, message).label("unknown variant"),
                    );
                    return Expr {
                        kind: ExprKind::Error,
                        ty: Ty::Error,
                        span,
                    };
                };
                self.construct_variant(id, index, args, Ty::Enum(id), span)
            }
            _ => {
                self.error(span, format!("unknown constructor `{}`", path.text()));
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
        }
    }

    fn check_option(
        &mut self,
        path: &ast::Path,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let some = path.last().name == "Some";
        let inner_expected = match expected {
            Some(Ty::Option(inner)) => Some((**inner).clone()),
            Some(other) if !other.is_error() => {
                let message = format!("expected {}, found Option", self.program.ty_name(other));
                self.error(span, message);
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
            _ => None,
        };

        if !some {
            if !args.is_empty() {
                self.error(span, "`#None` takes no arguments");
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
            let Some(inner) = inner_expected else {
                return self.uninferable(span, "#None", "Option<I64>");
            };
            return Expr {
                kind: ExprKind::Construct {
                    ctor: Ctor::Variant(EnumId::OPTION, EnumId::NONE),
                    args: Vec::new(),
                },
                ty: Ty::Option(Box::new(inner)),
                span,
            };
        }

        if args.len() != 1 || args[0].name.is_some() {
            self.error(span, "`#Some` takes one positional argument");
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let value = self.check_expr(&args[0].value, inner_expected.as_ref());
        let inner = inner_expected.unwrap_or_else(|| value.ty.clone());
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Variant(EnumId::OPTION, EnumId::SOME),
                args: vec![value],
            },
            ty: Ty::Option(Box::new(inner)),
            span,
        }
    }

    fn check_result(
        &mut self,
        path: &ast::Path,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let is_ok = path.last().name == "Ok";
        let parts = match expected {
            Some(Ty::Result(ok, err)) => Some(((**ok).clone(), (**err).clone())),
            Some(other) if !other.is_error() => {
                let message = format!("expected {}, found Result", self.program.ty_name(other));
                self.error(span, message);
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
            _ => None,
        };

        let name = if is_ok { "#Ok" } else { "#Err" };
        if args.len() != 1 || args[0].name.is_some() {
            self.error(span, format!("`{name}` takes one positional argument"));
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let side = parts
            .as_ref()
            .map(|(ok, err)| if is_ok { ok.clone() } else { err.clone() });
        let value = self.check_expr(&args[0].value, side.as_ref());

        let (ok, err) = match parts {
            Some(parts) => parts,
            None if is_ok => {
                return self.uninferable(span, name, "Result<I64, LoadError>");
            }
            None => return self.uninferable(span, name, "Result<I64, LoadError>"),
        };
        let variant = if is_ok { EnumId::OK } else { EnumId::ERR };
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Variant(EnumId::RESULT, variant),
                args: vec![value],
            },
            ty: Ty::Result(Box::new(ok), Box::new(err)),
            span,
        }
    }

    fn uninferable(&mut self, span: Span, what: &str, example: &str) -> Expr {
        self.push(
            Diagnostic::new(span, format!("cannot tell what type `{what}` builds here"))
                .label("no expected type at this position")
                .note(format!(
                    "annotate the binding or the return type, as in `let x: {example} = …`"
                )),
        );
        Expr {
            kind: ExprKind::Error,
            ty: Ty::Error,
            span,
        }
    }

    fn construct_record(&mut self, id: RecordId, args: &[ast::Arg], span: Span) -> Expr {
        let record = &self.program.records[id.index()];
        let name = record.name.clone();
        let names: Vec<String> = record.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = record.fields.iter().map(|f| f.ty.clone()).collect();
        let Some(order) = self.argument_order(&names, args, &name, "field", span) else {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let mut checked = Vec::with_capacity(types.len());
        for (index, ty) in types.iter().enumerate() {
            checked.push(self.check_expr(&args[order[index]].value, Some(ty)));
        }
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Record(id),
                args: checked,
            },
            ty: Ty::Record(id),
            span,
        }
    }

    fn construct_variant(
        &mut self,
        id: EnumId,
        index: usize,
        args: &[ast::Arg],
        ty: Ty,
        span: Span,
    ) -> Expr {
        let variant = &self.program.enums[id.index()].variants[index];
        let subject = format!("{}.{}", self.program.enums[id.index()].name, variant.name);
        let names: Vec<String> = variant.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = variant.fields.iter().map(|f| f.ty.clone()).collect();
        let Some(order) = self.argument_order(&names, args, &subject, "field", span) else {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let mut checked = Vec::with_capacity(types.len());
        for (i, field_ty) in types.iter().enumerate() {
            checked.push(self.check_expr(&args[order[i]].value, Some(field_ty)));
        }
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Variant(id, index),
                args: checked,
            },
            ty,
            span,
        }
    }

    // ---------------------------------------------------------------- blocks and control flow

    fn check_block(&mut self, block: &ast::Block, expected: Option<&Ty>, span: Span) -> Expr {
        self.scopes.push(Vec::new());

        // A trailing expression statement is the block's value. Everything before it is a
        // statement whose value is discarded.
        let tail_index = match block.stmts.last() {
            Some(ast::Stmt {
                kind: ast::StmtKind::Expr(_),
                ..
            }) => Some(block.stmts.len() - 1),
            _ => None,
        };

        let mut stmts = Vec::new();
        let mut diverges = false;
        for (index, stmt) in block.stmts.iter().enumerate() {
            if Some(index) == tail_index {
                break;
            }
            let checked = self.check_stmt(stmt);
            if let StmtKind::Expr(expr) | StmtKind::Let { value: expr, .. } = &checked.kind
                && expr.ty == Ty::Never
            {
                diverges = true;
            }
            if let StmtKind::Expr(expr) = &checked.kind
                && matches!(expr.ty, Ty::Task(_))
            {
                self.discarded_task(stmt.span);
            }
            stmts.push(checked);
        }

        let tail = tail_index.map(|index| {
            let ast::StmtKind::Expr(expr) = &block.stmts[index].kind else {
                unreachable!()
            };
            Box::new(self.check_expr(expr, expected))
        });

        self.scopes.pop();

        let ty = match &tail {
            Some(tail) => tail.ty.clone(),
            None if diverges => Ty::Never,
            None => Ty::Unit,
        };
        Expr {
            kind: ExprKind::Block { stmts, tail },
            ty,
            span,
        }
    }

    fn check_stmt(&mut self, stmt: &ast::Stmt) -> Stmt {
        let span = stmt.span;
        let kind = match &stmt.kind {
            ast::StmtKind::Let {
                mutable,
                name,
                ty,
                value,
            } => {
                let declared = ty.as_ref().map(|ty| self.resolve_ty(ty));
                let value = self.check_expr(value, declared.as_ref());
                let ty = declared.unwrap_or_else(|| match &value.ty {
                    Ty::Never => Ty::Unit,
                    ty => ty.clone(),
                });
                let local = self.declare_local(name.name.clone(), ty, *mutable, name.span);
                StmtKind::Let { local, value }
            }
            ast::StmtKind::Assign { target, value } => {
                // Checked as an assignment target, so that a reactor member which is real but not
                // writable here is told it cannot be *written* rather than that it cannot be read.
                self.assigning = true;
                let place = self.check_expr(target, None);
                self.assigning = false;
                self.check_assignable(&place, target.span);
                let value = self.check_expr(value, Some(&place.ty));
                StmtKind::Assign { place, value }
            }
            ast::StmtKind::Return(value) => {
                let ret = self.ret.clone();
                let value = match value {
                    Some(expr) => Some(Box::new(self.check_expr(expr, Some(&ret)))),
                    None => {
                        if !Ty::Unit.fits(&ret) {
                            let message =
                                format!("expected {}, found ()", self.program.ty_name(&ret));
                            self.error(span, message);
                        }
                        None
                    }
                };
                StmtKind::Expr(Expr {
                    kind: ExprKind::Return { value },
                    ty: Ty::Never,
                    span,
                })
            }
            ast::StmtKind::AfterCommit { task, returns } => {
                self.check_after_commit(task, returns.as_ref(), span)
            }
            ast::StmtKind::Expr(expr) => StmtKind::Expr(self.check_expr(expr, None)),
        };
        Stmt { kind, span }
    }

    /// `after_commit deliver(m) -> delivered`.
    ///
    /// The operand is *built* here and started only after the snapshot is published. Building runs
    /// nothing — that is what M2's laziness was for — so describing an effect in the middle of a
    /// turn cannot perform one, and no code path exists by which an effect observes an
    /// intermediate graph.
    fn check_after_commit(
        &mut self,
        task: &ast::Expr,
        returns: Option<&ast::Ident>,
        span: Span,
    ) -> StmtKind {
        if !self.in_handler {
            self.push(
                Diagnostic::new(span, "`after_commit` is only available inside an `on` handler")
                    .label("nothing here commits")
                    .note("a signal derives a value and requests nothing; effects are asked for where state changes"),
            );
            return StmtKind::Expr(self.error_expr(span));
        }

        // `Ctx::Effect` is the one place inside a turn where building a task is allowed. It still
        // may not *run* one, and its argument expressions are still evaluated during the turn, so
        // everything else a turn forbids stays forbidden.
        let outer = self.ctx;
        self.ctx = Ctx::Effect;
        let task = self.check_expr(task, None);
        self.ctx = outer;

        if task.ty.is_error() {
            return StmtKind::Expr(self.error_expr(span));
        }
        let Ty::Task(produced) = task.ty.clone() else {
            let message = format!(
                "`after_commit` describes work to start later, and this is {}",
                self.program.ty_name(&task.ty)
            );
            self.push(
                Diagnostic::new(task.span, message)
                    .label("not a task")
                    .note("call a `task fn`: the call builds the work without running it, which is what lets the snapshot be published first"),
            );
            return StmtKind::Expr(self.error_expr(span));
        };

        let Some(name) = returns else {
            if *produced != Ty::Unit {
                let message = format!(
                    "this effect produces {}, and nothing would receive it",
                    self.program.ty_name(&produced)
                );
                self.push(
                    Diagnostic::new(span, message)
                        .label("the value is dropped")
                        .note("name the input it comes back on: `after_commit … -> handled`"),
                );
                return StmtKind::Expr(self.error_expr(span));
            }
            return StmtKind::AfterCommit {
                task,
                returns: None,
            };
        };

        // A completion re-enters as a later input. That is the whole `EffectResult →
        // ReactorMailbox → a later turn` loop of `DESIGN.md` §2, spelled as one arrow.
        let id = self.reactor.expect("a handler belongs to a reactor");
        let reactor = &self.program.reactors[id.index()];
        let Some(index) = reactor.input(&name.name) else {
            let reactor_name = reactor.name.clone();
            self.push(
                Diagnostic::new(
                    name.span,
                    format!("`{reactor_name}` has no input `{}`", name.name),
                )
                .label("unknown input")
                .note(
                    "an effect's result comes back as a message, so it needs an input to arrive on",
                ),
            );
            return StmtKind::Expr(self.error_expr(span));
        };
        let wanted = reactor.inputs[index].ty.clone();
        if !produced.fits(&wanted) {
            let message = format!(
                "this effect produces {}, but `{}` takes {}",
                self.program.ty_name(&produced),
                name.name,
                self.program.ty_name(&wanted)
            );
            self.push(Diagnostic::new(span, message).label("the result would not fit"));
            return StmtKind::Expr(self.error_expr(span));
        }
        StmtKind::AfterCommit {
            task,
            returns: Some(index),
        }
    }

    /// An assignment target must be a local, or a chain of fields rooted at one, and that local
    /// must be `mut`.
    fn check_assignable(&mut self, place: &Expr, span: Span) {
        let mut cursor = place;
        loop {
            match &cursor.kind {
                ExprKind::Local(id) => {
                    let local = &self.locals[id.index()];
                    if local.mutable {
                        return;
                    }
                    let name = local.name.clone();
                    let diagnostic = match local.role {
                        LocalRole::Signal => {
                            Diagnostic::new(span, format!("`{name}` is a signal, and a signal is never assigned"))
                                .label("derived, not stored")
                                .note("a signal *is* its expression; to make it settable, declare it as `state` and assign it in a handler")
                        }
                        LocalRole::Param => {
                            Diagnostic::new(span, format!("`{name}` is a reactor parameter"))
                                .label("fixed when the reactor was created")
                                .note("declare a `state` cell initialised from it if it needs to change")
                        }
                        LocalRole::State(_) => {
                            Diagnostic::new(span, format!("`{name}` can only be assigned inside an `on` handler"))
                                .label("a node body is pure")
                                .note("state changes are what a handler is for; a signal derives from state rather than setting it")
                        }
                        LocalRole::Message => {
                            Diagnostic::new(span, format!("`{name}` is the message this handler was given"))
                                .label("cannot assign")
                        }
                        LocalRole::Ordinary => {
                            Diagnostic::new(span, format!("`{name}` is not declared `mut`"))
                                .label("cannot assign")
                                .note(format!("declare it as `let mut {name} = …`"))
                        }
                    };
                    self.push(diagnostic);
                    return;
                }
                ExprKind::Field { base, .. } => cursor = base,
                ExprKind::Error => return,
                _ => {
                    self.error(span, "only a variable or one of its fields can be assigned");
                    return;
                }
            }
        }
    }

    fn check_if(
        &mut self,
        cond: &ast::Expr,
        then: &ast::Block,
        els: &Option<Box<ast::Expr>>,
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let cond = self.check_expr(cond, Some(&Ty::Bool));
        let then = self.check_block(then, expected, then.span);
        let els = match els {
            Some(els) => {
                let expected = match expected {
                    Some(ty) => Some(ty.clone()),
                    None if then.ty != Ty::Never => Some(then.ty.clone()),
                    None => None,
                };
                Some(Box::new(self.check_expr(els, expected.as_ref())))
            }
            None => {
                if !then.ty.fits(&Ty::Unit) {
                    let message = format!(
                        "an `if` without an `else` must produce (), found {}",
                        self.program.ty_name(&then.ty)
                    );
                    self.error(span, message);
                }
                None
            }
        };
        let ty = match (&els, &then.ty) {
            (None, _) => Ty::Unit,
            (Some(els), Ty::Never) => els.ty.clone(),
            (Some(_), ty) => ty.clone(),
        };
        Expr {
            kind: ExprKind::If {
                cond: Box::new(cond),
                then: Box::new(then),
                els,
            },
            ty,
            span,
        }
    }

    fn check_match(
        &mut self,
        scrutinee: &ast::Expr,
        arms: &[ast::Arm],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let scrutinee = self.check_expr(scrutinee, None);
        let scrutinee_ty = scrutinee.ty.clone();
        if arms.is_empty() {
            self.error(span, "a `match` needs at least one arm");
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }

        let mut checked = Vec::with_capacity(arms.len());
        let mut result: Option<Ty> = expected.cloned();
        for arm in arms {
            self.scopes.push(Vec::new());
            let pat = self.check_pat(&arm.pat, &scrutinee_ty);
            let guard = arm
                .guard
                .as_ref()
                .map(|g| self.check_expr(g, Some(&Ty::Bool)));
            let body = self.check_expr(&arm.body, result.as_ref());
            self.scopes.pop();
            if result.is_none() && body.ty != Ty::Never && !body.ty.is_error() {
                result = Some(body.ty.clone());
            }
            checked.push(Arm {
                pat,
                guard,
                body,
                span: arm.span,
            });
        }

        self.check_exhaustive(&checked, &scrutinee_ty, span);
        let ty = result.unwrap_or(Ty::Never);
        Expr {
            kind: ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms: checked,
            },
            ty,
            span,
        }
    }

    /// Top-level coverage only: an arm names a variant, or it is irrefutable. Gaps hidden inside a
    /// nested pattern are not detected here and trap at runtime instead — a full usefulness
    /// algorithm can arrive with the rest of the pattern work.
    fn check_exhaustive(&mut self, arms: &[Arm], scrutinee: &Ty, span: Span) {
        if scrutinee.is_error() || *scrutinee == Ty::Never {
            return;
        }

        let mut covered = Vec::new();
        for arm in arms {
            if arm.guard.is_some() {
                continue;
            }
            let mut collect = |pat: &Pat| match &pat.kind {
                PatKind::Wild | PatKind::Bind(_) => covered.push(usize::MAX),
                PatKind::Variant { variant, .. } => covered.push(*variant),
                PatKind::Record { .. } => covered.push(usize::MAX),
                _ => {}
            };
            match &arm.pat.kind {
                PatKind::Or(alts) => alts.iter().for_each(&mut collect),
                _ => collect(&arm.pat),
            }
        }
        if covered.contains(&usize::MAX) {
            return;
        }

        let (enum_id, name) = match scrutinee {
            Ty::Enum(id) => (*id, self.program.enums[id.index()].name.clone()),
            Ty::Option(_) => (EnumId::OPTION, "Option".to_string()),
            Ty::Result(_, _) => (EnumId::RESULT, "Result".to_string()),
            other => {
                let message = format!(
                    "this `match` on {} needs a catch-all arm",
                    self.program.ty_name(other)
                );
                self.push(Diagnostic::new(span, message).note("add `_ => …`"));
                return;
            }
        };

        let missing: Vec<String> = self.program.enums[enum_id.index()]
            .variants
            .iter()
            .enumerate()
            .filter(|(index, _)| !covered.contains(index))
            .map(|(_, variant)| format!("#{name}.{}", variant.name))
            .collect();
        if !missing.is_empty() {
            self.push(
                Diagnostic::new(
                    span,
                    format!("this `match` does not cover {}", missing.join(", ")),
                )
                .label("not exhaustive")
                .note("add the missing arms, or a `_ => …` catch-all"),
            );
        }
    }

    fn check_try(&mut self, inner: &ast::Expr, span: Span) -> Expr {
        let inner = self.check_expr(inner, None);
        if inner.ty.is_error() {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let ret = self.ret.clone();
        match (&inner.ty, &ret) {
            (Ty::Result(ok, err), Ty::Result(_, ret_err)) => {
                if err != ret_err {
                    let message = format!(
                        "this fails with {}, but the function fails with {}",
                        self.program.ty_name(err),
                        self.program.ty_name(ret_err)
                    );
                    self.push(Diagnostic::new(span, message).note(
                        "there is no automatic error conversion; match and rebuild the error",
                    ));
                    return Expr {
                        kind: ExprKind::Error,
                        ty: Ty::Error,
                        span,
                    };
                }
                let ty = (**ok).clone();
                Expr {
                    kind: ExprKind::Try {
                        expr: Box::new(inner),
                        enum_id: EnumId::RESULT,
                    },
                    ty,
                    span,
                }
            }
            (Ty::Option(some), Ty::Option(_)) => {
                let ty = (**some).clone();
                Expr {
                    kind: ExprKind::Try {
                        expr: Box::new(inner),
                        enum_id: EnumId::OPTION,
                    },
                    ty,
                    span,
                }
            }
            (Ty::Result(_, _) | Ty::Option(_), ret) => {
                let message = format!(
                    "`?` needs the function to return the same shape, but it returns {}",
                    self.program.ty_name(ret)
                );
                self.push(Diagnostic::new(span, message).label("cannot propagate here"));
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
            (other, _) => {
                let message = format!(
                    "`?` applies to Result and Option, not {}",
                    self.program.ty_name(other)
                );
                self.error(span, message);
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
        }
    }

    // ---------------------------------------------------------------- patterns

    fn check_pat(&mut self, pat: &ast::Pat, ty: &Ty) -> Pat {
        let span = pat.span;
        match &pat.kind {
            ast::PatKind::Wild => Pat {
                kind: PatKind::Wild,
                span,
            },
            ast::PatKind::Binding(name) => {
                let local = self.declare_local(name.name.clone(), ty.clone(), false, name.span);
                Pat {
                    kind: PatKind::Bind(local),
                    span,
                }
            }
            ast::PatKind::Int(v) => {
                self.expect_pat_ty(&Ty::I64, ty, span);
                Pat {
                    kind: PatKind::Int(*v),
                    span,
                }
            }
            ast::PatKind::Str(v) => {
                self.expect_pat_ty(&Ty::Str, ty, span);
                Pat {
                    kind: PatKind::Str(v.clone()),
                    span,
                }
            }
            ast::PatKind::Bool(v) => {
                self.expect_pat_ty(&Ty::Bool, ty, span);
                Pat {
                    kind: PatKind::Bool(*v),
                    span,
                }
            }
            ast::PatKind::Or(alts) => {
                let checked: Vec<Pat> = alts.iter().map(|alt| self.check_pat(alt, ty)).collect();
                if checked.iter().any(binds_anything) {
                    self.push(
                        Diagnostic::new(span, "an alternative pattern may not bind names yet")
                            .note("each alternative would have to bind the same names; write separate arms"),
                    );
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                }
                Pat {
                    kind: PatKind::Or(checked),
                    span,
                }
            }
            ast::PatKind::Construct { path, args, rest } => {
                self.check_construct_pat(path, args, *rest, ty, span)
            }
        }
    }

    fn expect_pat_ty(&mut self, found: &Ty, expected: &Ty, span: Span) {
        if !found.fits(expected) {
            let message = format!(
                "this pattern matches {}, but the value is {}",
                self.program.ty_name(found),
                self.program.ty_name(expected)
            );
            self.error(span, message);
        }
    }

    fn check_construct_pat(
        &mut self,
        path: &ast::Path,
        args: &[ast::PatArg],
        rest: bool,
        ty: &Ty,
        span: Span,
    ) -> Pat {
        // Resolve the constructor against the type being matched, so `#Some(x)` and `#Ok(x)` need
        // no qualification and pick up their payload type from the scrutinee.
        let resolved = match (path.segments.len(), path.last().name.as_str(), ty) {
            (1, "None", Ty::Option(_)) => Some((EnumId::OPTION, EnumId::NONE, Vec::new())),
            (1, "Some", Ty::Option(inner)) => {
                Some((EnumId::OPTION, EnumId::SOME, vec![(**inner).clone()]))
            }
            (1, "Ok", Ty::Result(ok, _)) => {
                Some((EnumId::RESULT, EnumId::OK, vec![(**ok).clone()]))
            }
            (1, "Err", Ty::Result(_, err)) => {
                Some((EnumId::RESULT, EnumId::ERR, vec![(**err).clone()]))
            }
            _ => None,
        };

        if let Some((enum_id, variant, types)) = resolved {
            let names: Vec<String> = (0..types.len()).map(|i| i.to_string()).collect();
            let name = format!("#{}", path.text());
            let Some(sub) = self.pat_args(&names, &types, args, rest, &name, span) else {
                return Pat {
                    kind: PatKind::Error,
                    span,
                };
            };
            return Pat {
                kind: PatKind::Variant {
                    enum_id,
                    variant,
                    args: sub,
                },
                span,
            };
        }

        match path.segments.len() {
            1 => {
                let name = path.last().name.clone();
                if matches!(name.as_str(), "None" | "Some" | "Ok" | "Err") {
                    let message = format!(
                        "`#{name}` matches Option or Result, but the value is {}",
                        self.program.ty_name(ty)
                    );
                    self.error(span, message);
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                }
                let Some(TypeName::Record(id)) = self.types.get(&name) else {
                    self.error(span, format!("unknown record `{name}`"));
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                let id = *id;
                self.expect_pat_ty(&Ty::Record(id), ty, span);
                let record = &self.program.records[id.index()];
                let names: Vec<String> = record.fields.iter().map(|f| f.name.clone()).collect();
                let types: Vec<Ty> = record.fields.iter().map(|f| f.ty.clone()).collect();
                let Some(sub) = self.pat_args(&names, &types, args, rest, &name, span) else {
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                Pat {
                    kind: PatKind::Record {
                        record: id,
                        args: sub,
                    },
                    span,
                }
            }
            2 => {
                let enum_name = path.segments[0].name.clone();
                let variant_name = path.segments[1].name.clone();
                let Some(TypeName::Enum(id)) = self.types.get(&enum_name) else {
                    self.error(path.segments[0].span, format!("unknown enum `{enum_name}`"));
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                let id = *id;
                self.expect_pat_ty(&Ty::Enum(id), ty, span);
                let Some((index, variant)) = self.program.enums[id.index()].variant(&variant_name)
                else {
                    let message = format!("`{enum_name}` has no variant `{variant_name}`");
                    self.push(
                        Diagnostic::new(path.segments[1].span, message).label("unknown variant"),
                    );
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                let names: Vec<String> = variant.fields.iter().map(|f| f.name.clone()).collect();
                let types: Vec<Ty> = variant.fields.iter().map(|f| f.ty.clone()).collect();
                let subject = format!("{enum_name}.{variant_name}");
                let Some(sub) = self.pat_args(&names, &types, args, rest, &subject, span) else {
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                Pat {
                    kind: PatKind::Variant {
                        enum_id: id,
                        variant: index,
                        args: sub,
                    },
                    span,
                }
            }
            _ => {
                self.error(span, format!("unknown constructor `{}`", path.text()));
                Pat {
                    kind: PatKind::Error,
                    span,
                }
            }
        }
    }

    /// Expand a constructor pattern's arguments to full arity in declaration order, filling the
    /// gaps `..` leaves with wildcards.
    fn pat_args(
        &mut self,
        names: &[String],
        types: &[Ty],
        args: &[ast::PatArg],
        rest: bool,
        subject: &str,
        span: Span,
    ) -> Option<Vec<Pat>> {
        let named = args.iter().filter(|a| a.name.is_some()).count();
        if named != 0 && named != args.len() {
            self.error(
                span,
                "pattern arguments are either all named or all positional",
            );
            return None;
        }

        let mut slots: Vec<Option<&ast::Pat>> = vec![None; names.len()];
        if named == 0 {
            if args.len() > names.len() || (args.len() < names.len() && !rest) {
                let message = format!(
                    "`{subject}` has {} field{}, found {}",
                    names.len(),
                    if names.len() == 1 { "" } else { "s" },
                    args.len()
                );
                let mut diagnostic = Diagnostic::new(span, message);
                if args.len() < names.len() {
                    diagnostic = diagnostic.note("write `..` to ignore the rest");
                }
                self.push(diagnostic);
                return None;
            }
            for (slot, arg) in slots.iter_mut().zip(args) {
                *slot = Some(&arg.pat);
            }
        } else {
            for arg in args {
                let name = arg.name.as_ref().expect("all arguments are named");
                let Some(index) = names.iter().position(|n| *n == name.name) else {
                    self.push(
                        Diagnostic::new(
                            name.span,
                            format!("`{subject}` has no field named `{}`", name.name),
                        )
                        .label("unknown field"),
                    );
                    return None;
                };
                if slots[index].is_some() {
                    self.error(name.span, format!("`{}` is matched twice", name.name));
                    return None;
                }
                slots[index] = Some(&arg.pat);
            }
            if !rest && slots.iter().any(Option::is_none) {
                let missing: Vec<&str> = slots
                    .iter()
                    .enumerate()
                    .filter(|(_, slot)| slot.is_none())
                    .map(|(i, _)| names[i].as_str())
                    .collect();
                self.push(
                    Diagnostic::new(span, format!("missing fields: {}", missing.join(", ")))
                        .note("write `..` to ignore the rest"),
                );
                return None;
            }
        }

        Some(
            slots
                .into_iter()
                .zip(types)
                .map(|(slot, ty)| match slot {
                    Some(pat) => self.check_pat(pat, ty),
                    None => Pat {
                        kind: PatKind::Wild,
                        span,
                    },
                })
                .collect(),
        )
    }
}

/// What the syntactic scan worked out about one reactor.
struct Wiring {
    /// Dependency node indices per node, in the order the lifted function takes them.
    deps: Vec<Vec<usize>>,
    /// A topological order over the whole graph.
    order: Vec<usize>,
    /// Per input, the state nodes its handler assigns.
    writes: Vec<Vec<usize>>,
    /// False when the graph could not be built — a cycle, or a reference that is not a node. The
    /// bodies are then left unchecked rather than reported against a graph that does not exist.
    ok: bool,
}

/// The free names an expression mentions, honouring binders.
///
/// Purely syntactic, and deliberately so. Checking members in declaration order would report
/// `DESIGN.md` §3's flagship error — `signal a = b + 1` / `signal b = a + 1` — as *unknown name
/// `b`*, and that diagnostic is half of what this milestone exists to demonstrate. A scan yields
/// the edges, the cycle, and a topological order before any body is typed; the bodies are then
/// typed *in* that order, so forward references work and the cycle error is the cycle error.
struct Scan<'a> {
    members: &'a HashMap<String, Sort>,
    /// Names bound by enclosing `let`s and patterns, innermost last. A local shadows a member, so
    /// `let open = 1` inside a signal body is not a reference to the signal `open`.
    bound: Vec<Vec<String>>,
    reads: Vec<(String, Span)>,
    writes: Vec<(String, Span)>,
}

impl<'a> Scan<'a> {
    fn new(members: &'a HashMap<String, Sort>) -> Scan<'a> {
        Scan {
            members,
            bound: vec![Vec::new()],
            reads: Vec::new(),
            writes: Vec::new(),
        }
    }

    fn is_bound(&self, name: &str) -> bool {
        self.bound
            .iter()
            .any(|frame| frame.iter().any(|bound| bound == name))
    }

    fn bind(&mut self, name: &str) {
        self.bound
            .last_mut()
            .expect("a frame is open")
            .push(name.to_string());
    }

    fn read(&mut self, name: &str, span: Span) {
        if self.is_bound(name) || !self.members.contains_key(name) {
            return;
        }
        if !self.reads.iter().any(|(seen, _)| seen == name) {
            self.reads.push((name.to_string(), span));
        }
    }

    fn expr(&mut self, expr: &ast::Expr) {
        match &expr.kind {
            ast::ExprKind::Path(path) => {
                let head = &path.segments[0];
                self.read(&head.name, head.span);
            }
            ast::ExprKind::Field { base, .. } => self.expr(base),
            ast::ExprKind::Call { callee, args, .. } => {
                // The callee of a call is a function name, never a member. Scanning it would make
                // a member named like a function into a dependency of everything that calls it.
                if !matches!(callee.kind, ast::ExprKind::Path(_)) {
                    self.expr(callee);
                }
                for arg in args {
                    self.expr(&arg.value);
                }
            }
            ast::ExprKind::Construct { args, .. } | ast::ExprKind::SpawnReactor { args, .. } => {
                for arg in args {
                    self.expr(&arg.value);
                }
            }
            ast::ExprKind::Unary { expr, .. }
            | ast::ExprKind::Await(expr)
            | ast::ExprKind::Spawn(expr)
            | ast::ExprKind::Try(expr) => self.expr(expr),
            ast::ExprKind::Binary { lhs, rhs, .. } => {
                self.expr(lhs);
                self.expr(rhs);
            }
            ast::ExprKind::Index { base, index } => {
                self.expr(base);
                self.expr(index);
            }
            ast::ExprKind::Block(block) | ast::ExprKind::Scope(block) => self.block(block),
            ast::ExprKind::If { cond, then, els } => {
                self.expr(cond);
                self.block(then);
                if let Some(els) = els {
                    self.expr(els);
                }
            }
            ast::ExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.bound.push(Vec::new());
                    self.pat(&arm.pat);
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    self.expr(&arm.body);
                    self.bound.pop();
                }
            }
            ast::ExprKind::Lambda { params, body, .. } => {
                self.bound.push(Vec::new());
                for param in params {
                    self.pat(param);
                }
                self.expr(body);
                self.bound.pop();
            }
            ast::ExprKind::Unit
            | ast::ExprKind::Int(_)
            | ast::ExprKind::Float(_)
            | ast::ExprKind::Str(_)
            | ast::ExprKind::Bool(_) => {}
        }
    }

    fn block(&mut self, block: &ast::Block) {
        self.bound.push(Vec::new());
        for stmt in &block.stmts {
            match &stmt.kind {
                ast::StmtKind::Let { name, value, .. } => {
                    // The initialiser is scanned first: a binding is not in scope in its own value.
                    self.expr(value);
                    self.bind(&name.name);
                }
                ast::StmtKind::Assign { target, value } => {
                    self.expr(value);
                    match &target.kind {
                        // A bare name is a write and not a read.
                        ast::ExprKind::Path(path) if path.segments.len() == 1 => {
                            let head = &path.segments[0];
                            if !self.is_bound(&head.name) && self.members.contains_key(&head.name) {
                                self.writes.push((head.name.clone(), head.span));
                            }
                        }
                        // A projection reads the cell to rebuild it, so it is both.
                        _ => {
                            self.expr(target);
                            if let Some((name, span)) = head_name(target)
                                && !self.is_bound(&name)
                                && self.members.contains_key(&name)
                            {
                                self.writes.push((name, span));
                            }
                        }
                    }
                }
                ast::StmtKind::Return(value) => {
                    if let Some(value) = value {
                        self.expr(value);
                    }
                }
                // `returns` names an input, which is not a value and so not a dependency.
                ast::StmtKind::AfterCommit { task, .. } => self.expr(task),
                ast::StmtKind::Expr(expr) => self.expr(expr),
            }
        }
        self.bound.pop();
    }

    fn pat(&mut self, pat: &ast::Pat) {
        match &pat.kind {
            ast::PatKind::Binding(name) => self.bind(&name.name),
            ast::PatKind::Construct { args, .. } => {
                for arg in args {
                    self.pat(&arg.pat);
                }
            }
            ast::PatKind::Or(alts) => {
                for alt in alts {
                    self.pat(alt);
                }
            }
            ast::PatKind::Wild
            | ast::PatKind::Int(_)
            | ast::PatKind::Str(_)
            | ast::PatKind::Bool(_) => {}
        }
    }
}

fn push_once(list: &mut Vec<usize>, value: usize) {
    if !list.contains(&value) {
        list.push(value);
    }
}

/// The member declaration a node came from.
fn member_for<'m>(decl: &'m ast::ReactorDecl, name: &str) -> Option<&'m ast::Member> {
    decl.members.iter().find(|member| match &member.kind {
        ast::MemberKind::State { name: found, .. }
        | ast::MemberKind::Signal { name: found, .. } => found.name == name,
        _ => false,
    })
}

/// How many of a lifted function's locals are ordinary bindings rather than parameters.
///
/// Parameters are declared first and locals only ever appended, so the parameter count is the
/// number of leading locals that came from the lifting.
fn count_extra(locals: &[LocalDef]) -> usize {
    locals
        .iter()
        .filter(|local| local.role == LocalRole::Ordinary)
        .count()
}

/// A topological order over `deps`: every node after everything it depends on.
///
/// Depth-first from each node in source order, which is what makes the result a function of the
/// program rather than of a hash seed. Graph construction must not iterate a `HashMap`: a
/// randomised order would make the propagation plan differ between runs, and a milestone whose
/// central claim is turn determinism cannot afford that.
fn topological(deps: &[Vec<usize>]) -> Vec<usize> {
    let mut order = Vec::with_capacity(deps.len());
    let mut placed = vec![false; deps.len()];
    for start in 0..deps.len() {
        if placed[start] {
            continue;
        }
        let mut stack = vec![(start, 0usize)];
        while let Some((node, next)) = stack.pop() {
            if next < deps[node].len() {
                stack.push((node, next + 1));
                let dep = deps[node][next];
                if !placed[dep] && !stack.iter().any(|(open, _)| *open == dep) {
                    stack.push((dep, 0));
                }
            } else if !placed[node] {
                placed[node] = true;
                order.push(node);
            }
        }
    }
    order
}

/// Every function this expression calls.
fn collect_calls(expr: &Expr, found: &mut Vec<FnId>) {
    match &expr.kind {
        ExprKind::Call { callee, args } => {
            if !found.contains(callee) {
                found.push(*callee);
            }
            for arg in args {
                collect_calls(arg, found);
            }
        }
        ExprKind::Builtin { args, .. }
        | ExprKind::Construct { args, .. }
        | ExprKind::SpawnReactor { args, .. } => {
            for arg in args {
                collect_calls(arg, found);
            }
        }
        ExprKind::Field { base: inner, .. }
        | ExprKind::Unary { expr: inner, .. }
        | ExprKind::Await { expr: inner }
        | ExprKind::Scope { body: inner }
        | ExprKind::Spawn { expr: inner }
        | ExprKind::Try { expr: inner, .. }
        | ExprKind::ReactorInput { reactor: inner, .. }
        | ExprKind::ReactorExport { reactor: inner, .. } => collect_calls(inner, found),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::ShortCircuit { lhs, rhs, .. } => {
            collect_calls(lhs, found);
            collect_calls(rhs, found);
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_calls(scrutinee, found);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_calls(guard, found);
                }
                collect_calls(&arm.body, found);
            }
        }
        ExprKind::If { cond, then, els } => {
            collect_calls(cond, found);
            collect_calls(then, found);
            if let Some(els) = els {
                collect_calls(els, found);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match &stmt.kind {
                    StmtKind::Let { value, .. } => collect_calls(value, found),
                    StmtKind::Assign { place, value } => {
                        collect_calls(place, found);
                        collect_calls(value, found);
                    }
                    StmtKind::AfterCommit { task, .. } => {
                        for arg in effect_arguments(task) {
                            collect_calls(arg, found);
                        }
                    }
                    StmtKind::Expr(expr) => collect_calls(expr, found),
                }
            }
            if let Some(tail) = tail {
                collect_calls(tail, found);
            }
        }
        ExprKind::Return { value } => {
            if let Some(value) = value {
                collect_calls(value, found);
            }
        }
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Error => {}
    }
}

/// The parts of an `after_commit` operand that actually run during the turn.
///
/// The head call does not: `after_commit deliver(m)` *builds* `deliver(m)` and the runtime starts
/// it once the snapshot is published, so neither what `deliver` calls nor how long it takes is a
/// property of the turn. Its arguments are another matter — those are evaluated on the spot, and
/// everything a turn forbids still applies to them.
///
/// This is the whole of why laziness was worth having. If calling a `task fn` ran it, there would
/// be no way to describe an effect from inside a turn at all.
fn effect_arguments(task: &Expr) -> &[Expr] {
    match &task.kind {
        ExprKind::Call { args, .. } | ExprKind::Builtin { args, .. } => args,
        _ => std::slice::from_ref(task),
    }
}

/// The first impure builtin an expression calls, if any.
fn impure_builtin(expr: &Expr) -> Option<(Builtin, Span)> {
    let mut found = None;
    walk(expr, &mut |expr| {
        if found.is_some() {
            return;
        }
        if let ExprKind::Builtin { builtin, .. } = &expr.kind
            && !builtin.is_pure()
        {
            found = Some((*builtin, expr.span));
        }
    });
    found
}

/// The nearest function reachable from `start` that calls an impure builtin.
fn reachable_impurity(
    calls: &[Vec<FnId>],
    impurities: &[Option<(Builtin, Span)>],
    start: FnId,
) -> Option<(FnId, Builtin, Span)> {
    let mut seen = vec![false; calls.len()];
    // Breadth-first, so the function reported is the one closest to the node body: that is the
    // call the reader has to look at, and the rest of the chain follows from it.
    let mut queue = std::collections::VecDeque::from([start]);
    seen[start.index()] = true;
    while let Some(function) = queue.pop_front() {
        if let Some((builtin, span)) = impurities[function.index()] {
            return Some((function, builtin, span));
        }
        for &callee in &calls[function.index()] {
            if !seen[callee.index()] {
                seen[callee.index()] = true;
                queue.push_back(callee);
            }
        }
    }
    None
}

/// Visit every subexpression, outermost first.
fn walk(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expr);
    match &expr.kind {
        ExprKind::Call { args, .. }
        | ExprKind::Builtin { args, .. }
        | ExprKind::Construct { args, .. }
        | ExprKind::SpawnReactor { args, .. } => {
            for arg in args {
                walk(arg, visit);
            }
        }
        ExprKind::Field { base: inner, .. }
        | ExprKind::Unary { expr: inner, .. }
        | ExprKind::Await { expr: inner }
        | ExprKind::Scope { body: inner }
        | ExprKind::Spawn { expr: inner }
        | ExprKind::Try { expr: inner, .. }
        | ExprKind::ReactorInput { reactor: inner, .. }
        | ExprKind::ReactorExport { reactor: inner, .. } => walk(inner, visit),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::ShortCircuit { lhs, rhs, .. } => {
            walk(lhs, visit);
            walk(rhs, visit);
        }
        ExprKind::Match { scrutinee, arms } => {
            walk(scrutinee, visit);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    walk(guard, visit);
                }
                walk(&arm.body, visit);
            }
        }
        ExprKind::If { cond, then, els } => {
            walk(cond, visit);
            walk(then, visit);
            if let Some(els) = els {
                walk(els, visit);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match &stmt.kind {
                    StmtKind::Let { value, .. } => walk(value, visit),
                    StmtKind::Assign { place, value } => {
                        walk(place, visit);
                        walk(value, visit);
                    }
                    StmtKind::AfterCommit { task, .. } => {
                        for arg in effect_arguments(task) {
                            walk(arg, visit);
                        }
                    }
                    StmtKind::Expr(expr) => walk(expr, visit),
                }
            }
            if let Some(tail) = tail {
                walk(tail, visit);
            }
        }
        ExprKind::Return { value } => {
            if let Some(value) = value {
                walk(value, visit);
            }
        }
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Error => {}
    }
}

/// A cycle in the call graph reachable from `start`, as the functions that close it.
///
/// The search is over the *reachable* subgraph rather than the whole program: an ordinary
/// recursive function is perfectly legal, and only becomes an error when a turn can reach it.
fn reachable_cycle(calls: &[Vec<FnId>], start: FnId) -> Option<Vec<FnId>> {
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        White,
        Grey,
        Black,
    }
    let mut marks = vec![Mark::White; calls.len()];
    let mut path: Vec<FnId> = vec![start];
    let mut stack = vec![(start, 0usize)];
    marks[start.index()] = Mark::Grey;

    while let Some((function, next)) = stack.pop() {
        let edges = &calls[function.index()];
        if next >= edges.len() {
            marks[function.index()] = Mark::Black;
            path.pop();
            continue;
        }
        stack.push((function, next + 1));
        let callee = edges[next];
        match marks[callee.index()] {
            Mark::Grey => {
                let at = path.iter().position(|id| *id == callee).unwrap_or(0);
                let mut cycle = path[at..].to_vec();
                cycle.push(callee);
                return Some(cycle);
            }
            Mark::Black => {}
            Mark::White => {
                marks[callee.index()] = Mark::Grey;
                path.push(callee);
                stack.push((callee, 0));
            }
        }
    }
    None
}

/// The local a projection chain is rooted at: `a` in `a.b.c`.
fn head_name(expr: &ast::Expr) -> Option<(String, Span)> {
    match &expr.kind {
        ast::ExprKind::Path(path) => {
            let head = &path.segments[0];
            Some((head.name.clone(), head.span))
        }
        ast::ExprKind::Field { base, .. } | ast::ExprKind::Index { base, .. } => head_name(base),
        _ => None,
    }
}

fn binds_anything(pat: &Pat) -> bool {
    match &pat.kind {
        PatKind::Bind(_) => true,
        PatKind::Variant { args, .. } | PatKind::Record { args, .. } => {
            args.iter().any(binds_anything)
        }
        PatKind::Or(alts) => alts.iter().any(binds_anything),
        _ => false,
    }
}
