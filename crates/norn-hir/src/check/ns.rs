use super::reactor::Wiring;
use super::*;

impl Checker {
    pub(super) fn new(modules: usize) -> Checker {
        // `Option` and `Result` are seeded as ordinary enums so that construction, matching, and
        // lowering treat them exactly like a user enum. Only their type arguments are special.
        let span = Span::new(0, 0);
        let option = EnumDef {
            name: "Option".into(),
            type_params: Vec::new(),
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
            type_params: Vec::new(),
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
            type_params: Vec::new(),
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
                structs: Vec::new(),
                enums: vec![option, result, io_error],
                fns: Vec::new(),
                reactors: Vec::new(),
                main: None,
            },
            errors: (0..modules).map(|_| Vec::new()).collect(),
            ns: (0..modules).map(|_| ModuleNs::new()).collect(),
            current: 0,
            fn_owner: Vec::new(),
            reactor_owner: Vec::new(),
            fn_of_item: (0..modules).map(|_| Vec::new()).collect(),
            names: Vec::new(),
            keys: Vec::new(),
            stems: Vec::new(),
            key_index: HashMap::new(),
            decls: (0..modules).map(|_| HashMap::new()).collect(),
            import_target: (0..modules).map(|_| Vec::new()).collect(),
            pending_fn_imports: Vec::new(),
            signatures: Vec::new(),
            param_modes: Vec::new(),
            mode_pinned: Vec::new(),
            declared_uses: Vec::new(),
            uses_spans: Vec::new(),
            declared_reactor_uses: Vec::new(),
            reactor_uses_spans: Vec::new(),
            locals: Vec::new(),
            scopes: Vec::new(),
            ret: Ty::Unit,
            fn_name: String::new(),
            ctx: Ctx::Plain,
            members: HashMap::new(),
            reactor: None,
            in_handler: false,
            assigning: false,
            loops: Vec::new(),
            generics: Generics::new(),
            type_params_in_scope: Vec::new(),
            // `Eq` is seeded the way Option and Result are: a compiler-defined marker with no
            // methods, satisfied by exactly the scalar types, so `==` on a bounded `T` costs
            // the runtime nothing it was not already doing.
            traits: vec![TraitDef {
                name: "Eq".into(),
                module: usize::MAX,
                methods: Vec::new(),
            }],
            impls: Vec::new(),
            reactor_methods: Vec::new(),
            self_ty: None,
            fn_bounds: Vec::new(),
            bounds_in_scope: Vec::new(),
            struct_owner: Vec::new(),
            // Parallel to the three seeded enums, which no module declared.
            enum_owner: vec![usize::MAX; 3],
        }
    }

    pub(super) fn error(&mut self, span: Span, message: impl Into<String>) {
        self.errors[self.current].push(Diagnostic::new(span, message));
    }

    pub(super) fn push(&mut self, diagnostic: Diagnostic) {
        self.errors[self.current].push(diagnostic);
    }

    // ---------------------------------------------------------------- program

    /// Every phase runs over every module before the next phase starts — all declares before all
    /// defines before all bodies — so cross-file references resolve whatever order files were
    /// discovered in, and an import cycle is not an error: there are no module initialisers, so
    /// there is no order for a cycle to violate.
    pub(super) fn run(&mut self, inputs: &[ModuleInput]) {
        self.names = inputs.iter().map(|input| input.name.clone()).collect();
        self.keys = inputs.iter().map(|input| input.key.clone()).collect();
        self.stems = inputs
            .iter()
            .map(|input| {
                let base = input.name.rsplit('/').next().unwrap_or(&input.name);
                base.strip_suffix(".norn").unwrap_or(base).to_string()
            })
            .collect();
        for (index, key) in self.keys.iter().enumerate() {
            self.key_index.entry(key.clone()).or_insert(index);
        }

        self.each(inputs, Checker::collect_decls);
        self.each(inputs, Checker::check_specifiers);
        self.each(inputs, Checker::declare_types);
        // Type imports bind before types are defined, because a field may name an imported type;
        // function imports cannot bind until every module's `declare_fns` has run.
        self.each(inputs, Checker::bind_imports);
        // Instances allocated while types are being defined queue their fills, because the
        // template a field names may not have its own fields yet; the drain right after is what
        // guarantees every instance any later pass observes has real fields.
        self.generics.defining_types = true;
        self.each(inputs, Checker::define_types);
        self.drain_type_fills();
        // Trait member signatures resolve after the fills so they may mention an instance;
        // impls wait until every function exists, because their conformance appends functions.
        self.each(inputs, Checker::define_traits);
        self.each(inputs, Checker::declare_fns);
        self.bind_fn_imports();
        self.each(inputs, Checker::declare_impls);
        // Reactors are declared, scanned, and checked between signatures and bodies, because a
        // `task fn` body may mention a reactor and a node body may call any function.
        self.each(inputs, Checker::declare_reactors);
        // Now that every reactor's members exist, an impl written for a handle can be held to
        // them: a method may not take the name of an input or an exported signal.
        self.check_reactor_methods();
        let graphs: Vec<Vec<Wiring>> = inputs
            .iter()
            .enumerate()
            .map(|(index, input)| {
                self.current = index;
                self.scan_reactors(input.module)
            })
            .collect();
        for ((index, input), graphs) in inputs.iter().enumerate().zip(graphs) {
            self.current = index;
            self.check_reactors(input.module, graphs);
        }
        self.each(inputs, Checker::check_fns);
        // Between bodies and the whole-program passes, so `check_turns` and `check_moves` see
        // every generic instance as an ordinary monomorphic function.
        self.monomorphize();
        self.check_turns();
        // Capability inference, on the same settled call graph: what a function uses is what its
        // body reaches, and a written `uses { … }` is checked against that rather than consulted
        // while the body is walked.
        self.infer_uses();
        // Sink inference runs immediately before `check_moves`, on the same tables it will
        // enforce: every executable body is concrete by now, so a mode is a per-instance fact.
        self.infer_sinks();
        self.check_moves();
        // The settled modes become part of the program, rows padded to arity with `Read` — a
        // lifted body's row is shorter than its arity, and its parameters are reactor members.
        for (index, def) in self.program.fns.iter_mut().enumerate() {
            let mut modes = self.param_modes.get(index).cloned().unwrap_or_default();
            modes.resize(def.params, Mode::Read);
            def.modes = modes;
        }
    }

    /// One phase, over every module in input order.
    pub(super) fn each(&mut self, inputs: &[ModuleInput], phase: fn(&mut Checker, &ast::Module)) {
        for (index, input) in inputs.iter().enumerate() {
            self.current = index;
            phase(self, input.module);
        }
    }

    /// The display-name prefix a non-entry module's functions and reactors carry: "fmt.digits",
    /// "fmt.Gate". The entry module stays unprefixed, so a one-file program reads as it always did.
    pub(super) fn qualified(&self, name: &str) -> String {
        if self.current == 0 || self.stems[self.current].is_empty() {
            name.to_string()
        } else {
            format!("{}.{name}", self.stems[self.current])
        }
    }

    /// The exports view, straight off the AST: available before any checking has run, which is
    /// what lets import binding know a name's kind before the name has an id.
    pub(super) fn collect_decls(&mut self, module: &ast::Module) {
        let mut decls = HashMap::new();
        for item in &module.items {
            let (name, kind, exported) = match item {
                ast::Item::Fn(decl) => (&decl.name, DeclKind::Fn, decl.exported),
                ast::Item::Struct(decl) => (&decl.name, DeclKind::Struct, decl.exported),
                ast::Item::Enum(decl) => (&decl.name, DeclKind::Enum, decl.exported),
                ast::Item::Reactor(decl) => (&decl.name, DeclKind::Reactor, decl.exported),
                ast::Item::Trait(decl) => (&decl.name, DeclKind::Trait, decl.exported),
                // An impl declares no name: it travels with its trait and its type, which is
                // why there is no `export impl` for this view to record.
                ast::Item::Impl(_) => continue,
            };
            decls
                .entry(name.name.clone())
                .or_insert((kind, exported.is_some()));
        }
        self.decls[self.current] = decls;
    }

    /// Resolve every import specifier to a module, or say why it does not name one. Path policy
    /// lives here rather than in the parser so that `norn check` on disk and an in-memory test
    /// agree about what a specifier means.
    pub(super) fn check_specifiers(&mut self, module: &ast::Module) {
        let mut targets = Vec::with_capacity(module.imports.len());
        for decl in &module.imports {
            let span = decl.specifier_span;
            let target = match resolve_specifier(&self.keys[self.current], &decl.specifier) {
                Err(SpecifierError::Bare) => {
                    self.push(
                        Diagnostic::new(
                            span,
                            format!("`{}` does not name a module", decl.specifier),
                        )
                        .label("not `std/…` or a relative path")
                        .note("a module is the standard library's (`std/fmt`) or a file named by where it is (`./fmt`, `../util/strings`); packages will take this shape, but do not exist yet"),
                    );
                    None
                }
                Err(SpecifierError::Extension) => {
                    let trimmed = decl.specifier.trim_end_matches(".norn");
                    self.push(
                        Diagnostic::new(span, "the `.norn` extension is implied")
                            .label("spelled out here")
                            .note(format!(
                                "write `\"{trimmed}\"`; the file it names is still `{trimmed}.norn`"
                            )),
                    );
                    None
                }
                Ok(resolved) => {
                    let (key, std) = match resolved {
                        Resolved::File(key) => (key, false),
                        Resolved::Std(key) => (key, true),
                    };
                    if key == self.keys[self.current] {
                        self.push(
                            Diagnostic::new(span, "a file cannot import itself")
                                .label("this is the importing file"),
                        );
                        None
                    } else {
                        match self.key_index.get(&key) {
                            Some(&index) => Some(index),
                            // Same words as the loader's miss, because for an embedder that skips
                            // the loader this arm is the same miss.
                            None if std => {
                                self.push(
                                    Diagnostic::new(
                                        span,
                                        format!(
                                            "no module `{}` in the standard library",
                                            decl.specifier
                                        ),
                                    )
                                    .note(format!(
                                        "the standard library provides {}",
                                        crate::stdlib::catalogue()
                                    )),
                                );
                                None
                            }
                            None => {
                                self.push(
                                    Diagnostic::new(
                                        span,
                                        format!("cannot find module `{}`", decl.specifier),
                                    )
                                    .note(format!("expected a module at `{key}`")),
                                );
                                None
                            }
                        }
                    }
                }
            };
            targets.push(target);
        }
        self.import_target[self.current] = targets;
    }

    /// Bind what a module imports, and say everything that is wrong with its import list — each
    /// bad item exactly once. Types and reactors bind here, before `define_types` needs them;
    /// functions have no id yet, so the good ones go on a pending list for `bind_fn_imports`.
    pub(super) fn bind_imports(&mut self, module: &ast::Module) {
        // Names this module's import list has already bound, so two imports of one name collide
        // whichever forms or files they came from.
        let mut claimed: HashMap<String, Span> = HashMap::new();
        for (index, decl) in module.imports.iter().enumerate() {
            let Some(target) = self.import_target[self.current][index] else {
                continue;
            };
            match &decl.kind {
                ast::ImportKind::Namespace(name) => {
                    // A namespace binding may not collide with anything: keeping the namespace
                    // disjoint from every other kind of name is what keeps resolution one rule.
                    if let Some(what) = self.import_collision(&name.name, &claimed) {
                        self.push(
                            Diagnostic::new(
                                name.span,
                                format!("the imported name `{}` is already taken", name.name),
                            )
                            .label(what)
                            .note("pick another name after `as`"),
                        );
                        continue;
                    }
                    claimed.insert(name.name.clone(), name.span);
                    self.ns[self.current]
                        .namespaces
                        .insert(name.name.clone(), target);
                }
                ast::ImportKind::Named(items) => {
                    for item in items {
                        let source = &item.name.name;
                        let local = item.alias.as_ref().unwrap_or(&item.name);
                        let Some(&(kind, exported)) = self.decls[target].get(source) else {
                            let file = self.names[target].clone();
                            self.push(
                                Diagnostic::new(
                                    item.name.span,
                                    format!("`{source}` is not defined in `{}`", decl.specifier),
                                )
                                .label("unknown name")
                                .note(format!("{file} declares no `{source}`")),
                            );
                            continue;
                        };
                        if !exported {
                            self.not_exported(source, &decl.specifier, target, item.name.span);
                            continue;
                        }
                        if let Some(what) = self.import_collision(&local.name, &claimed) {
                            self.push(
                                Diagnostic::new(
                                    item.span,
                                    format!("the imported name `{}` is already taken", local.name),
                                )
                                .label(what)
                                .note(format!(
                                    "rename the import with `as`, as in `{source} as other`"
                                )),
                            );
                            continue;
                        }
                        claimed.insert(local.name.clone(), item.span);
                        match kind {
                            DeclKind::Fn => self.pending_fn_imports.push((
                                self.current,
                                local.name.clone(),
                                target,
                                source.clone(),
                                item.span,
                            )),
                            DeclKind::Trait => {
                                // Trait ids exist already: every module's `declare_types` has
                                // run, and traits register there beside the types.
                                let Some(&id) = self.ns[target].traits.get(source) else {
                                    continue;
                                };
                                self.ns[self.current].traits.insert(local.name.clone(), id);
                            }
                            DeclKind::Struct | DeclKind::Enum | DeclKind::Reactor => {
                                // The target's namespaces are populated: every module's
                                // `declare_types` has run by the time any module binds.
                                let Some(resolved) = self.ns[target].types.get(source).cloned()
                                else {
                                    // The target refused the declaration (a duplicate, say); it
                                    // already has an error of its own.
                                    continue;
                                };
                                if let TypeName::Reactor(id) = resolved {
                                    // Mirror a local reactor, which lives in both namespaces.
                                    self.ns[self.current]
                                        .reactors
                                        .insert(local.name.clone(), id);
                                }
                                self.ns[self.current]
                                    .types
                                    .insert(local.name.clone(), resolved);
                            }
                        }
                    }
                }
            }
        }
    }

    /// What an imported name would collide with, if anything.
    pub(super) fn import_collision(
        &self,
        local: &str,
        claimed: &HashMap<String, Span>,
    ) -> Option<&'static str> {
        if is_builtin_variant(local) {
            return Some("a built-in constructor");
        }
        if Builtin::from_name(local).is_some() {
            return Some("a built-in function");
        }
        if claimed.contains_key(local) {
            return Some("bound by an earlier import");
        }
        if self.ns[self.current].namespaces.contains_key(local) {
            return Some("an imported module");
        }
        if self.decls[self.current].contains_key(local) {
            return Some("declared in this file");
        }
        if self.ns[self.current].types.contains_key(local) {
            return Some("a built-in type");
        }
        // Declared traits are caught by the decls check above; what this guards is the seeded
        // `Eq`, which no file declares.
        if self.ns[self.current].traits.contains_key(local) {
            return Some("a built-in trait");
        }
        None
    }

    /// The second half of import binding: give each pending function import its id, now that
    /// every module's `declare_fns` has run.
    pub(super) fn bind_fn_imports(&mut self) {
        for (module, local, target, source, _span) in std::mem::take(&mut self.pending_fn_imports) {
            // A missing entry means the target refused the declaration; it has its own error.
            let Some(&id) = self.ns[target].fns.get(&source) else {
                continue;
            };
            self.ns[module].fns.insert(local, id);
        }
    }

    /// Resolve the first two segments of a path whose head is a `* as` namespace binding.
    ///
    /// `None` when the head is not a namespace — the caller falls through to its own "unknown"
    /// answer. `Some(Err(()))` when it is one but the member does not resolve: unknown or
    /// unexported, each already diagnosed here, so the caller only has to produce an error value.
    pub(super) fn resolve_ns(&mut self, path: &ast::Path) -> Option<Result<NsItem, ()>> {
        let head = &path.segments[0];
        let &target = self.ns[self.current].namespaces.get(&head.name)?;
        let member = &path.segments[1];
        let span = head.span.to(member.span);
        let Some(&(kind, exported)) = self.decls[target].get(&member.name) else {
            let file = self.names[target].clone();
            self.push(
                Diagnostic::new(
                    span,
                    format!("`{}` is not defined in `{}`", member.name, head.name),
                )
                .label("unknown name")
                .note(format!("{file} declares no `{}`", member.name)),
            );
            return Some(Err(()));
        };
        if !exported {
            let name = member.name.clone();
            let shown = head.name.clone();
            self.not_exported(&name, &shown, target, span);
            return Some(Err(()));
        }
        // A trait is neither a value nor a type, so every caller of this resolver would only
        // mis-teach it; the one diagnostic lives here instead.
        if kind == DeclKind::Trait {
            self.push(
                Diagnostic::new(span, format!("`{}` is a trait", path.text()))
                    .label("not a value or a type")
                    .note("a trait names behaviour: implement it with `impl`, and reach its methods on a value"),
            );
            return Some(Err(()));
        }
        let item = match kind {
            DeclKind::Fn => self.ns[target]
                .fns
                .get(&member.name)
                .map(|&id| NsItem::Fn(id)),
            _ => match self.ns[target].types.get(&member.name) {
                Some(TypeName::Struct(id)) => Some(NsItem::Struct(*id)),
                Some(TypeName::Enum(id)) => Some(NsItem::Enum(*id)),
                Some(TypeName::Reactor(id)) => Some(NsItem::Reactor(*id)),
                // The target refused the declaration — a duplicate, or a fn whose name a type
                // already claims. It has an error of its own; do not add a second.
                Some(TypeName::Builtin(_)) | None => None,
            },
        };
        Some(item.ok_or(()))
    }

    /// The shared privacy diagnostic: at an import item now, and at namespace accesses once those
    /// resolve. `shown` is how the referring site spelled the module — a specifier or a bound name.
    pub(super) fn not_exported(&mut self, name: &str, shown: &str, target: usize, span: Span) {
        let file = self.names[target].clone();
        let kind = self.decls[target]
            .get(name)
            .map_or("declaration", |(kind, _)| kind.describe());
        self.push(
            Diagnostic::new(span, format!("`{name}` is not exported by `{shown}`"))
                .label("private to its file")
                .note(format!(
                    "the {kind} is declared in {file}; write `export` before it to make it public"
                )),
        );
    }
}
