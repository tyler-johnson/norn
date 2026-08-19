use super::*;

impl Checker {
    /// Pass one: every type name exists before any type is resolved, so declarations may refer to
    /// one another in any order.
    pub(super) fn declare_types(&mut self, module: &ast::Module) {
        self.ns[self.current]
            .types
            .insert("I64".into(), TypeName::Builtin(Ty::I64));
        self.ns[self.current]
            .types
            .insert("F64".into(), TypeName::Builtin(Ty::F64));
        self.ns[self.current]
            .types
            .insert("Bool".into(), TypeName::Builtin(Ty::Bool));
        self.ns[self.current]
            .types
            .insert("String".into(), TypeName::Builtin(Ty::Str));
        self.ns[self.current]
            .types
            .insert("Bytes".into(), TypeName::Builtin(Ty::Bytes));
        self.ns[self.current].types.insert(
            "Listener".into(),
            TypeName::Builtin(Ty::Resource(Resource::Listener)),
        );
        self.ns[self.current].types.insert(
            "Connection".into(),
            TypeName::Builtin(Ty::Resource(Resource::Connection)),
        );
        self.ns[self.current].types.insert(
            "File".into(),
            TypeName::Builtin(Ty::Resource(Resource::File)),
        );
        // `Flow` is registered so that redeclaring it is an error, but `resolve_ty` intercepts the
        // name before this entry is consulted: the only writable spelling is `Flow<Bytes>`.
        self.ns[self.current].types.insert(
            "Flow".into(),
            TypeName::Builtin(Ty::Resource(Resource::Flow)),
        );
        self.ns[self.current]
            .types
            .insert("IoError".into(), TypeName::Enum(EnumId::IO_ERROR));
        // `Option` and `Result` have their own `Ty` spellings and `resolve_ty` checks those
        // before consulting this map, so registering them changes nothing about types. What it
        // does is give the *value* namespace a head to resolve — `Option.None` is a variant
        // construction — and make `enum Option` a redeclaration rather than a shadow.
        self.ns[self.current]
            .types
            .insert("Option".into(), TypeName::Enum(EnumId::OPTION));
        self.ns[self.current]
            .types
            .insert("Result".into(), TypeName::Enum(EnumId::RESULT));

        for item in &module.items {
            let (name, span) = match item {
                ast::Item::Struct(decl) => (&decl.name, decl.span),
                ast::Item::Enum(decl) => (&decl.name, decl.span),
                ast::Item::Reactor(decl) => (&decl.name, decl.span),
                ast::Item::Fn(_) => continue,
                // Temporary, deleted when the trait passes land later in the item 7 wave: the
                // grammar is ahead of the checker, and saying so beats an unknown-name cascade.
                ast::Item::Trait(decl) => {
                    self.push(
                        Diagnostic::new(
                            decl.name.span,
                            "`trait` declarations are parsed but not checked yet",
                        )
                        .label("not checked yet")
                        .note("traits land later in the generics wave; see BOOTSTRAP.md §8 item 7"),
                    );
                    continue;
                }
                ast::Item::Impl(decl) => {
                    self.push(
                        Diagnostic::new(
                            decl.trait_path.span,
                            "`impl` blocks are parsed but not checked yet",
                        )
                        .label("not checked yet")
                        .note("traits land later in the generics wave; see BOOTSTRAP.md §8 item 7"),
                    );
                    continue;
                }
            };
            if self.ns[self.current].types.contains_key(&name.name) {
                self.push(
                    Diagnostic::new(name.span, format!("`{}` is declared twice", name.name))
                        .label("duplicate type"),
                );
                continue;
            }
            let resolved = match item {
                ast::Item::Struct(decl) => {
                    let id = StructId(self.program.structs.len() as u32);
                    let type_params = self.type_param_names(&decl.type_params);
                    self.program.structs.push(StructDef {
                        name: decl.name.name.clone(),
                        type_params,
                        fields: Vec::new(),
                        span,
                    });
                    TypeName::Struct(id)
                }
                ast::Item::Enum(decl) => {
                    let id = EnumId(self.program.enums.len() as u32);
                    let type_params = self.type_param_names(&decl.type_params);
                    self.program.enums.push(EnumDef {
                        name: decl.name.name.clone(),
                        type_params,
                        variants: Vec::new(),
                        span,
                    });
                    TypeName::Enum(id)
                }
                // A reactor handle is a type in the same sense a `Listener` is: it is spelled by
                // its own name, and it names the thing rather than describing its shape.
                ast::Item::Reactor(decl) => {
                    let id = ReactorId(self.program.reactors.len() as u32);
                    self.reactor_owner.push(self.current);
                    self.program.reactors.push(ReactorDef {
                        name: self.qualified(&decl.name.name),
                        params: Vec::new(),
                        uses: Vec::new(),
                        inputs: Vec::new(),
                        nodes: Vec::new(),
                        slots: Vec::new(),
                        order: Vec::new(),
                        exports: Vec::new(),
                        span,
                    });
                    self.ns[self.current]
                        .reactors
                        .insert(decl.name.name.clone(), id);
                    TypeName::Reactor(id)
                }
                ast::Item::Fn(_) | ast::Item::Trait(_) | ast::Item::Impl(_) => unreachable!(),
            };
            self.ns[self.current]
                .types
                .insert(name.name.clone(), resolved);
        }
    }

    /// The declared type parameter names, duplicates refused: two `T`s would be one hole with
    /// two spellings.
    fn type_param_names(&mut self, params: &[ast::TypeParam]) -> Vec<String> {
        let mut names: Vec<String> = Vec::new();
        for param in params {
            if names.contains(&param.name.name) {
                self.push(
                    Diagnostic::new(
                        param.name.span,
                        format!("type parameter `{}` is declared twice", param.name.name),
                    )
                    .label("duplicate parameter"),
                );
                continue;
            }
            names.push(param.name.name.clone());
        }
        names
    }

    /// Pass two: fill in field and payload types, each declaration's own type parameters in
    /// scope while its fields resolve.
    pub(super) fn define_types(&mut self, module: &ast::Module) {
        for item in &module.items {
            self.type_params_in_scope.clear();
            match item {
                ast::Item::Struct(decl) => {
                    let Some(TypeName::Struct(id)) =
                        self.ns[self.current].types.get(&decl.name.name)
                    else {
                        continue;
                    };
                    let id = *id;
                    self.type_params_in_scope =
                        self.program.structs[id.index()].type_params.clone();
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
                    self.program.structs[id.index()].fields = fields;
                }
                ast::Item::Enum(decl) => {
                    let Some(TypeName::Enum(id)) = self.ns[self.current].types.get(&decl.name.name)
                    else {
                        continue;
                    };
                    let id = *id;
                    self.type_params_in_scope = self.program.enums[id.index()].type_params.clone();
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
                            ast::VariantPayload::Struct(decls) => {
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
                ast::Item::Fn(_)
                | ast::Item::Reactor(_)
                | ast::Item::Trait(_)
                | ast::Item::Impl(_) => {}
            }
        }
        self.type_params_in_scope.clear();
    }

    pub(super) fn declare_fns(&mut self, module: &ast::Module) {
        let mut of_item: Vec<Option<FnId>> = vec![None; module.items.len()];
        for (index, item) in module.items.iter().enumerate() {
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
            if is_builtin_variant(&decl.name.name) {
                self.push(
                    Diagnostic::new(
                        decl.name.span,
                        format!("`{}` is a built-in constructor", decl.name.name),
                    )
                    .label("cannot be redefined")
                    .note("`None`, `Some`, `Ok`, and `Err` always name the Option and Result constructors"),
                );
                continue;
            }
            // Construction is spelled like a call, so call position must be unambiguous: one
            // name cannot both build a value and call a function.
            let clash = match self.ns[self.current].types.get(&decl.name.name) {
                Some(TypeName::Struct(_)) => Some("struct"),
                Some(TypeName::Enum(_)) => Some("enum"),
                Some(TypeName::Reactor(_)) => Some("reactor"),
                Some(TypeName::Builtin(_)) | None => None,
            };
            if let Some(what) = clash {
                self.push(
                    Diagnostic::new(
                        decl.name.span,
                        format!("`{}` is already the name of a {what}", decl.name.name),
                    )
                    .label("a call must be unambiguous")
                    .note(format!(
                        "`{0}(…)` has to mean one thing, and the {what} `{0}` already claims it",
                        decl.name.name
                    )),
                );
                continue;
            }
            if self.ns[self.current].fns.contains_key(&decl.name.name) {
                self.push(
                    Diagnostic::new(
                        decl.name.span,
                        format!("`{}` is declared twice", decl.name.name),
                    )
                    .label("duplicate function"),
                );
                continue;
            }
            let type_params = self.type_param_names(&decl.type_params);
            self.type_params_in_scope = type_params.clone();
            let params: Vec<(String, Ty)> = decl
                .params
                .iter()
                .map(|p| (p.name.name.clone(), self.resolve_param_ty(&p.ty)))
                .collect();
            let ret = decl.ret.as_ref().map_or(Ty::Unit, |ty| self.resolve_ty(ty));
            self.type_params_in_scope.clear();
            let uses = self.capabilities(&decl.uses);
            let id = FnId(self.program.fns.len() as u32);
            of_item[index] = Some(id);
            self.fn_owner.push(self.current);
            self.ns[self.current].fns.insert(decl.name.name.clone(), id);
            self.signatures.push((params.clone(), ret.clone()));
            self.program.fns.push(FnDef {
                // A non-entry module's functions display with their file's stem — "fmt.digits" —
                // the way lifted reactor members already display dotted. Resolution still goes by
                // the bare name; only what traps and traces print changes.
                name: self.qualified(&decl.name.name),
                type_params,
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
            // Only the entry module's `main` is an entry point; an imported `main` is an ordinary
            // function.
            if decl.name.name == "main" && self.current == 0 {
                if self.program.fns[id.index()].type_params.is_empty() {
                    self.program.main = Some(id);
                } else {
                    self.push(
                        Diagnostic::new(decl.name.span, "`main` cannot be generic")
                            .label("the entry point")
                            .note("the runtime calls `main` directly and has no type arguments to supply"),
                    );
                }
            }
        }
        self.fn_of_item[self.current] = of_item;
    }

    /// Resolve a `uses { … }` list. The vocabulary is closed, so an unknown name is an error that
    /// says what the three are rather than a capability nobody grants.
    pub(super) fn capabilities(&mut self, uses: &[ast::Path]) -> Vec<Capability> {
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

    pub(super) fn check_fns(&mut self, module: &ast::Module) {
        for (index, item) in module.items.iter().enumerate() {
            let ast::Item::Fn(decl) = item else { continue };
            // Bodies pair with declarations by position, not by name: a display-name prefix or a
            // duplicate must never silently skip a body or check one against the wrong signature.
            let Some(id) = self.fn_of_item[self.current][index] else {
                continue;
            };
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
            self.loops = Vec::new();
            // A template body is checked exactly once, its parameters opaque: this scope is what
            // lets a `let` annotation inside it spell `List<T>`.
            self.type_params_in_scope = self.program.fns[id.index()].type_params.clone();
            for ((name, ty), param) in params.iter().zip(&decl.params) {
                self.declare_param(name.clone(), ty.clone(), param.name.span);
            }
            let body = self.check_block(&decl.body, Some(&ret), decl.body.span);
            self.type_params_in_scope.clear();
            let locals = std::mem::take(&mut self.locals);
            self.program.fns[id.index()].locals = locals;
            self.program.fns[id.index()].body = body;
        }
    }

    // ---------------------------------------------------------------- reactors

    /// Pair each reactor declaration with the id `declare_types` gave it, skipping a redeclaration
    /// so that a duplicate name does not quietly fold two reactors into one.
    pub(super) fn reactor_items<'m>(
        &self,
        module: &'m ast::Module,
    ) -> Vec<(ReactorId, &'m ast::ReactorDecl)> {
        let mut seen: Vec<ReactorId> = Vec::new();
        let mut out = Vec::new();
        for item in &module.items {
            let ast::Item::Reactor(decl) = item else {
                continue;
            };
            let Some(&id) = self.ns[self.current].reactors.get(&decl.name.name) else {
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
    pub(super) fn declare_lifted(&mut self, name: String, span: Span) -> FnId {
        let id = FnId(self.program.fns.len() as u32);
        self.fn_owner.push(self.current);
        self.signatures.push((Vec::new(), Ty::Error));
        self.program.fns.push(FnDef {
            name,
            type_params: Vec::new(),
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
}
