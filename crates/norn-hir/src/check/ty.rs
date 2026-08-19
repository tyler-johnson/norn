use super::*;

impl Checker {
    /// A parameter is the one place a reference may be written, so it is the one caller that does
    /// not go through `resolve_ty`.
    pub(super) fn resolve_param_ty(&mut self, ty: &ast::Type) -> Ty {
        match &ty.kind {
            ast::TypeKind::Ref { mutable: true, .. } => {
                self.exclusive_borrow(ty.span);
                Ty::Error
            }
            ast::TypeKind::Ref { inner, .. } => {
                // `&&T` is `&T`: re-borrowing a borrowed parameter to pass it on is the ordinary
                // thing to write, and it should not need a different spelling from the first borrow.
                let inner = self.resolve_param_ty(inner);
                match inner {
                    Ty::Ref(_) | Ty::Error => inner,
                    owned => Ty::Ref(Box::new(owned)),
                }
            }
            _ => self.resolve_ty(ty),
        }
    }

    /// The diagnostic `&mut` gets instead of a meaning. One exclusive-borrow rule is a borrow
    /// checker, and v0 has nothing that needs one.
    pub(super) fn exclusive_borrow(&mut self, span: Span) {
        self.push(
            Diagnostic::new(span, "`&mut` has no meaning yet")
                .label("exclusive borrows arrive with mutation through references")
                .note("v0 borrows only to read: `&T` lets a call look at a value without taking it")
                .note("to change something, take it by value and return it, or hold it in a reactor's `state`"),
        );
    }

    pub(super) fn resolve_ty(&mut self, ty: &ast::Type) -> Ty {
        match &ty.kind {
            ast::TypeKind::Unit => Ty::Unit,
            // A reference is writable in exactly one position, which is what makes "a borrow may
            // not escape" a fact about the grammar rather than an analysis: there is nowhere to
            // store one. `Ty::Error` rather than the pointee, so that a return type nobody may
            // write does not then disagree with the body that returns one.
            ast::TypeKind::Ref { mutable, .. } => {
                if *mutable {
                    self.exclusive_borrow(ty.span);
                } else {
                    self.push(
                        Diagnostic::new(ty.span, "a reference cannot be written here")
                            .label("`&` is only a parameter type")
                            .note("a borrow lasts for the call it is passed to, so there is nowhere else it could be kept")
                            .note("to hold the value, name it by its own type and take ownership of it"),
                    );
                }
                Ty::Error
            }
            ast::TypeKind::Path { path, args } => {
                // `Self` answers before anything else could: inside a trait it is the reserved
                // parameter slot, inside an impl it is the receiver, and anywhere else it is a
                // teaching diagnostic rather than a name lookup.
                if path.segments.len() == 1 && path.segments[0].name == "Self" {
                    if !args.is_empty() {
                        self.push(
                            Diagnostic::new(ty.span, "`Self` takes no type arguments")
                                .note("it stands for the implementing type whole"),
                        );
                        return Ty::Error;
                    }
                    match &self.self_ty {
                        Some(resolved) => return resolved.clone(),
                        None => {
                            self.push(
                                Diagnostic::new(ty.span, "`Self` has no meaning here")
                                    .label("outside a trait or impl")
                                    .note("`Self` names the implementing type, so it is written inside `trait` and `impl` declarations"),
                            );
                            return Ty::Error;
                        }
                    }
                }
                // A declared type parameter answers first: inside `fn map<T>(…)`, `T` is the
                // parameter whatever else the module calls `T`.
                if path.segments.len() == 1
                    && let Some(index) = self
                        .type_params_in_scope
                        .iter()
                        .position(|param| *param == path.segments[0].name)
                {
                    if !args.is_empty() {
                        self.push(
                            Diagnostic::new(
                                ty.span,
                                format!(
                                    "`{}` is a type parameter and takes no type arguments",
                                    path.segments[0].name
                                ),
                            )
                            .note("a parameter stands for a whole type; only a declared generic type takes arguments"),
                        );
                        return Ty::Error;
                    }
                    return Ty::Param {
                        index: index as u32,
                        name: path.segments[0].name.clone(),
                    };
                }
                if path.segments.len() != 1 {
                    // `fmt.Config` in type position. The special single-segment names — Option,
                    // Task, Flow, and the rest — are seeded, never declared, so none of them can
                    // sit behind a namespace and none is checked for here.
                    if path.segments.len() == 2
                        && self.ns[self.current]
                            .namespaces
                            .contains_key(&path.segments[0].name)
                    {
                        let item = match self.resolve_ns(path) {
                            Some(Ok(item)) => item,
                            _ => return Ty::Error,
                        };
                        let resolved = match item {
                            NsItem::Struct(id) => TypeName::Struct(id),
                            NsItem::Enum(id) => TypeName::Enum(id),
                            NsItem::Reactor(id) => TypeName::Reactor(id),
                            NsItem::Fn(_) => {
                                self.push(Diagnostic::new(
                                    path.span,
                                    format!("`{}` is a function, not a type", path.text()),
                                ));
                                return Ty::Error;
                            }
                        };
                        return self.named_ty(resolved, &path.text(), args, ty.span);
                    }
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
                    // A flow is generic in spelling only: `Bytes` is the one element type v0 has,
                    // so the argument is checked here rather than becoming a type parameter.
                    "Flow" => {
                        if args.len() == 1 {
                            match self.resolve_ty(&args[0]) {
                                Ty::Bytes => return Ty::Resource(Resource::Flow),
                                // Already reported; a second diagnostic would be noise.
                                Ty::Error => return Ty::Error,
                                _ => {}
                            }
                        }
                        self.push(
                            Diagnostic::new(ty.span, "the only flow in v0 is `Flow<Bytes>`")
                                .note("flows of other element types arrive with typed layout; see BOOTSTRAP.md §8"),
                        );
                        return Ty::Error;
                    }
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
                match self.ns[self.current].types.get(name).cloned() {
                    Some(resolved) => self.named_ty(resolved, name, args, ty.span),
                    None if self.ns[self.current].traits.contains_key(name) => {
                        self.push(
                            Diagnostic::new(path.span, format!("`{name}` is a trait, not a type"))
                                .label("names behaviour, not a shape")
                                .note("a value's type is what implements the trait; there are no trait objects"),
                        );
                        Ty::Error
                    }
                    None => {
                        self.error(path.span, format!("unknown type `{name}`"));
                        Ty::Error
                    }
                }
            }
        }
    }

    /// A named type met in type position, with whatever `<…>` arguments were written:
    /// instantiate a template, refuse arguments on anything else.
    fn named_ty(
        &mut self,
        resolved: TypeName,
        display: &str,
        args: &[ast::Type],
        span: Span,
    ) -> Ty {
        match resolved {
            TypeName::Struct(id) => {
                let params = self.program.structs[id.index()].type_params.clone();
                if params.is_empty() {
                    if !args.is_empty() {
                        self.no_type_args(display, span);
                        return Ty::Error;
                    }
                    return Ty::Struct(id);
                }
                let Some(resolved_args) = self.template_args(display, &params, args, span) else {
                    return Ty::Error;
                };
                match self.instantiate_struct(id, resolved_args, span, 0) {
                    Some(instance) => Ty::Struct(instance),
                    None => Ty::Error,
                }
            }
            TypeName::Enum(id) => {
                let params = self.program.enums[id.index()].type_params.clone();
                if params.is_empty() {
                    if !args.is_empty() {
                        self.no_type_args(display, span);
                        return Ty::Error;
                    }
                    return Ty::Enum(id);
                }
                let Some(resolved_args) = self.template_args(display, &params, args, span) else {
                    return Ty::Error;
                };
                match self.instantiate_enum(id, resolved_args, span, 0) {
                    Some(instance) => Ty::Enum(instance),
                    None => Ty::Error,
                }
            }
            TypeName::Reactor(id) => {
                if !args.is_empty() {
                    self.no_type_args(display, span);
                    return Ty::Error;
                }
                Ty::Reactor(id)
            }
            TypeName::Builtin(ty) => {
                if !args.is_empty() {
                    self.no_type_args(display, span);
                    return Ty::Error;
                }
                ty
            }
        }
    }

    pub(super) fn no_type_args(&mut self, display: &str, span: Span) {
        self.push(
            Diagnostic::new(span, format!("`{display}` takes no type arguments"))
                .note("its declaration has no type parameters"),
        );
    }

    /// Whether the right number of type arguments was written for a template, the mismatch
    /// reported with the declaration quoted.
    pub(super) fn template_arity(
        &mut self,
        display: &str,
        params: &[String],
        found: usize,
        span: Span,
    ) -> bool {
        if found == params.len() {
            return true;
        }
        let plural = if params.len() == 1 {
            "argument"
        } else {
            "arguments"
        };
        self.push(
            Diagnostic::new(
                span,
                format!(
                    "`{display}` takes {} type {plural}, found {found}",
                    params.len()
                ),
            )
            .note(format!(
                "the declaration is `{display}<{}>`",
                params.join(", ")
            )),
        );
        false
    }

    /// Check arity and resolve the written arguments of a template mention. An argument that is
    /// already `Ty::Error` bails to `Ty::Error` rather than minting a poisoned instance.
    fn template_args(
        &mut self,
        display: &str,
        params: &[String],
        args: &[ast::Type],
        span: Span,
    ) -> Option<Vec<Ty>> {
        if !self.template_arity(display, params, args.len(), span) {
            return None;
        }
        let resolved: Vec<Ty> = args.iter().map(|arg| self.resolve_ty(arg)).collect();
        if resolved.iter().any(Ty::is_error) {
            return None;
        }
        Some(resolved)
    }

    pub(super) fn type_args(
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

    /// A `let`, or a name a pattern binds. A reference may not be given a name: `resolve_ty` keeps
    /// one out of every written position, and this keeps one out of the inferred position that is
    /// left, so `let held = &conn` is answered here rather than becoming the one way to smuggle a
    /// borrow past the end of the call it belongs to.
    pub(super) fn declare_local(
        &mut self,
        name: String,
        ty: Ty,
        mutable: bool,
        span: Span,
    ) -> LocalId {
        let ty = if ty.is_ref() {
            self.push(
                Diagnostic::new(span, format!("`{name}` would be a borrow"))
                    .label("a borrow cannot be given a name")
                    .note("`&` lasts for the call it is handed to, and a name outlives that")
                    .note("pass it where it is needed — `f(&conn)` — or bind the value itself and take ownership of it"),
            );
            Ty::Error
        } else {
            ty
        };
        self.declare_role(name, ty, mutable, LocalRole::Ordinary, span)
    }

    /// A parameter, which is the one position where a reference may be written down.
    pub(super) fn declare_param(&mut self, name: String, ty: Ty, span: Span) -> LocalId {
        self.declare_role(name, ty, false, LocalRole::Ordinary, span)
    }

    pub(super) fn declare_role(
        &mut self,
        name: String,
        ty: Ty,
        mutable: bool,
        role: LocalRole,
        span: Span,
    ) -> LocalId {
        // The four bare constructor names are unbindable. A binding named `Some` could never be
        // read back — the name always resolves to the constructor — so it is refused where it is
        // written rather than left to confuse every later use. The local is still declared, so
        // that whatever was checked against it does not cascade.
        if is_builtin_variant(&name) {
            self.push(
                Diagnostic::new(span, format!("`{name}` cannot be a binding"))
                    .label("a built-in constructor")
                    .note("`None`, `Some`, `Ok`, and `Err` always name the Option and Result constructors"),
            );
        }
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

    pub(super) fn lookup_local(&self, name: &str) -> Option<LocalId> {
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
    pub(super) fn expect(&mut self, found: Expr, expected: Option<&Ty>, span: Span) -> Expr {
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
            // Owned where a borrow was wanted, or the reverse. The types alone would say what
            // differs; what a reader needs is which of the two the call does to their value.
            if found.ty.owned().fits(expected.owned()) && found.ty.is_ref() != expected.is_ref() {
                self.borrow_mismatch(expected, span);
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
}
