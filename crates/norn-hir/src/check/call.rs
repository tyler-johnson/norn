use super::*;

impl Checker {
    pub(super) fn check_call(
        &mut self,
        callee: &ast::Expr,
        type_args: &[ast::Type],
        args: &[ast::Arg],
        expected: Option<&Ty>,
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
        let name = &path.last().name;

        // The four bare constructor names first: they are unbindable, so nothing else can
        // answer for them.
        if path.segments.len() == 1 && is_builtin_variant(name) {
            return match name.as_str() {
                "None" | "Some" => self.check_option(path, args, expected, span),
                _ => self.check_result(path, args, expected, span),
            };
        }

        // `Enum.Variant(…)` is a construction spelled like a call, which is what it is.
        if path.segments.len() == 2
            && let Some(TypeName::Enum(id)) =
                self.ns[self.current].types.get(&path.segments[0].name)
        {
            let id = *id;
            let Some((index, _)) = self.program.enums[id.index()].variant(name) else {
                let message = format!("`{}` has no variant `{name}`", path.segments[0].name);
                self.push(Diagnostic::new(path.segments[1].span, message).label("unknown variant"));
                return self.error_expr(span);
            };
            // Option and Result build `Ty::Option`/`Ty::Result` values whose payload types come
            // from the expectation, so they route through the builtin checkers.
            if id == EnumId::OPTION {
                return self.check_option(path, args, expected, span);
            }
            if id == EnumId::RESULT {
                return self.check_result(path, args, expected, span);
            }
            return self.construct_variant(id, index, args, Ty::Enum(id), span);
        }

        if path.segments.len() != 1 {
            // A local enum head has answered by now, so a namespace head cannot be shadowed by
            // one — the two are disjoint by construction.
            if self.ns[self.current]
                .namespaces
                .contains_key(&path.segments[0].name)
            {
                return self.check_ns_call(path, args, span);
            }
            self.error(path.span, format!("unknown function `{}`", path.text()));
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }

        if let Some(builtin) = Builtin::from_name(name) {
            return self.check_builtin(builtin, args, span);
        }

        let Some(&id) = self.ns[self.current].fns.get(name) else {
            // Construction is spelled like a call; resolution is what tells the two apart. A
            // struct name builds the struct, and the type namespace answers before the reactor
            // member fallback does — matching the scan in `reactor_graph`, which skips type
            // names for the same reason.
            if let Some(kind) = self.ns[self.current].types.get(name) {
                match kind {
                    TypeName::Struct(id) => {
                        let id = *id;
                        return self.construct_struct(id, args, span);
                    }
                    TypeName::Enum(id) => {
                        let example = self.enum_example(*id);
                        self.push(
                            Diagnostic::new(path.span, format!("`{name}` is an enum"))
                                .note(format!("name the variant, as in `{name}.{example}`")),
                        );
                        return self.error_expr(span);
                    }
                    TypeName::Reactor(_) => {
                        self.push(
                            Diagnostic::new(path.span, format!("`{name}` is a reactor"))
                                .label("not a function")
                                .note(format!("create one with `spawn reactor {name}(…)`")),
                        );
                        return self.error_expr(span);
                    }
                    TypeName::Builtin(_) => {}
                }
            }
            return self.check_member_call(name, path.span, args, span);
        };
        self.call_fn(id, &name.clone(), args, span)
    }

    /// The call itself, once the callee is a known function: argument matching, and the capability
    /// check where the task is *built* — calling a `task fn` builds one, it does not run one,
    /// which is why authority is asked here rather than at the `await`.
    pub(super) fn call_fn(
        &mut self,
        id: FnId,
        display: &str,
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
        let (params, ret) = self.signatures[id.index()].clone();
        let param_names: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
        let Some(order) = self.argument_order(&param_names, args, display, "parameter", span)
        else {
            return self.error_expr(span);
        };

        let mut checked = Vec::with_capacity(params.len());
        for (index, (_, ty)) in params.iter().enumerate() {
            let arg = &args[order[index]];
            checked.push(self.check_expr(&arg.value, Some(ty)));
        }

        let ty = if self.program.fns[id.index()].is_task {
            let needs = self.program.fns[id.index()].uses.clone();
            self.require_task_authority(display, &needs, span);
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

    /// A dotted call whose head is a namespace binding: `fmt.digits(2)`, `fmt.Config(width: 3)`,
    /// `fmt.Shape.Dot(p)` — each the namespaced spelling of a call form that already exists.
    pub(super) fn check_ns_call(
        &mut self,
        path: &ast::Path,
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
        let resolved = match self.resolve_ns(path) {
            Some(Ok(item)) => item,
            _ => return self.error_expr(span),
        };
        let written = path.text();
        match (resolved, path.segments.len()) {
            (NsItem::Fn(id), 2) => self.call_fn(id, &written, args, span),
            (NsItem::Struct(id), 2) => self.construct_struct(id, args, span),
            (NsItem::Enum(id), 2) => {
                let example = self.enum_example(id);
                self.push(
                    Diagnostic::new(path.span, format!("`{written}` is an enum"))
                        .note(format!("name the variant, as in `{written}.{example}`")),
                );
                self.error_expr(span)
            }
            (NsItem::Reactor(_), 2) => {
                self.push(
                    Diagnostic::new(path.span, format!("`{written}` is a reactor"))
                        .label("not a function")
                        .note(format!("create one with `spawn reactor {written}(…)`")),
                );
                self.error_expr(span)
            }
            (NsItem::Enum(id), 3) => {
                let variant_name = &path.segments[2].name;
                let Some((index, _)) = self.program.enums[id.index()].variant(variant_name) else {
                    let head = format!("{}.{}", path.segments[0].name, path.segments[1].name);
                    let message = format!("`{head}` has no variant `{variant_name}`");
                    self.push(
                        Diagnostic::new(path.segments[2].span, message).label("unknown variant"),
                    );
                    return self.error_expr(span);
                };
                self.construct_variant(id, index, args, Ty::Enum(id), span)
            }
            _ => {
                self.error(path.span, format!("unknown function `{written}`"));
                self.error_expr(span)
            }
        }
    }

    /// A representative variant spelling, for the "name the variant" teach.
    pub(super) fn enum_example(&self, id: EnumId) -> String {
        self.program.enums[id.index()].variants.first().map_or_else(
            || "Variant".to_string(),
            |v| {
                if v.fields.is_empty() {
                    v.name.clone()
                } else {
                    format!("{}(…)", v.name)
                }
            },
        )
    }

    /// A reactor member named in call position.
    ///
    /// A signal is two things: a node whose value the graph maintains, and the pure function that
    /// derives it. Naming one reuses the value; calling one reuses the definition. A call carries no
    /// temporal semantics at all — it is that function applied to the arguments written here — which
    /// is why it is legal in a handler where reading the node is not. What made a read ambiguous was
    /// the name eliding its arguments; a call spells them, so "which values is this?" is answered at
    /// the call site rather than by a rule about when the turn recomputes.
    ///
    /// One consequence worth naming: a body reached this way runs on the caller's frame, with the
    /// caller's `cx`, rather than with the `cx: None` the propagation path calls node bodies with.
    /// Purity is still enforced — statically by `verify_pure`, transitively by `check_turns` — but
    /// on this path it is a checked property rather than a structurally impossible one.
    pub(super) fn check_member_call(
        &mut self,
        name: &str,
        name_span: Span,
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
        let (Some(sort), Some(id)) = (self.members.get(name).copied(), self.reactor) else {
            self.error(name_span, format!("unknown function `{name}`"));
            return self.error_expr(span);
        };
        if sort != Sort::Signal {
            let diagnostic = match sort {
                Sort::State => Diagnostic::new(
                    name_span,
                    format!("`{name}` is a state cell, not a function"),
                )
                .label("state holds a value; it does not derive one")
                .note("only a signal has a body to call"),
                Sort::Param => Diagnostic::new(
                    name_span,
                    format!("`{name}` is a reactor parameter, not a function"),
                )
                .label("a parameter holds a value; it does not derive one")
                .note("only a signal has a body to call"),
                Sort::Input => {
                    Diagnostic::new(name_span, format!("`{name}` is an input, not a function"))
                        .label("an input is a mailbox")
                        .note(format!("respond to it with `on {name}(…) {{ … }}`"))
                }
                Sort::Signal => unreachable!("handled above"),
            };
            self.push(diagnostic);
            return self.error_expr(span);
        }

        let node = self.node_index(id, name).expect("a member with a sort");
        let NodeKind::Signal { body } = self.program.reactors[id.index()].nodes[node].kind else {
            unreachable!("`Sort::Signal` is a signal node")
        };
        // Parameters are the signal's dependencies, in the order its lifted body takes them, which
        // is the contract `hir::Node::deps` states and the propagation path already relies on.
        let deps = self.program.reactors[id.index()].nodes[node].deps.clone();
        let ret = self.program.reactors[id.index()].nodes[node].ty.clone();
        let mut param_names = Vec::with_capacity(deps.len());
        let mut param_tys = Vec::with_capacity(deps.len());
        for dep in &deps {
            let dep_node = &self.program.reactors[id.index()].nodes[dep.index()];
            param_names.push(dep_node.name.clone());
            param_tys.push(dep_node.ty.clone());
        }

        let Some(order) = self.argument_order(&param_names, args, name, "parameter", span) else {
            return self.error_expr(span);
        };
        let mut checked = Vec::with_capacity(param_tys.len());
        for (index, ty) in param_tys.iter().enumerate() {
            let arg = &args[order[index]];
            checked.push(self.check_expr(&arg.value, Some(ty)));
        }
        Expr {
            kind: ExprKind::Call {
                callee: body,
                args: checked,
            },
            ty: ret,
            span,
        }
    }

    pub(super) fn check_builtin(
        &mut self,
        builtin: Builtin,
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
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
    pub(super) fn check_send(&mut self, args: &[ast::Arg], span: Span) -> Expr {
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
    pub(super) fn check_latest(&mut self, args: &[ast::Arg], span: Span) -> Expr {
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
    pub(super) fn check_spawn_reactor(
        &mut self,
        path: &ast::Path,
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
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
        // One segment answers from this file's reactors — which is where a named import lands
        // too; two reach through a namespace binding, export-checked like any other access.
        let resolved = if path.segments.len() == 1 {
            self.ns[self.current]
                .reactors
                .get(&path.segments[0].name)
                .copied()
        } else if path.segments.len() == 2
            && self.ns[self.current]
                .namespaces
                .contains_key(&path.segments[0].name)
        {
            match self.resolve_ns(path) {
                Some(Ok(NsItem::Reactor(id))) => Some(id),
                Some(Ok(_)) => {
                    self.push(
                        Diagnostic::new(path.span, format!("`{name}` is not a reactor"))
                            .label("not a reactor"),
                    );
                    return self.error_expr(span);
                }
                _ => return self.error_expr(span),
            }
        } else {
            None
        };
        let Some(id) = resolved else {
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
    pub(super) fn argument_order(
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

    pub(super) fn check_option(
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
                self.error(span, "`None` takes no arguments");
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
            let Some(inner) = inner_expected else {
                return self.uninferable(span, "None", "Option<I64>");
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
            self.error(span, "`Some` takes one positional argument");
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

    pub(super) fn check_result(
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

        let name = if is_ok { "Ok" } else { "Err" };
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

    pub(super) fn uninferable(&mut self, span: Span, what: &str, example: &str) -> Expr {
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

    pub(super) fn construct_struct(&mut self, id: StructId, args: &[ast::Arg], span: Span) -> Expr {
        let strukt = &self.program.structs[id.index()];
        let name = strukt.name.clone();
        let names: Vec<String> = strukt.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = strukt.fields.iter().map(|f| f.ty.clone()).collect();
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
                ctor: Ctor::Struct(id),
                args: checked,
            },
            ty: Ty::Struct(id),
            span,
        }
    }

    pub(super) fn construct_variant(
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
}
