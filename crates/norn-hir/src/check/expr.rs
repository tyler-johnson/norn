use super::turns::effect_arguments;
use super::*;

impl Checker {
    pub(super) fn check_expr(&mut self, expr: &ast::Expr, expected: Option<&Ty>) -> Expr {
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
            ast::ExprKind::Path(path) => self.check_path(path, expected),
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
            } => self.check_call(callee, type_args, args, expected, span),
            ast::ExprKind::Block(block) => self.check_block(block, expected, span),
            ast::ExprKind::If { cond, then, els } => self.check_if(cond, then, els, expected, span),
            ast::ExprKind::While { cond, body } => self.check_while(cond, body, expected, span),
            ast::ExprKind::Loop { body } => self.check_loop(body, expected, span),
            ast::ExprKind::Break { value } => self.check_break(value.as_deref(), span),
            ast::ExprKind::Continue => self.check_continue(span),
            ast::ExprKind::Match { scrutinee, arms } => {
                self.check_match(scrutinee, arms, expected, span)
            }
            ast::ExprKind::Try(inner) => self.check_try(inner, span),
            ast::ExprKind::Index { base, index } => self.check_index(base, index, span),
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

    /// A task built here and started later may not be holding a borrow.
    ///
    /// This is the whole of the escape analysis that is not already a fact about where a reference
    /// can be written. A `Task<T>` is the one value in v0 that outlives the expression that made it,
    /// so it is the one value that could carry a borrow past the call it belongs to. `await f(&x)`
    /// is exempt for a reason worth stating: the awaiting task is parked for the duration, so it
    /// cannot invalidate the borrow itself, and ownership is unique, so no one else can either.
    pub(super) fn no_borrowed_arguments(&mut self, task: &Expr, what: &str, when: &str) {
        for arg in effect_arguments(task) {
            if !arg.ty.is_ref() {
                continue;
            }
            let name = self.program.ty_name(arg.ty.owned());
            self.push(
                Diagnostic::new(arg.span, format!("`{what}` cannot be handed a borrow"))
                    .label(format!("this is borrowed, and the task {when}"))
                    .note(format!(
                        "the work is built here and started later, so it has to own its {name}"
                    ))
                    .note("drop the `&` to move the value in; `await f(&x)` is the form that may borrow, because the task is finished by the time that line is"),
            );
        }
    }

    /// `&` written where ownership was wanted, or left out where a borrow was. Both are one
    /// character from correct, so the diagnostic's job is to say which way the value is going.
    pub(super) fn borrow_mismatch(&mut self, expected: &Ty, span: Span) {
        let name = self.program.ty_name(expected.owned());
        let diagnostic = if expected.is_ref() {
            Diagnostic::new(
                span,
                format!("this borrows the {name} rather than taking it"),
            )
            .label("write `&` here")
            .note("the call only looks at it, so the value stays yours afterwards")
        } else {
            Diagnostic::new(span, format!("this takes the {name}"))
                .label("drop the `&`")
                .note("ownership moves into the call, and the value cannot be used here again")
        };
        self.push(diagnostic);
    }

    pub(super) fn error_expr(&self, span: Span) -> Expr {
        Expr {
            kind: ExprKind::Error,
            ty: Ty::Error,
            span,
        }
    }

    /// Whether the running function may create a task at all, and whether it declared the authority
    /// the task it is creating needs. Both questions belong here, at the point of creation: once a
    /// `Task<T>` is a value, nothing downstream can tell what it will do.
    pub(super) fn require_task_authority(
        &mut self,
        what: &str,
        needs: &[Capability],
        span: Span,
    ) -> bool {
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
    pub(super) fn discarded_task(&mut self, span: Span) {
        self.push(
            Diagnostic::new(span, "this builds a task and then discards it")
                .label("the task never runs")
                .note("`await` it to run it here, or `spawn` it to run it alongside"),
        );
    }

    pub(super) fn check_await(&mut self, inner: &ast::Expr, span: Span) -> Expr {
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
            let diagnostic = Diagnostic::new(span, message)
                .label("not a task")
                .note("a task comes from calling a `task fn`, and nothing else in v0");
            let diagnostic = self.with_opaque_note(diagnostic, &task.ty);
            self.push(diagnostic);
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

    pub(super) fn check_scope(
        &mut self,
        block: &ast::Block,
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
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
        let body = self.check_block(block, expected, block.span);
        let ty = body.ty.clone();
        Expr {
            kind: ExprKind::Scope {
                body: Box::new(body),
            },
            ty,
            span,
        }
    }

    pub(super) fn check_spawn(&mut self, inner: &ast::Expr, span: Span) -> Expr {
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
        let task = self.check_expr(inner, None);
        if task.ty.is_error() {
            return self.error_expr(span);
        }
        self.no_borrowed_arguments(&task, "spawn", "runs after this line");
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

    pub(super) fn check_path(&mut self, path: &ast::Path, expected: Option<&Ty>) -> Expr {
        let span = path.span;
        let head = &path.segments[0];
        // A local shadows everything, including a struct or enum of the same name — which is why
        // `let Shape = …` followed by `Shape.Empty` is a field-access error on the local rather
        // than a construction. The four builtin constructor names are the exception, and only
        // because they are unbindable: nothing can exist for them to shadow.
        let Some(local) = self.lookup_local(&head.name) else {
            if path.segments.len() == 1 && is_builtin_variant(&head.name) {
                return match head.name.as_str() {
                    "None" | "Some" => self.check_option(path, &[], expected, span),
                    _ => self.check_result(path, &[], expected, span),
                };
            }
            // Inside a reactor, a name that does not resolve is very often a member that is real
            // but unreadable *here*, and saying which is the whole difference between a diagnostic
            // that teaches the rule and one that looks like a typo.
            if let Some(sort) = self.members.get(&head.name).copied() {
                self.unreadable_member(&head.name, sort, span);
                return self.error_expr(span);
            }
            // A dotted path whose head names an enum is a variant construction: `Shape.Empty`.
            if path.segments.len() >= 2
                && let Some(TypeName::Enum(id)) = self.ns[self.current].types.get(&head.name)
            {
                let id = *id;
                return self.check_variant_path(id, path, 0, expected, span);
            }
            // A namespace binding answers last among the file-level names, and nothing it answers
            // for can also be a local, a member, or an enum head — collisions were banned at the
            // import, which is what keeps this one lookup rather than a precedence rule.
            if self.ns[self.current].namespaces.contains_key(&head.name) {
                if path.segments.len() == 1 {
                    self.push(
                        Diagnostic::new(
                            span,
                            format!("`{}` is a module namespace, not a value", head.name),
                        )
                        .label("names a file")
                        .note(format!(
                            "reach what it exports through it, as in `{}.name`",
                            head.name
                        )),
                    );
                    return self.error_expr(span);
                }
                return match self.resolve_ns(path) {
                    Some(Ok(NsItem::Enum(id))) => {
                        self.check_variant_path(id, path, 1, expected, span)
                    }
                    Some(Ok(NsItem::Fn(_))) => {
                        self.push(
                            Diagnostic::new(span, "functions are not values yet")
                                .label(format!("`{}` can only be called", path.text()))
                                .note("first-class functions arrive with closures in M7"),
                        );
                        self.error_expr(span)
                    }
                    Some(Ok(NsItem::Struct(_))) => {
                        self.push(
                            Diagnostic::new(
                                span,
                                format!("`{}` is a struct, not a value", path.text()),
                            )
                            .note(format!("construct one, as in `{}(…)`", path.text())),
                        );
                        self.error_expr(span)
                    }
                    Some(Ok(NsItem::Reactor(_))) => {
                        self.push(
                            Diagnostic::new(
                                span,
                                format!("`{}` is a reactor, not a value", path.text()),
                            )
                            .note(format!(
                                "create one with `spawn reactor {}(…)`",
                                path.text()
                            )),
                        );
                        self.error_expr(span)
                    }
                    _ => self.error_expr(span),
                };
            }
            if path.segments.len() == 1 && self.ns[self.current].fns.contains_key(&head.name) {
                self.push(
                    Diagnostic::new(span, "functions are not values yet")
                        .label(format!("`{}` can only be called", head.name))
                        .note("first-class functions arrive with closures in M7"),
                );
            } else if self.ns[self.current].traits.contains_key(&head.name) {
                self.push(
                    Diagnostic::new(span, format!("`{}` is a trait, not a value", head.name))
                        .note("a trait names behaviour: implement it with `impl`, and reach its methods on a value"),
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

    /// A bare dotted path whose head names an enum: `Shape.Empty`, `IoError.NotFound`.
    ///
    /// Only a unit variant can be built without an argument list; a payload-carrying variant is
    /// answered with the arguments it is missing. Segments after the variant are field accesses,
    /// which fail the way field access on an enum always does.
    pub(super) fn check_variant_path(
        &mut self,
        id: EnumId,
        path: &ast::Path,
        first: usize,
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        // `first` is the index of the enum-name segment: 0 for a local head, 1 behind a namespace
        // — `fmt.Shape.Dot` resolves with the same code as `Shape.Dot`.
        if path.segments.len() < first + 2 {
            let written = path.text();
            let example = self.enum_example(id);
            self.push(
                Diagnostic::new(span, format!("`{written}` is an enum"))
                    .note(format!("name the variant, as in `{written}.{example}`")),
            );
            return self.error_expr(span);
        }
        let enum_name = &path.segments[first].name;
        let variant_name = &path.segments[first + 1].name;
        let variant_span = path.segments[0].span.to(path.segments[first + 1].span);
        let Some((index, variant)) = self.program.enums[id.index()].variant(variant_name) else {
            let message = format!("`{enum_name}` has no variant `{variant_name}`");
            self.push(
                Diagnostic::new(path.segments[first + 1].span, message).label("unknown variant"),
            );
            return self.error_expr(span);
        };
        let fields: Vec<String> = if variant.positional {
            variant.fields.iter().map(|_| "…".to_string()).collect()
        } else {
            variant
                .fields
                .iter()
                .map(|f| format!("{}: …", f.name))
                .collect()
        };
        // `Option.None` and friends build `Ty::Option`/`Ty::Result` values whose payload types
        // come from the expectation, so they route through the builtin checkers. They are seeded
        // rather than declared, so no namespace can reach them: `first` is always 0 here.
        if (id == EnumId::OPTION || id == EnumId::RESULT) && path.segments.len() == first + 2 {
            return if id == EnumId::OPTION {
                self.check_option(path, &[], expected, span)
            } else {
                self.check_result(path, &[], expected, span)
            };
        }
        if !fields.is_empty() {
            self.push(
                Diagnostic::new(
                    variant_span,
                    format!("`{enum_name}.{variant_name}` carries a payload"),
                )
                .label("not a unit variant")
                .note(format!(
                    "construct it with its fields, as in `{enum_name}.{variant_name}({})`",
                    fields.join(", ")
                )),
            );
            return self.error_expr(span);
        }
        // The expectation belongs to the whole path: with segments after the variant it is the
        // projection's, not the construction's.
        let expected = if path.segments.len() == first + 2 {
            expected
        } else {
            None
        };
        let mut expr = self.construct_variant(id, index, &[], expected, variant_span);
        for segment in &path.segments[first + 2..] {
            expr = self.field_access(expr, segment, path.segments[0].span.to(segment.span));
        }
        expr
    }

    /// `is_full(count, limit)` — the call to write where a read of a signal was attempted. Naming
    /// the dependencies is the whole point: a call says which values it is a function of, and that
    /// is the question a read leaves open.
    pub(super) fn signal_call_hint(&self, name: &str) -> String {
        let Some(id) = self.reactor else {
            return format!("{name}()");
        };
        let Some(node) = self.node_index(id, name) else {
            return format!("{name}()");
        };
        let reactor = &self.program.reactors[id.index()];
        let deps: Vec<&str> = reactor.nodes[node]
            .deps
            .iter()
            .map(|dep| reactor.nodes[dep.index()].name.as_str())
            .collect();
        format!("{name}({})", deps.join(", "))
    }

    /// A reactor member that exists but is not in scope where it was written.
    pub(super) fn unreadable_member(&mut self, name: &str, sort: Sort, span: Span) {
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
            Sort::Signal => {
                let call = self.signal_call_hint(name);
                Diagnostic::new(
                    span,
                    format!("an `on` handler cannot read the signal `{name}`"),
                )
                .label("signals are recomputed after the handler runs")
                .note("reading it here would mean the previous turn's value, which is never what was meant")
                .note(format!("call it with the values you mean: `{call}`"))
            }
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

    pub(super) fn field_access(&mut self, base: Expr, name: &ast::Ident, span: Span) -> Expr {
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

        // Field access reads through a borrow — `&T` and `T` are the same values — and then
        // strips every `Shared` layer of the base, the same rule lowering applies when it pushes
        // deref projections. A `Ref` is only ever outermost, so one peel is enough; the base
        // keeps its own type, and the borrow is erased before lowering reads it.
        let mut base_ty = base.ty.owned();
        while let Ty::Shared(inner) = base_ty {
            base_ty = inner;
        }
        let Ty::Struct(id) = *base_ty else {
            let message = format!("{} has no fields", self.program.ty_name(&base.ty));
            let diagnostic =
                Diagnostic::new(span, message).label(format!("`{}` accessed here", name.name));
            let diagnostic = self.with_opaque_note(diagnostic, &base.ty);
            self.push(diagnostic);
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let Some((index, field)) = self.program.structs[id.index()].field(&name.name) else {
            let strukt = self.program.structs[id.index()].name.clone();
            self.push(
                Diagnostic::new(
                    name.span,
                    format!("`{strukt}` has no field `{}`", name.name),
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

    /// `data[i]` — sugar for the hidden `bytes_at` builtin, and `Bytes` is the one type it works
    /// on in v0. A `&Bytes` indexes too: borrows are erased before the runtime, so the expansion
    /// is the same expression `check_builtin` would build for a pure two-argument builtin.
    pub(super) fn check_index(&mut self, base: &ast::Expr, index: &ast::Expr, span: Span) -> Expr {
        let base = self.check_expr(base, None);
        if base.ty.is_error() {
            return self.error_expr(span);
        }
        if *base.ty.owned() != Ty::Bytes {
            let message = format!(
                "only `Bytes` can be indexed in v0, not {}",
                self.program.ty_name(&base.ty)
            );
            let diagnostic = Diagnostic::new(span, message)
                .note("collections and their indexing arrive with the standard library");
            let diagnostic = self.with_opaque_note(diagnostic, &base.ty);
            self.push(diagnostic);
            return self.error_expr(span);
        }
        let index = self.check_expr(index, Some(&Ty::I64));
        Expr {
            kind: ExprKind::Builtin {
                builtin: Builtin::BytesAt,
                args: vec![base, index],
            },
            ty: Ty::I64,
            span,
        }
    }

    pub(super) fn check_unary(&mut self, op: ast::UnOp, inner: &ast::Expr, span: Span) -> Expr {
        if matches!(op, ast::UnOp::RefMut) {
            self.exclusive_borrow(span);
            return self.check_expr(inner, None);
        }
        // A borrow erases: the expression is the operand, wearing a type that says the call it is
        // handed to will not take it away. Nothing downstream of the checker learns that `&` was
        // written, which is why lowering and the runtime are untouched by ownership.
        if matches!(op, ast::UnOp::Ref) {
            let mut inner = self.check_expr(inner, None);
            inner.ty = match inner.ty {
                Ty::Ref(_) | Ty::Error | Ty::Never => inner.ty,
                owned => Ty::Ref(Box::new(owned)),
            };
            // The `&` is part of what a diagnostic about this expression should underline, even
            // though it is not part of what the expression evaluates to.
            inner.span = span;
            return inner;
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
                let ty = ty.clone();
                let diagnostic = self.with_opaque_note(Diagnostic::new(span, message), &ty);
                self.push(diagnostic);
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

    pub(super) fn check_binary(
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
                Ty::Bytes => Some((BinOp::Concat, Ty::Bytes)),
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
                Ty::I64 | Ty::F64 | Ty::Bool | Ty::Str | Ty::Bytes => {
                    Some((if op == A::Eq { BinOp::Eq } else { BinOp::Ne }, Ty::Bool))
                }
                // `T: Eq` opens `==` inside the template. Both engines already compare values
                // structurally, and only the scalar types satisfy `Eq`, so the instances this
                // monomorphizes into are exactly the arms above.
                Ty::Param { index, .. }
                    if self
                        .bounds_in_scope
                        .get(*index as usize)
                        .is_some_and(|bounds| bounds.contains(&TraitId::EQ)) =>
                {
                    Some((if op == A::Eq { BinOp::Eq } else { BinOp::Ne }, Ty::Bool))
                }
                _ => None,
            },
            A::Lt | A::Le | A::Gt | A::Ge => match operand {
                Ty::I64 | Ty::F64 | Ty::Str | Ty::Bytes => {
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
                    "structural equality on structs and enums is not derived yet; match instead",
                );
            }
            let operand = operand.clone();
            let diagnostic = self.with_opaque_note(diagnostic, &operand);
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

    pub(super) fn check_block(
        &mut self,
        block: &ast::Block,
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
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

    pub(super) fn check_stmt(&mut self, stmt: &ast::Stmt) -> Stmt {
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
            ast::StmtKind::After { task, returns } => {
                self.check_after(task, returns.as_ref(), span)
            }
            ast::StmtKind::Expr(expr) => StmtKind::Expr(self.check_expr(expr, None)),
        };
        Stmt { kind, span }
    }

    /// `after deliver(m) -> delivered`.
    ///
    /// The operand is *built* here and started only after the snapshot is published. Building runs
    /// nothing — that is what M2's laziness was for — so describing an effect in the middle of a
    /// turn cannot perform one, and no code path exists by which an effect observes an
    /// intermediate graph.
    pub(super) fn check_after(
        &mut self,
        task: &ast::Expr,
        returns: Option<&ast::Ident>,
        span: Span,
    ) -> StmtKind {
        if !self.in_handler {
            self.push(
                Diagnostic::new(span, "`after` is only available inside an `on` handler")
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
        // Unreachable in v0 — a turn has nothing borrowable in scope, because nothing a reactor
        // holds may be affine and a reference cannot be a member. It is written anyway, because the
        // rule belongs to `after` and not to what `after` can currently reach.
        self.no_borrowed_arguments(&task, "after", "starts once the snapshot is published");
        let Ty::Task(produced) = task.ty.clone() else {
            let message = format!(
                "`after` describes work to start later, and this is {}",
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
                        .note("name the input it comes back on: `after … -> handled`"),
                );
                return StmtKind::Expr(self.error_expr(span));
            }
            return StmtKind::After {
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
        StmtKind::After {
            task,
            returns: Some(index),
        }
    }

    /// An assignment target must be a local, or a chain of fields rooted at one, and that local
    /// must be `mut`.
    pub(super) fn check_assignable(&mut self, place: &Expr, span: Span) {
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
                ExprKind::Field { base, .. } => {
                    // A read reaches through a `Shared` (field access derefs), so without this
                    // guard the walk would too — and a shared value is immutable.
                    if matches!(base.ty.owned(), Ty::Shared(_)) {
                        self.push(
                            Diagnostic::new(span, "cannot assign through a shared value")
                                .label("shared values are immutable")
                                .note("`unshare` it, change the copy, and `shared` the result"),
                        );
                        return;
                    }
                    cursor = base;
                }
                ExprKind::Error => return,
                _ => {
                    self.error(span, "only a variable or one of its fields can be assigned");
                    return;
                }
            }
        }
    }
}
