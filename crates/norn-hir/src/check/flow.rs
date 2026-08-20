use super::*;

impl Checker {
    pub(super) fn check_if(
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

    pub(super) fn check_while(
        &mut self,
        cond: &ast::Expr,
        body: &ast::Block,
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        if self.ctx.in_turn() {
            self.unterminating("while", span);
            return self.error_expr(span);
        }
        // The frame opens before the condition: a `break` in a condition targets this loop, because
        // the condition re-runs every iteration and is as much part of the loop as the body.
        self.loops.push(LoopCtx {
            is_loop: false,
            result: None,
            saw_break: false,
            first_value: None,
        });
        let cond = self.check_expr(cond, Some(&Ty::Bool));
        let body = self.check_block(body, Some(&Ty::Unit), body.span);
        self.loops.pop();
        if let Some(expected) = expected
            && !Ty::Unit.fits(expected)
        {
            let message = format!("expected {}, found ()", self.program.ty_name(expected));
            self.push(Diagnostic::new(span, message).note(
                "a `while` produces `()`; `loop` with `break value` is how a loop yields one",
            ));
            return self.error_expr(span);
        }
        Expr {
            kind: ExprKind::While {
                cond: Box::new(cond),
                body: Box::new(body),
            },
            ty: Ty::Unit,
            span,
        }
    }

    pub(super) fn check_loop(
        &mut self,
        body: &ast::Block,
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        if self.ctx.in_turn() {
            self.unterminating("loop", span);
            return self.error_expr(span);
        }
        self.loops.push(LoopCtx {
            is_loop: true,
            result: expected.cloned(),
            saw_break: false,
            first_value: None,
        });
        let body = self.check_block(body, Some(&Ty::Unit), body.span);
        let frame = self.loops.pop().expect("pushed above");
        // No `break` at all means the expression never produces a value; only bare breaks mean it
        // produces nothing in particular.
        let ty = if frame.saw_break {
            frame.result.unwrap_or(Ty::Unit)
        } else {
            Ty::Never
        };
        Expr {
            kind: ExprKind::Loop {
                body: Box::new(body),
            },
            ty,
            span,
        }
    }

    pub(super) fn check_break(&mut self, value: Option<&ast::Expr>, span: Span) -> Expr {
        if self.loops.is_empty() {
            self.push(
                Diagnostic::new(span, "`break` is only available inside a loop")
                    .label("there is no loop to leave"),
            );
            return self.error_expr(span);
        }
        let last = self.loops.len() - 1;
        let value = match value {
            Some(value) if !self.loops[last].is_loop => {
                self.push(
                    Diagnostic::new(span, "`break` can only carry a value out of a `loop`")
                        .label("this `while` produces ()"),
                );
                // The value is still checked for its own errors; the break itself stays bare so
                // nothing downstream cascades.
                self.check_expr(value, None);
                self.loops[last].saw_break = true;
                None
            }
            Some(value) => {
                // First break wins: it settles the loop's type, and every later break is checked
                // against it — the same first-arm-wins agreement a `match` uses.
                let expected = self.loops[last].result.clone();
                let checked = self.check_expr(value, expected.as_ref());
                let frame = &mut self.loops[last];
                frame.saw_break = true;
                if frame.result.is_none() && checked.ty != Ty::Never && !checked.ty.is_error() {
                    frame.result = Some(checked.ty.clone());
                }
                if frame.first_value.is_none() {
                    frame.first_value = Some(span);
                }
                Some(Box::new(checked))
            }
            None => {
                self.loops[last].saw_break = true;
                let is_loop = self.loops[last].is_loop;
                let result = self.loops[last].result.clone();
                let first_value = self.loops[last].first_value;
                match result {
                    Some(result) if is_loop && !Ty::Unit.fits(&result) => {
                        let result = self.program.ty_name(&result);
                        let mut diagnostic = Diagnostic::new(span, "`break` needs a value here")
                            .label(format!(
                                "this leaves the loop with nothing, and the loop produces {result}"
                            ));
                        if let Some(at) = first_value {
                            diagnostic =
                                diagnostic.secondary(at, "the loop's type was settled here");
                        }
                        self.push(diagnostic);
                    }
                    Some(_) => {}
                    None => {
                        if is_loop {
                            self.loops[last].result = Some(Ty::Unit);
                        }
                    }
                }
                None
            }
        };
        Expr {
            kind: ExprKind::Break { value },
            ty: Ty::Never,
            span,
        }
    }

    pub(super) fn check_continue(&mut self, span: Span) -> Expr {
        if self.loops.is_empty() {
            self.push(
                Diagnostic::new(span, "`continue` is only available inside a loop")
                    .label("there is no loop to continue"),
            );
            return self.error_expr(span);
        }
        Expr {
            kind: ExprKind::Continue,
            ty: Ty::Never,
            span,
        }
    }

    pub(super) fn check_match(
        &mut self,
        scrutinee: &ast::Expr,
        arms: &[ast::Arm],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let scrutinee = self.check_expr(scrutinee, None);
        // A `match` on an affine value takes it apart — a consumption fact `infer_sinks` reads
        // per instance — so there is no non-consuming deconstruction left to gate here.
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
    pub(super) fn check_exhaustive(&mut self, arms: &[Arm], scrutinee: &Ty, span: Span) {
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
                PatKind::Struct { .. } => covered.push(usize::MAX),
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
            .map(|(_, variant)| format!("{name}.{}", variant.name))
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

    pub(super) fn check_try(&mut self, inner: &ast::Expr, span: Span) -> Expr {
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
                let other = other.clone();
                let diagnostic = self.with_opaque_note(Diagnostic::new(span, message), &other);
                self.push(diagnostic);
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
        }
    }

    // ---------------------------------------------------------------- patterns

    pub(super) fn check_pat(&mut self, pat: &ast::Pat, ty: &Ty) -> Pat {
        let span = pat.span;
        match &pat.kind {
            ast::PatKind::Wild => Pat {
                kind: PatKind::Wild,
                span,
            },
            ast::PatKind::Binding(name) => {
                // The four builtin constructor names never bind: `None =>` is the arm that
                // matches the empty Option, not a catch-all, and unbindability is what makes
                // reading it that way safe.
                if is_builtin_variant(&name.name) {
                    return self.builtin_variant_pat(&name.name, &[], false, ty, span);
                }
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

    pub(super) fn expect_pat_ty(&mut self, found: &Ty, expected: &Ty, span: Span) {
        if !found.fits(expected) {
            let message = format!(
                "this pattern matches {}, but the value is {}",
                self.program.ty_name(found),
                self.program.ty_name(expected)
            );
            self.error(span, message);
        }
    }

    pub(super) fn check_construct_pat(
        &mut self,
        path: &ast::Path,
        args: &[ast::PatArg],
        rest: bool,
        ty: &Ty,
        span: Span,
    ) -> Pat {
        // Resolve the builtin constructors against the type being matched, so `Some(x)` and
        // `Ok(x)` need no qualification and pick up their payload type from the scrutinee.
        if path.segments.len() == 1 && is_builtin_variant(&path.last().name) {
            let name = path.last().name.clone();
            return self.builtin_variant_pat(&name, args, rest, ty, span);
        }

        match path.segments.len() {
            1 => {
                let name = path.last().name.clone();
                let Some(TypeName::Struct(id)) = self.ns[self.current].types.get(&name) else {
                    self.error(span, format!("unknown struct `{name}`"));
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                let id = *id;
                self.struct_pat(id, &name, args, rest, ty, span)
            }
            2 => {
                let enum_name = path.segments[0].name.clone();
                let variant_name = path.segments[1].name.clone();
                if let Some(TypeName::Enum(id)) = self.ns[self.current].types.get(&enum_name) {
                    let id = *id;
                    // `Option.Some(x)` and friends: their scrutinees are `Ty::Option`/`Ty::Result`
                    // rather than `Ty::Enum`, so they route through the builtin resolution once
                    // the variant name is known to be real.
                    if id == EnumId::OPTION || id == EnumId::RESULT {
                        if self.program.enums[id.index()]
                            .variant(&variant_name)
                            .is_none()
                        {
                            let message = format!("`{enum_name}` has no variant `{variant_name}`");
                            self.push(
                                Diagnostic::new(path.segments[1].span, message)
                                    .label("unknown variant"),
                            );
                            return Pat {
                                kind: PatKind::Error,
                                span,
                            };
                        }
                        return self.builtin_variant_pat(&variant_name, args, rest, ty, span);
                    }
                    return self.variant_pat(
                        id,
                        &enum_name,
                        &variant_name,
                        path.segments[1].span,
                        args,
                        rest,
                        ty,
                        span,
                    );
                }
                // `fmt.Config(width: w)` — an imported struct matched through its namespace.
                if self.ns[self.current].namespaces.contains_key(&enum_name) {
                    return match self.resolve_ns(path) {
                        Some(Ok(NsItem::Struct(id))) => {
                            self.struct_pat(id, &path.text(), args, rest, ty, span)
                        }
                        Some(Ok(NsItem::Enum(id))) => {
                            let written = path.text();
                            let example = self.enum_example(id);
                            self.push(
                                Diagnostic::new(span, format!("`{written}` is an enum"))
                                    .note(format!("name the variant, as in `{written}.{example}`")),
                            );
                            Pat {
                                kind: PatKind::Error,
                                span,
                            }
                        }
                        Some(Ok(_)) => {
                            self.error(span, format!("unknown constructor `{}`", path.text()));
                            Pat {
                                kind: PatKind::Error,
                                span,
                            }
                        }
                        _ => Pat {
                            kind: PatKind::Error,
                            span,
                        },
                    };
                }
                self.error(path.segments[0].span, format!("unknown enum `{enum_name}`"));
                Pat {
                    kind: PatKind::Error,
                    span,
                }
            }
            3 if self.ns[self.current]
                .namespaces
                .contains_key(&path.segments[0].name) =>
            {
                // `fmt.Shape.Dot(p)` — an imported enum's variant matched through its namespace.
                match self.resolve_ns(path) {
                    Some(Ok(NsItem::Enum(id))) => {
                        let display =
                            format!("{}.{}", path.segments[0].name, path.segments[1].name);
                        self.variant_pat(
                            id,
                            &display,
                            &path.segments[2].name.clone(),
                            path.segments[2].span,
                            args,
                            rest,
                            ty,
                            span,
                        )
                    }
                    Some(Ok(_)) => {
                        self.error(span, format!("unknown constructor `{}`", path.text()));
                        Pat {
                            kind: PatKind::Error,
                            span,
                        }
                    }
                    _ => Pat {
                        kind: PatKind::Error,
                        span,
                    },
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

    /// A struct pattern, once the struct is resolved: `Config(width: w)`, spelled locally or
    /// through a namespace.
    pub(super) fn struct_pat(
        &mut self,
        id: StructId,
        display: &str,
        args: &[ast::PatArg],
        rest: bool,
        ty: &Ty,
        span: Span,
    ) -> Pat {
        // A pattern naming a template matches through the scrutinee's instance: `Pair(a, b)`
        // against a `Pair<I64, Bool>` proceeds with the instance id, whose fields are concrete,
        // so the sub-patterns type through untouched machinery.
        let id = match ty {
            Ty::Struct(scrutinee)
                if *scrutinee != id
                    && self
                        .struct_base(*scrutinee)
                        .is_some_and(|(base, _)| base == id) =>
            {
                *scrutinee
            }
            _ => id,
        };
        self.expect_pat_ty(&Ty::Struct(id), ty, span);
        let strukt = &self.program.structs[id.index()];
        let names: Vec<String> = strukt.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = strukt.fields.iter().map(|f| f.ty.clone()).collect();
        let Some(sub) = self.pat_args(&names, &types, args, rest, display, span) else {
            return Pat {
                kind: PatKind::Error,
                span,
            };
        };
        Pat {
            kind: PatKind::Struct {
                strukt: id,
                args: sub,
            },
            span,
        }
    }

    /// A user enum's variant pattern, once the enum is resolved. Option and Result never arrive
    /// here — their scrutinees carry their own `Ty` spellings and route through the builtin path.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn variant_pat(
        &mut self,
        id: EnumId,
        enum_display: &str,
        variant_name: &str,
        variant_span: Span,
        args: &[ast::PatArg],
        rest: bool,
        ty: &Ty,
        span: Span,
    ) -> Pat {
        // The struct-pattern rule again: a template named in a pattern proceeds with the
        // scrutinee's instance, whose payload types are concrete.
        let id = match ty {
            Ty::Enum(scrutinee)
                if *scrutinee != id
                    && self
                        .enum_base(*scrutinee)
                        .is_some_and(|(base, _)| base == id) =>
            {
                *scrutinee
            }
            _ => id,
        };
        self.expect_pat_ty(&Ty::Enum(id), ty, span);
        let Some((index, variant)) = self.program.enums[id.index()].variant(variant_name) else {
            let message = format!("`{enum_display}` has no variant `{variant_name}`");
            self.push(Diagnostic::new(variant_span, message).label("unknown variant"));
            return Pat {
                kind: PatKind::Error,
                span,
            };
        };
        let names: Vec<String> = variant.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = variant.fields.iter().map(|f| f.ty.clone()).collect();
        let subject = format!("{enum_display}.{variant_name}");
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

    /// One of the four bare constructor names in a pattern, resolved against the scrutinee — which
    /// is what lets `Some(x)` and `Ok(x)` need no qualification and pick up their payload type.
    pub(super) fn builtin_variant_pat(
        &mut self,
        name: &str,
        args: &[ast::PatArg],
        rest: bool,
        ty: &Ty,
        span: Span,
    ) -> Pat {
        let resolved = match (name, ty) {
            ("None", Ty::Option(_)) => Some((EnumId::OPTION, EnumId::NONE, Vec::new())),
            ("Some", Ty::Option(inner)) => {
                Some((EnumId::OPTION, EnumId::SOME, vec![(**inner).clone()]))
            }
            ("Ok", Ty::Result(ok, _)) => Some((EnumId::RESULT, EnumId::OK, vec![(**ok).clone()])),
            ("Err", Ty::Result(_, err)) => {
                Some((EnumId::RESULT, EnumId::ERR, vec![(**err).clone()]))
            }
            _ => None,
        };
        let Some((enum_id, variant, types)) = resolved else {
            let message = format!(
                "`{name}` matches Option or Result, but the value is {}",
                self.program.ty_name(ty)
            );
            self.error(span, message);
            return Pat {
                kind: PatKind::Error,
                span,
            };
        };
        let names: Vec<String> = (0..types.len()).map(|i| i.to_string()).collect();
        let Some(sub) = self.pat_args(&names, &types, args, rest, name, span) else {
            return Pat {
                kind: PatKind::Error,
                span,
            };
        };
        Pat {
            kind: PatKind::Variant {
                enum_id,
                variant,
                args: sub,
            },
            span,
        }
    }

    /// Expand a constructor pattern's arguments to full arity in declaration order, filling the
    /// gaps `..` leaves with wildcards.
    pub(super) fn pat_args(
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

pub(super) fn binds_anything(pat: &Pat) -> bool {
    match &pat.kind {
        PatKind::Bind(_) => true,
        PatKind::Variant { args, .. } | PatKind::Struct { args, .. } => {
            args.iter().any(binds_anything)
        }
        PatKind::Or(alts) => alts.iter().any(binds_anything),
        _ => false,
    }
}
