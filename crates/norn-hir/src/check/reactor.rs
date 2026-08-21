use super::*;

impl Checker {
    /// Pass one: names, parameters, capabilities, input and state *types*, and the member
    /// namespace. No expression is looked at — the scan that decides what order to look at them in
    /// has not run yet.
    pub(super) fn declare_reactors(&mut self, module: &ast::Module) {
        for (id, decl) in self.reactor_items(module) {
            // Lifted member names hang off the reactor's display name, so a non-entry module's
            // members compose to "fmt.Gate.on.opened". In-file diagnostics keep the written name.
            let display = self.program.reactors[id.index()].name.clone();
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
                if is_builtin_variant(&name.name) {
                    checker.push(
                        Diagnostic::new(
                            name.span,
                            format!("`{}` cannot be the name of a member", name.name),
                        )
                        .label("a built-in constructor")
                        .note("`None`, `Some`, `Ok`, and `Err` always name the Option and Result constructors"),
                    );
                    return false;
                }
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
                // Modes are a fact about calls; a reactor parameter is state, written once when
                // the reactor is created, and spawning already hands the arguments over.
                let mode = match param.mode {
                    ast::ParamMode::Read => None,
                    ast::ParamMode::Sink(at) => Some(("sink", at)),
                    ast::ParamMode::Mut(at) => Some(("mut", at)),
                };
                if let Some((word, at)) = mode {
                    self.push(
                        Diagnostic::new(at, "a reactor parameter has no mode")
                            .label(format!("`{word}` does not apply here"))
                            .note("`spawn reactor` always hands its arguments over; there is no call for a mode to describe"),
                    );
                }
                let ty = self.resolve_ty(&param.ty);
                let ty = self.reactor_ty(ty, "parameter", &param.name.name, param.span);
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

            // Positions of `on` members that meant to declare an input and did not: a type with no
            // queue clause, a clause with no type, or a name already taken. Each has been reported
            // once already, and pairing them again as "has no input" would bury the diagnostic
            // that says what to write.
            let mut undeclared: Vec<usize> = Vec::new();
            for (position, member) in decl.members.iter().enumerate() {
                match &member.kind {
                    ast::MemberKind::Input { name, ty, queue } => {
                        if !claim(self, &mut taken, name) {
                            continue;
                        }
                        let ty = self.resolve_ty(ty);
                        let ty = self.reactor_ty(ty, "input", &name.name, member.span);
                        let capacity = self.capacity(&queue.capacity);
                        let overflow = self.overflow(&queue.overflow);
                        let handler =
                            self.declare_lifted(format!("{display}.on.{}", name.name), member.span);
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
                        let ty = self.reactor_ty(ty, "state cell", &name.name, member.span);
                        let init = self
                            .declare_lifted(format!("{display}.{}.init", name.name), member.span);
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
                        let body =
                            self.declare_lifted(format!("{display}.{}", name.name), member.span);
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
                    // A queue clause is what makes an `on` a declaration: with one, this member
                    // *is* the input, and does everything the `Input` arm above does. Without one
                    // it declares nothing, so it claims nothing — the `input` it answers to owns
                    // the name.
                    ast::MemberKind::On {
                        input,
                        params,
                        queue,
                        ..
                    } => {
                        let Some(queue) = queue else {
                            if let Some(param) = params.iter().find(|p| p.ty.is_some()) {
                                self.push(
                                    Diagnostic::new(
                                        param.span,
                                        format!(
                                            "a type here declares `{}`, so it needs a queue policy",
                                            input.name
                                        ),
                                    )
                                    .label("no queue policy")
                                    .note(format!(
                                        "an input is a bounded mailbox: write `on {name}({bound}: …) [capacity: …, overflow: …]`, or drop the type and let an `input {name}` member declare it",
                                        name = input.name,
                                        bound = param.name.name,
                                    )),
                                );
                                undeclared.push(position);
                            }
                            continue;
                        };
                        if !claim(self, &mut taken, input) {
                            undeclared.push(position);
                            continue;
                        }
                        // The parameter *defines* the message type here rather than being checked
                        // against one, so an untyped parameter leaves nothing to declare.
                        let ty = match params.first() {
                            None => Ty::Unit,
                            Some(param) => match &param.ty {
                                Some(ty) => {
                                    let ty = self.resolve_ty(ty);
                                    self.reactor_ty(ty, "input", &input.name, param.span)
                                }
                                None => {
                                    self.push(
                                        Diagnostic::new(
                                            param.span,
                                            format!(
                                                "`{}` is declared here, so `{}` needs the message type",
                                                input.name, param.name.name
                                            ),
                                        )
                                        .label("no type on the message")
                                        .secondary(queue.span, "this queue clause declares the input")
                                        .note(format!(
                                            "write `on {name}({bound}: …) [capacity: …, overflow: …]`, or drop the clause and let an `input {name}` member declare it",
                                            name = input.name,
                                            bound = param.name.name,
                                        )),
                                    );
                                    Ty::Error
                                }
                            },
                        };
                        let capacity = self.capacity(&queue.capacity);
                        let overflow = self.overflow(&queue.overflow);
                        let handler = self
                            .declare_lifted(format!("{display}.on.{}", input.name), member.span);
                        inputs.push(InputDef {
                            name: input.name.clone(),
                            ty,
                            capacity,
                            overflow,
                            handler,
                            plan: Vec::new(),
                            // The declaring half of the member, not the body: a diagnostic that
                            // points at "the input" should not underline the whole handler.
                            span: input.span.to(queue.span),
                        });
                    }
                }
            }

            // A handler is matched to its input by name, so both directions have to be checked:
            // an input with no handler can never do anything, and a handler for no input responds
            // to a message that cannot arrive.
            let mut handled: Vec<usize> = Vec::new();
            for (position, member) in decl.members.iter().enumerate() {
                let ast::MemberKind::On { input, .. } = &member.kind else {
                    continue;
                };
                // A member that meant to declare and did not still *handles* whatever the name
                // turns out to mean, so it pairs as usual — it just says nothing more about it.
                let reported = undeclared.contains(&position);
                let Some(index) = inputs.iter().position(|i| i.name == input.name) else {
                    if reported {
                        continue;
                    }
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
                    if reported {
                        continue;
                    }
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
    pub(super) fn scan_reactors(&mut self, module: &ast::Module) -> Vec<Wiring> {
        let mut wirings = Vec::new();
        for (id, decl) in self.reactor_items(module) {
            wirings.push(self.scan_reactor(id, decl));
        }
        wirings
    }

    pub(super) fn scan_reactor(&mut self, id: ReactorId, decl: &ast::ReactorDecl) -> Wiring {
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
                    // Calling a signal is calling a function of nodes that have no value yet, for
                    // the same reason reading one is: there has been no turn.
                    for (found, span) in &scan.calls {
                        if Builtin::from_name(found).is_some()
                            || self.ns[self.current].fns.contains_key(found)
                            || self.ns[self.current].types.contains_key(found)
                        {
                            continue;
                        }
                        let Some(sort) = members.get(found) else {
                            continue;
                        };
                        self.push(
                            Diagnostic::new(
                                *span,
                                format!(
                                    "a `state` initialiser cannot call the {} `{found}`",
                                    sort.describe()
                                ),
                            )
                            .label("initialisers run before the first turn")
                            .note("read a constructor parameter instead, or derive the value with a signal"),
                        );
                        ok = false;
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
                    // Calling a signal names its *definition* rather than its value, so it is not a
                    // read — but the callee's body has to be typed before this one, and an edge is
                    // what says so. The edge is redundant at runtime rather than wrong: whatever
                    // moved the callee's value moved one of the arguments passed to it too.
                    for (found, _) in &scan.calls {
                        if Builtin::from_name(found).is_some()
                            || self.ns[self.current].fns.contains_key(found)
                            || self.ns[self.current].types.contains_key(found)
                        {
                            continue;
                        }
                        if let Some(Sort::Signal) = members.get(found) {
                            let dep = self.node_index(id, found).expect("a member with a sort");
                            push_once(&mut deps[node], dep);
                        }
                    }
                }
                ast::MemberKind::On {
                    input,
                    params,
                    body,
                    ..
                } => {
                    let Some(index) = self.program.reactors[id.index()].input(&input.name) else {
                        continue;
                    };
                    // The handler's own message binding shadows any member of the same name.
                    let mut scan = Scan::new(&members);
                    for param in params {
                        scan.bind(&param.name.name);
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
    pub(super) fn check_reactors(&mut self, module: &ast::Module, wirings: Vec<Wiring>) {
        for ((id, decl), wiring) in self.reactor_items(module).into_iter().zip(wirings) {
            if !wiring.ok {
                continue;
            }
            self.check_reactor(id, decl, &wiring);
        }
    }

    pub(super) fn check_reactor(
        &mut self,
        id: ReactorId,
        decl: &ast::ReactorDecl,
        wiring: &Wiring,
    ) {
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
            let (body, annotation, signal) = match &member.kind {
                ast::MemberKind::State { ty, init, .. } => (init, Some(ty), None),
                ast::MemberKind::Signal { name, ty, body, .. } => {
                    (body, ty.as_ref(), Some(name.name.clone()))
                }
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
            // A signal's type is inferred rather than written, so the affinity rule has to be
            // applied to what came out. Nothing in v0 can reach an affine value from inside a turn
            // — the purity rules see to that — so this is a backstop rather than a diagnostic
            // anyone is expected to meet, and it stays right as the turn vocabulary grows. `state`
            // is not re-checked here; its written type was answered in `declare_reactors`.
            let ty = match &signal {
                Some(signal) => self.reactor_ty(ty, "signal", signal, node_span),
                None => ty,
            };
            self.finish_member(function, ty.clone(), checked);
            self.program.reactors[id.index()].nodes[node].ty = ty;
        }

        // Handlers last: every node type is known by now, so a handler can be checked in one pass
        // whatever order it was written in.
        for member in &decl.members {
            let ast::MemberKind::On {
                input,
                params,
                body,
                ..
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
    ///
    /// In the split form this is a rule the handler is checked against. In the merged form it is
    /// the *definition* — `declare_reactors` read the message type off the parameter, so an `on`
    /// with no parameter is what makes an input carry `()` — and checking it here is then a
    /// tautology that costs nothing and keeps one code path.
    pub(super) fn bind_message(
        &mut self,
        input: &str,
        params: &[ast::HandlerParam],
        ty: &Ty,
        span: Span,
    ) {
        let wanted = if *ty == Ty::Unit { 0 } else { 1 };
        if params.len() == wanted {
            if let Some(param) = params.first() {
                self.declare_role(
                    param.name.name.clone(),
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
                param.name.name.clone(),
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
    pub(super) fn begin_member(
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
        self.loops = Vec::new();
        // Reactors declare no type parameters, so nothing generic is ever in scope here.
        self.type_params_in_scope.clear();
        self.bounds_in_scope.clear();
        self.reactor = Some(id);
        self.in_handler = handler;
        // A node body sees only what it depends on; a handler sees state but never a signal. Both
        // are expressed by simply not binding the rest, with `members` supplying the diagnostic.
        self.members = members.clone();
        let _ = reactor_name;
    }

    pub(super) fn bind_node(&mut self, id: ReactorId, node: usize, mutable: bool) {
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

    pub(super) fn finish_member(&mut self, function: FnId, ret: Ty, body: Expr) {
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
    pub(super) fn plans(&mut self, id: ReactorId, wiring: &Wiring) {
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

    /// Nothing a reactor holds may be affine.
    ///
    /// Two reasons, and the second settles it on its own. A reactor's slots are the durable state
    /// projection `DESIGN.md` §14 asks for, and a descriptor is not part of any projection — it
    /// cannot be written down, restored, or replayed. And an input declared `overflow: drop_oldest`
    /// discards messages by design, so a mailbox carrying handles would leak one every time it
    /// filled, silently, with nobody to blame. Keeping ownership out of the graph is what
    /// `examples/reactors/server.norn` already does on purpose: the reactor counts sockets and
    /// never holds one.
    pub(super) fn reactor_ty(&mut self, ty: Ty, what: &str, name: &str, span: Span) -> Ty {
        if !self.program.affine(&ty) {
            return ty;
        }
        let spelled = self.program.ty_name(&ty);
        self.push(
            Diagnostic::new(
                span,
                format!("a reactor's {what} cannot hold a `{spelled}`"),
            )
            .label(format!("`{name}` would own something the graph cannot close"))
            .note("a reactor's state is a value that could be written down and restored, and an open descriptor is not")
            .note("count what a task owns and send the reactor the count: see `examples/reactors/server.norn`"),
        );
        Ty::Error
    }

    pub(super) fn member_namespace(&self, id: ReactorId) -> HashMap<String, Sort> {
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

    pub(super) fn node_index(&self, id: ReactorId, name: &str) -> Option<usize> {
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
    pub(super) fn find_cycle(&self, id: ReactorId, deps: &[Vec<usize>]) -> Option<Vec<usize>> {
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
    pub(super) fn report_cycle(&mut self, id: ReactorId, cycle: &[usize]) {
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

    pub(super) fn capacity(&mut self, expr: &ast::Expr) -> usize {
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

    pub(super) fn overflow(&mut self, name: &ast::Ident) -> Overflow {
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
}

/// What the syntactic scan worked out about one reactor.
pub(super) struct Wiring {
    /// Dependency node indices per node, in the order the lifted function takes them.
    pub(super) deps: Vec<Vec<usize>>,
    /// A topological order over the whole graph.
    pub(super) order: Vec<usize>,
    /// Per input, the state nodes its handler assigns.
    pub(super) writes: Vec<Vec<usize>>,
    /// False when the graph could not be built — a cycle, or a reference that is not a node. The
    /// bodies are then left unchecked rather than reported against a graph that does not exist.
    pub(super) ok: bool,
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
    /// Member names in *call* position. Separate from `reads` because whether one is a dependency
    /// depends on what the name resolves to, and a scan does not resolve — a built-in or a
    /// top-level `fn` of the same name wins, and only the checker knows those.
    calls: Vec<(String, Span)>,
}

impl<'a> Scan<'a> {
    fn new(members: &'a HashMap<String, Sort>) -> Scan<'a> {
        Scan {
            members,
            bound: vec![Vec::new()],
            reads: Vec::new(),
            writes: Vec::new(),
            calls: Vec::new(),
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

    fn call(&mut self, name: &str, span: Span) {
        if self.is_bound(name) || !self.members.contains_key(name) {
            return;
        }
        if !self.calls.iter().any(|(seen, _)| seen == name) {
            self.calls.push((name.to_string(), span));
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
                // A path callee is never a *read*: scanning it would make a member named like a
                // function into a dependency of everything that calls it. It is recorded as a call
                // instead, because calling a signal does create an edge — the callee's body has to
                // be typed before the caller's — and only the checker can tell the two apart.
                match &callee.kind {
                    ast::ExprKind::Path(path) if path.segments.len() == 1 => {
                        let head = &path.segments[0];
                        self.call(&head.name, head.span);
                    }
                    ast::ExprKind::Path(_) => {}
                    _ => self.expr(callee),
                }
                for arg in args {
                    self.expr(&arg.value);
                }
            }
            ast::ExprKind::SpawnReactor { args, .. } => {
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
            // A loop binds nothing; even a `break` value has to be scanned, because a member read
            // in it is a dependency like any other.
            ast::ExprKind::While { cond, body } => {
                self.expr(cond);
                self.block(body);
            }
            ast::ExprKind::Loop { body } => self.block(body),
            ast::ExprKind::Break { value } => {
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            ast::ExprKind::Continue => {}
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
                ast::StmtKind::After { task, .. } => self.expr(task),
                ast::StmtKind::Expr(expr) => self.expr(expr),
            }
        }
        self.bound.pop();
    }

    fn pat(&mut self, pat: &ast::Pat) {
        match &pat.kind {
            // The four builtin constructor names are matches, not bindings, and unbindable
            // besides — so they never shadow a member.
            ast::PatKind::Binding(name) if is_builtin_variant(&name.name) => {}
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

pub(super) fn push_once(list: &mut Vec<usize>, value: usize) {
    if !list.contains(&value) {
        list.push(value);
    }
}

/// The member declaration a node came from.
pub(super) fn member_for<'m>(decl: &'m ast::ReactorDecl, name: &str) -> Option<&'m ast::Member> {
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
pub(super) fn count_extra(locals: &[LocalDef]) -> usize {
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
pub(super) fn topological(deps: &[Vec<usize>]) -> Vec<usize> {
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

/// The local a projection chain is rooted at: `a` in `a.b.c`.
pub(super) fn head_name(expr: &ast::Expr) -> Option<(String, Span)> {
    match &expr.kind {
        ast::ExprKind::Path(path) => {
            let head = &path.segments[0];
            Some((head.name.clone(), head.span))
        }
        ast::ExprKind::Field { base, .. } | ast::ExprKind::Index { base, .. } => head_name(base),
        _ => None,
    }
}
