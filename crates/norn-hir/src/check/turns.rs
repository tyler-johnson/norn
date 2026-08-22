use super::*;

impl Checker {
    /// The one diagnostic every purity rule shares. A turn is not a place where the world can
    /// notice anything happening, and every way to break that says so the same way.
    pub(super) fn impure(&mut self, what: &str, does: &str, span: Span) {
        self.push(
            Diagnostic::new(
                span,
                format!("`{what}` cannot appear in a reactor, because it {does}"),
            )
            .label("a turn is pure")
            .note(
                "a turn runs to a fixed point with nothing able to observe it part-way; effects leave it through `after`",
            ),
        );
    }

    /// The other diagnostic a turn's rules share. Purity is why a turn cannot be observed;
    /// termination is why it is over. A loop is the one construct whose finiteness the checker
    /// cannot see, so turn-reachable code may not contain one — the same shape as the recursion
    /// rule, and together they are what keeps every turn provably terminating.
    pub(super) fn unterminating(&mut self, what: &str, span: Span) {
        self.push(
            Diagnostic::new(
                span,
                format!("a `{what}` cannot appear in a turn, because a turn must end"),
            )
            .label("a loop is not provably finite")
            .note(
                "turn-reachable code has neither loops nor recursion, which is what makes every turn provably terminating",
            )
            .note("compute the value with a bounded expression, or move the work into a `task fn` and request it with `after`"),
        );
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
    /// functions, cost annotations, cooperative budgets. The answer is still a theorem, narrowed
    /// from the language to the turn-reachable subgraph: code a turn can reach may contain neither
    /// recursion nor loops, so a turn is a finite tree of calls over bounded expressions and must
    /// return. One pass over the call graph proves it, with no annotation burden and no runtime
    /// budget — loops and recursion live in `fn`s and `task fn`s, which is where every corpus
    /// shape already wants them.
    pub(super) fn check_turns(&mut self) {
        let mut turn_fns: Vec<(FnId, Span, usize)> = Vec::new();
        for (index, reactor) in self.program.reactors.iter().enumerate() {
            let owner = self.reactor_owner[index];
            for node in &reactor.nodes {
                match node.kind {
                    NodeKind::Param { .. } => {}
                    NodeKind::State { init, .. } => turn_fns.push((init, node.span, owner)),
                    NodeKind::Signal { body, .. } => turn_fns.push((body, node.span, owner)),
                }
            }
            for input in &reactor.inputs {
                turn_fns.push((input.handler, input.span, owner));
            }
            // Creation is a turn, so `init` is subject to every rule a handler is. Its lifted
            // function carries the member's own span, which is where a diagnostic belongs.
            if let Some(init) = reactor.init {
                turn_fns.push((init, self.program.fns[init.index()].span, owner));
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
        let loops: Vec<Option<(&'static str, Span)>> = self
            .program
            .fns
            .iter()
            .map(|def| first_loop(&def.body))
            .collect();

        for (function, span, owner) in turn_fns {
            // The diagnostics land in the file that owns the reactor — the turn is what has to
            // change, wherever the function it reaches was written.
            self.current = owner;
            // Reported once per turn function even when several reachable functions are impure:
            // the first one is what has to change, and listing the rest is noise until it does.
            if let Some((culprit, builtin, at)) = reachable_impurity(&calls, &impurities, function)
                && culprit != function
            {
                let name = self.program.fns[culprit.index()].name.clone();
                let mut diagnostic = Diagnostic::new(
                    span,
                    format!("this reaches `{}`, which calls `{}`", name, builtin.name()),
                )
                .label("a turn is pure");
                // A secondary span renders against *this* file's text, so one that points into
                // another module has to travel as a note instead: the name carries the location.
                let culprit_owner = self.fn_owner[culprit.index()];
                diagnostic = if culprit_owner == owner {
                    diagnostic.secondary(
                        at,
                        format!("`{}` is something the world can see happen", builtin.name()),
                    )
                } else {
                    diagnostic.note(format!(
                        "`{}` is something the world can see happen; `{name}` calls it in {}",
                        builtin.name(),
                        self.names[culprit_owner]
                    ))
                };
                self.push(
                    diagnostic
                        .note("purity is not the same question as authority: `print` needs no capability and is still observable")
                        .note("effects leave a turn through `after`, which starts them once the snapshot is published"),
                );
            }

            // The other half of the termination rule. The direct guard already refused a loop
            // written in the turn itself, so only a loop reached through a call is news here —
            // hence the same `culprit != function` shape the impurity report has.
            if let Some((culprit, what, at)) = reachable_loop(&calls, &loops, function)
                && culprit != function
            {
                let name = self.program.fns[culprit.index()].name.clone();
                let mut diagnostic = Diagnostic::new(
                    span,
                    format!("this reaches `{name}`, which contains a `{what}`"),
                )
                .label("a turn must end");
                // As with impurity: a secondary span renders against *this* file's text, so one
                // that points into another module travels as a note instead.
                let culprit_owner = self.fn_owner[culprit.index()];
                diagnostic = if culprit_owner == owner {
                    diagnostic.secondary(at, "a loop is not provably finite")
                } else {
                    diagnostic.note(format!(
                        "a loop is not provably finite, and `{name}` contains one in {}",
                        self.names[culprit_owner]
                    ))
                };
                self.push(
                    diagnostic
                        .note("turn-reachable code has neither loops nor recursion, which is what makes every turn provably terminating")
                        .note("compute the value with a bounded expression, or move the work into a `task fn` and request it with `after`"),
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
            let mut diagnostic = Diagnostic::new(span, message).label("reached from here");
            // As above: the culprit's span only means something in its own file.
            let culprit_owner = self.fn_owner[culprit.index()];
            diagnostic = if culprit_owner == owner {
                diagnostic.secondary(
                    self.program.fns[culprit.index()].span,
                    format!("the cycle is {}", names.join(" → ")),
                )
            } else {
                diagnostic.note(format!(
                    "the cycle is {}, declared in {}",
                    names.join(" → "),
                    self.names[culprit_owner]
                ))
            };
            diagnostic = diagnostic
                .note("turn-reachable code has neither loops nor recursion, which is what makes termination provable rather than hoped for")
                .note("compute the value with a bounded expression, or move the work into a `task fn` and request it with `after`");
            self.push(diagnostic);
        }
    }
}

/// Every function this expression calls.
pub(super) fn collect_calls(expr: &Expr, found: &mut Vec<FnId>) {
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
        | ExprKind::Loop { body: inner }
        | ExprKind::ReactorInput { reactor: inner, .. }
        | ExprKind::ReactorExport { reactor: inner, .. } => collect_calls(inner, found),
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::ShortCircuit { lhs, rhs, .. }
        | ExprKind::While {
            cond: lhs,
            body: rhs,
        } => {
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
                    StmtKind::After { task, .. } => {
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
        ExprKind::Return { value } | ExprKind::Break { value } => {
            if let Some(value) = value {
                collect_calls(value, found);
            }
        }
        ExprKind::Continue => {}
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Error => {}
    }
}

/// The parts of an `after` operand that actually run during the turn.
///
/// The head call does not: `after deliver(m)` *builds* `deliver(m)` and the runtime starts
/// it once the snapshot is published, so neither what `deliver` calls nor how long it takes is a
/// property of the turn. Its arguments are another matter — those are evaluated on the spot, and
/// everything a turn forbids still applies to them.
///
/// This is the whole of why laziness was worth having. If calling a `task fn` ran it, there would
/// be no way to describe an effect from inside a turn at all.
pub(super) fn effect_arguments(task: &Expr) -> &[Expr] {
    match &task.kind {
        ExprKind::Call { args, .. } | ExprKind::Builtin { args, .. } => args,
        _ => std::slice::from_ref(task),
    }
}

/// The first impure builtin an expression calls, if any.
pub(super) fn impure_builtin(expr: &Expr) -> Option<(Builtin, Span)> {
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
pub(super) fn reachable_impurity(
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

/// The first loop an expression contains, if any: which word to blame, and where.
pub(super) fn first_loop(expr: &Expr) -> Option<(&'static str, Span)> {
    let mut found = None;
    walk(expr, &mut |expr| {
        if found.is_some() {
            return;
        }
        match &expr.kind {
            ExprKind::While { .. } => found = Some(("while", expr.span)),
            ExprKind::Loop { .. } => found = Some(("loop", expr.span)),
            _ => {}
        }
    });
    found
}

/// The nearest function reachable from `start` that contains a loop — `reachable_impurity`'s
/// shape, for the same reason: the function closest to the turn is the call the reader has to
/// look at.
pub(super) fn reachable_loop(
    calls: &[Vec<FnId>],
    loops: &[Option<(&'static str, Span)>],
    start: FnId,
) -> Option<(FnId, &'static str, Span)> {
    let mut seen = vec![false; calls.len()];
    let mut queue = std::collections::VecDeque::from([start]);
    seen[start.index()] = true;
    while let Some(function) = queue.pop_front() {
        if let Some((what, span)) = loops[function.index()] {
            return Some((function, what, span));
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
pub(super) fn walk(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
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
        | ExprKind::Loop { body: inner }
        | ExprKind::ReactorInput { reactor: inner, .. }
        | ExprKind::ReactorExport { reactor: inner, .. } => walk(inner, visit),
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::ShortCircuit { lhs, rhs, .. }
        | ExprKind::While {
            cond: lhs,
            body: rhs,
        } => {
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
                    StmtKind::After { task, .. } => {
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
        ExprKind::Return { value } | ExprKind::Break { value } => {
            if let Some(value) = value {
                walk(value, visit);
            }
        }
        ExprKind::Continue => {}
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
pub(super) fn reachable_cycle(calls: &[Vec<FnId>], start: FnId) -> Option<Vec<FnId>> {
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

impl Checker {
    /// A `send` to a `wait` port from anywhere an `after` can reach.
    ///
    /// `Overflow::Wait` parks the sender on a list that retains the message, which is real
    /// backpressure exactly when the sender's own progress is what produces messages: a task
    /// looping on `await send(players.moved, pos)` stops, so the socket stops being drained. From
    /// a reactor's effect task it is no backpressure at all. A reactor is driven by its inbox and
    /// its effects are fire-and-forget — it *cannot* stall on its outbox, since one that could
    /// would take no turns and any cycle would deadlock — so it keeps taking turns and spawns a
    /// fresh task per turn while the earlier ones are parked. The mailbox stays bounded and the
    /// waiter list absorbs the excess, which is the same memory with less clarity.
    ///
    /// So the rule is positional rather than about either end's identity: what makes `wait` sound
    /// is where the sender stands, and an effect task stands nowhere that can be slowed down.
    /// Refusing it costs nothing real — blocking there never saved the message, it queued the
    /// sender instead.
    ///
    /// A `spawn` in a task loop has the same unbounded shape and stays legal, because `spawn` is
    /// the developer saying they will not wait for this one. `after` is a reactor's only spelling
    /// for leaving a turn, so there is no such declaration to read into it.
    ///
    /// Post-monomorphization, beside `infer_uses` and for its reason: every executable body is
    /// concrete, templates are inert and skipped, and the `(span, message)` dedupe collapses the
    /// per-instance duplicates. Pre-mono would work today only because nothing can reach an input
    /// through a type parameter — which is exactly what item 13 would change.
    pub(super) fn check_effect_backpressure(&mut self) {
        let sends: Vec<Option<WaitSend>> = self
            .program
            .fns
            .iter()
            .map(|def| {
                if def.inert {
                    None
                } else {
                    first_wait_send(&self.program, &def.body)
                }
            })
            .collect();
        if sends.iter().all(Option::is_none) {
            return;
        }

        let calls: Vec<Vec<FnId>> = self
            .program
            .fns
            .iter()
            .map(|def| {
                let mut found = Vec::new();
                if !def.inert {
                    collect_calls(&def.body, &mut found);
                }
                found
            })
            .collect();

        let mut errors: Vec<(usize, Diagnostic)> = Vec::new();
        for index in 0..self.program.fns.len() {
            if self.program.fns[index].inert {
                continue;
            }
            let owner = self.fn_owner[index];
            let mut roots = Vec::new();
            after_roots(&self.program.fns[index].body, &mut roots);
            for (span, root) in roots {
                // The root itself counts, unlike the turn rules' `culprit != function` guard: the
                // everyday shape is a one-line `task fn` whose whole body is the send, and no
                // earlier pass has said anything about it.
                let Some((culprit, send)) = reachable_wait_send(&calls, &sends, root) else {
                    continue;
                };
                let name = self.program.fns[culprit.index()].name.clone();
                let reactor = self.program.reactors[send.reactor.index()].name.clone();
                let input = self.program.reactors[send.reactor.index()].inputs[send.input]
                    .name
                    .clone();
                let mut diagnostic = Diagnostic::new(
                    span,
                    format!(
                        "this reaches `{name}`, which sends to `{reactor}.{input}`, a `wait` input"
                    ),
                )
                .label("an effect cannot be given backpressure");
                // As everywhere else here: a secondary span renders against *this* file's text, so
                // one pointing into another module travels as a note carrying the module name.
                let culprit_owner = self.fn_owner[culprit.index()];
                diagnostic = if culprit_owner == owner {
                    diagnostic.secondary(
                        send.span,
                        "a `wait` input parks its sender, and this sender is a fresh task every turn",
                    )
                } else {
                    diagnostic.note(format!(
                        "a `wait` input parks its sender, and this sender is a fresh task every turn; `{name}` sends in {}",
                        self.names[culprit_owner]
                    ))
                };
                errors.push((
                    owner,
                    diagnostic
                        .note("backpressure propagates from a task into a reactor and never from a reactor to a reactor: a reactor is driven by its inbox, so parking its effect task never slows it down and the waiter list grows instead")
                        .note("give the input a larger queue with an observable overflow policy, or add a credit or ack input on the producer, which between reactors is the only place flow control can honestly live"),
                ));
            }
        }
        self.report(errors);
    }
}

/// One `send` to a `wait` port: where it is written, and which port it names.
#[derive(Clone, Copy)]
pub(super) struct WaitSend {
    span: Span,
    reactor: ReactorId,
    input: usize,
}

/// Every `after` in this body, as the statement to blame and the function it starts.
///
/// The head call is the root because `collect_calls` deliberately drops it: what a `task fn` does
/// is not a property of the turn that requested it, which is the whole of why `after` is lazy. It
/// is exactly the property *this* pass is about, so the closure has to be seeded with it by hand.
/// An operand that is not a call names no function statically and starts no walk.
pub(super) fn after_roots(expr: &Expr, out: &mut Vec<(Span, FnId)>) {
    walk_stmts(expr, &mut |stmt| {
        if let StmtKind::After { task, .. } = &stmt.kind
            && let ExprKind::Call { callee, .. } = &task.kind
        {
            out.push((stmt.span, *callee));
        }
    });
}

/// Visit every statement an expression contains — `walk`'s traversal, statements instead of
/// expressions.
fn walk_stmts(expr: &Expr, visit: &mut impl FnMut(&Stmt)) {
    walk(expr, &mut |expr| {
        if let ExprKind::Block { stmts, .. } = &expr.kind {
            for stmt in stmts {
                visit(stmt);
            }
        }
    });
}

/// The first `send` in this body whose target is a `wait` input.
///
/// Resolving the policy is always possible. `Ty::Input` carries only the message type, but it is
/// unspellable — `resolve_ty` never produces one, and the only way to obtain one is
/// `reactor.input` at the point of use — so a `send` target is written out as the port it is, and
/// the reactor's own declaration says what that port promises.
pub(super) fn first_wait_send(program: &Program, expr: &Expr) -> Option<WaitSend> {
    let mut found = None;
    walk(expr, &mut |expr| {
        if found.is_some() {
            return;
        }
        let ExprKind::Builtin {
            builtin: Builtin::Send,
            args,
        } = &expr.kind
        else {
            return;
        };
        let Some(port) = args.first() else {
            return;
        };
        let ExprKind::ReactorInput { reactor, index } = &port.kind else {
            return;
        };
        let Ty::Reactor(id) = reactor.ty else {
            return;
        };
        if program.reactors[id.index()].inputs[*index].overflow == Overflow::Wait {
            found = Some(WaitSend {
                span: expr.span,
                reactor: id,
                input: *index,
            });
        }
    });
    found
}

/// The nearest function reachable from `start` that sends to a `wait` port —
/// `reachable_impurity`'s shape, and its reason: the function closest to the `after` is the call
/// the reader has to look at, and the rest of the chain follows from it.
pub(super) fn reachable_wait_send(
    calls: &[Vec<FnId>],
    sends: &[Option<WaitSend>],
    start: FnId,
) -> Option<(FnId, WaitSend)> {
    let mut seen = vec![false; calls.len()];
    let mut queue = std::collections::VecDeque::from([start]);
    seen[start.index()] = true;
    while let Some(function) = queue.pop_front() {
        if let Some(send) = sends[function.index()] {
            return Some((function, send));
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
