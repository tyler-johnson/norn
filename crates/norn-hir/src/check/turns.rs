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
