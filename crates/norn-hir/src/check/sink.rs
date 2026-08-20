//! Sink inference: which parameters consume what they are handed.
//!
//! A parameter's mode is `Read` unless the function's own body proves otherwise — a written
//! `sink` asserts it, and a body that consumes the parameter infers it. The pass runs after
//! monomorphization and immediately before `check_moves`, on the same tables `check_moves`
//! enforces: every executable body is concrete by then, so a mode is a per-instance fact, which
//! is what lets `walk<T>(x: T)` read at `T = I64` and consume at `T = Connection`.
//!
//! The fixpoint is deliberately plain: repeated passes in `FnId` order, flipping `Read` to
//! `Sink` where a body consumes — through the current state of every callee — until nothing
//! changes. Modes only ever move one way, so the loop is monotone and terminates; Vec order and
//! keyed lookups keep it deterministic, the `generics` discipline. Only affine parameters are
//! candidates — nothing consumes a copyable except a `sink` position, and a copy handed onward
//! costs the caller nothing — and pinned rows (written `sink`, trait contracts) never flip.
//!
//! Two enforcement walks ride on the settled tables, because both need final modes:
//! - a trait's contract is declared, not inferred, so an impl body that consumes a read-pinned
//!   affine parameter is an error at the impl rather than a silent flip;
//! - `spawn` and `after` start work that outlives the call that built it, so an affine argument
//!   must land on a `Sink` parameter — the task has to own its descriptor. A direct `await`
//!   follows the modes alone: the awaiting task is parked, so a read cannot outlive it.

use super::*;

impl Checker {
    pub(super) fn infer_sinks(&mut self) {
        // Pad every mode row to its function's arity. Lifted reactor members declare no written
        // parameter list, so their rows start empty; the padding is `Read` and pinned, because a
        // member is never affine and a contract nobody wrote should not be inferred against.
        for (index, def) in self.program.fns.iter().enumerate() {
            let have = self.param_modes[index].len();
            if have < def.params {
                let missing = def.params - have;
                self.param_modes[index].extend(std::iter::repeat_n(Mode::Read, missing));
                self.mode_pinned[index].extend(std::iter::repeat_n(true, missing));
            }
        }

        loop {
            let mut changed = false;
            for index in 0..self.program.fns.len() {
                let flips: Vec<usize> = {
                    let def = &self.program.fns[index];
                    if def.inert {
                        continue;
                    }
                    let candidates: Vec<usize> = (0..def.params)
                        .filter(|&param| {
                            self.param_modes[index][param] == Mode::Read
                                && !self.mode_pinned[index][param]
                                && self.program.affine(&def.locals[param].ty)
                        })
                        .collect();
                    if candidates.is_empty() {
                        continue;
                    }
                    let mut consumed = vec![None; def.params];
                    value(&def.body, &self.param_modes, &mut consumed);
                    candidates
                        .into_iter()
                        .filter(|&param| consumed[param].is_some())
                        .collect()
                };
                for param in flips {
                    self.param_modes[index][param] = Mode::Sink;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        self.enforce_pins();
        self.enforce_task_ownership();
    }

    /// The declared-contract check: a pinned `Read` on an affine parameter means every caller
    /// keeps ownership, so a body that consumes it anyway is wrong at the body — the only pinned
    /// reads are trait contracts, whose declaration has no body to infer from.
    fn enforce_pins(&mut self) {
        let mut errors: Vec<(usize, Diagnostic)> = Vec::new();
        for (index, def) in self.program.fns.iter().enumerate() {
            if def.inert {
                continue;
            }
            let suspects: Vec<usize> = (0..def.params)
                .filter(|&param| {
                    self.param_modes[index][param] == Mode::Read
                        && self.mode_pinned[index][param]
                        && self.program.affine(&def.locals[param].ty)
                })
                .collect();
            if suspects.is_empty() {
                continue;
            }
            let mut consumed = vec![None; def.params];
            value(&def.body, &self.param_modes, &mut consumed);
            for param in suspects {
                let Some(at) = consumed[param] else { continue };
                let local = &def.locals[param];
                let name = local.name.clone();
                let display = def.name.clone();
                errors.push((
                    self.fn_owner[index],
                    Diagnostic::new(at, format!("`{name}` is a read parameter, and this takes it"))
                        .label("consumed here")
                        .secondary(local.span, "declared to read")
                        .note(format!(
                            "`{display}` implements a trait method whose `{name}` is declared without `sink`: every caller keeps ownership, so the body may only read it"
                        ))
                        .note("declare the parameter `sink` at the trait to let every impl consume it"),
                ));
            }
        }
        self.report(errors);
    }

    /// The spawn rule: work started by `spawn` or `after` outlives the call that built it, so an
    /// affine argument must land on a `Sink` parameter — the modes-era successor of the borrow
    /// refusal, and verified against the same corpus: every spawned resource-taker closes what it
    /// is handed, so a `Read` here is a genuine mistake, not a style.
    fn enforce_task_ownership(&mut self) {
        let mut errors: Vec<(usize, Diagnostic)> = Vec::new();
        for (index, def) in self.program.fns.iter().enumerate() {
            if def.inert {
                continue;
            }
            let mut sites: Vec<(&Expr, &'static str)> = Vec::new();
            collect_started(&def.body, &mut sites);
            for (task, what) in sites {
                let (callee_name, modes): (String, Vec<Mode>) = match &task.kind {
                    ExprKind::Call { callee, args } => (
                        self.program.fns[callee.index()].name.clone(),
                        args.iter()
                            .enumerate()
                            .map(|(position, _)| {
                                self.param_modes
                                    .get(callee.index())
                                    .and_then(|modes| modes.get(position))
                                    .copied()
                                    .unwrap_or(Mode::Read)
                            })
                            .collect(),
                    ),
                    ExprKind::Builtin { builtin, args } => (
                        builtin.name().to_string(),
                        builtin
                            .signature()
                            .0
                            .iter()
                            .map(|(_, mode)| *mode)
                            .chain(std::iter::repeat(Mode::Read))
                            .take(args.len())
                            .collect(),
                    ),
                    // A bare task value: its arguments moved when it was built.
                    _ => continue,
                };
                let (ExprKind::Call { args, .. } | ExprKind::Builtin { args, .. }) = &task.kind
                else {
                    unreachable!("matched above");
                };
                for (arg, mode) in args.iter().zip(modes) {
                    if mode == Mode::Sink || !self.program.affine(&arg.ty) {
                        continue;
                    }
                    let ty = self.program.ty_name(&arg.ty);
                    errors.push((
                        self.fn_owner[index],
                        Diagnostic::new(
                            arg.span,
                            format!("work started with `{what}` must own its {ty}"),
                        )
                        .label(format!("`{callee_name}` only reads this"))
                        .note(format!(
                            "the task runs after this line, so a parameter that reads would leave the {ty} with two users and one owner"
                        ))
                        .note(format!(
                            "make `{callee_name}` consume it — close it in the body, or declare the parameter `sink`"
                        )),
                    ));
                }
            }
        }
        self.report(errors);
    }

    /// File the diagnostics under their owners, deduplicated on (span, message): instances
    /// inherit their template's spans, so a mistake written once in a template would otherwise
    /// report once per instantiation — the `check_moves` discipline.
    fn report(&mut self, errors: Vec<(usize, Diagnostic)>) {
        for (owner, diagnostic) in errors {
            let seen = self.errors[owner]
                .iter()
                .any(|d| d.span == diagnostic.span && d.message == diagnostic.message);
            if !seen {
                self.errors[owner].push(diagnostic);
            }
        }
    }
}

/// `spawn` and `after` operands, with the word to blame in the diagnostic.
fn collect_started<'e>(expr: &'e Expr, out: &mut Vec<(&'e Expr, &'static str)>) {
    match &expr.kind {
        ExprKind::Spawn { expr: task } => {
            out.push((task, "spawn"));
            collect_started(task, out);
        }
        ExprKind::Field { base: inner, .. }
        | ExprKind::Unary { expr: inner, .. }
        | ExprKind::Await { expr: inner }
        | ExprKind::Try { expr: inner, .. }
        | ExprKind::Scope { body: inner }
        | ExprKind::ReactorInput { reactor: inner, .. }
        | ExprKind::ReactorExport { reactor: inner, .. }
        | ExprKind::Loop { body: inner } => collect_started(inner, out),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::ShortCircuit { lhs, rhs, .. } => {
            collect_started(lhs, out);
            collect_started(rhs, out);
        }
        ExprKind::Call { args, .. }
        | ExprKind::Builtin { args, .. }
        | ExprKind::Construct { args, .. }
        | ExprKind::SpawnReactor { args, .. } => {
            for arg in args {
                collect_started(arg, out);
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_started(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_started(guard, out);
                }
                collect_started(&arm.body, out);
            }
        }
        ExprKind::If { cond, then, els } => {
            collect_started(cond, out);
            collect_started(then, out);
            if let Some(els) = els {
                collect_started(els, out);
            }
        }
        ExprKind::While { cond, body } => {
            collect_started(cond, out);
            collect_started(body, out);
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match &stmt.kind {
                    StmtKind::Let { value, .. } | StmtKind::Expr(value) => {
                        collect_started(value, out)
                    }
                    StmtKind::Assign { place, value } => {
                        collect_started(place, out);
                        collect_started(value, out);
                    }
                    StmtKind::After { task, .. } => {
                        out.push((task, "after"));
                        collect_started(task, out);
                    }
                }
            }
            if let Some(tail) = tail {
                collect_started(tail, out);
            }
        }
        ExprKind::Return { value } | ExprKind::Break { value } => {
            if let Some(value) = value {
                collect_started(value, out);
            }
        }
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Continue
        | ExprKind::Error => {}
    }
}

// ---------------------------------------------------------------- the consumption walk
//
// A structural mirror of `Moves`' value/place split, with none of its state: the question is
// only "is this parameter ever used where a value is taken", so branches, joins, and liveness
// are irrelevant — any occurrence counts, and the first span is kept for the pin diagnostic.
// Keeping the dispatch identical to `moves.rs` is the point: what inference calls consumption
// is exactly what enforcement will treat as a move.

/// An expression whose value is consumed.
fn value(expr: &Expr, param_modes: &[Vec<Mode>], consumed: &mut [Option<Span>]) {
    match &expr.kind {
        ExprKind::Local(id) => {
            if let Some(slot) = consumed.get_mut(id.index())
                && slot.is_none()
            {
                *slot = Some(expr.span);
            }
        }
        // A field read copies; the root is only named.
        ExprKind::Field { base, .. } => place(base, param_modes, consumed),
        _ => parts(expr, param_modes, consumed),
    }
}

/// An expression only part of which is read: nothing is taken from a parameter it roots.
fn place(expr: &Expr, param_modes: &[Vec<Mode>], consumed: &mut [Option<Span>]) {
    match &expr.kind {
        ExprKind::Local(_) => {}
        ExprKind::Field { base, .. } => place(base, param_modes, consumed),
        _ => parts(expr, param_modes, consumed),
    }
}

fn parts(expr: &Expr, param_modes: &[Vec<Mode>], consumed: &mut [Option<Span>]) {
    match &expr.kind {
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Continue
        | ExprKind::Error => {}
        ExprKind::Field { base, .. } => place(base, param_modes, consumed),
        ExprKind::Unary { expr, .. } => value(expr, param_modes, consumed),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::ShortCircuit { lhs, rhs, .. } => {
            value(lhs, param_modes, consumed);
            value(rhs, param_modes, consumed);
        }
        // The mode split `Moves` enforces, read from the current fixpoint state: a `Sink`
        // argument is consumed, a `Read` argument is only named.
        ExprKind::Call { callee, args } => {
            for (index, arg) in args.iter().enumerate() {
                let mode = param_modes
                    .get(callee.index())
                    .and_then(|modes| modes.get(index))
                    .copied()
                    .unwrap_or(Mode::Read);
                match mode {
                    Mode::Sink => value(arg, param_modes, consumed),
                    Mode::Read => place(arg, param_modes, consumed),
                }
            }
        }
        ExprKind::Builtin { builtin, args } => {
            let (params, _) = builtin.signature();
            for (index, arg) in args.iter().enumerate() {
                match params.get(index).map_or(Mode::Read, |(_, mode)| *mode) {
                    Mode::Sink => value(arg, param_modes, consumed),
                    Mode::Read => place(arg, param_modes, consumed),
                }
            }
        }
        // A constructor's payload is stored, and a spawned reactor owns its arguments.
        ExprKind::Construct { args, .. } | ExprKind::SpawnReactor { args, .. } => {
            for arg in args {
                value(arg, param_modes, consumed);
            }
        }
        // Deconstruction: a `match` on an owned value takes it apart, which is a consumption
        // fact about the scrutinee — this is what closes the read-half gate's template-time gap,
        // per instance.
        ExprKind::Match { scrutinee, arms } => {
            value(scrutinee, param_modes, consumed);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    value(guard, param_modes, consumed);
                }
                value(&arm.body, param_modes, consumed);
            }
        }
        ExprKind::If { cond, then, els } => {
            value(cond, param_modes, consumed);
            value(then, param_modes, consumed);
            if let Some(els) = els {
                value(els, param_modes, consumed);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match &stmt.kind {
                    StmtKind::Let { value: rhs, .. } => value(rhs, param_modes, consumed),
                    StmtKind::Assign {
                        place: target,
                        value: rhs,
                    } => {
                        value(rhs, param_modes, consumed);
                        place(target, param_modes, consumed);
                    }
                    StmtKind::After { task, .. } => value(task, param_modes, consumed),
                    StmtKind::Expr(expr) => value(expr, param_modes, consumed),
                }
            }
            if let Some(tail) = tail {
                value(tail, param_modes, consumed);
            }
        }
        ExprKind::Await { expr } | ExprKind::Spawn { expr } | ExprKind::Try { expr, .. } => {
            value(expr, param_modes, consumed)
        }
        ExprKind::Scope { body } => value(body, param_modes, consumed),
        ExprKind::ReactorInput { reactor, .. } | ExprKind::ReactorExport { reactor, .. } => {
            place(reactor, param_modes, consumed)
        }
        ExprKind::Return { value: inner } | ExprKind::Break { value: inner } => {
            if let Some(inner) = inner {
                value(inner, param_modes, consumed);
            }
        }
        ExprKind::While { cond, body } => {
            value(cond, param_modes, consumed);
            value(body, param_modes, consumed);
        }
        ExprKind::Loop { body } => value(body, param_modes, consumed),
    }
}
