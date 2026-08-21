use super::*;

impl Checker {
    /// Pass six: what a moved value's single owner means for a body that has already typed.
    /// Ordinary values copy (BOOTSTRAP §8 item 5): the tracked set is `Program::affine` —
    /// resources, tasks, and any aggregate reaching one — so `close(conn); read(conn)` is the
    /// error double-close always was, and a struct of two I64s is used as often as it is named.
    ///
    /// It runs over typed HIR rather than inside `check_fns` because it needs both halves of what
    /// checking produced — types, to know which values move, and spans, to say where — and needs to
    /// perturb neither. There is no fixed point to reach: the only joins are where an `if` or a
    /// `match` comes back together, and a loop is walked once, because the loop rule — a body may
    /// not move anything it did not declare — means a legal body leaves outer ownership exactly
    /// where it found it, so one walk stands for every iteration. Recursion is the language's one
    /// other cycle and it crosses a call boundary, where parameters are fresh.
    pub(super) fn check_moves(&mut self) {
        let mut errors: Vec<(usize, Vec<Diagnostic>)> = Vec::new();
        for (index, function) in self.program.fns.iter().enumerate() {
            let mut moves = Moves {
                program: &self.program,
                param_modes: &self.param_modes,
                locals: &function.locals,
                moved: vec![None; function.locals.len()],
                declared: (0..function.locals.len())
                    .map(|local| local < function.params)
                    .collect(),
                frames: Vec::new(),
                diverged: false,
                errors: Vec::new(),
            };
            moves.value(&function.body);
            errors.push((self.fn_owner[index], moves.errors));
        }
        // Deduplicated on (span, message): checking is per instance, so a double use written once
        // in a template would otherwise report identically once per instantiation.
        for (owner, found) in errors {
            for diagnostic in found {
                let seen = self.errors[owner]
                    .iter()
                    .any(|d| d.span == diagnostic.span && d.message == diagnostic.message);
                if !seen {
                    self.errors[owner].push(diagnostic);
                }
            }
        }
    }
}

/// Slot-wise union of move states, keeping the first span seen for each local.
pub(super) fn union(into: &mut [Option<Span>], from: &[Option<Span>]) {
    for (slot, state) in into.iter_mut().zip(from) {
        if slot.is_none() {
            *slot = *state;
        }
    }
}

/// The advice for a lost task, shared between "already moved" and "moved inside a loop": reading
/// is never the answer for one, because running it twice is what was wanted and is not what a
/// read would give.
pub(super) fn task_advice() -> String {
    "a task is work to be done once; build another call if it should happen again".to_string()
}

/// Whether a match scrutinee was *read* rather than moved: a field chain rooted at a name — the
/// shape `value()` walks with `place()`. This is what a match keeps reading between guards, and
/// the only shape safe to re-walk; a bare affine name moves into the match, deconstruction being
/// a consuming use.
fn read_as_place(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Field { base, .. } => rooted_at_local(base),
        _ => false,
    }
}

fn rooted_at_local(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Local(_) => true,
        ExprKind::Field { base, .. } => rooted_at_local(base),
        _ => false,
    }
}

/// One function body's worth of ownership, tracked as it is walked.
///
/// `moved[local]` is `None` while the name still holds its value and `Some(span)` once it does not,
/// remembering where it went so the diagnostic can show both ends. An affine local moves at any
/// whole-value use; an ordinary local is copied — copying is not an event — and changes state
/// only at a `sink` position, which revokes whatever name it is handed.
struct Moves<'p> {
    program: &'p Program,
    /// The settled mode tables, indexed by `FnId` in lockstep with the checker's signatures —
    /// what an argument position means. Missing entries read as `Read`: a lifted body's row is
    /// shorter than its arity, and its parameters are reactor members, which are never affine.
    param_modes: &'p [Vec<Mode>],
    locals: &'p [LocalDef],
    moved: Vec<Option<Span>>,
    /// Which locals have been declared on the path walked so far: parameters at entry, everything
    /// else as its `let` or pattern binding is reached. What the loop rule means by "outside the
    /// loop" is exactly "declared before the loop was entered".
    declared: Vec<bool>,
    /// One frame per enclosing loop: the union of `moved` at every `break` and `continue` that
    /// targeted it. Together with the body's fall-through state this is everything that can reach
    /// the loop's back edge or its exit.
    frames: Vec<Vec<Option<Span>>>,
    /// Whether the path being walked has already left the function. A branch that returns
    /// contributes nothing to what follows it, which is why `if x { return } else { close(c) }`
    /// leaves `c` moved rather than "maybe moved".
    diverged: bool,
    errors: Vec<Diagnostic>,
}

impl Moves<'_> {
    /// An expression whose value is consumed. This is where a move happens.
    fn value(&mut self, expr: &Expr) {
        match &expr.kind {
            // Liveness is asked unconditionally: an ordinary local never moves by *type*, but a
            // `sink` position revokes any name it is handed, and a revoked name is gone however
            // cheap its value was to copy.
            ExprKind::Local(id) => {
                if self.live(*id, expr.span) && self.moves(*id) {
                    self.moved[id.index()] = Some(expr.span);
                }
            }
            // A field read copies — single ownership applies to whole values, so reading `p.x`
            // takes nothing — unless the field's own type is *affine*: a copied descriptor would
            // be a second owner, and a `match` is how a resource-holding aggregate is taken
            // apart.
            ExprKind::Field { base, index } => {
                if self.program.affine(&expr.ty) {
                    self.out_of_field(base, *index, expr.span);
                }
                self.place(base);
            }
            _ => self.parts(expr),
        }
    }

    /// An expression only part of which is read: the base of a field access, or an argument at
    /// a `Read` position. The root still has to be live, but nothing moves.
    fn place(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Local(id) => {
                self.live(*id, expr.span);
            }
            ExprKind::Field { base, .. } => self.place(base),
            _ => self.parts(expr),
        }
    }

    /// An argument at a `Sink` position: the caller's name dies whatever its type. This is the
    /// one place a copyable local is marked moved — a written `sink` is assertive, and revoking
    /// the name is what the assertion means — while everything that is not a bare name behaves
    /// as the value it is.
    fn consume(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Local(id) => {
                if self.live(*id, expr.span) {
                    self.moved[id.index()] = Some(expr.span);
                }
            }
            _ => self.value(expr),
        }
    }

    /// Everything that is neither a name nor a projection: walked in evaluation order, so that the
    /// first use of a moved value is the one reported.
    fn parts(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Local(_)
            | ExprKind::Error => {}
            ExprKind::Field { base, .. } => self.place(base),
            ExprKind::Unary { expr, .. } => self.value(expr),
            ExprKind::Binary { lhs, rhs, .. } => {
                self.value(lhs);
                self.value(rhs);
            }
            // The right side of `&&` may not run. A move that may have happened is a move: the
            // alternative is a name that is live on one path and gone on another, with no way to
            // tell which from the line that uses it.
            ExprKind::ShortCircuit { lhs, rhs, .. } => {
                self.value(lhs);
                self.value(rhs);
            }
            // A call's arguments follow the callee's modes: a `Sink` position takes the value —
            // the caller's name dies there — and a `Read` position only has to name something
            // that is live. This is what makes passing a value not a move.
            ExprKind::Call { callee, args } => {
                for (index, arg) in args.iter().enumerate() {
                    match self.fn_mode(*callee, index) {
                        Mode::Sink => self.consume(arg),
                        // Placeholder until the call-site wave: a `Mut` argument is a live place.
                        Mode::Read | Mode::Mut => self.place(arg),
                    }
                }
            }
            ExprKind::Builtin { builtin, args } => {
                let (params, _) = builtin.signature();
                for (index, arg) in args.iter().enumerate() {
                    let mode = params.get(index).map_or(Mode::Read, |(_, mode)| *mode);
                    match mode {
                        Mode::Sink => self.consume(arg),
                        Mode::Read | Mode::Mut => self.place(arg),
                    }
                }
            }
            // A constructor's payload is stored: the aggregate owns what it was built from, so
            // every argument is a whole-value use.
            ExprKind::Construct { args, .. } | ExprKind::SpawnReactor { args, .. } => {
                for arg in args {
                    self.value(arg);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.value(scrutinee);
                self.arms(scrutinee, arms);
            }
            ExprKind::If { cond, then, els } => {
                self.value(cond);
                let entry = self.moved.clone();
                let taken = self.branch(|this| this.value(then));
                let missed = match els {
                    Some(els) => {
                        self.moved = entry.clone();
                        self.branch(|this| this.value(els))
                    }
                    // An `if` with no `else` has a path on which nothing happened at all.
                    None => (entry.clone(), false),
                };
                self.rejoin(entry, vec![taken, missed]);
            }
            ExprKind::Block { stmts, tail } => {
                for stmt in stmts {
                    self.stmt(stmt);
                }
                if let Some(tail) = tail {
                    self.value(tail);
                }
            }
            ExprKind::Await { expr } | ExprKind::Spawn { expr } | ExprKind::Try { expr, .. } => {
                self.value(expr)
            }
            ExprKind::Scope { body } => self.value(body),
            // A reactor handle copies — it names something a scope owns — so reaching one of its
            // members reads a name and takes nothing.
            ExprKind::ReactorInput { reactor, .. } | ExprKind::ReactorExport { reactor, .. } => {
                self.place(reactor)
            }
            ExprKind::Return { value } => {
                if let Some(value) = value {
                    self.value(value);
                }
                self.diverged = true;
            }
            // The loop rule: a body — condition included, it re-runs every iteration — may not
            // move a value declared outside the loop. Body-locals are fresh each pass and
            // move freely. A legal body is therefore a no-op on outer ownership, which is what
            // lets one walk stand for every iteration: afterwards `moved` is restored to the entry
            // state, and the body-locals' stale entries are unobservable because nothing after the
            // loop can name them.
            ExprKind::While { cond, body } => {
                let entry = self.moved.clone();
                let declared = self.declared.clone();
                self.frames.push(vec![None; self.moved.len()]);
                self.value(cond);
                // The condition's own state reaches the back edge even when the body diverges on
                // every path, so it joins the summary unconditionally.
                let after_cond = self.moved.clone();
                let (body_state, body_diverged) = self.branch(|this| this.value(body));
                let mut summary = self.frames.pop().expect("pushed above");
                union(&mut summary, &after_cond);
                if !body_diverged {
                    union(&mut summary, &body_state);
                }
                self.escaped_moves(&entry, &declared, &summary);
                self.moved = entry;
            }
            ExprKind::Loop { body } => {
                let entry = self.moved.clone();
                let declared = self.declared.clone();
                self.frames.push(vec![None; self.moved.len()]);
                let (body_state, body_diverged) = self.branch(|this| this.value(body));
                let mut summary = self.frames.pop().expect("pushed above");
                if !body_diverged {
                    union(&mut summary, &body_state);
                }
                self.escaped_moves(&entry, &declared, &summary);
                self.moved = entry;
                // A `loop` nothing breaks out of never reaches the code after it.
                if expr.ty == Ty::Never {
                    self.diverged = true;
                }
            }
            // Like `return`, these end their path — what follows them in the tree is unreachable —
            // but unlike a `return`, their moves do not leave the function: a `continue` feeds the
            // back edge and a `break` feeds the exit. So the state is recorded in the loop's frame
            // *before* the path diverges, or `rejoin` would drop it.
            ExprKind::Break { value } => {
                if let Some(value) = value {
                    self.value(value);
                }
                self.record_exit();
                self.diverged = true;
            }
            ExprKind::Continue => {
                self.record_exit();
                self.diverged = true;
            }
        }
    }

    /// The arms of a `match`, each starting from the state the scrutinee left behind.
    fn arms(&mut self, scrutinee: &Expr, arms: &[Arm]) {
        let mut entry = self.moved.clone();
        let mut outcomes = Vec::new();
        for arm in arms {
            self.moved = entry.clone();
            self.bind(&arm.pat);
            if let Some(guard) = &arm.guard {
                // A guard runs even when its arm does not, so whatever it took is taken for every
                // arm after it. That is the difference between a guard and a body: one ran, the
                // other ran if it matched.
                self.value(guard);
                // When the scrutinee was read as a place — a field chain rooted at a name —
                // the match is still reading it after every failed guard, so a guard that moved
                // its root has taken what the next arm examines. Re-walking such a scrutinee is a
                // liveness check and nothing else. The filter is load-bearing twice over: an
                // owned name moved *into* the match would re-report its own legitimate move, and
                // a scrutinee with a call in it would double-count the call's argument moves.
                if read_as_place(scrutinee) {
                    self.place(scrutinee);
                }
                entry = self.moved.clone();
            }
            outcomes.push(self.branch(|this| this.value(&arm.body)));
        }
        self.rejoin(entry, outcomes);
    }

    /// Run one branch from the current state and take back what it produced, leaving the walker
    /// undiverged and ready for the next one.
    fn branch(&mut self, body: impl FnOnce(&mut Self)) -> (Vec<Option<Span>>, bool) {
        let outer = std::mem::replace(&mut self.diverged, false);
        body(self);
        let diverged = std::mem::replace(&mut self.diverged, outer);
        (self.moved.clone(), diverged)
    }

    /// Merge the branches back together. A name is moved afterwards if any branch that can reach
    /// the join moved it; if none of them can, the code after the join is unreachable and the state
    /// does not matter, so the entry state is kept and the path stays diverged.
    fn rejoin(&mut self, entry: Vec<Option<Span>>, outcomes: Vec<(Vec<Option<Span>>, bool)>) {
        let reaching: Vec<&Vec<Option<Span>>> = outcomes
            .iter()
            .filter(|(_, diverged)| !diverged)
            .map(|(moved, _)| moved)
            .collect();
        if reaching.is_empty() {
            self.moved = entry;
            self.diverged = true;
            return;
        }
        let mut merged = entry;
        for (index, slot) in merged.iter_mut().enumerate() {
            if slot.is_none() {
                *slot = reaching.iter().find_map(|state| state[index]);
            }
        }
        self.moved = merged;
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let { local, value } => {
                self.value(value);
                // The name is fresh whatever it shadows, and whatever it held on an earlier line of
                // a `match` arm it does not hold now.
                self.moved[local.index()] = None;
                self.declared[local.index()] = true;
            }
            StmtKind::Assign { place, value } => {
                self.value(value);
                match &place.kind {
                    // Assigning a whole name gives it something to own again, so a value that was
                    // moved out of it is no longer the value it has.
                    ExprKind::Local(id) => self.moved[id.index()] = None,
                    _ => self.place(place),
                }
            }
            // The operand is *built* here: its arguments are evaluated now and move now, even
            // though the work runs after the snapshot is published.
            StmtKind::After { task, .. } => self.value(task),
            StmtKind::Expr(expr) => self.value(expr),
        }
    }

    /// Names a pattern introduces. They are fresh, and binding part of a scrutinee is how an
    /// affine aggregate is taken apart — the scrutinee moved as a whole, and the pieces are named
    /// here — while an ordinary scrutinee simply copies into them.
    fn bind(&mut self, pat: &Pat) {
        match &pat.kind {
            PatKind::Bind(id) => {
                self.moved[id.index()] = None;
                self.declared[id.index()] = true;
            }
            PatKind::Variant { args, .. } | PatKind::Struct { args, .. } => {
                for arg in args {
                    self.bind(arg);
                }
            }
            PatKind::Or(alts) => {
                for alt in alts {
                    self.bind(alt);
                }
            }
            _ => {}
        }
    }

    /// Union the current state into the innermost loop's frame: this path is about to jump to the
    /// loop's back edge or exit, and what it moved arrives there with it.
    fn record_exit(&mut self) {
        let moved = self.moved.clone();
        let frame = self
            .frames
            .last_mut()
            .expect("the checker rejects a stray `break` or `continue`");
        union(frame, &moved);
    }

    /// Report every local the loop moved without declaring. `summary` is everything that can
    /// reach the back edge or the exit; only locals a move or a `sink` took ever hold `Some`,
    /// so the move set needs no separate check. The advice: `x = f(x)` inside the body is legal — the
    /// name owns again at the bottom of the pass — and a value each pass should own outright is
    /// declared inside the loop.
    fn escaped_moves(
        &mut self,
        entry: &[Option<Span>],
        declared: &[bool],
        summary: &[Option<Span>],
    ) {
        for (index, moved_at) in summary.iter().enumerate() {
            let Some(at) = moved_at else { continue };
            // Declared inside the loop is fine — fresh each pass. Already moved at entry has been
            // reported at the use site inside, and once is enough.
            if !declared[index] || entry[index].is_some() {
                continue;
            }
            let local = &self.locals[index];
            let name = local.name.clone();
            let ty = self.program.ty_name(&local.ty);
            let advice = match local.ty {
                Ty::Task(_) => task_advice(),
                _ => "declare it inside the loop if each pass should have its own".to_string(),
            };
            let rule = if self.program.affine(&local.ty) {
                format!(
                    "a `{ty}` has one owner; the first pass of the loop hands it over, and the next would find it gone"
                )
            } else {
                format!(
                    "a `{ty}` copies, but the first pass of the loop hands it to a `sink` parameter, and the next would find the name gone"
                )
            };
            self.errors.push(
                Diagnostic::new(*at, format!("`{name}` cannot be moved inside a loop"))
                    .label("moved here")
                    .secondary(local.span, "…but it was declared outside the loop")
                    .note(rule)
                    .note(advice),
            );
        }
    }

    fn moves(&self, id: LocalId) -> bool {
        self.program.affine(&self.locals[id.index()].ty)
    }

    /// What the callee declared (or inference settled) for one argument position. Out-of-range
    /// reads as `Read`: a lifted body's mode row is shorter than its arity, and its parameters
    /// are reactor members, which are never affine.
    fn fn_mode(&self, callee: FnId, index: usize) -> Mode {
        self.param_modes
            .get(callee.index())
            .and_then(|modes| modes.get(index))
            .copied()
            .unwrap_or(Mode::Read)
    }

    /// Report a use of something that is not there any more. `false` means it was already reported
    /// at this use, so the caller should not also record a second move.
    fn live(&mut self, id: LocalId, span: Span) -> bool {
        let Some(moved) = self.moved[id.index()] else {
            return true;
        };
        let local = &self.locals[id.index()];
        let name = local.name.clone();
        let ty = self.program.ty_name(&local.ty);
        // An ordinary local is only ever marked moved by a `sink` position — its values copy, so
        // nothing else takes them — and the diagnostic should say that rather than "one owner".
        if !self.program.affine(&local.ty) {
            self.errors.push(
                Diagnostic::new(span, format!("`{name}` was given away"))
                    .label("used here")
                    .secondary(moved, "given here")
                    .note(format!(
                        "a `{ty}` copies, but it was handed to a `sink` parameter, and the name does not survive that"
                    ))
                    .note(format!(
                        "`let kept = {name}` before the call keeps a copy under a name of its own"
                    )),
            );
            return false;
        }
        // What took the value was a consuming position — a `sink` parameter, a constructor
        // payload, a deconstructing `match` — because a read takes nothing. The advice is the
        // doctrine, except for a task, which has to be built again: running it twice is what was
        // wanted, and no reordering gives that.
        let advice = match local.ty {
            Ty::Task(_) => task_advice(),
            _ => "reads are unmarked and take nothing; what consumes is a `sink` position, a constructor payload, or a deconstructing `match`".to_string(),
        };
        self.errors.push(
            Diagnostic::new(span, format!("`{name}` has already been moved"))
                .label("used here")
                .secondary(moved, "moved here")
                .note(format!(
                    "a `{ty}` has one owner, and using it as a value is what hands it over"
                ))
                .note(advice),
        );
        false
    }

    fn out_of_field(&mut self, base: &Expr, index: usize, span: Span) {
        let field = match &base.ty {
            Ty::Struct(id) => self.program.structs[id.index()].fields[index].name.clone(),
            _ => index.to_string(),
        };
        let whole = self.program.ty_name(&base.ty);
        self.errors.push(
            Diagnostic::new(span, format!("`{field}` cannot be moved out of a `{whole}`"))
                .label("this would leave the rest of the value with no owner")
                .note("an owned value moves whole; `match` is what takes one apart, as in `match session { Session(conn: conn) => … }`")
                .note("a position that only reads can be handed the whole value: reads are unmarked, and take nothing"),
        );
    }
}
