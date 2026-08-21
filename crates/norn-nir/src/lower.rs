//! HIR to NIR.
//!
//! Everything that nests becomes control flow here. `match` becomes a chain of tests, one arm at a
//! time; `&&` and `||` become branches so they stop evaluating where the source says they do; `?`
//! becomes a switch with an early return on the failing side. What is left is blocks, assignments,
//! and terminators — which is the shape a state-machine transform and a code generator both want.
//!
//! Arm testing is sequential rather than a decision tree. That can retest a tag several times, and
//! it is the obvious thing to improve once something measures it; correctness does not depend on
//! it, and the flat IR makes replacing it a local change.

use norn_hir::hir;

use crate::nir::*;

pub fn lower(program: &hir::Program) -> Program {
    let field = |f: &hir::FieldDef| FieldLayout {
        name: f.name.clone(),
        ty: f.ty.clone(),
    };
    let structs = program
        .structs
        .iter()
        .map(|strukt| StructLayout {
            name: strukt.name.clone(),
            fields: strukt.fields.iter().map(field).collect(),
        })
        .collect();
    let enums = program
        .enums
        .iter()
        .map(|def| EnumLayout {
            name: def.name.clone(),
            variants: def
                .variants
                .iter()
                .map(|v| VariantLayout {
                    name: v.name.clone(),
                    fields: v.fields.iter().map(field).collect(),
                    positional: v.positional,
                })
                .collect(),
        })
        .collect();

    let fns = program
        .fns
        .iter()
        .map(|def| lower_fn(program, def))
        .collect();
    let reactors = program.reactors.iter().map(lower_reactor).collect();
    let lowered = Program {
        structs,
        enums,
        fns,
        reactors,
        main: program.main.map(|id| id.index()),
    };
    verify_turns(&lowered);
    lowered
}

fn lower_reactor(def: &hir::ReactorDef) -> Reactor {
    Reactor {
        name: def.name.clone(),
        params: def.params.iter().map(|(_, ty)| ty.clone()).collect(),
        nodes: def
            .nodes
            .iter()
            .map(|node| Node {
                name: node.name.clone(),
                ty: node.ty.clone(),
                deps: node.deps.iter().map(|dep| dep.index()).collect(),
                kind: match node.kind {
                    hir::NodeKind::Param { slot, index } => NodeKind::Param { slot, index },
                    hir::NodeKind::State { slot, init } => NodeKind::State {
                        slot,
                        init: init.index(),
                    },
                    hir::NodeKind::Signal { body } => NodeKind::Signal { body: body.index() },
                },
            })
            .collect(),
        slots: def.slots.iter().map(|node| node.index()).collect(),
        inputs: def
            .inputs
            .iter()
            .map(|input| Input {
                name: input.name.clone(),
                ty: input.ty.clone(),
                capacity: input.capacity,
                overflow: input.overflow,
                handler: input.handler.index(),
                plan: input.plan.iter().map(|node| node.index()).collect(),
            })
            .collect(),
        order: def.order.iter().map(|node| node.index()).collect(),
        exports: def.exports.iter().map(|node| node.index()).collect(),
    }
}

/// Reject anything a turn may not do, in the lowered form rather than the source.
///
/// Purity is therefore checked twice: in HIR against what was written, with spans, and here against
/// what lowering produced. The second check is cheap and catches a different class of mistake — a
/// lowering that introduced a suspension point or a spawn that no source expression asked for. The
/// interpreter's `Option<&mut Cx>` is the third line, and traps if both of these are wrong.
fn verify_turns(program: &Program) {
    for reactor in &program.reactors {
        for node in &reactor.nodes {
            match node.kind {
                NodeKind::Param { .. } => {}
                NodeKind::State { init, .. } => verify_pure(program, init, false),
                NodeKind::Signal { body } => verify_pure(program, body, false),
            }
        }
        for input in &reactor.inputs {
            verify_pure(program, input.handler, true);
        }
    }
}

fn verify_pure(program: &Program, id: FnId, handler: bool) {
    let function = &program.fns[id];
    let bad = |what: &str| -> ! {
        panic!(
            "lowered `{}` contains {what}, which a turn cannot do",
            function.name
        )
    };
    for block in &function.blocks {
        for instr in &block.instrs {
            match instr {
                Instr::Spawn(_) => bad("a spawn"),
                Instr::ScopeEnter => bad("a scope"),
                Instr::SpawnReactor { .. } => bad("a reactor creation"),
                // `SetSlot` and `Emit` are what a handler is *for*, and meaningless anywhere else.
                Instr::SetSlot(..) | Instr::Emit { .. } if !handler => {
                    bad("a slot write or an effect request outside a handler")
                }
                Instr::SetSlot(..) | Instr::Emit { .. } => {}
                Instr::Assign(_, rvalue) => match rvalue {
                    Rvalue::Task(..) | Rvalue::BuiltinTask(..) if !handler => bad("a task"),
                    Rvalue::Builtin(builtin, _) if !builtin.is_pure() => bad("an impure builtin"),
                    _ => {}
                },
            }
        }
        match block.term {
            Term::Await { .. } => bad("an await"),
            Term::ScopeExit { .. } => bad("a scope exit"),
            _ => {}
        }
    }

    // Belt and braces like everything above, plus one thing only this layer can check: the block
    // graph must be acyclic, whether the cycle came from a loop the checker somehow missed or from
    // a back edge a future lowering introduces by accident. Not a lower-block-id test — match
    // lowering legitimately jumps backward to pre-allocated join blocks — but a real cycle check,
    // depth-first with an on-stack mark.
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        White,
        Grey,
        Black,
    }
    let mut marks = vec![Mark::White; function.blocks.len()];
    let mut stack = vec![(0usize, 0usize)];
    marks[0] = Mark::Grey;
    while let Some((block, next)) = stack.pop() {
        let successors = function.blocks[block].term.successors();
        if next >= successors.len() {
            marks[block] = Mark::Black;
            continue;
        }
        stack.push((block, next + 1));
        match marks[successors[next]] {
            Mark::Grey => bad("a loop"),
            Mark::Black => {}
            Mark::White => {
                marks[successors[next]] = Mark::Grey;
                stack.push((successors[next], 0));
            }
        }
    }
}

fn lower_fn(program: &hir::Program, def: &hir::FnDef) -> Function {
    let mut lowerer = Lowerer {
        program,
        locals: def.locals.iter().map(|l| l.name.clone()).collect(),
        // An inert def's locals were cut to its parameters, and its `()` body allocates no
        // temporaries, so copying whatever is there keeps the vectors in lockstep for every class.
        tys: def.locals.iter().map(|l| l.ty.clone()).collect(),
        ret: def.ret.clone(),
        roles: def.locals.iter().map(|l| l.role).collect(),
        blocks: vec![Block::default()],
        current: 0,
        open_scopes: 0,
        loops: Vec::new(),
    };
    let result = lowerer.expr(&def.body);
    // A body of type `!` has already returned on every path; the terminator here is unreachable,
    // but every block must have one.
    lowerer.terminate(Term::Return(result));
    let blocks = prune(lowerer.blocks);
    Function {
        name: def.name.clone(),
        kind: if def.is_task {
            FnKind::Task
        } else {
            FnKind::Plain
        },
        params: def.params,
        modes: def.modes.clone(),
        locals: lowerer.locals,
        tys: lowerer.tys,
        ret: lowerer.ret,
        inert: def.inert,
        blocks,
    }
}

/// Drop the blocks nothing reaches and renumber what is left.
///
/// Lowering creates them deliberately — the code after a `return`, a join no arm falls into — and
/// leaving them in would make every NIR dump harder to read than the program it came from.
fn prune(blocks: Vec<Block>) -> Vec<Block> {
    let mut reachable = vec![false; blocks.len()];
    let mut queue = vec![0usize];
    while let Some(block) = queue.pop() {
        if std::mem::replace(&mut reachable[block], true) {
            continue;
        }
        queue.extend(blocks[block].term.successors());
    }

    let mut renumbered = vec![usize::MAX; blocks.len()];
    let mut next = 0;
    for (index, live) in reachable.iter().enumerate() {
        if *live {
            renumbered[index] = next;
            next += 1;
        }
    }

    blocks
        .into_iter()
        .zip(&reachable)
        .filter(|(_, live)| **live)
        .map(|(mut block, _)| {
            block.term.retarget(&renumbered);
            block
        })
        .collect()
}

struct Lowerer<'p> {
    program: &'p hir::Program,
    locals: Vec<String>,
    /// The type of each local, grown in lockstep with `locals`.
    tys: Vec<hir::Ty>,
    /// The function's return type: what `try_expr`'s rebuilt `Err`/`None` temporaries have.
    ret: hir::Ty,
    /// What each local is. Only a handler has any that are not `Ordinary`, and the one that matters
    /// here is `State`: assigning to such a local is a commit, and is where `SetSlot` comes from.
    roles: Vec<hir::LocalRole>,
    blocks: Vec<Block>,
    current: BlockId,
    /// Scopes open around the expression being lowered. A `return` or a `?` that crosses one has to
    /// leave it, so the exits are emitted before the return.
    open_scopes: usize,
    /// The loops enclosing the expression being lowered, innermost last: what `break` and
    /// `continue` jump to.
    loops: Vec<LoopFrame>,
}

#[derive(Clone)]
struct LoopFrame {
    /// The back-edge and `continue` target. A `while`'s condition lowers *inside* it, so jumping
    /// here re-evaluates the condition.
    header: BlockId,
    /// Where `break` jumps.
    exit: BlockId,
    /// Where `break value` writes before jumping. `None` for a `while`, whose breaks are bare.
    dest: Option<Place>,
    /// `open_scopes` when the loop was entered. A `break` or `continue` from inside a `scope {}`
    /// has to leave every scope opened since, the way `return_from` leaves them all.
    open_scopes_at_entry: usize,
}

impl Lowerer<'_> {
    fn temp(&mut self, ty: hir::Ty) -> LocalId {
        let id = self.locals.len();
        self.locals.push(String::new());
        self.tys.push(ty);
        id
    }

    fn new_block(&mut self) -> BlockId {
        self.blocks.push(Block::default());
        self.blocks.len() - 1
    }

    fn emit(&mut self, place: Place, rvalue: Rvalue) {
        self.push_instr(Instr::Assign(place, rvalue));
    }

    fn push_instr(&mut self, instr: Instr) {
        self.blocks[self.current].instrs.push(instr);
    }

    /// Return from the function, leaving every scope still open on the way out. Each exit is a
    /// terminator, so a `return` from inside two scopes becomes two states and then the return.
    fn return_from(&mut self, value: Operand) {
        for _ in 0..self.open_scopes {
            let resume = self.new_block();
            self.terminate(Term::ScopeExit { resume });
            self.switch_to(resume);
        }
        self.terminate(Term::Return(value));
    }

    /// Jump to `target`, exiting every scope opened since `depth` first, the way `return_from`
    /// leaves them all on the way out of the function. The code the source wrote after the jump
    /// lands in a fresh block nothing reaches, exactly as after a `return`; `prune` deletes it.
    fn divert(&mut self, depth: usize, target: BlockId) {
        for _ in depth..self.open_scopes {
            let resume = self.new_block();
            self.terminate(Term::ScopeExit { resume });
            self.switch_to(resume);
        }
        self.terminate(Term::Goto(target));
        let unreachable = self.new_block();
        self.switch_to(unreachable);
    }

    /// Terminate the current block, unless a `return` already terminated it.
    fn terminate(&mut self, term: Term) {
        if matches!(self.blocks[self.current].term, Term::Trap(_)) {
            self.blocks[self.current].term = term;
        }
    }

    fn terminate_at(&mut self, block: BlockId, term: Term) {
        if matches!(self.blocks[block].term, Term::Trap(_)) {
            self.blocks[block].term = term;
        }
    }

    fn switch_to(&mut self, block: BlockId) {
        self.current = block;
    }

    /// Evaluate `expr` into a fresh temporary and return a place naming it.
    fn expr_place(&mut self, expr: &hir::Expr) -> Place {
        let operand = self.expr(expr);
        match operand {
            Operand::Copy(place) => place,
            operand => {
                let temp = Place::local(self.temp(expr.ty.clone()));
                self.emit(temp.clone(), Rvalue::Use(operand));
                temp
            }
        }
    }

    fn assign_to(&mut self, dest: &Place, expr: &hir::Expr) {
        let value = self.expr(expr);
        self.emit(dest.clone(), Rvalue::Use(value));
    }

    fn expr(&mut self, expr: &hir::Expr) -> Operand {
        // Bound before the match: several arms destructure a field also named `expr`, and the
        // type a temporary gets is always the *outer* expression's.
        let ty = &expr.ty;
        match &expr.kind {
            hir::ExprKind::Unit => Operand::Const(Const::Unit),
            hir::ExprKind::Int(v) => Operand::Const(Const::Int(*v)),
            hir::ExprKind::Float(v) => Operand::Const(Const::Float(*v)),
            hir::ExprKind::Bool(v) => Operand::Const(Const::Bool(*v)),
            hir::ExprKind::Str(v) => Operand::Const(Const::Str(v.as_str().into())),
            hir::ExprKind::Local(id) => Operand::Copy(Place::local(id.index())),
            hir::ExprKind::Field { base, index } => {
                // Field access strips every `Shared` layer of the base — the checker's rule,
                // restated here as deref projections. The base expression kept its `Shared`
                // type, which is what says how many layers to peel.
                let mut place = self.expr_place(base);
                let mut base_ty = &base.ty;
                while let hir::Ty::Shared(inner) = base_ty {
                    place = place.deref();
                    base_ty = inner;
                }
                Operand::Copy(place.field(*index))
            }
            hir::ExprKind::Unary { op, expr } => {
                let operand = self.expr(expr);
                let temp = Place::local(self.temp(ty.clone()));
                self.emit(temp.clone(), Rvalue::Unary(*op, operand));
                Operand::Copy(temp)
            }
            hir::ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.expr(lhs);
                let rhs = self.expr(rhs);
                let temp = Place::local(self.temp(ty.clone()));
                self.emit(temp.clone(), Rvalue::Binary(*op, lhs, rhs));
                Operand::Copy(temp)
            }
            hir::ExprKind::ShortCircuit { and, lhs, rhs } => self.short_circuit(*and, lhs, rhs),
            hir::ExprKind::Call { callee, args } => {
                let args: Vec<Operand> = args.iter().map(|arg| self.expr(arg)).collect();
                let temp = Place::local(self.temp(ty.clone()));
                // A call to a `task fn` builds a task rather than pushing a frame. Nothing runs
                // until something awaits or spawns it.
                let rvalue = if self.program.fns[callee.index()].is_task {
                    // A task fn never declares `mut` — refused at declaration — so building one
                    // drops the argument places with nothing to write back into.
                    debug_assert!(
                        !self.program.fns[callee.index()]
                            .modes
                            .contains(&hir::Mode::Mut)
                    );
                    Rvalue::Task(callee.index(), args)
                } else {
                    // The checker guarantees every `Mut` position holds a place: the writeback
                    // target is the argument operand's own place, and the call's own result
                    // lands in a fresh temporary, so the two writes can never alias.
                    debug_assert!(
                        self.program.fns[callee.index()]
                            .modes
                            .iter()
                            .zip(&args)
                            .all(|(mode, arg)| {
                                *mode != hir::Mode::Mut || matches!(arg, Operand::Copy(_))
                            })
                    );
                    Rvalue::Call(callee.index(), args)
                };
                self.emit(temp.clone(), rvalue);
                Operand::Copy(temp)
            }
            hir::ExprKind::Builtin { builtin, args } => {
                let args = args.iter().map(|arg| self.expr(arg)).collect();
                let temp = Place::local(self.temp(ty.clone()));
                let rvalue = if builtin.is_task() {
                    Rvalue::BuiltinTask(*builtin, args)
                } else {
                    // A builtin's `Mut` position holds a place, exactly as a call's does — the
                    // checker enforces the same contract through the same mode dispatch, and the
                    // interpreter's writeback destructures the operand on the strength of it.
                    debug_assert!(builtin.signature().0.iter().zip(&args).all(
                        |((_, mode), arg)| {
                            *mode != hir::Mode::Mut || matches!(arg, Operand::Copy(_))
                        }
                    ));
                    Rvalue::Builtin(*builtin, args)
                };
                self.emit(temp.clone(), rvalue);
                Operand::Copy(temp)
            }
            hir::ExprKind::Construct { ctor, args } => {
                let args = args.iter().map(|arg| self.expr(arg)).collect();
                let rvalue = match ctor {
                    hir::Ctor::Struct(id) => Rvalue::Struct(id.index(), args),
                    hir::Ctor::Variant(id, variant) => Rvalue::Variant(id.index(), *variant, args),
                };
                let temp = Place::local(self.temp(ty.clone()));
                self.emit(temp.clone(), rvalue);
                Operand::Copy(temp)
            }
            hir::ExprKind::Block { stmts, tail } => {
                for stmt in stmts {
                    self.stmt(stmt);
                }
                match tail {
                    Some(tail) => self.expr(tail),
                    None => Operand::Const(Const::Unit),
                }
            }
            hir::ExprKind::If { cond, then, els } => {
                self.if_expr(ty.clone(), cond, then, els.as_deref())
            }
            hir::ExprKind::While { cond, body } => {
                let header = self.new_block();
                let exit = self.new_block();
                self.terminate(Term::Goto(header));
                self.switch_to(header);
                // The frame opens before the condition lowers: the condition is re-evaluated every
                // iteration, so it lives inside the header and a `break` in it targets this loop.
                self.loops.push(LoopFrame {
                    header,
                    exit,
                    dest: None,
                    open_scopes_at_entry: self.open_scopes,
                });
                let cond = self.expr(cond);
                let body_block = self.new_block();
                self.terminate(Term::Branch {
                    cond,
                    then: body_block,
                    els: exit,
                });
                self.switch_to(body_block);
                self.expr(body);
                // A no-op when the body already diverted; otherwise the back edge.
                self.terminate(Term::Goto(header));
                self.loops.pop();
                self.switch_to(exit);
                Operand::Const(Const::Unit)
            }
            hir::ExprKind::Loop { body } => {
                let dest = Place::local(self.temp(ty.clone()));
                let header = self.new_block();
                let exit = self.new_block();
                self.terminate(Term::Goto(header));
                self.switch_to(header);
                self.loops.push(LoopFrame {
                    header,
                    exit,
                    dest: Some(dest.clone()),
                    open_scopes_at_entry: self.open_scopes,
                });
                self.expr(body);
                self.terminate(Term::Goto(header));
                self.loops.pop();
                // A `loop` no break leaves keeps `exit` unreachable, and `prune` deletes it.
                self.switch_to(exit);
                Operand::Copy(dest)
            }
            hir::ExprKind::Break { value } => {
                let frame = self
                    .loops
                    .last()
                    .expect("the checker rejects a stray `break`")
                    .clone();
                // The value lowers first — it may await, or open and close scopes of its own — and
                // only then do the loop's scopes unwind.
                if let Some(dest) = &frame.dest {
                    let value = match value {
                        Some(value) => self.expr(value),
                        None => Operand::Const(Const::Unit),
                    };
                    self.emit(dest.clone(), Rvalue::Use(value));
                }
                self.divert(frame.open_scopes_at_entry, frame.exit);
                Operand::Const(Const::Unit)
            }
            hir::ExprKind::Continue => {
                let frame = self
                    .loops
                    .last()
                    .expect("the checker rejects a stray `continue`")
                    .clone();
                self.divert(frame.open_scopes_at_entry, frame.header);
                Operand::Const(Const::Unit)
            }
            hir::ExprKind::Match { scrutinee, arms } => {
                self.match_expr(ty.clone(), scrutinee, arms)
            }
            hir::ExprKind::Try { expr, enum_id } => {
                self.try_expr(ty.clone(), expr, enum_id.index())
            }
            hir::ExprKind::Await { expr } => {
                let task = self.expr(expr);
                let dest = Place::local(self.temp(ty.clone()));
                let resume = self.new_block();
                self.terminate(Term::Await {
                    task,
                    dest: dest.clone(),
                    resume,
                });
                self.switch_to(resume);
                Operand::Copy(dest)
            }
            hir::ExprKind::Scope { body } => {
                let dest = Place::local(self.temp(ty.clone()));
                self.push_instr(Instr::ScopeEnter);
                self.open_scopes += 1;
                self.assign_to(&dest, body);
                self.open_scopes -= 1;
                let resume = self.new_block();
                self.terminate(Term::ScopeExit { resume });
                self.switch_to(resume);
                Operand::Copy(dest)
            }
            hir::ExprKind::Spawn { expr } => {
                let task = self.expr(expr);
                self.push_instr(Instr::Spawn(task));
                Operand::Const(Const::Unit)
            }
            hir::ExprKind::Return { value } => {
                let operand = match value {
                    Some(value) => self.expr(value),
                    None => Operand::Const(Const::Unit),
                };
                self.return_from(operand);
                // Anything the source wrote after a `return` lands in a block nothing reaches.
                let unreachable = self.new_block();
                self.switch_to(unreachable);
                Operand::Const(Const::Unit)
            }
            hir::ExprKind::SpawnReactor { reactor, args } => {
                let args = args.iter().map(|arg| self.expr(arg)).collect();
                let dest = Place::local(self.temp(ty.clone()));
                self.push_instr(Instr::SpawnReactor {
                    dest: dest.clone(),
                    reactor: reactor.index(),
                    args,
                });
                Operand::Copy(dest)
            }
            hir::ExprKind::ReactorInput { reactor, index } => {
                let handle = self.expr(reactor);
                let temp = Place::local(self.temp(ty.clone()));
                self.emit(temp.clone(), Rvalue::ReactorInput(handle, *index));
                Operand::Copy(temp)
            }
            hir::ExprKind::ReactorExport { reactor, index } => {
                let handle = self.expr(reactor);
                let temp = Place::local(self.temp(ty.clone()));
                self.emit(temp.clone(), Rvalue::ReactorExport(handle, *index));
                Operand::Copy(temp)
            }
            hir::ExprKind::Error => Operand::Const(Const::Unit),
        }
    }

    fn stmt(&mut self, stmt: &hir::Stmt) {
        match &stmt.kind {
            hir::StmtKind::Let { local, value } => {
                let place = Place::local(local.index());
                self.assign_to(&place, value);
            }
            hir::StmtKind::Assign { place, value } => {
                let target = self.place(place);
                self.assign_to(&target, value);
                // A commit is emitted in place, right after the local it mirrors is written, so
                // the order the turn commits in is the order the handler wrote in.
                if let hir::ExprKind::Local(id) = place.kind
                    && let hir::LocalRole::State(slot) = self.roles[id.index()]
                {
                    self.push_instr(Instr::SetSlot(
                        slot,
                        Operand::Copy(Place::local(id.index())),
                    ));
                }
            }
            // Emitted in place too, and for a sharper reason: an `after` inside a branch
            // that was not taken must not fire, and the only way to be sure of that is for the
            // request to be an instruction on the path rather than a list built beside it.
            hir::StmtKind::After { task, returns } => {
                let task = self.expr(task);
                self.push_instr(Instr::Emit {
                    task,
                    returns: *returns,
                });
            }
            hir::StmtKind::Expr(expr) => {
                self.expr(expr);
            }
        }
    }

    /// The left-hand side of an assignment, which the checker has already proved is a local or a
    /// chain of fields rooted at one.
    fn place(&mut self, expr: &hir::Expr) -> Place {
        match &expr.kind {
            hir::ExprKind::Local(id) => Place::local(id.index()),
            hir::ExprKind::Field { base, index } => {
                // No deref peel here: `check_assignable` refused a `Shared`-typed base, so a
                // write never traverses one.
                debug_assert!(
                    !matches!(base.ty, hir::Ty::Shared(_)),
                    "a write projected through a shared value survived checking"
                );
                self.place(base).field(*index)
            }
            _ => Place::local(self.temp(expr.ty.clone())),
        }
    }

    fn short_circuit(&mut self, and: bool, lhs: &hir::Expr, rhs: &hir::Expr) -> Operand {
        let dest = Place::local(self.temp(hir::Ty::Bool));
        let lhs = self.expr(lhs);
        self.emit(dest.clone(), Rvalue::Use(lhs));

        let rhs_block = self.new_block();
        let join = self.new_block();
        let cond = Operand::Copy(dest.clone());
        // `a && b` evaluates `b` only when `a` held; `a || b` only when it did not.
        let term = if and {
            Term::Branch {
                cond,
                then: rhs_block,
                els: join,
            }
        } else {
            Term::Branch {
                cond,
                then: join,
                els: rhs_block,
            }
        };
        self.terminate(term);

        self.switch_to(rhs_block);
        let rhs = self.expr(rhs);
        self.emit(dest.clone(), Rvalue::Use(rhs));
        self.terminate(Term::Goto(join));

        self.switch_to(join);
        Operand::Copy(dest)
    }

    fn if_expr(
        &mut self,
        ty: hir::Ty,
        cond: &hir::Expr,
        then: &hir::Expr,
        els: Option<&hir::Expr>,
    ) -> Operand {
        let dest = Place::local(self.temp(ty));
        let cond = self.expr(cond);
        let then_block = self.new_block();
        let else_block = self.new_block();
        let join = self.new_block();
        self.terminate(Term::Branch {
            cond,
            then: then_block,
            els: else_block,
        });

        self.switch_to(then_block);
        self.assign_to(&dest, then);
        self.terminate(Term::Goto(join));

        self.switch_to(else_block);
        match els {
            Some(els) => self.assign_to(&dest, els),
            None => self.emit(dest.clone(), Rvalue::Use(Operand::Const(Const::Unit))),
        }
        self.terminate(Term::Goto(join));

        self.switch_to(join);
        Operand::Copy(dest)
    }

    fn match_expr(&mut self, ty: hir::Ty, scrutinee: &hir::Expr, arms: &[hir::Arm]) -> Operand {
        let dest = Place::local(self.temp(ty));
        let value = self.expr_place(scrutinee);
        let join = self.new_block();

        // One test block per arm, chained: a failed test falls through to the next arm, and the
        // last failure traps.
        let mut test_blocks: Vec<BlockId> = Vec::with_capacity(arms.len());
        for _ in arms {
            test_blocks.push(self.new_block());
        }
        let fallthrough = self.new_block();
        self.terminate_at(fallthrough, Term::Trap("no match arm applied"));
        self.terminate(Term::Goto(test_blocks[0]));

        for (index, arm) in arms.iter().enumerate() {
            let next = test_blocks.get(index + 1).copied().unwrap_or(fallthrough);
            self.switch_to(test_blocks[index]);
            let body_block = self.new_block();
            self.test(&arm.pat, &value, body_block, next);

            self.switch_to(body_block);
            if let Some(guard) = &arm.guard {
                let cond = self.expr(guard);
                let guarded = self.new_block();
                self.terminate(Term::Branch {
                    cond,
                    then: guarded,
                    els: next,
                });
                self.switch_to(guarded);
            }
            self.assign_to(&dest, &arm.body);
            self.terminate(Term::Goto(join));
        }

        self.switch_to(join);
        Operand::Copy(dest)
    }

    /// Emit the test for `pat` against `value`, jumping to `success` when it matches and `fail`
    /// when it does not. Bindings are assigned along the successful path only.
    fn test(&mut self, pat: &hir::Pat, value: &Place, success: BlockId, fail: BlockId) {
        match &pat.kind {
            hir::PatKind::Wild | hir::PatKind::Error => {
                self.terminate(Term::Goto(success));
            }
            hir::PatKind::Bind(local) => {
                self.emit(
                    Place::local(local.index()),
                    Rvalue::Use(Operand::Copy(value.clone())),
                );
                self.terminate(Term::Goto(success));
            }
            hir::PatKind::Int(v) => self.test_const(value, Const::Int(*v), success, fail),
            hir::PatKind::Bool(v) => self.test_const(value, Const::Bool(*v), success, fail),
            hir::PatKind::Str(v) => {
                self.test_const(value, Const::Str(v.as_str().into()), success, fail)
            }
            hir::PatKind::Struct { args, .. } => {
                self.test_fields(args, value, None, success, fail);
            }
            hir::PatKind::Variant { variant, args, .. } => {
                let matched = self.new_block();
                self.terminate(Term::SwitchTag {
                    scrutinee: value.clone(),
                    cases: vec![(*variant, matched)],
                    default: fail,
                });
                self.switch_to(matched);
                // The switch just proved the tag, so the field reads below are downcasts.
                self.test_fields(args, value, Some(*variant), success, fail);
            }
            hir::PatKind::Or(alts) => {
                // Alternatives bind nothing, so each may simply be tried in turn.
                for (index, alt) in alts.iter().enumerate() {
                    let next = if index + 1 == alts.len() {
                        fail
                    } else {
                        self.new_block()
                    };
                    self.test(alt, value, success, next);
                    if index + 1 < alts.len() {
                        self.switch_to(next);
                    }
                }
            }
        }
    }

    fn test_const(&mut self, value: &Place, expected: Const, success: BlockId, fail: BlockId) {
        let temp = Place::local(self.temp(hir::Ty::Bool));
        self.emit(
            temp.clone(),
            Rvalue::Binary(
                hir::BinOp::Eq,
                Operand::Copy(value.clone()),
                Operand::Const(expected),
            ),
        );
        self.terminate(Term::Branch {
            cond: Operand::Copy(temp),
            then: success,
            els: fail,
        });
    }

    /// Test each sub-pattern of an aggregate in turn; the last one jumps to `success`. A variant's
    /// payload projects with the tag the caller's switch established; a struct's projects plainly.
    fn test_fields(
        &mut self,
        args: &[hir::Pat],
        value: &Place,
        variant: Option<usize>,
        success: BlockId,
        fail: BlockId,
    ) {
        if args.is_empty() {
            self.terminate(Term::Goto(success));
            return;
        }
        for (index, arg) in args.iter().enumerate() {
            let field = match variant {
                Some(variant) => value.downcast(variant, index),
                None => value.field(index),
            };
            let next = if index + 1 == args.len() {
                success
            } else {
                self.new_block()
            };
            self.test(arg, &field, next, fail);
            if index + 1 < args.len() {
                self.switch_to(next);
            }
        }
    }

    /// `e?` — take the payload when the value succeeded, and return the failure otherwise.
    fn try_expr(&mut self, ty: hir::Ty, expr: &hir::Expr, enum_id: usize) -> Operand {
        let value = self.expr_place(expr);
        let dest = Place::local(self.temp(ty));
        let ok_block = self.new_block();
        let fail_block = self.new_block();

        // Both `Result` and `Option` put success at tag 0 and 1 respectively, so the tag to take
        // depends on which one is being unwrapped.
        let (ok_tag, ok_field) = if enum_id == norn_hir::hir::EnumId::RESULT.index() {
            (norn_hir::hir::EnumId::OK, true)
        } else {
            (norn_hir::hir::EnumId::SOME, true)
        };
        let _ = ok_field;
        self.terminate(Term::SwitchTag {
            scrutinee: value.clone(),
            cases: vec![(ok_tag, ok_block)],
            default: fail_block,
        });

        self.switch_to(fail_block);
        if enum_id == norn_hir::hir::EnumId::RESULT.index() {
            // Rebuild `Err(e)` at the function's own error type, which the checker has already
            // proved is the same type.
            let error = value.downcast(norn_hir::hir::EnumId::ERR, 0);
            let rebuilt = Place::local(self.temp(self.ret.clone()));
            self.emit(
                rebuilt.clone(),
                Rvalue::Variant(
                    enum_id,
                    norn_hir::hir::EnumId::ERR,
                    vec![Operand::Copy(error)],
                ),
            );
            self.return_from(Operand::Copy(rebuilt));
        } else {
            let rebuilt = Place::local(self.temp(self.ret.clone()));
            self.emit(
                rebuilt.clone(),
                Rvalue::Variant(enum_id, norn_hir::hir::EnumId::NONE, Vec::new()),
            );
            self.return_from(Operand::Copy(rebuilt));
        }

        self.switch_to(ok_block);
        self.emit(
            dest.clone(),
            Rvalue::Use(Operand::Copy(value.downcast(ok_tag, 0))),
        );
        Operand::Copy(dest)
    }
}
