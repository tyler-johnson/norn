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
    let records = program
        .records
        .iter()
        .map(|record| RecordLayout {
            name: record.name.clone(),
            fields: record.fields.iter().map(|f| f.name.clone()).collect(),
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
                    fields: v.fields.iter().map(|f| f.name.clone()).collect(),
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
    Program {
        records,
        enums,
        fns,
        main: program.main.map(|id| id.index()),
    }
}

fn lower_fn(program: &hir::Program, def: &hir::FnDef) -> Function {
    let mut lowerer = Lowerer {
        program,
        locals: def.locals.iter().map(|l| l.name.clone()).collect(),
        blocks: vec![Block::default()],
        current: 0,
        open_scopes: 0,
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
        locals: lowerer.locals,
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
    blocks: Vec<Block>,
    current: BlockId,
    /// Scopes open around the expression being lowered. A `return` or a `?` that crosses one has to
    /// leave it, so the exits are emitted before the return.
    open_scopes: usize,
}

impl Lowerer<'_> {
    fn temp(&mut self) -> LocalId {
        let id = self.locals.len();
        self.locals.push(String::new());
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
                let temp = Place::local(self.temp());
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
        match &expr.kind {
            hir::ExprKind::Unit => Operand::Const(Const::Unit),
            hir::ExprKind::Int(v) => Operand::Const(Const::Int(*v)),
            hir::ExprKind::Float(v) => Operand::Const(Const::Float(*v)),
            hir::ExprKind::Bool(v) => Operand::Const(Const::Bool(*v)),
            hir::ExprKind::Str(v) => Operand::Const(Const::Str(v.as_str().into())),
            hir::ExprKind::Local(id) => Operand::Copy(Place::local(id.index())),
            hir::ExprKind::Field { base, index } => {
                let base = self.expr_place(base);
                Operand::Copy(base.field(*index))
            }
            hir::ExprKind::Unary { op, expr } => {
                let operand = self.expr(expr);
                let temp = Place::local(self.temp());
                self.emit(temp.clone(), Rvalue::Unary(*op, operand));
                Operand::Copy(temp)
            }
            hir::ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.expr(lhs);
                let rhs = self.expr(rhs);
                let temp = Place::local(self.temp());
                self.emit(temp.clone(), Rvalue::Binary(*op, lhs, rhs));
                Operand::Copy(temp)
            }
            hir::ExprKind::ShortCircuit { and, lhs, rhs } => self.short_circuit(*and, lhs, rhs),
            hir::ExprKind::Call { callee, args } => {
                let args = args.iter().map(|arg| self.expr(arg)).collect();
                let temp = Place::local(self.temp());
                // A call to a `task fn` builds a task rather than pushing a frame. Nothing runs
                // until something awaits or spawns it.
                let rvalue = if self.program.fns[callee.index()].is_task {
                    Rvalue::Task(callee.index(), args)
                } else {
                    Rvalue::Call(callee.index(), args)
                };
                self.emit(temp.clone(), rvalue);
                Operand::Copy(temp)
            }
            hir::ExprKind::Builtin { builtin, args } => {
                let args = args.iter().map(|arg| self.expr(arg)).collect();
                let temp = Place::local(self.temp());
                let rvalue = if builtin.is_task() {
                    Rvalue::BuiltinTask(*builtin, args)
                } else {
                    Rvalue::Builtin(*builtin, args)
                };
                self.emit(temp.clone(), rvalue);
                Operand::Copy(temp)
            }
            hir::ExprKind::Construct { ctor, args } => {
                let args = args.iter().map(|arg| self.expr(arg)).collect();
                let rvalue = match ctor {
                    hir::Ctor::Record(id) => Rvalue::Record(id.index(), args),
                    hir::Ctor::Variant(id, variant) => Rvalue::Variant(id.index(), *variant, args),
                };
                let temp = Place::local(self.temp());
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
            hir::ExprKind::If { cond, then, els } => self.if_expr(cond, then, els.as_deref()),
            hir::ExprKind::Match { scrutinee, arms } => self.match_expr(scrutinee, arms),
            hir::ExprKind::Try { expr, enum_id } => self.try_expr(expr, enum_id.index()),
            hir::ExprKind::Await { expr } => {
                let task = self.expr(expr);
                let dest = Place::local(self.temp());
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
                let dest = Place::local(self.temp());
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
            hir::ExprKind::SpawnReactor { .. }
            | hir::ExprKind::ReactorInput { .. }
            | hir::ExprKind::ReactorExport { .. } => unimplemented!("reactor lowering"),
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
                let place = self.place(place);
                self.assign_to(&place, value);
            }
            hir::StmtKind::AfterCommit { .. } => unimplemented!("reactor lowering"),
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
            hir::ExprKind::Field { base, index } => self.place(base).field(*index),
            _ => Place::local(self.temp()),
        }
    }

    fn short_circuit(&mut self, and: bool, lhs: &hir::Expr, rhs: &hir::Expr) -> Operand {
        let dest = Place::local(self.temp());
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

    fn if_expr(&mut self, cond: &hir::Expr, then: &hir::Expr, els: Option<&hir::Expr>) -> Operand {
        let dest = Place::local(self.temp());
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

    fn match_expr(&mut self, scrutinee: &hir::Expr, arms: &[hir::Arm]) -> Operand {
        let dest = Place::local(self.temp());
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
            hir::PatKind::Record { args, .. } => {
                self.test_fields(args, value, success, fail);
            }
            hir::PatKind::Variant { variant, args, .. } => {
                let matched = self.new_block();
                self.terminate(Term::SwitchTag {
                    scrutinee: value.clone(),
                    cases: vec![(*variant, matched)],
                    default: fail,
                });
                self.switch_to(matched);
                self.test_fields(args, value, success, fail);
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
        let temp = Place::local(self.temp());
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

    /// Test each sub-pattern of an aggregate in turn; the last one jumps to `success`.
    fn test_fields(&mut self, args: &[hir::Pat], value: &Place, success: BlockId, fail: BlockId) {
        if args.is_empty() {
            self.terminate(Term::Goto(success));
            return;
        }
        for (index, arg) in args.iter().enumerate() {
            let field = value.field(index);
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
    fn try_expr(&mut self, expr: &hir::Expr, enum_id: usize) -> Operand {
        let value = self.expr_place(expr);
        let dest = Place::local(self.temp());
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
            // Rebuild `#Err(e)` at the function's own error type, which the checker has already
            // proved is the same type.
            let error = value.field(0);
            let rebuilt = Place::local(self.temp());
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
            let rebuilt = Place::local(self.temp());
            self.emit(
                rebuilt.clone(),
                Rvalue::Variant(enum_id, norn_hir::hir::EnumId::NONE, Vec::new()),
            );
            self.return_from(Operand::Copy(rebuilt));
        }

        self.switch_to(ok_block);
        self.emit(dest.clone(), Rvalue::Use(Operand::Copy(value.field(0))));
        Operand::Copy(dest)
    }
}
