//! Capability inference: what authority a body actually reaches.
//!
//! A function's `uses` set is what its body reaches, transitively — the builtins it calls that
//! need authority, plus everything the functions and reactors it builds tasks from reach in turn.
//! Nothing has to be written down. A written `uses { … }` is an assertion checked against the
//! inferred set and required to match it exactly: a capability the body reaches but the clause
//! omits is an error, and so is one the clause names but the body never reaches. Writing the
//! clause is how a public function pins its authority so a later release cannot widen it in
//! silence; not writing it is the everyday spelling.
//!
//! The pass runs after monomorphization, beside `infer_sinks` and for the same reason: every
//! executable body is concrete by then, so a set is a per-instance fact and templates — neutered
//! to inert unit bodies — are skipped. An instance inherits its template's written clause, spans
//! and all, so an assertion written once reports once, the (span, message) dedupe collapsing the
//! rest.
//!
//! The fixpoint is the plain one `infer_sinks` uses: repeated sweeps in `FnId` order and then
//! `ReactorId` order, unioning callee sets into caller sets until nothing moves. Sets only ever
//! grow over a five-element vocabulary, so the loop is monotone and terminates — recursion and
//! mutual recursion converge with no cycle detection at all, which is why `uses` never has to be
//! written to break a loop. Vec order and index lookups keep it deterministic, the `generics`
//! discipline.
//!
//! One deliberate difference from `check_turns`, which walks the same call graph: `collect_calls`
//! there *excludes* an `after`'s head call, because the task it builds does not run during the
//! turn. Here the head is exactly what matters — `after wait(ms)` is where a reactor's authority
//! comes from — so the walk below takes the operand whole.

use super::*;

/// Something a body reaches that carries authority with it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reach {
    Fn(FnId),
    Reactor(ReactorId),
    Builtin(Builtin),
}

/// One reach, and the span to blame for it. Edges are collected once, before the fixpoint: the
/// sweep then costs a union per edge rather than a walk per body, and the witness search that
/// explains a failed assertion gets the graph it needs for free.
#[derive(Clone, Copy)]
struct Edge {
    reach: Reach,
    span: Span,
}

/// How many names a witness chain prints before it gives up and says `…`. A chain is an
/// explanation, not a proof: past a handful of hops the reader wants the two ends.
const CHAIN: usize = 6;

impl Checker {
    pub(super) fn infer_uses(&mut self) {
        let edges: Vec<Vec<Edge>> = self
            .program
            .fns
            .iter()
            .map(|def| {
                let mut found = Vec::new();
                if !def.inert {
                    collect_edges(&def.body, &mut found);
                }
                found
            })
            .collect();
        let members: Vec<Vec<FnId>> = self.program.reactors.iter().map(members_of).collect();

        let mut fns: Vec<Vec<Capability>> = vec![Vec::new(); self.program.fns.len()];
        let mut reactors: Vec<Vec<Capability>> = vec![Vec::new(); self.program.reactors.len()];

        loop {
            let mut changed = false;
            for index in 0..edges.len() {
                let mut wanted: Vec<Capability> = Vec::new();
                for edge in &edges[index] {
                    match edge.reach {
                        Reach::Builtin(builtin) => extend(&mut wanted, builtin.capabilities()),
                        Reach::Fn(callee) => extend(&mut wanted, &fns[callee.index()]),
                        Reach::Reactor(id) => extend(&mut wanted, &reactors[id.index()]),
                    };
                }
                changed |= extend(&mut fns[index], &wanted);
            }
            // A reactor's authority is its members': the handlers are where `after` names the
            // tasks it launches, and a spawner reaches all of it through the handle.
            for id in 0..reactors.len() {
                let mut wanted: Vec<Capability> = Vec::new();
                for member in &members[id] {
                    extend(&mut wanted, &fns[member.index()]);
                }
                changed |= extend(&mut reactors[id], &wanted);
            }
            if !changed {
                break;
            }
        }

        self.check_assertions(&edges, &members, &fns, &reactors);

        // The inferred sets become the program's. Nothing after the checker reads them — this is
        // what the editor and any later authority tooling ask, and it is the honest answer now
        // that the written clause is no longer the only one there was.
        for (def, uses) in self.program.fns.iter_mut().zip(fns) {
            def.uses = uses;
        }
        for (def, uses) in self.program.reactors.iter_mut().zip(reactors) {
            def.uses = uses;
        }
    }

    /// Hold every written clause to the settled sets, both ways round.
    fn check_assertions(
        &mut self,
        edges: &[Vec<Edge>],
        members: &[Vec<FnId>],
        fns: &[Vec<Capability>],
        reactors: &[Vec<Capability>],
    ) {
        let witness = Witness {
            program: &self.program,
            edges,
            members,
            fns,
            reactors,
            declared: &self.declared_uses,
            declared_reactors: &self.declared_reactor_uses,
        };
        let mut errors: Vec<(usize, Diagnostic)> = Vec::new();

        for index in 0..self.program.fns.len() {
            let Some(declared) = self.declared_uses[index].as_ref() else {
                continue;
            };
            if self.program.fns[index].inert {
                continue;
            }
            let name = &self.program.fns[index].name;
            let owner = self.fn_owner[index];
            for capability in &fns[index] {
                if declared.iter().any(|(seen, _)| seen == capability) {
                    continue;
                }
                if let Some(diagnostic) = witness.undeclared(index, name, *capability, &fns[index])
                {
                    errors.push((owner, diagnostic));
                }
            }
            for (capability, at) in declared {
                if !fns[index].contains(capability) {
                    errors.push((owner, unreached(name, *capability, *at, &fns[index])));
                }
            }
        }

        for id in 0..self.program.reactors.len() {
            let Some(declared) = self.declared_reactor_uses[id].as_ref() else {
                continue;
            };
            let name = &self.program.reactors[id].name;
            for capability in &reactors[id] {
                if declared.iter().any(|(seen, _)| seen == capability) {
                    continue;
                }
                // The blame belongs in the member that reaches it, wherever that member is: a
                // reactor's clause is a promise about the whole graph under it.
                for member in &members[id] {
                    if !fns[member.index()].contains(capability) {
                        continue;
                    }
                    if let Some(diagnostic) =
                        witness.undeclared(member.index(), name, *capability, &reactors[id])
                    {
                        errors.push((self.fn_owner[member.index()], diagnostic));
                    }
                    break;
                }
            }
            for (capability, at) in declared {
                if !reactors[id].contains(capability) {
                    errors.push((
                        self.reactor_owner[id],
                        unreached(name, *capability, *at, &reactors[id]),
                    ));
                }
            }
        }

        // `report` is `infer_sinks`', and the dedupe is why: an assertion written once in a
        // template must not report once per instance.
        self.report(errors);
    }
}

/// The settled tables, for the searches that have to explain themselves.
struct Witness<'a> {
    program: &'a Program,
    edges: &'a [Vec<Edge>],
    members: &'a [Vec<FnId>],
    fns: &'a [Vec<Capability>],
    reactors: &'a [Vec<Capability>],
    declared: &'a [Option<Vec<(Capability, Span)>>],
    declared_reactors: &'a [Option<Vec<(Capability, Span)>>],
}

impl Witness<'_> {
    /// A capability the body reaches and the clause does not name, reported where the reaching
    /// happens: the call inside the declaring function that leads to it, with the rest of the way
    /// down carried as a note. The span is the one a reader can act on — the chain explains why.
    fn undeclared(
        &self,
        index: usize,
        name: &str,
        capability: Capability,
        inferred: &[Capability],
    ) -> Option<Diagnostic> {
        let edge = self.reaching_edge(index, capability)?;
        let mut seen = Vec::new();
        let trail = self.trail(edge.reach, capability, &mut seen);
        let first = trail.first()?.clone();
        let message = format!(
            "`{name}` does not declare the capability `{}`",
            capability.name()
        );
        let label = if matches!(edge.reach, Reach::Builtin(_)) {
            format!("`{first}` uses it")
        } else {
            format!("`{first}` reaches it")
        };
        let mut diagnostic = Diagnostic::new(edge.span, message).label(label);
        if trail.len() > 1 {
            let path: Vec<String> = trail
                .iter()
                .map(|name| {
                    if name == "…" {
                        name.clone()
                    } else {
                        format!("`{name}`")
                    }
                })
                .collect();
            diagnostic = diagnostic.note(format!("through {}", path.join(" → ")));
        }
        Some(diagnostic.note(format!(
            "a written `uses {{ … }}` is the whole set: write `{}`, or drop the clause and let it be inferred",
            render(inferred)
        )))
    }

    /// The first edge of a body that leads to `capability`, in the order the body wrote them.
    fn reaching_edge(&self, index: usize, capability: Capability) -> Option<Edge> {
        self.edges[index]
            .iter()
            .find(|edge| self.supplies(edge.reach, capability))
            .copied()
    }

    fn supplies(&self, reach: Reach, capability: Capability) -> bool {
        match reach {
            Reach::Builtin(builtin) => builtin.capabilities().contains(&capability),
            Reach::Fn(callee) => self.fns[callee.index()].contains(&capability),
            Reach::Reactor(id) => self.reactors[id.index()].contains(&capability),
        }
    }

    /// Whether something already declares the capability itself, which is where a chain stops:
    /// past a written clause the reader has a name to look up rather than a path to follow.
    fn declares(&self, reach: Reach, capability: Capability) -> bool {
        let row = match reach {
            Reach::Fn(callee) => self.declared[callee.index()].as_ref(),
            Reach::Reactor(id) => self.declared_reactors[id.index()].as_ref(),
            Reach::Builtin(_) => None,
        };
        row.is_some_and(|declared| declared.iter().any(|(seen, _)| *seen == capability))
    }

    /// The names from one reach down to whatever ultimately needs the authority.
    fn trail(&self, from: Reach, capability: Capability, seen: &mut Vec<Reach>) -> Vec<String> {
        let mut out = Vec::new();
        let mut at = from;
        loop {
            match at {
                Reach::Builtin(builtin) => {
                    out.push(builtin.name().to_string());
                    return out;
                }
                Reach::Fn(callee) => out.push(self.program.fns[callee.index()].name.clone()),
                Reach::Reactor(id) => out.push(self.program.reactors[id.index()].name.clone()),
            }
            if seen.contains(&at) || self.declares(at, capability) {
                return out;
            }
            seen.push(at);
            if out.len() >= CHAIN {
                out.push("…".to_string());
                return out;
            }
            let next = match at {
                Reach::Fn(callee) => self
                    .reaching_edge(callee.index(), capability)
                    .map(|edge| edge.reach),
                // A reactor's authority arrives through whichever member reaches it.
                Reach::Reactor(id) => self.members[id.index()]
                    .iter()
                    .find(|member| self.fns[member.index()].contains(&capability))
                    .map(|member| Reach::Fn(*member)),
                Reach::Builtin(_) => None,
            };
            match next {
                Some(next) => at = next,
                None => return out,
            }
        }
    }
}

/// A capability the clause names and the body never reaches. Under an exact reading this is as
/// wrong as omitting one: the clause says what the authority *is*, and authority nobody exercises
/// is authority nobody meant to grant.
fn unreached(name: &str, capability: Capability, at: Span, inferred: &[Capability]) -> Diagnostic {
    Diagnostic::new(
        at,
        format!(
            "`{name}` declares the capability `{}` and never uses it",
            capability.name()
        ),
    )
    .label("nothing in the body reaches it")
    .note("a written `uses { … }` is exact: the compiler infers the set, and writing one asserts what it must be")
    .note(format!("the inferred set is `{}`", render(inferred)))
}

/// How a set is spelled back to the reader. The empty set is `uses { }` — a real clause, and the
/// assertion that a task reaches nothing.
fn render(capabilities: &[Capability]) -> String {
    if capabilities.is_empty() {
        return "uses { }".to_string();
    }
    let names: Vec<&str> = capabilities.iter().map(|c| c.name()).collect();
    format!("uses {{ {} }}", names.join(", "))
}

/// Merge `from` into `into`, kept sorted and deduplicated; whether anything moved is the
/// fixpoint's only termination signal.
fn extend(into: &mut Vec<Capability>, from: &[Capability]) -> bool {
    let mut changed = false;
    for capability in from {
        if let Err(at) = into.binary_search(capability) {
            into.insert(at, *capability);
            changed = true;
        }
    }
    changed
}

/// The lifted functions a reactor is made of: every handler, and every node body. Only handlers
/// can hold an `after`, so the pure bodies contribute nothing — they are walked for uniformity,
/// not necessity.
fn members_of(reactor: &ReactorDef) -> Vec<FnId> {
    let mut out: Vec<FnId> = Vec::new();
    for node in &reactor.nodes {
        match node.kind {
            NodeKind::Param { .. } => {}
            NodeKind::State { init, .. } => out.push(init),
            NodeKind::Signal { body, .. } => out.push(body),
        }
    }
    for input in &reactor.inputs {
        out.push(input.handler);
    }
    // `init` can hold an `after` too, so what it reaches joins the reactor's union.
    if let Some(init) = reactor.init {
        out.push(init);
    }
    out
}

/// Everything an expression reaches for authority, deduplicated on the reach so that each one
/// keeps the first span it was written at.
fn collect_edges(expr: &Expr, found: &mut Vec<Edge>) {
    let push = |reach: Reach, span: Span, found: &mut Vec<Edge>| {
        if !found.iter().any(|edge| edge.reach == reach) {
            found.push(Edge { reach, span });
        }
    };
    match &expr.kind {
        ExprKind::Call { callee, args } => {
            push(Reach::Fn(*callee), expr.span, found);
            for arg in args {
                collect_edges(arg, found);
            }
        }
        ExprKind::Builtin { builtin, args } => {
            if !builtin.capabilities().is_empty() {
                push(Reach::Builtin(*builtin), expr.span, found);
            }
            for arg in args {
                collect_edges(arg, found);
            }
        }
        ExprKind::SpawnReactor { reactor, args } => {
            push(Reach::Reactor(*reactor), expr.span, found);
            for arg in args {
                collect_edges(arg, found);
            }
        }
        ExprKind::Construct { args, .. } => {
            for arg in args {
                collect_edges(arg, found);
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
        | ExprKind::ReactorExport { reactor: inner, .. } => collect_edges(inner, found),
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::ShortCircuit { lhs, rhs, .. }
        | ExprKind::While {
            cond: lhs,
            body: rhs,
        } => {
            collect_edges(lhs, found);
            collect_edges(rhs, found);
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_edges(scrutinee, found);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_edges(guard, found);
                }
                collect_edges(&arm.body, found);
            }
        }
        ExprKind::If { cond, then, els } => {
            collect_edges(cond, found);
            collect_edges(then, found);
            if let Some(els) = els {
                collect_edges(els, found);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match &stmt.kind {
                    StmtKind::Let { value, .. } => collect_edges(value, found),
                    StmtKind::Assign { place, value } => {
                        collect_edges(place, found);
                        collect_edges(value, found);
                    }
                    // The head call included, unlike `collect_calls`: `after deliver(m)` is
                    // precisely where a reactor's authority is spent, even though the task it
                    // builds runs after the turn rather than during it.
                    StmtKind::After { task, .. } => collect_edges(task, found),
                    StmtKind::Expr(expr) => collect_edges(expr, found),
                }
            }
            if let Some(tail) = tail {
                collect_edges(tail, found);
            }
        }
        ExprKind::Return { value } | ExprKind::Break { value } => {
            if let Some(value) = value {
                collect_edges(value, found);
            }
        }
        ExprKind::Continue
        | ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Error => {}
    }
}
