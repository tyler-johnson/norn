# Bootstrapping Norn

*Implementation plan · companion to [DESIGN.md](./DESIGN.md)*

`DESIGN.md` describes a language. This document describes the shortest honest path from an empty
repository to a native compiler for a subset of it, and states explicitly what that subset leaves
out.

| | |
|---|---|
| **Status** | Active plan |
| **Goal** | `norn build service.norn -o service` produces a native binary running a real HTTP service |
| **Host language** | Rust (stable, 1.97+) |
| **Target** | aarch64-linux initially; nothing in the design is arch-specific |

---

## Contents

- [1. Sequencing principle](#1--sequencing-principle)
- [2. Architecture](#2--architecture)
- [3. Backend strategy](#3--backend-strategy)
- [4. The v0 language subset](#4--the-v0-language-subset)
- [5. Milestones](#5--milestones)
- [6. Turn traces as the test harness](#6--turn-traces-as-the-test-harness)
- [7. Crate layout](#7--crate-layout)
- [8. Deferred work](#8--deferred-work)

---

## 1 · Sequencing principle

The design document's Phase 1 proposes an interpreter to settle semantics; the stated goal here is a
native compiler. These are not in tension, provided the interpreter is not a separate program.

Frontend, intermediate representation, and **runtime** are shared between the two execution
strategies. Only the final step — walk the IR versus emit code for it — differs. Under that
arrangement the interpreter costs roughly ten percent extra over building the native path alone, and
it buys a differential oracle: the same program, executed both ways, must produce a byte-identical
turn trace. A young native backend has no other cheap source of truth, and this one cannot be
retrofitted later.

The corollary governs where work happens:

> Lowering of tasks to explicit state machines, and of reactors to state slots plus a propagation
> plan, belongs in the IR — not in the backend.

If the interpreter executes explicit continuations rather than riding the host call stack, the native
backend is mostly a printer. If it rides the host stack, the two engines diverge in exactly the
places (suspension, cancellation, reentry) where the language makes its most interesting claims.

## 2 · Architecture

```
source (.norn)
    ↓
norn-syntax        lexer, parser, concrete syntax tree
    ↓
norn-hir           name resolution, type checking, typed AST
    ↓                  reactive analysis: dependency graph, causality,
    ↓                  effect sets, move checking, queue policy
norn-nir           lowered IR: no await, no reactors.
    ↓              explicit state machines, explicit state slots.
    ├──────────────────────────────┐
    ↓                              ↓
norn-nir::interp            norn-codegen
    ↘                              ↙
              norn-rt
     scheduler · epoll · timers · mailboxes
     turn loop · flows · affine resource table
```

Both execution paths link the same `norn-rt`. A runtime bug reproduces identically under the
interpreter, where it is debuggable.

## 3 · Backend strategy

Code generation is not the difficult part of this language. The difficult parts are the runtime
(scheduler, I/O, mailbox, turn loop) and the static analyses (causality, effects, moves). The
backend should therefore be made as cheap as possible for as long as possible.

**Decision: emit a restricted subset of Rust and compile it with `rustc`.**

The restriction is the substance of the decision. Generated code may use structs, enums, `match`,
loops, `Rc`/`Arc`, and calls into `norn-rt`. It may **not** use `async`, lifetimes, or traits. That
subset maps one-to-one onto a direct Cranelift backend later, so the eventual swap is mechanical.
The moment generated code leans on `rustc`'s `async` lowering or its borrow checker, Norn has
borrowed semantics it must eventually own, and the swap stops being mechanical.

Alternatives considered:

| Option | Assessment |
|---|---|
| Emit C, compile with `gcc` | Equivalent work minus the `rustc` dependency, plus a hand-rolled value and reference-count ABI. Viable; no advantage at this stage. |
| Direct Cranelift (`cranelift-object` → link with `gcc`) | The intended end state. Deferred until NIR stabilises, because it is slow to first light and NIR will churn. |
| LLVM via `inkwell` | Rejected. Build cost on the target hardware is prohibitive and the dependency is heavy for a project this early. |

## 4 · The v0 language subset

### Included

- **Values** — `I64`, `F64`, `Bool`, `String`, `Bytes`, records, enums with payloads, `match`,
  built-in `Result<T, E>` and `Option<T>` with `?`.
- **Tasks** — `task fn`, `await`, `scope { spawn ... }`, cancellation, structured join on scope exit.
- **Reactors** — static graphs only: `input` with declared capacity and overflow policy, `state`,
  `signal`, `event`, the operators `hold` / `scan` / `count` / `map` / `merge` / `combine`,
  `after_commit` effect requests, `export`, `.latest()`, `.send()`.
- **Memory** — move checking, affine operating-system resources released on scope exit *and* on
  cancellation, `Shared<T>` immutable reference counting.
- **Effects** — `uses { ... }` as a checked annotation.
- **I/O** — TCP, timers, files, HTTP/1.1, `Flow<Bytes>` with genuine demand signalling.

### Excluded, deliberately

Generics; traits; a borrow checker (`&T` is permitted only as a non-escaping parameter, enforced
syntactically); dynamic subgraphs (`switch`); macros and derives; modules beyond a single file; a
multi-threaded work-stealing scheduler; capability *inference*.

The cut worth defending is **static reactor graphs**. Dynamic switching is where graph arenas,
region reclamation, and subscription lifetimes all become load-bearing — it is the majority of
`DESIGN.md` §7. A static graph compiles instead to a fixed struct of state slots plus a
topologically ordered propagation function: a few hundred lines rather than a research project. It
still demonstrates glitch freedom, turn determinism, and effects-after-commit, which are the claims
the design rests on. `switch` arrives after the trace tooling exists to debug it.

## 5 · Milestones

### M0 — Skeleton

Cargo workspace, `norn` CLI, lexer, parser, concrete syntax tree, snapshot test harness. Parses the
value subset (records, enums, functions, `let`, `match`, expressions). No semantics yet.

*Done when:* `norn parse examples/*.norn` round-trips and every snapshot is committed.

### M1 — Value core

Monomorphic type checker, HIR, lowering to NIR, NIR interpreter. Records, enums, `match`, `Result`,
`Option`, `?`.

*Done when:* `norn run hello.norn` executes ordinary computation end to end.

### M2 — Tasks and runtime

`norn-rt` with a single-threaded epoll loop, timers, and TCP. `task fn`, `await`, `scope`,
cancellation — lowered to explicit state machines **in NIR**, executed as heap continuations by the
interpreter. Work-stealing across threads is deferred; one thread is sufficient to be honest about
suspension and cancellation.

*Done when:* a TCP echo server written in Norn runs under the interpreter, and cancelling its scope
closes every socket.

### M3 — Reactors

The thesis milestone. Static dependency graph construction, instantaneous-cycle rejection with a
readable diagnostic, topological propagation plan, state-slot allocation. Runtime mailbox with the
declared overflow policy, serial turn execution, atomic snapshot publication, effect launch strictly
after stabilisation.

*Done when:* the configuration-watching reactor from `DESIGN.md` §5 runs; `norn graph App` prints
the dependency graph; turn traces are deterministic and golden-tested.

### M4 — Ownership

Move checking, affine resource tracking, `Shared<T>`. Resources close deterministically on scope
exit, on error propagation, and on cancellation.

*Done when:* use-after-move and double-close are compile errors, and a cancelled request is
observably leak-free.

### M5 — Native backend

NIR → restricted Rust → `rustc` → binary. `norn build svc.norn -o svc`.

*Done when:* every M1–M4 test produces a byte-identical turn trace under both engines.

### M6 — HTTP and flows

Minimal HTTP/1.1 in `norn-rt`, `Flow<Bytes>` with demand-driven transfer, `pipe_to`.

*Done when:* the worked example in `DESIGN.md` §10 compiles and runs as a native binary.

## 6 · Turn traces as the test harness

Build the trace format before building the reactors it describes.

Every reactor test is a golden file over a structured trace: input sequence number → stateful nodes
updated → signals recomputed, in order → published version → effect requests issued. Glitch freedom
and turn determinism are the claims the entire design rests on; if they are observable only by
reading runtime source, regressions will pass unnoticed.

The same artifact serves three purposes:

1. the differential oracle between interpreter and native backend (§1);
2. the regression suite for propagation order and effect timing;
3. the first implementation of `tool trace` from `DESIGN.md` §12 — so the tooling story and the test
   harness are one piece of work rather than two.

## 7 · Crate layout

```
norn/
├── DESIGN.md
├── BOOTSTRAP.md
├── Cargo.toml               workspace
├── crates/
│   ├── norn-syntax/         lexer, parser, CST, spans, diagnostics
│   ├── norn-hir/            resolution, types, reactive analysis     (M1)
│   ├── norn-nir/            lowered IR + interpreter                 (M1)
│   ├── norn-rt/             scheduler, I/O, mailboxes, turn loop     (M2)
│   ├── norn-codegen/        NIR → restricted Rust                    (M5)
│   └── norn/                CLI: parse · run · build · graph · trace
├── examples/
└── tests/                   snapshot and golden-trace corpora
```

## 8 · Deferred work

Ordered roughly by when it becomes worth doing, not by importance:

1. **M7 — dynamic subgraphs.** `switch`, child graph regions, reactor-local arenas, subscription
   lifetimes. Requires the trace tooling from M3.
2. **Multi-threaded scheduler.** Work stealing, parallel reactors on separate workers. The
   single-threaded loop is a correctness baseline to differential-test against.
3. **Cranelift backend.** Replaces the Rust emitter once NIR has stopped churning; removes `rustc`
   from the deployment path.
4. **Borrow checking.** Until then, `&T` as a non-escaping parameter only.
5. **Generics and traits.** Required before a real standard library.
6. **Capability inference, test handlers.** `uses { ... }` is checked but not inferred in v0.
7. **Derives and constrained attributes.** `@derive(Json)`, `@http_api` — `DESIGN.md` §8 stage 2.
8. **Durable state projections, supervision policy.**
