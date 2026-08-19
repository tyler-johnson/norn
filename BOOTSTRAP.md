# Bootstrapping Norn

*Implementation plan · companion to [DESIGN.md](./DESIGN.md)*

`DESIGN.md` describes a language. This document describes the shortest honest path from an empty
repository to a native compiler for a subset of it, and states explicitly what that subset leaves
out.

| | |
|---|---|
| **Status** | Goal reached — M0–M6 settled; what remains is §8 |
| **Goal** | `norn build service.norn -o service` produces a native binary running a real HTTP service — demonstrated by `examples/http/files.norn` |
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
norn-syntax        lexer, parser, spanned AST
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
     scheduler · poll(2) · timers · mailboxes
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
loops, `Rc`/`Arc`, and calls into `norn-rt`. It may **not** use `async` or lifetimes, and it may
contain no trait *definitions* and no generics. What it must do is implement `norn-rt`'s two engine
traits monomorphically: it already produces a `Box<dyn Body<V>>` for every task, and from M3 it also
implements `Graph<V>` for the reactor tables. Those two are the ABI between backend and runtime, and
a vtable of fixed shape is not what this rule exists to prevent. That subset maps one-to-one onto a
direct Cranelift backend later, so the eventual swap is mechanical.
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

- **Values** — `I64`, `F64`, `Bool`, `String`, `Bytes`, structs, enums with payloads, `match`,
  built-in `Result<T, E>` and `Option<T>` with `?`.
- **Tasks** — `task fn`, `await`, `spawn`, `scope`, cancellation, structured join on scope exit.
  A spawn is owned by the nearest enclosing `scope { … }`, or by the task body when there is none;
  `scope` narrows ownership to a region shorter than the function. (Originally `spawn` *required*
  an enclosing `scope`; the requirement was dropped once it was clear the runtime's implicit
  outermost scope — which always existed as a backstop — is the right default owner, and the
  mandatory wrapper was pure ceremony.)
- **Reactors** — static graphs only: `input` with declared capacity and overflow policy, `state`,
  `signal`, `on` handlers, `after` effect requests, `export`, `latest`, and `send`.
  `uses { … }` applies to a reactor as well as to a task: it is the authority the reactor's effects
  need, and the spawner's set must cover it.

  An input has two spellings, and a queue clause on an `on` is the discriminator between them.
  `on queued(id: I64) [capacity: 8, overflow: reject] { … }` declares the input and answers it in
  one member; `input queued: I64 [capacity: 8, overflow: reject]` plus `on queued(id) { … }` splits
  the same thing across two. The merged form exists because the pairing is a bijection the checker
  enforces in both directions, so writing it twice buys three failure modes and no expressiveness,
  and because the message type belongs where the message is bound. The split form survives because
  M7's operator vocabulary — `hold`, `scan`, `merge`, and the `event` nodes they run on — consumes
  an input that no `on` responds to, and a grammar with no way to write one would make M7 a
  breaking change rather than an addition. The cost, stated rather than discovered later: a
  reactor's boundary is no longer scannable under a single leading `input`.

  A signal is also *callable* from anywhere inside its own reactor: `is_full(count + 1, limit)`
  applies the lifted body to arguments written at the call site. Naming a signal reuses its value,
  calling one reuses its definition, and only the second is legal in an `on` handler — a call has no
  temporal semantics to get wrong, because it says which values it is a function of. Its parameters
  are the signal's dependencies in `deps` order, so the callee is ordered before the caller and a
  self-call is the ordinary cycle error. A `state` initialiser may not call one: it runs before the
  first turn. Purity on this path is carried by `check_turns`' walk over the call graph rather than
  by the `cx: None` the propagation path calls node bodies with.

  `combine` is struck, subsumed by lifting: a signal expression may mention any number of nodes and
  is lifted to a function of them, so combining is what an ordinary expression already does. `hold`,
  `scan`, `count`, `map`, `merge`, `delay`, and `keyed` are deferred alongside `event` nodes — they
  are stream shape and scheduling rather than causality, and M3 is the causality milestone.

  `latest` and `send` are ordinary functions over a *closed handle table*: `reactor.input` and
  `reactor.export` are the only members a handle has. The language has no method resolution, so
  `.latest()` and `.send()` cannot be spelled as methods until it does.
- **Memory** — move checking for affine values, and affine operating-system resources released on
  scope exit *and* on cancellation.

  The affine set is small and named: operating-system resources, a built-but-unstarted `Task<T>`,
  and any struct or enum that reaches one. Ordinary values stay copyable, because nothing in v0 can
  observe the difference — the interpreter clones, and the native backend that would make a copy
  cost something is M5. Move checking for ordinary values arrives with it, and until then
  `print(p); print(p)` is legal.

  `Shared<T>` is deferred for the same reason: with ordinary values copyable it is a representation
  choice with no observable effect, and an inert type in the language is worse than an absent one.
  `Bytes` arrived with M6, where `Flow<Bytes>` gives it work to do — with copying slices, because a
  clone-everything engine cannot make zero-copy observable. The borrowed representation waits with
  §8 item 6, alongside everything else that needs values to have layout.
- **Effects** — `uses { ... }` as a checked annotation.
- **I/O** — TCP, timers, files, HTTP/1.1, `Flow<Bytes>` with genuine demand signalling.

### Excluded, deliberately

Generics; traits; a borrow checker (`&T` is permitted only as a non-escaping parameter, enforced
syntactically); dynamic subgraphs (`switch`); macros and derives; a multi-threaded work-stealing
scheduler; capability *inference*. Modules were on this list — "beyond a single file" — until the
post-M6 module work landed them: a program is now a graph of files, subdirectories included, and
§8 item 12 records the surface that settled.

"Enforced syntactically" turned out to mean something sharper than a rule: `resolve_ty` produces a
reference type only in parameter position and `declare_local` refuses to name one, so there is no
field, return, payload, `let`, or reactor member that could hold a borrow. The one value in v0 that
outlives the expression building it is a `Task<T>`, so `spawn` and `after` reject a borrowed
argument and that is the whole of the escape analysis. `await f(&x)` is exempt because the awaiting
task is parked for the duration and ownership is unique: it cannot invalidate the borrow itself, and
nobody else holds the value. `&mut` is left with a diagnostic rather than a meaning, since one
exclusive-borrow rule is a borrow checker.

The cut worth defending is **static reactor graphs**. Dynamic switching is where graph arenas,
region reclamation, and subscription lifetimes all become load-bearing — it is the majority of
`DESIGN.md` §7. A static graph compiles instead to a fixed struct of state slots plus a
topologically ordered propagation function: a few hundred lines rather than a research project. It
still demonstrates glitch freedom, turn determinism, and effects-after-commit, which are the claims
the design rests on. `switch` arrives after the trace tooling exists to debug it.

## 5 · Milestones

### M0 — Skeleton

Cargo workspace, `norn` CLI, lexer, parser, spanned AST, snapshot test harness. Parses the value
subset (structs, enums, functions, `let`, `match`, expressions). No semantics yet.

The AST does not retain comments or layout, so round-tripping means idempotence of the canonical
printer rather than byte equality with the source: `print(parse(print(parse(s))))` must equal
`print(parse(s))`, and the two parses must yield the same tree. That property fails loudly whenever
the printer and the parser disagree about how a construct nests, which is the class of bug a
hand-written recursive-descent parser produces most often.

Two layout rules keep the grammar free of semicolons: statements within a block are separated by
line breaks, and a postfix chain continues across a line break only for `.` — a `(`, `[`, or `?`
opening a fresh line starts something new.

Two further rules keep spelling out of the grammar entirely. **Construction is spelled like a
call**, covering structs and enum variants alike in both expressions and patterns; name resolution
in the checker, not the grammar, is what tells building from calling:

```
let user  = User(id: 7, name: name)      // builds a value
let error = LoadError.Invalid("bad")     // so does this
let body  = http.text(status: 200)       // this calls a function

match error {
    LoadError.NotFound       => "not found"
    LoadError.Io(code, msg)  => msg
    other                    => describe(other)
}
```

Two consequences follow, and both remove a rule rather than adding one. A brace is *always* a
block — there is no struct-literal syntax to disambiguate it from, so no construct needs to disable
literals in its condition or scrutinee position. And in a pattern, shape is the whole distinction:
a bare name *always* binds, while a dotted or parenthesised one matches, so `NotFound` is a binding
and `LoadError.NotFound` is a match.

Because call position must be unambiguous, a `fn` may not share its name with a struct, enum, or
reactor. The four built-in constructor names are the one carve-out on the pattern rule: `None`,
`Some`, `Ok`, and `Err` stay bare — resolved by the expected type in expressions and by the
scrutinee in patterns — and in exchange they are unbindable: no local, parameter, pattern binding,
`fn`, or reactor member may claim them, which is what keeps `None =>` from quietly becoming a
catch-all binding.

**Nothing in the grammar depends on whether a name is capitalised.** That is a deliberate
constraint: capitalisation is a convention a formatter or linter may enforce, never something the
parser consults. The mistake this invites — writing `User { id: 7 }` — produces a diagnostic
naming the correct form.

*Done when:* `norn parse examples/*.norn` succeeds, every example is print-idempotent, and the
snapshot corpus — ASTs, canonical renderings, and rendered diagnostics for the deliberately broken
examples — is committed.

### M1 — Value core

Monomorphic type checker, HIR, lowering to NIR, NIR interpreter. Records, enums, `match`, `Result`,
`Option`, `?`.

The checker is **bidirectional**: an expression is checked against the type its position demands
when there is one, and synthesises a type when there is not. That is what lets `None` and `Err(e)`
work with no inference variables anywhere — the expectation supplies the argument the expression
cannot know on its own — and where no expectation exists the checker says so rather than guessing.
`Option` and `Result` are seeded as ordinary enums in the first two slots of the enum table, so
construction, matching, and lowering treat them exactly like a user enum; only their type arguments
are special.

**NIR is flat from the start.** Each function is a list of basic blocks, each a straight run of
assignments ending in one terminator. `match` lowers to a chain of tag switches and equality tests,
`&&` and `||` to branches, `?` to a switch with an early return. Nothing nests. That is the whole
reason to have a separate IR at this milestone: M2 splits a block at each suspension point to build
a state machine, and M5 walks these blocks to emit code, and neither step should have to understand
`match`.

The interpreter manages calls with an **explicit frame stack** rather than the host call stack.
Nothing in M1 needs that — pure functions would recurse on Rust's stack quite happily — but
suspension in M2 does, and retrofitting it later would mean rewriting every path that can call.

Two known gaps, both deliberate. Exhaustiveness checking covers top-level variants only, so a gap
hidden inside a nested pattern traps at runtime rather than failing to compile; a full usefulness
algorithm can arrive with the rest of the pattern work. And `&T` was transparent — it resolved to
`T` — until M4 gave ownership meaning.

*Done when:* `norn run examples/run/hello.norn` executes ordinary computation end to end, every
program in `examples/run/` has a snapshot pairing its lowered IR with its output, and every program
in `examples/type-errors/` has a snapshot of what the checker says about it.

### M2 — Tasks and runtime

`norn-rt` with a single-threaded `poll(2)` loop, timers, and TCP. `task fn`, `await`, `scope`,
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

The done-when is stated against a worked example built from TCP and timers rather than against
`DESIGN.md` §5's configuration watcher. That six-line sketch needs `fs.read_json<Config>` (generics),
file I/O, an inotify `fs.watch`, `map_task`, and `Event.once` — five things v0 excludes — so passing
it would mean building most of M6 first. The claims it was chosen to demonstrate are unchanged; only
the program making them is smaller.

*Done when:* `examples/reactors/gate.norn` runs — a reactor counting what the M2 echo server holds
open — and its golden trace shows one recompute pass and one publish per turn, an effect starting
only after the publish of the turn that requested it, and a snapshot whose diamond-descended fields
never disagree; `norn graph <file> [Name]` prints nodes, slots, the topological order, the per-input
propagation plans, and the exports; every overflow policy is observable in a trace;
`examples/reactor-errors/` snapshots one diagnostic per rule, `cycle.norn` among them; and every
example reproduces its trace exactly under `--virtual-clock`.

### M4 — Ownership

Move checking over the affine set — operating-system resources, a built-but-unstarted `Task<T>`, and
any aggregate reaching one — with `&T` as a real type in parameter position. Resources close
deterministically on scope exit, on error propagation, and on cancellation.

Two of those three already held when the milestone opened; the first did not. Resources were owned
by the task rather than by the scope, so a descriptor opened inside a `scope { … }` stayed open until
the whole surrounding task ended. `Scope` owns them now, and because lowering already unwinds every
open scope on every path out of a function, closing on the way out of a scope is also what delivers
closing on error propagation.

Nothing a reactor holds may be affine — a slot is the durable state projection §14 asks for and a
descriptor cannot be written down and restored, and an input declared `overflow: drop_oldest` would
leak a socket every time its mailbox filled. `Shared<T>` and ordinary-value moves are deferred to
M5; see §4.

*Done when:* use-after-move and double-close are compile errors, and a cancelled request is
observably leak-free.

### M5 — Native backend

NIR → restricted Rust → `rustc` → binary. `norn build svc.norn -o svc`.

Generated code keeps the interpreter's value representation: one dynamically tagged `Value` enum,
aggregates behind `Rc` with copy-on-write. NIR carries no types — nothing after HIR ever did — so a
typed layout would have meant threading `hir::Ty` through lowering first, and the done-when asks
for byte-identical traces, which the shared representation delivers by construction. Typed layout
is now the entry fee for §8's item 6 rather than a side effect of this milestone. (The fee was
paid 2026-08-19, as item 6a: NIR is typed end to end and the backend generates typed values, this
milestone's dynamic representation surviving only as the boundary enum at the runtime seams — and
the traces stayed byte-identical by comparison, the differential oracle refereeing, rather than by
construction.)

The backend is a printer with a prelude. `norn-codegen` emits a prelude ported from the
interpreter item for item — trap text included, because trap messages interpolate `{:?}` of the
value and operator enums and stderr is part of the oracle — then the program: blocks as match
arms, block `b` of a `task fn` as state `2b`, and state `2b + 1` re-executing only the terminator,
so a woken task re-asks its suspension point without re-running the instructions before it.
Awaiting a `task fn` pushes an explicit frame, exactly the interpreter's shape; a plain function
compiles to a direct Rust call, which is sound because `Rvalue::Call` can never target anything
that parks.

`rustc` is the only tool `norn build` needs. The compiler embeds `norn-rt`'s sources at its own
build time, compiles them to an rlib once per (toolchain, flags, sources) hash under
`~/.cache/norn`, and links each program with a single `rustc --extern norn_rt=…`. No cargo, no
checkout, and a toolchain switch re-keys the cache rather than mislinking.

The oracle compares engine against engine, never snapshots. The differential tests run every
deterministic example both ways and require stdout, stderr — the trace — and the exit code to
match byte for byte, with a trap corpus for the message coupling; `NORN_BLESS` cannot bless the
engines into agreement. The two live-socket programs get native mirrors of the echo and server
tests, asserting the same structural claims against a real clock.

*Done when:* every M1–M4 test produces a byte-identical turn trace under both engines.

### M6 — HTTP and flows

Minimal HTTP/1.1 in `norn-rt`, `Flow<Bytes>` with demand-driven transfer, `pipe_to`.

The done-when is stated against v0-spelled examples rather than against `DESIGN.md` §10's service.
That sketch leans on closures, `for await`, generics, method resolution, the event
operators, route patterns with bound parameters, and JSON — fifteen-odd constructs that are M7 or
later (the loops it also wanted have since landed) — so passing it would mean building the rest of
the language first. §10 stays as the
aspirational sketch; the programs making M6's claims are `examples/http/hello.norn` and
`examples/http/files.norn`, the second being §5's streaming upload and download respelled with
free functions and `match` dispatch on the method.

The wire, settled: request line plus headers, strict CRLF, an 8 KiB head cap; bodies delimited by
`Content-Length` only, `Transfer-Encoding` rejected outright; every response carries
`Content-Length` and `Connection: close`. Chunked bodies, keep-alive, and an HTTP client are
deferred (§8). One consequence is worth naming: every v0 flow knows its length up front — a file's
size, a body's `Content-Length` — so a close-delimited transfer has no representation and nothing
pretends to implement one. Malformed input is an `Err(IoError…)` value, never a trap: the peer is
not something the program can be blamed for.

In the model, a flow is a resource-table entry, so affinity, scope ownership, close-on-cancel,
and the `open`/`close` trace lines all come from machinery M4 built, and the
nothing-a-reactor-holds-is-affine rule covers flows with no new rule. `pipe_to` is a runtime-owned
state machine with at most one ≤4 KiB chunk in flight — the demand claim, observable as one `pipe`
trace line per delivered chunk — rather than Norn-level recursion over some `flow_next`, which
would grow a frame per chunk on a large transfer; v0 has no `flow_next` at all, and a flow is
consumed only by `pipe_to` and `http_respond_flow`. `http_read_request` consumes the Connection
and converts its table entry into a Request in place, same id and same descriptor, which is what
keeps the trace's open/close pairing 1:1.

*Done when:* `examples/http/hello.norn` and `examples/http/files.norn` run identically under
`norn run` and as `norn build` binaries: a PUT streams a multi-chunk body to disk through
`pipe_to` and lands byte for byte; a GET streams the file back with the declared length; a missing
file is a 404; and an upload abandoned mid-body — promised long, delivered short, held open
through shutdown — is cancelled with its request, its body flow, and its half-written file all
closed, the trace pairing every `open` with a `close`.

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
│   ├── norn-syntax/         lexer, parser, spanned AST, diagnostics
│   ├── norn-hir/            resolution, types, reactive analysis     (M1)
│   ├── norn-nir/            lowered IR + interpreter                 (M1)
│   ├── norn-rt/             scheduler, I/O, mailboxes, turn loop     (M2)
│   ├── norn-codegen/        NIR → restricted Rust                    (M5)
│   └── norn/                CLI: parse · run · build · graph · trace
├── examples/                parse corpus
│   ├── errors/              programs that must not parse
│   ├── run/                 programs that must check, lower, and run
│   ├── tasks/               programs whose NIR, output, and trace are golden  (M2)
│   ├── tcp/                 the echo server                                   (M2)
│   ├── http/                the hello server and the file server              (M6)
│   ├── modules/             the multi-file program: entry, library, subdirectory
│   ├── reactors/            programs whose graph and turn trace are golden    (M3)
│   ├── reactor-errors/      reactors that must not check                      (M3)
│   ├── ownership-errors/    programs that must not check, about ownership     (M4)
│   └── type-errors/         programs that must not check
├── editors/
│   └── vscode/              grammar, snippets, and a `norn check` matcher
└── crates/*/tests/          snapshot and golden-trace corpora
```

## 8 · Deferred work

Ordered roughly by when it becomes worth doing, not by importance:

1. **M7 — dynamic subgraphs and the operator vocabulary.** `switch`, child graph regions,
   reactor-local arenas, subscription lifetimes. Closures arrive here too — nothing in M3's surface
   needed one, and dynamic switching is what real closures are for — and with them `event` nodes,
   `export event`, and the operators M3 deferred: `hold`, `scan`, `count`, `map`, `merge`, `delay`,
   `keyed`, and `map_task` policies. **Effect policies belong here too** — a per-request pending
   queue on `after`, and cancellation of obsolete work when a newer request supersedes an in-flight
   one. M3 launches every request and lets the scope cancel what is outstanding, which is correct
   but has no way to say "only the latest matters"; saying so needs a policy vocabulary on `after`,
   and that is the same scheduling question as `map_task`'s rather than a causality one. The read
   side of an event also wants `for await` — the loop construct it sits on now exists, and the
   subscription semantics are what remain M7's. Requires the trace tooling from M3.
2. **Multi-threaded scheduler.** Work stealing, parallel reactors on separate workers. The
   single-threaded loop is a correctness baseline to differential-test against.
3. **Language server.** `norn-lsp` over stdio: diagnostics first, which is `norn_hir::check`'s
   spanned output and nothing new, then semantic tokens, hover, and go-to-definition off the typed
   HIR. `editors/vscode/` is the stopgap — a TextMate grammar has to find types by position, and
   semantic tokens are what replace that guess with the checker's answer.
4. **Cranelift backend.** Replaces the Rust emitter once NIR has stopped churning; removes `rustc`
   from the deployment path.
5. **Borrow checking.** Until then, `&T` as a non-escaping parameter only, and no `&mut` at all.
   Partial moves wait here too: M4 rejects moving out of a field rather than tracking it, because a
   half-moved struct has no name in this language and `match` already takes one apart.
6. **Move checking for ordinary values, and `Shared<T>`.** Both wait on a typed value
   representation — and the representation landed first, as its own wave: **6a, typed NIR and a
   typed backend (2026-08-19), zero surface change.** The item decomposes as 6a (landed), 6b
   (`Shared<T>`, `Bytes` views, `+` on `Bytes`), and 6c (ordinary-value moves, taking item 5's
   read half with them).

   What 6a did. NIR carries `hir::Ty` end to end — `Function.tys` in lockstep with `locals`, plus
   `ret` and an `inert` flag for the generics drain's neutered defs; typed layouts; typed reactor
   params, nodes, and inputs — and `Place` projections gained `Proj::Downcast { variant, field }`,
   because field 0 of an enum has a different type per variant and every site that projects into a
   payload sits under control flow that already proved the tag (MIR's `PlaceElem::Downcast`, for
   the same reason; writes never traverse enums, so downcasts are read-path only). The NIR printer
   shows all of it — `local _5: Option<I64>`, `_4.0@Some` — and that text is the review artifact
   the backend was written against.

   The representation rule: generated aggregates are flat Rust types, one `S{id}`/`E{id}` per
   concrete table entry, with Option/Result instantiations interned as synthetic enum-table
   entries by a deterministic no-hash walk; any field whose type is a named aggregate or an
   Option/Result is stored behind `Rc`, scalars and handles inline, `Rc<str>`/`Rc<[u8]>` for
   text and bytes. Copying is a memcpy plus refcount bumps, never a deep copy; recursive types are
   legal automatically; full flattening waits for 6c's moves, which are what make it sound.
   Bodies are fully typed — the operator dispatch, the coercions, and every value-shape trap died
   as types — and the dynamic `Value` survives only as a generated boundary enum at the nine
   runtime seams, wrapped and unwrapped by static type, never inside the call graph. One `TaskVal`
   enum types built tasks, `poll_task` is the single home of io mapping, and frames are
   per-task-fn structs of typed locals. The interpreter is untouched and stays the reference
   implementation; `norn-rt` never changed. The differential oracle therefore flipped from
   by-construction to by-comparison: stdout, stderr, and exit code byte-identical while the
   representation diverges — the render contract down to `NaN.0`, the NaN-ordering trap's
   `Float({v:?})` spelling, and the shallow `moved_resources` scan all pinned by it.

   The item's stated purpose was that the cost first becomes measurable, and it is: a copy-heavy
   scratch program (a 1000-cons list folded 3000 times, plus two million projected struct-field
   writes) runs in ~0.96s under M5's dynamic backend and ~0.073s under the typed one — 13× —
   with identical output.

   Still waiting here, now 6b's: zero-copy `Bytes` views — M6's `bytes_slice` copies, and so does
   the proto-std gate's `bytes_concat`, because a clone-everything representation cannot make
   sharing observable — and `+` on `Bytes`, which is only worth having once concatenation has a
   cost model to answer to. The model now exists. 6c is the move checking itself.
7. **Generics and traits — landed.** The gate on the general standard library, shipped as one
   wave (2026-08-19) because each half is the other's first consumer: bounds need traits to
   name, and a trait's worth shows first on a type parameter. Item 12 records what "collections"
   was decided to mean; std/list is the first of them.

   The surface: type parameters on `struct`, `enum`, and `fn` declarations (`List<T>`,
   `swap<A, B>`); call-site inference — the expectation solves return-position parameters first,
   then the arguments left to right — with the explicit `f<I64>(…)` spelling as the fallback and
   an "annotate or say it explicitly" refusal where nothing pins a parameter down; `trait` and
   `impl` declarations, with `trait`, `impl`, and `for` promoted out of the reserved list.
   Trait members are signatures only, first parameter `Self` by value, and the method spelling
   `value.to_string()` is exactly the rewrite it looks like: receiver prepended, plain call —
   a local head shadows enum and namespace heads in call position the way it always did in value
   position. Impls are held to three rules: orphan (the trait's module or the receiver's;
   builtin receivers only the trait's, which is how std/fmt owns `impl Display for I64`),
   coherence (one impl per trait and receiver, program-wide), and conformance (the trait's
   method set exactly, signatures equal under `Self := receiver`). Bounds live on functions
   alone — `fn contains<T: Eq>`, `+`-separated — and propagate by declaration, never search.
   `Eq` is the compiler's method-less marker, satisfied by exactly the five scalar types until
   item 9's derives, and it is what `==` on a bounded `T` costs: nothing, both engines already
   comparing structurally. `Display` (`to_string(Self) -> String`, infallible rendering only)
   lives in std/fmt beside the free function its I64 impl delegates to.

   The architecture, allowed by one enabling fact: types are fully erased at lowering, so the
   whole implementation is check-time monomorphization inside `norn-hir` — NIR, both engines,
   the backend, and the prelude changed zero lines. A template body is checked once, its
   parameters opaque (Rust's model; a bound adds capabilities, it never re-checks), and a
   monomorphization pass between bodies and the whole-program passes clones each requested
   instance with types substituted and callees remapped — generic-calls-generic composes through
   symbolic instances, a method on a bounded `T` through symbolic trait-call stubs resolved per
   instance via the impls. Instances are ordinary monomorphic defs with names like
   `list.take<I64>`, appended in deterministic insertion order (no map iteration anywhere in
   discovery — instance ids are a pure function of the AST), deduped on (template, arguments),
   and fused against polymorphic recursion at depth 32 with a 4096-instance ceiling behind it.
   Templates and stubs are neutered to inert unit bodies afterwards. Traits are entirely
   checker-side: `hir::Program` grew no tables.

   The dogfood retired all three hand expansions: std/list wrote the cons list once
   (structure-only — `length`, `empty`, `append`, `reverse`, `take`, `drop`, `nth`,
   `contains<T: Eq>`, `join<T: Display>`, the last a std module bounding on a std trait;
   map/filter/fold wait for M7's closures), std/http's `Headers` became `List<Header>` with
   byte-identical wire behaviour, and posts.norn moved into the reactors corpus as
   `List<Post>`/`List<Delta>` — its untested-example gap closing as a side effect, its trace now
   pinned by the reactors snapshot corpus and the differential oracle. The migrations settled a
   placement rule: functions that compare an element's fields (`named`, `insert`) stay beside
   the fields they read, not in std/list.

   The deferral ledger, each a recorded narrowing: associated types; default method bodies;
   trait objects (never planned — dispatch is static, a bound is not a type); generic traits;
   generic impls (`impl<T> Display for List<T>` parses and is refused); user `Eq` impls and
   derived equality (item 9); `Ord` and operator traits (comparisons stay builtin-typed);
   inherent impls — methods come from traits only, so `req.header(h)` stays `header(req, h)`;
   extension methods on builtin types (`2.seconds` still waits); `self` receiver sugar; `where`
   clauses (still reserved); borrow receivers (`&Self` is refused — receivers move); and `task`
   members with `uses` clauses (parse-permissive, check-refused). One plan amendment made in
   flight: "unified under one trait" became *unified where the signatures agree* — `Display` is
   infallible rendering only, and std/bytes's fallible `to_string(Bytes) -> Option<String>`
   stays a free function, fallibility living in the type as the naming format demands.
8. **Capability inference, test handlers.** `uses { ... }` is checked but not inferred in v0.
9. **Derives and constrained attributes.** `@derive(Json)`, `@http_api` — `DESIGN.md` §8 stage 2.
10. **Durable state projections, supervision policy.**
11. **The rest of HTTP, and general flows.** M6's wire is deliberately narrow, and each narrowing
    is a deferral: chunked transfer encoding and keep-alive (v0 bodies are `Content-Length` and
    every response says `Connection: close`); an HTTP client (std/http's `get` — M6 is
    server-only); route patterns with bound parameters (`files.norn` dispatches on
    `match req.method` because there is nothing to bind a path segment to). General flow sources
    and sinks wait here too — `flow_next` itself has since landed with the std/http wave (item
    12), but in v0 a flow still only ever comes from a file, and `Flow<T>` beyond `Bytes` waited
    on item 7's generics, now landed: this entry's own work is what gates it today.
    `coalesce_latest` remains a
    §10 gap rather than M6 work: it is an overflow policy, not a wire feature.
12. **Modules — landed — and the standard library that dissolves the builtins.** Earlier than its
    position suggests: modules gate the standard library, and item 7 does not — the ordering
    below explains why. The module half is done, and this entry records the surface that settled.
    A file *is* a module and carries no name of its own — the `module <name>` header is gone from
    the language, the filename is the identity, and the importing file names it by path. Imports
    are full ECMAScript syntax and semantics with the Node specifier convention:
    `import { digits, pad as p } from "./fmt"` and `import * as fmt from "./fmt"`, specifiers
    quoted and resolved relative to the importing file, `.norn` implied, subdirectories in,
    cycles legal (no module initialisers means no order to violate). `export` before `fn`,
    `task fn`, `struct`, `enum`, or `reactor` marks what a file offers; everything else is
    file-private. Bare `std/…` specifiers resolve to standard-library modules written in Norn
    and embedded in the compiler — `norn-hir`'s `stdlib` table, the `rt_sources.rs` precedent,
    keys extensionless and provenance carried by `resolve_specifier` so a relative `./std/fs`
    stays a user file — while other bare specifiers are refused: the package lane exists with
    zero syntax change left to make. `use` and
    `module` are no longer keywords (the `uses { … }` capability clause is untouched);
    `import` is one, `as` was promoted out of the reserved list, and `from` is contextual,
    still bindable everywhere else.

    The decision this entry records, made after M6: the standard library follows Rust's model,
    not Go's. Users should think in terms of libraries, so the builtin table is scaffolding with
    unstable spellings — 23 nameable and now shrinking: `bytes_text` fell first, `text_unchecked`
    (the table's first `_unchecked` trust boundary) arriving in its place, and the std/http wave
    then took nine more while adding the five flow/file intrinsics beneath them — plus
    the syntax-carried `bytes_at` behind `data[i]`, each implemented twice (an interpreter arm
    and its prelude mirror, trap text as ABI) and each nameable one a name no user function may
    take. Go keeps its
    builtins forever and affords short names by keeping the set near fifteen and shadowable;
    Norn's set is bigger, growing, and reserved, so staying on that road means either squatting
    on `read`/`open`/`close` or weakening the closed vocabulary that `uses` checking leans on.
    Rust's road ends better: std code written in Norn is one implementation executed by both
    engines, so the differential oracle covers it for free and the mirror stops growing with the
    language. Until the absorption begins, the bar for a new builtin is "cannot wait for std".

    The absorption comes in two waves with different gates. The proto-std needs no generics —
    Go's `net/http` predates Go's generics by a decade, and `Option`/`Result` are already
    spellable at concrete types. Its gates are modules — met, above — a loop construct — met: `while` and `loop`, `break` and
    `continue`, expressions all, with turns barred from reaching them so the termination theorem
    narrowed instead of dying — and a few byte primitives — met: `data[i]` indexing (out of range
    traps, like `bytes_slice`) and `byte` with `bytes_concat` for building. Every proto-std gate
    is met and the lane is live: `std/fmt` (`to_string`, `to_int`) is the first embedded module,
    one implementation executed by both engines with the differential oracle covering it for
    free, and the six hand-written `digits` copies the examples grew are gone. `std/time` joined
    it: `wait(ms)` is `sleep` wrapped in a task fn — the named clock effect `after` requires,
    since `after` takes only named task fns to keep a reactor's effect vocabulary explicit — and
    `seconds`/`minutes` are plain multiplications until the `2.seconds` method spelling exists
    (`delay` stays reserved for the FRP signal operator, which is why the name is `wait`).
    Recorded absences: `timeout` waits for a race/select primitive that does not exist — scopes
    join everything — until a real consumer, likely the std/http client, drives it; `now()` is
    deliberately absent, absolute-time reads breaking virtual-clock determinism.
    Std names follow a format — a guideline, not a strict rule. Conversions are `to_<target>`
    (`to_string`, `to_int`; `digits` and `parse_int` renamed to fit), guessable on the first try
    and reading unchanged as the future method (`n.to_string()`). The source type lives in the
    module today and the receiver tomorrow, never in the function name — `i64_to_string` would
    re-import the builtin-table disease std exists to cure, and the same name in different std
    modules is the intended pattern, unified under one trait — `Display`, now that item 7 has
    landed, exactly where the signatures agree — rather than by
    ad-hoc overloading, which is deliberately not built. Quantity constructors stay bare nouns
    (`seconds(2)` reads as "2 seconds", later the literal-like `2.seconds`); effects stay bare
    imperative verbs (`wait`, `send`), which is what makes a reactor's `after` list read as a
    list of verbs; fallibility lives in the type, never the name (`to_int(s) -> Option<I64>`, no
    `try_`), with `_unchecked` reserved for the intrinsic layer underneath.
    The first dissolution is done: `bytes_text` was deleted from the table and reimplemented as
    `std/bytes`'s `to_string(Bytes) -> Option<String>` — a UTF-8 validator written in Norn over
    the trusting `text_unchecked` intrinsic, which traps on invalid input like `data[i]` out of
    range. That established the delete-and-import migration every later dissolution follows:
    delete the name, flip the users to imports, one commit, atomic by construction since
    builtins are reserved names. (One temporary wrinkle: `import * as bytes` is refused while
    `bytes` itself remains a builtin name, so `std/bytes` is imported by named items; the
    namespace frees itself the day the `bytes` builtin dissolves.)
    The std/http wave followed, and what was recorded as two steps — "std/http, then
    `flow_next`" — landed as one, because the ordering was circular: dissolving `Request` kills
    both flow endpoints at once, the `request_body` source and the request-as-sink. The wire
    went `Bytes` first (`tcp_read` yields them, `tcp_write` takes them; breaking freely — nobody
    is using the language, and syscalls speak bytes), and five intrinsics grew beneath the
    absorption: `flow_next` (an empty chunk means exhausted), `flow_len`, `flow_close`,
    `file_write`, `file_close`, every one carrying an empty capability set because the open
    handle is the authority — `file_create` and `flow_of_file` checked theirs at the open, and
    those two never dissolve: they are the `uses` seam. On that seam `pipe_to` became
    `std/flow`'s `pipe` — the `_to` suffix was doing the sink argument's job — taking the golden
    per-chunk `pipe` trace lines with it, since the transfer is user code now and the runtime
    has nothing per-chunk to say. Then `std/http` dissolved the eight `http_*` builtins and the
    `Request` *resource* the honest way: `read_request` borrows the Connection, gathers bytes,
    and re-asks the pure `head` parser, so a request is an ordinary Norn struct, a malformed
    head is `Err(IoError.Other(rule))` naming the violated rule, and the connection stays the
    traced, scope-closed seam, with the respond family consuming it so answering and closing
    remain one act. That commit had to be atomic beyond the usual recipe: the checker seeded the
    type name `Request` into every namespace, so the module could not declare its struct until
    the resource died in the same change. std/http imports `to_int` from `std/fmt` — the first
    std→std import — and its exported `head` is what makes the wire rules testable as ordinary
    Norn: `examples/run/http-head.norn` pins every parse rule and every deliberate delta (ASCII
    heads, last-wins duplicate headers, any status rendering with the empty reason phrase HTTP
    permits) under the snapshot corpus and the differential oracle, where the Rust parser's unit
    tests used to live. The demand claim outlived the machinery it was built on: it is now the
    one-chunk-per-iteration shape of the std loops, still observable in the abandoned-upload
    cancellation and the multi-chunk roundtrip the live file-server tests make.
    (`examples/tasks.norn`'s `import * as http` now names a real module but stays parse-only —
    the client surface it sketches does not exist; its `std/fs`/`std/json` imports still
    diagnose as unknown std modules and stand until those exist. Its `std/time` line
    half-landed: `seconds` is real, `mebibytes` is not time's to provide.)
    The general std's gate has lifted: item 7's generics and traits landed, and std/list opened
    the collections lane (the record lives on item 7). Two of the three things this sentence
    used to wait for remain waiting on other grounds — `Flow<T>` beyond `Bytes` on item 11's own
    flow work, and `req.header(h)` on inherent impls, which item 7 deliberately did not ship:
    methods come from traits, and `header` belongs to no trait.
    "Collections" means both sequence shapes rather than a choice between them (2026-08-19): the
    persistent cons list that every v0 collection was by hand — `Headers`, `Rows`, `Deltas`
    were three copies of one list, monomorphized by retyping, and all three now ride std/list's
    `List<T>` — and a contiguous growable sequence.
    The two do not overlap, they trade: O(1) prepend with full tail sharing against O(1) index and
    dense iteration, and a language whose turns are pure and whose old values must stay valid wants
    the sharing as much as a byte-pusher wants the buffer. Maps and sets follow them; `DESIGN.md`
    §11 wants the incremental kind, which is a propagation property and not a second type. `List<T>`
    is the cons list's name — `DESIGN.md`'s core semantics already writes `List<EffectRequest>`,
    so the name was load-bearing before the library existed, and std/list now spells it — which
    leaves the contiguous one's spelling the open question. That half additionally waits on item 6: a clone-everything representation
    cannot price a buffer honestly, the same reason zero-copy `Bytes` slices wait there. Whatever
    lands must make finiteness structural, because `for` earns its way into a turn only by being
    bounded by the data (`DESIGN.md` §14).
    What never dissolves is a small intrinsic layer at the syscall boundary, which is also where
    `uses { … }` keeps doing its checking: the authority seam stays a closed, named table after
    every name above it has become a library.
