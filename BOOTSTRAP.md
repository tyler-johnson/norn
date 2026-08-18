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
- **Tasks** — `task fn`, `await`, `scope { spawn ... }`, cancellation, structured join on scope exit.
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
syntactically); dynamic subgraphs (`switch`); macros and derives; modules beyond a single file; a
multi-threaded work-stealing scheduler; capability *inference*.

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
is now the entry fee for §8's item 6 rather than a side effect of this milestone.

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
That sketch leans on closures, `for await` and loops, generics, method resolution, the event
operators, route patterns with bound parameters, and JSON — fifteen-odd constructs that are M7 or
later — so passing it would mean building the rest of the language first. §10 stays as the
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
   side of an event also wants `for await`, which needs a loop construct. Requires the trace tooling
   from M3.
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
   representation. M5's backend deliberately kept the interpreter's dynamically tagged, `Rc`-shared
   values, so copying still costs a reference-count bump; the backend that gives values layout is
   where the cost first becomes measurable, and where these two stop being inert. Zero-copy `Bytes`
   slices wait here too — M6's `bytes_slice` copies, because a clone-everything representation
   cannot make sharing observable — and so does `+` on `Bytes`, which is only worth having once
   concatenation has a cost model to answer to.
7. **Generics and traits.** Required before a real standard library.
8. **Capability inference, test handlers.** `uses { ... }` is checked but not inferred in v0.
9. **Derives and constrained attributes.** `@derive(Json)`, `@http_api` — `DESIGN.md` §8 stage 2.
10. **Durable state projections, supervision policy.**
11. **The rest of HTTP, and general flows.** M6's wire is deliberately narrow, and each narrowing
    is a deferral: chunked transfer encoding and keep-alive (v0 bodies are `Content-Length` and
    every response says `Connection: close`); an HTTP client (`http_get` — M6 is server-only);
    route patterns with bound parameters (`files.norn` dispatches on `match request_method(&req)`
    because there is nothing to bind a path segment to). General flow sources and sinks wait here
    too, along with a `flow_next` for consuming a flow from Norn code once a loop construct makes
    that shape reasonable — in v0 a flow comes from a file or a request body and is consumed only
    by `pipe_to` and `http_respond_flow`, wholly inside the runtime. `coalesce_latest` remains a
    §10 gap rather than M6 work: it is an overflow policy, not a wire feature.
