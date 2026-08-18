# Toward a Native, Server-Oriented Functional Reactive Language

*Exploratory whitepaper · unnamed concept*

A consideration of what a general-purpose systems language might look like if functional reactive programming, structured concurrency, server I/O, and ownership were designed as one coherent model rather than assembled as libraries.

| | |
|---|---|
| **Status** | Idea, not specification |
| **Audience** | Language and systems designers |
| **Revision** | August 2026 |

---

## Contents

- [Abstract](#abstract)
- [1. Motivation](#1--motivation)
- [2. Design thesis](#2--design-thesis)
- [3. Programming model](#3--programming-model)
- [4. Concurrency and parallelism](#4--concurrency-and-parallelism)
- [5. Server I/O](#5--server-io)
- [6. Effects, capabilities, and failure](#6--effects-capabilities-and-failure)
- [7. Memory management](#7--memory-management)
- [8. Metaprogramming](#8--metaprogramming)
- [9. Compiler and runtime](#9--compiler-and-runtime)
- [10. Worked example](#10--worked-example)
- [11. Game-server case study](#11--game-server-case-study)
- [12. Application fit and adoption rationale](#12--application-fit-and-adoption-rationale)
- [13. Novelty and related work](#13--novelty-and-related-work)
- [14. Open design questions](#14--open-design-questions)
- [15. Implementation and evaluation path](#15--implementation-and-evaluation-path)
- [Conclusion](#conclusion)
- [Selected references](#selected-references)

> **Document posture** — This is deliberately exploratory. Syntax is illustrative; semantic boundaries are the proposal.

---

## Abstract

Functional reactive programming is often experienced through libraries layered over languages whose fundamental execution model remains imperative and callback-oriented. This paper asks what changes when reactivity is instead a property of the language, compiler, scheduler, effect system, and memory model.

The proposed language is intended for ordinary server software: HTTP services, outbound requests, file and socket I/O, streaming, background work, timers, configuration, and long-lived state. It separates finite asynchronous procedures from persistent reactive relationships. `Task<T>` represents one eventual result; `Flow<T>` represents a backpressured sequence; `Event<T>` represents discrete occurrences; `Signal<T>` represents a current value that changes over time; and a `Reactor` owns a transactional reactive graph.

Concurrency is organized around cheap structured tasks and isolated reactors. A reactor handles one input at a time, stabilizes its graph atomically, publishes coherent snapshots, and starts effects only after stabilization. Values cross reactor boundaries by ownership transfer, immutable sharing, or bounded flows. Ordinary values use ownership and borrowing; operating-system resources are affine; dynamic reactive graphs live in reactor-local arenas that can be reclaimed at quiescent points.

The result is not "Rust plus signals" or "Go plus observables." Its potential contribution is a tighter principle: **ownership defines the boundary of reactive consistency, parallel execution, effects, and reclamation.** The components have clear precedents, but their combination may constitute a novel server-oriented language design if supported by a precise semantics and empirical evaluation.

> **One-sentence proposal**
>
> A reactor owns mutable temporal state and processes each input as an atomic, glitch-free turn; tasks perform finite effects around that turn, and the type system governs every value, resource, effect, and queue that crosses the boundary.

---

## 1 · Motivation

### FRP deserves language semantics, not only library conventions

Early FRP work treated behaviors and events as compositional values with explicit temporal meaning, rather than merely as callback containers.[^1] Contemporary ReactiveX systems are highly useful for composing asynchronous and event-based sequences, but their core abstraction remains an observable sequence inside a host language.[^2] That host language still determines mutation, lifetime, I/O, concurrency, and error behavior.

This mismatch becomes especially visible on servers. An observable pipeline can describe that values flow from one operation to another, but it does not inherently determine whether several dependent updates are one transaction, which effects may observe an intermediate state, how a file handle is transferred into a response, whether a cancelled request releases its resources, or how much data may wait in a queue.

A language designed around FRP could make those questions explicit and checkable. The goal is not to make every computation reactive. The goal is to give persistent relationships a first-class semantics while preserving straightforward procedural code for finite work.

### The server problem is broader than event propagation

A normal service needs to perform at least five different kinds of computation:

| Type | Role | Description |
|---|---|---|
| `Value<T>` | Ordinary computation | Parsing JSON, transforming records, validating input, and calculating results. |
| `Task<T>` | Finite asynchronous work | One HTTP request, one file read, one database operation, or one timeout. |
| `Flow<T>` | Streaming transfer | Request bodies, files, database rows, logs, or any sequence requiring backpressure. |
| `Event<T>` | Discrete occurrence | A file changed, a timer fired, a job finished, or an input arrived at a reactor. |
| `Signal<T>` | Temporal value | The current configuration, health state, routing table, aggregate, or derived view. |
| `Reactor` | Consistency boundary | An owner of mutable temporal state and the graph that derives coherent values from it. |

Many reactive systems attempt to force several of these into a single abstraction. That usually creates hidden buffering, awkward one-shot operations, unclear cancellation, or accidental state machines. The proposed design instead gives each concept a narrow role and makes conversions between them visible.

### Design goals

- **Coherent reactive state.** A reaction observes and publishes complete graph states, never partially propagated combinations.
- **Ordinary server ergonomics.** Opening an HTTP listener, making a request, and reading or writing a file should be direct, typed, cancellable operations.
- **Safe parallelism by construction.** Isolated reactors and owned messages should remove most shared-memory synchronization from application code.
- **Predictable resource cleanup.** Files, sockets, transactions, streams, subscriptions, and child tasks should have deterministic owners.
- **Visible pressure and loss.** Every asynchronous boundary should state whether it waits, rejects, drops, coalesces, or buffers—and how much.
- **Native deployment.** Programs should compile ahead of time to compact binaries with an integrated asynchronous runtime.
- **Toolable semantics.** The compiler and IDE should expose reactive graphs, effects, ownership transfers, task boundaries, and generated code.

### Non-goals

The first version should not attempt distributed transactional FRP, transparent remote signals, a universal physical-time model, hard real-time guarantees, or a language in which every value is implicitly reactive. It should also avoid treating persistence as automatic serialization of a live graph. Those may be research directions, but they would obscure the local semantics that must be understood first.

---

## 2 · Design thesis

### Separate finite procedures from persistent relationships

The central division is between *tasks* and *reactors*.

A task is a finite, effectful procedure. It starts, may suspend, may spawn scoped children, and eventually returns, fails, or is cancelled. Tasks own ordinary local state and operating-system resources. They are the natural place for HTTP handlers, file operations, database transactions, and orchestration.

A reactor is a long-lived owner of temporal state. It receives inputs, updates stateful nodes, recomputes dependent signals, and publishes a stable result. A turn is pure and non-suspending. The reactor may describe effects to be launched after stabilization, but no external effect executes while the graph is in an intermediate state.

**Execution domains**

```
┌─────────────────────┐                ┌────────────────────────────┐                ┌──────────────────────────┐
│ Tasks & I/O         │  owned         │ Reactor turn               │  → effects     │ Tasks & consumers        │
│ HTTP, files,        │  inputs →      │ stabilize graph ·          │    & views     │ responses, writes, logs, │
│ sockets, timers,    │                │ commit state ·             │                │ downstream services      │
│ databases           │                │ publish snapshot           │                │                          │
└─────────────────────┘                └────────────────────────────┘                └──────────────────────────┘
```

This is similar in spirit to the Actor–Reactor Model explored in Stella, which separates effectful actors from side-effect-free reactors.[^4] The proposed design, however, treats the separation as one part of a broader systems language: native compilation, structured asynchronous tasks, owned resources, backpressured byte flows, typed effects, and reactor-local memory management are intended to be designed together.

### Why effects happen after stabilization

Consider one input that changes both a user's authorization and the set of visible records. If a logging call, network send, or file write can execute after the first dependency updates but before the second, the outside world can observe a state that never existed as a complete logical result. Rolling that effect back is generally impossible.

Therefore a reactor turn produces two things:

```
// Core semantics
stabilize : ReactorState × Input
          → ReactorState × List<EffectRequest>

execute   : EffectRequest
          → Task<EffectResult>

EffectResult → ReactorMailbox → a later turn
```

The reactive transaction is deterministic given its prior state and ordered input. The effect layer is not necessarily deterministic, but its results re-enter the reactor explicitly. This boundary provides a stable point for tracing, replay, persistence, and testing.

---

## 3 · Programming model

### A small set of temporal types

#### Ordinary values, tasks, flows, events, and signals

| Type | Meaning | Lifetime / pressure | Typical use |
|---|---|---|---|
| `T` | An ordinary value available now. | Owned or borrowed. | Configuration records, parsed JSON, domain values. |
| `Task<T>` | One computation that will eventually return, fail, or be cancelled. | Structured lifetime; no queue. | HTTP calls, file reads, database queries. |
| `Flow<T>` | A potentially long sequence consumed under demand. | Backpressured by default. | Byte bodies, files, database rows, log streams. |
| `Event<T>` | Discrete occurrences within a reactor's temporal domain. | No implicit cross-reactor buffer. | Completions, timers, changes, domain inputs. |
| `Signal<T>` | A current value recomputed when dependencies change. | Retains one stable value. | Current config, health, aggregates, derived views. |
| `Reactor` | An owner of stateful nodes and a transactional dependency graph. | Serial turns; local graph arena. | Service state, cache, tenant, session, subsystem. |

These types should not be aliases for one generalized stream. Their different laws are part of the language. A task has exactly one terminal outcome. A flow has demand and cancellation. An event has occurrences in a reactor turn. A signal has one current value and cannot represent an unbounded history.

#### Reactive turns

Each reactor owns a mailbox and processes one input at a time. The runtime assigns a reactor-local sequence number, executes all affected state transitions, recomputes dependencies in causal order, and publishes exported values only after the graph is stable.

**Lifecycle of one input**

```
Receive input
  → Update stateful nodes
  → Propagate dependencies
  → Reach fixed point
  → Publish stable snapshot
  → Launch declared effects
  → Return results as inputs
```

Within one turn, a signal expression is pure, non-blocking, and non-suspending:

```
// Illustrative syntax
signal full_name = user.first_name + " " + user.last_name
signal greeting  = "Hello, " + full_name
signal can_edit  = session.role.allows(Edit) && document.is_open
```

**Mentioning a node in a signal expression reads its current value, and the whole expression is lifted to a function of the nodes it mentions.** `full_name` above depends on `user` because it names it; `greeting` depends on `full_name` for the same reason; nothing declares a subscription. That rule is what lets ordinary expressions — arithmetic, `match`, `if`, constructors, calls to pure functions — serve as the reactive vocabulary, rather than an operator for each shape.

Because a signal *is* that lifted function, it can also be applied directly: **naming a signal reuses its value; calling it reuses its definition.**

```
// Illustrative syntax
signal is_full = count >= limit

on added(n) {
    if is_full(count + n, limit) { rejected = rejected + 1 } else { count = count + n }
}
```

A handler may not *read* a signal. It runs before propagation, so the value it would see is last turn's — and the alternatives are worse than late, they are incoherent: recomputing on demand mid-handler, or propagating after each assignment, both hand the handler a half-committed state and reproduce exactly the glitch above. The retained value is at least the fixed point of a state that genuinely existed.

Calling sidesteps the question rather than answering it. `is_full(count + n, limit)` has no temporal semantics at all; it is a pure function applied to arguments written at the call site, and `count + n` is a value no node holds — which is the point, since a guard deciding whether to commit is asking about the state it is about to produce. The ambiguity in a read was never staleness as such: it was a *name* eliding its arguments. Spelling them removes it.

The rule is scoped to what it can mean. Only a signal is callable, because only a signal has a body; the call is legal anywhere inside its own reactor but has no spelling outside one, since a handle exposes only inputs and exports; and a `state` initialiser may not call one, because it runs before any turn has given the nodes it derives from a value.

If one input replaces `user`, no observer sees a new first name with an old last name. If one input changes both `session` and `document`, `can_edit` is published only after both changes have propagated.

### State and feedback

This section and §5 and §10 write reactors in an operator-chain style; §6 writes them with explicit `state` and `on` handlers. Both are sketches of the same semantics, and **the v0 subset implements §6's**: explicit state cells with signals as pure derived views. The operator style needs generics and method resolution, which v0 does not have; §6's needs neither, and the last of the open questions below notes that explicit durable state cells are also the friendlier model for snapshotting.

State is explicit through operators such as `hold`, `scan`, and `delay`. An instantaneous dependency cycle is rejected:

```
// Rejected
signal a = b + 1
signal b = a + 1
// error: instantaneous causality cycle a → b → a
```

A feedback loop must cross a temporal boundary:

```
// Accepted
signal request_count = request_finished.count(from: 0)

signal rolling_latency = request_finished.scan(
    Ewma.new(weight: 0.2),
    (average, duration) => average.add(duration)
)
```

The compiler can therefore construct a causal graph, detect cycles, allocate state slots, and produce clear diagnostics.

### Dynamic graph structure

Real systems require subscriptions and subgraphs whose structure changes. A switching operation should create a child graph region whose lifetime follows the selected branch:

```
// Dynamic subgraph
signal selected_tenant: TenantId = ...

signal tenant_view = selected_tenant.switch(id => {
    observe_tenant(id)
})
```

When the selected tenant changes, the old child region is disconnected, its scoped tasks are cancelled, its event sources are closed, and its nodes become reclaimable after the current turn. Dynamic reactivity is thus a language-managed lifetime rather than a convention to manually unsubscribe.

---

## 4 · Concurrency and parallelism

### Cheap tasks outside; serial consistency inside

The language would use an M:N scheduler: many cheap tasks multiplexed over a smaller set of operating-system threads. Network operations, timers, and supported file operations park the task rather than block a worker. CPU-heavy work is placed in an explicit compute pool.

### Structured tasks

```
// Structured concurrency
scope {
    spawn serve_http(listener)
    spawn refresh_credentials()
    spawn export_metrics()

    await process.shutdown_signal()
}
// Leaving the scope cancels and joins all three children.
```

A task spawned inside a scope cannot silently outlive it. Cancellation flows downward; completion and failure flow upward. Detaching work requires an explicit runtime operation and should be rare.

### Reactors as parallel islands

One reactor processes only one turn at a time, but independent reactors may execute concurrently:

```
// Parallel components
let accounts = spawn reactor AccountService()
let metrics  = spawn reactor Metrics()
let config   = spawn reactor Configuration("./config.json")

await metrics.request_finished.send(duration)
```

The send moves an owned message into a bounded mailbox. The receiving reactor handles it during a later turn. Because mutable state does not cross the boundary, applications rarely need locks.

### Concurrency policy is part of the expression

An event that starts tasks must say how multiple occurrences interact:

```
// Task mapping policies
event parsed = files.map_task(
    parallel(16),
    parse_file
)

event config = changes.map_task(
    latest,
    task _ => reload_config()
)

event migrated = migrations.map_task(
    serial,
    run_migration
)

event account_results = commands.map_task(
    keyed(by: cmd => cmd.account_id, parallel_keys: 128),
    process_account_command
)
```

| Policy | Meaning | Suitable for |
|---|---|---|
| `serial` | Preserve every occurrence and run one task at a time. | Migrations, ordered mutations, append operations. |
| `parallel(n)` | Run at most *n* tasks; excess input follows an explicit queue policy. | Independent file parsing, fan-out requests. |
| `latest` | Cancel obsolete work when a newer occurrence arrives. | Configuration reloads, searches, replaceable refreshes. |
| `keyed` | Serialize each key while allowing different keys to proceed concurrently. | Accounts, tenants, sessions, entities. |

This makes behavior that is often hidden behind stream-flattening operators visible in source, documentation, diagnostics, and performance tooling.

### Determinism has a boundary

The design promises deterministic stabilization *given a prior reactor state and an ordered input*. It does not pretend the outside world is deterministic. Two network completions may arrive in either order. The system records that order, and each subsequent turn remains coherent. Applications that require stronger ordering introduce sequence numbers, keyed serialization, or domain-specific protocols.

Lingua Franca demonstrates that reactor-oriented systems can expose deterministic interaction while finding safe parallelism.[^6] The proposed language differs by making reactors one native abstraction within a broader general-purpose server language rather than a polyglot coordination layer.

---

## 5 · Server I/O

### HTTP, files, sockets, and streams remain ordinary code

A frequent failure of ambitious language designs is that their central abstraction looks elegant while routine work becomes ceremonial. Here, I/O should be direct. The reactive system handles relationships; task code handles finite operations.

### Opening an HTTP server

```
// HTTP server
task fn main() -> Result<()>
    uses { net.listen, process.signals, logging }
{
    let app = spawn reactor App("./config.json")
    let server = await http.listen("0.0.0.0:8080")?

    scope {
        spawn server.serve(
            concurrency: 512,
            handler: task request => handle(app, request)
        )

        await process.shutdown_signal()
    }

    return Ok(())
}
```

The listener is an affine resource owned by `server`. The scope owns the serving task. Shutdown cancels new accepts, drains or cancels in-flight handlers according to policy, and closes the listener.

### Making an outbound request

```
// HTTP client
task fn fetch_profile(base: Url, id: UserId)
    -> Result<Profile, FetchError>
    uses { net.connect, clock }
{
    let response = await http.get(base / "profiles" / id)
        .timeout(2.seconds)?

    return await response.json<Profile>(
        limit: 2.mebibytes
    )?
}
```

Timeout and cancellation are part of task structure. The response body is a resource that must be consumed, transferred, or dropped; dropping it closes or returns the underlying connection according to the client pool's contract.

### Reading and watching a file

```
// File I/O and reactivity
let initial = await fs.read_json<Config>("./config.json")?

reactor Configuration(path: Path, initial: Config) {
    source changed = fs.watch(path).modified

    event loaded = Event.once(())
        .merge(changed.map(_ => ()))
        .map_task(latest, task _ => fs.read_json<Config>(path))

    export signal current = loaded.ok().hold(initial)
    export event errors   = loaded.err()
}
```

The watcher is a long-lived event source owned by the reactor. File reads remain tasks. Their completions become events. A failed read does not corrupt the current signal; it appears on an explicit error event.

### Streaming uploads and downloads

```
// Backpressured bytes
POST "/files/{name}" => {
    let path = safe_child(Path("./data"), request.param("name"))?
    let output = await fs.create(path)?

    await request.body.pipe_to(output)?
    http.empty(status: 204)
}

GET "/files/{name}" => {
    let path = safe_child(Path("./data"), request.param("name"))?
    let file = await fs.open(path, Read)?

    http.response(
        status: 200,
        body: file.into_body()
    )
}
```

`request.body` is a `Flow<Bytes>`. The destination requests data as it can accept it, so a slow disk does not cause an unbounded in-memory event queue. In the download case, ownership of the file moves into the response body and the HTTP runtime closes it on completion, client disconnect, or cancellation.

### Why a flow is not an event

An event models logical occurrences inside a reactor. A flow models transfer under demand. Conflating them makes backpressure ambiguous: should the producer pause, should occurrences be retained, and who owns buffered values? The type distinction allows the compiler and runtime to make a stronger promise:

> Every flow is demand-driven; every event crossing an execution boundary declares a finite mailbox policy.

---

## 6 · Effects, capabilities, and failure

### Pure propagation; explicit authority

Reactive expressions cannot perform I/O, suspend, lock, or execute unbounded computation. A signal may call pure functions and bounded total operations. Tasks declare the capabilities they require:

```
// Effect declaration
task fn load_user(id: UserId) -> Result<User, LoadError>
    uses { database.read, clock }
{
    ...
}

task fn replace_file(path: Path, contents: Flow<Bytes>)
    -> Result<()>
    uses { fs.write }
{
    ...
}
```

A package that does not declare `net.connect` cannot start making outbound requests in a later release without changing its public effect signature. Tests can supply fake capabilities for clocks, filesystems, HTTP, randomness, and process signals.

Koka is an important precedent for treating effects and handlers as part of a typed general-purpose language rather than informal documentation.[^9] This proposal would use a narrower, systems-oriented effect model whose main jobs are authority tracking, test substitution, and preserving the pure reactor-turn boundary.

### Effect requests are values

A reactor may produce a typed description of work:

```
// Effect after commit
reactor Mailbox() {
    input send: OutgoingMessage

    state pending = Map<MessageId, DeliveryState>()

    on send(message) {
        pending = pending.insert(message.id, Queued)

        after deliver(message) -> delivery_finished
    }

    on delivery_finished(id, result) {
        pending = pending.update(id, DeliveryState.from(result))
    }
}
```

The exact syntax is open — v0 spells the result channel `-> delivery_finished` rather than `.returns(…)`, since it has no method resolution — but the semantics are not: the state indicating that delivery is queued becomes stable before delivery begins. A completion becomes a later input. This supports tracing and deterministic tests without claiming that an email or HTTP call can be rolled back.

### Failure domains

Ordinary failures are typed results. Cancellation is a distinct outcome propagated by scopes. Panics indicate violated internal assumptions and are contained at task or reactor boundaries. A supervision layer may restart a reactor from an initial value, a durable snapshot, or a parent-provided recovery function, but restart policy should be explicit rather than inherited from an opaque global runtime.

Questions about exactly-once delivery, transaction coupling, and durable outboxes belong to libraries and protocols built on this model. The language should make them possible and observable, not promise them automatically.

---

## 7 · Memory management

### Ownership where it clarifies; local collection where it does not

A uniform Rust-style borrow checker applied directly to a dynamic reactive graph would likely be difficult to use. Long-lived closures, switching subgraphs, delayed feedback, subscriptions, and task callbacks have lifetimes governed by graph reachability and temporal structure rather than lexical blocks. Conversely, a uniform tracing garbage collector would weaken deterministic cleanup of files, sockets, and response bodies and could introduce global pause behavior.

The proposed design therefore uses several coordinated mechanisms.

### Ordinary values: ownership and borrowing

Non-copy values have one owner. Assignment and function calls move them unless borrowed:

```
// Ownership
let body = await request.body.read_all(limit: 8.mebibytes)?
consume(body)

log(body)
// error: `body` was moved into consume
```

```
// Borrowing
fn display_name(user: &User) -> &String {
    return &user.profile.display_name
}

fn normalize(user: &mut User) {
    user.profile.display_name = user.profile.display_name.trim()
}
```

At a given point there may be any number of immutable borrows or one mutable borrow. Most lifetimes are inferred. Explicit lifetime parameters are reserved for lower-level APIs.

### Suspension is a lifetime boundary

```
// Borrow across await
let user = &mut cache[id]
await http.get(url)
user.status = Active

// error: exclusive borrow may not remain live while this task is suspended
```

The task instead extracts owned request data, performs the I/O, and reacquires access afterward. Scoped child tasks may borrow a parent's values because the compiler knows they cannot outlive the scope:

```
// Scoped borrowing
let records = load_records()

scope {
    spawn scoped { validate(&records) }
    spawn scoped { build_index(&records) }
}
```

> **v0 answers this positionally rather than by analysis.** A reference is producible only in parameter position and cannot be given a name, so there is no field, return, payload, `let`, or reactor member that could hold one. The single value that outlives the expression building it is a `Task<T>`, so `spawn` and an effect request reject a borrowed argument — and `await f(&x)` is left alone, because the awaiting task is parked for the duration and ownership is unique, so it cannot invalidate the borrow itself and nobody else holds the value. That is a lifetime boundary enforced by where a thing can be written rather than by inference, and it holds only while there are no loops and no aliasing. `&mut`, scoped borrowing of a parent's values, and explicit lifetimes all wait for the real borrow checker; see `BOOTSTRAP.md` §8.

### Cross-reactor transfer

Mutable references never cross reactor boundaries. A message is either moved, deeply immutable and shared, or encoded into a bounded flow. This links memory safety to concurrency safety.

```
// Message transfer
await worker.process.send(job)       // moves `job`
await catalog.publish.send(shared(snapshot))
await socket.write.send(bytes_flow)  // transfers a backpressured flow endpoint
```

Project Verona explicitly investigates concurrent ownership as a language model,[^7] while Pony demonstrates how a type system and actor runtime can be co-designed to support race freedom and actor-local concurrent garbage collection.[^8] Those systems suggest that memory management can exploit isolation guarantees rather than treating the heap as one undifferentiated global object graph.

### Affine operating-system resources

Files, sockets, transactions, response bodies, watchers, and timers are non-copyable. Each must be closed, moved, or dropped at scope exit:

```
// Affine resource
let file = await fs.open(path, Read)?
let body = file.into_body()

await file.read(buffer)
// error: ownership of `file` moved into `body`
```

This statically prevents common failures such as using a closed handle, committing a transaction twice, sending the same response body twice, or concurrently driving a non-shareable socket from unrelated tasks.

### Immutable sharing and byte buffers

Servers need cheap sharing of configuration, schemas, routing tables, snapshots, and byte buffers. `Shared<T>` provides immutable reference-counted sharing. References can be non-atomic within one reactor and upgraded to atomic representation when crossing a thread or reactor boundary.

```
// Shared immutable values
let schema: Shared<Schema> = shared(load_schema())

let packet: Bytes = ...
let header  = packet.slice(0, 32)
let payload = packet.slice(32, packet.len)
```

There is no general-purpose `Shared<Mutable<T>>`. Shared mutation requires a reactor, an explicitly atomic type, or an opt-in lock from a low-level concurrency package.

> **Neither `Shared<T>` nor `Bytes` is in v0.** Sharing is an answer to the cost of copying, and v0's ordinary values are copied freely by an engine that clones — there is nothing yet that could tell a share from a copy. M5's native backend deliberately kept that cloned representation, so both now arrive with the backend that gives values layout, which is the first thing that makes the difference measurable. Affine ownership of operating-system resources, described above, is implemented in full.


### Reactive graphs: reactor-local arenas

Each reactor owns a graph arena. Signal and event handles refer to nodes in that arena; application variables do not individually own nodes. Roots include exported values, active external subscriptions, event sources, pending task continuations, and currently selected dynamic branches.

After a turn, the reactor is at a quiescent point. It can reclaim detached child regions and, when necessary, trace a small local graph to collect cycles. Other reactors continue running. This avoids both lexical-lifetime contortions for graph topology and a whole-process stop-the-world collector.

| Memory class | Mechanism | Reason |
|---|---|---|
| Task-local ordinary data | Ownership, borrowing, escape analysis, temporary regions | Fast allocation and deterministic reclamation. |
| OS resources | Affine ownership and deterministic drop | Cleanup must follow cancellation and all error paths. |
| Immutable shared data | Reference-counted `Shared<T>` | Cheap snapshots and zero-copy transfer. |
| Reactor state | Exclusive reactor ownership | No data races or application locks. |
| Reactive graph nodes | Local arena, regions, epoch retirement, occasional local tracing | Dynamic graph lifetimes are not purely lexical. |
| Cross-boundary queues | Bounded mailboxes and demand-driven flows | Concurrency must not become an implicit memory leak. |

### Queue capacity is memory semantics

```
// Bounded mailbox
input commands: Command [
    capacity: 4096,
    overflow: wait
]
```

Alternative policies include `reject`, `drop_oldest`, `drop_newest`, and `coalesce_latest`. A signal retains one value rather than a history. A flow transmits according to downstream demand. The type system cannot prove that arbitrary application data stays small, but the runtime should never create unbounded asynchronous storage implicitly.

---

## 8 · Metaprogramming

### The language should eventually have macros—but FRP must not be implemented by them

The first implementation should avoid general procedural macros. Core constructs such as `reactor`, `signal`, `event`, `task`, `await`, `hold`, and `delay` must have compiler-defined semantics. The compiler needs direct visibility into graph dependencies, suspension points, effects, ownership, and causality.

Ordinary reactive composition should use functions and generics:

```
// Library-level composition
fn moving_average(
    samples: Event<Float>,
    count: USize
) -> Signal<Float> {
    samples.window(count).map(mean).hold(0.0)
}
```

### Where metaprogramming earns its cost

Server ecosystems contain repetitive structural integration: serializers, routers, RPC stubs, database mappings, schemas, command-line parsers, FFI bindings, and test generators. These are suitable for constrained code generation:

```
// Derivation and attributes
@derive(Eq, Hash, Json, Schema)
record User {
    id: UserId
    name: String
    email: Email
}

@http_api(prefix: "/v1")
interface UsersApi {
    @get("/users/{id}")
    task fn get_user(id: UserId)
        -> Result<User, NotFound>

    @post("/users")
    task fn create_user(body: Json<CreateUser>)
        -> Result<User, ValidationError>
}
```

The API declaration could generate route registration, parameter parsing, JSON codecs, a typed client, and an interface schema. It should not secretly define scheduling, queueing, or effect semantics.

### A staged macro system

| Stage | Capability | Why start here |
|---|---|---|
| 1 | Compile-time evaluation of ordinary pure functions | Many "macro" use cases are computations over values, not syntax. |
| 2 | Built-in derives and constrained declaration attributes | Covers serialization, schemas, and common framework glue with strong tooling. |
| 3 | Hygienic declarative syntax macros with typed syntax categories | Supports control-flow-shaped abstractions without arbitrary compiler execution. |
| 4 | Sandboxed typed procedural macros | Allows advanced ecosystem tooling after the type and effect model stabilizes. |

Rust distinguishes declarative macros from procedural macros that consume and produce syntax token streams.[^10] That power has enabled a rich ecosystem, but this proposal should prefer semantic representations over unrestricted token processing. Scala 3 offers a useful precedent for macros that manipulate typed expressions such as `Expr[T]` and typed syntax trees.[^11]

### Typed and sandboxed expansion

```
// Typed macro sketch
macro fn instrument<T, Effects>(
    operation: TypedTaskExpr<T, Effects>
) -> TypedTaskExpr<T, Effects + Logging> {
    ...
}
```

The macro signature reveals that instrumentation adds a logging effect. A macro representation could expose value type, effect set, ownership mode, suspension behavior, reactive domain, and source location. Generated code is then rechecked by the ordinary type, effect, borrow, and causality passes.

Procedural macros should run in a deterministic sandbox with bounded resources, no network access, and only declared file inputs. They should have no semantic privilege: a macro cannot forge a capability, suppress a borrow error, introduce an unchecked reactive cycle, or publish mutable reactor state.

### Expansion must remain observable

The toolchain should provide commands such as:

```
lang expand service.lang
lang graph App
lang effects App
lang ownership App
lang queues App
```

An IDE should show generated declarations, graph nodes, effects, task boundaries, queue capacities, and ownership transfers, with source mappings back to the macro invocation. In a reactive language, hiding generated temporal topology is especially dangerous.

---

## 9 · Compiler and runtime

### Native code with a deliberately visible runtime

Compiling directly to native code does not mean runtime-free execution. Cheap tasks, asynchronous I/O, timers, mailboxes, graph propagation, cancellation, and local graph reclamation all require runtime support. The objective is a compact and predictable runtime whose semantic responsibilities are part of the language contract.

### Compilation pipeline

```
parse source
    ↓
expand hygienic declarative syntax
    ↓
resolve declarations and names
    ↓
run derives and typed macro expansion
    ↓
type and effect checking
    ↓
ownership and borrow checking
    ↓
build reactive dependency graphs
    ↓
causality, turn, and queue analysis
    ↓
lower tasks to coroutine state machines
    ↓
lower reactors to state slots + propagation plans
    ↓
generate native code
```

Static reactor graphs can become compact dependency tables and direct function calls. Stateful operators become fields in reactor storage. Dynamic operators allocate child graph regions. Task functions lower to resumable state machines. The native backend could initially target an established compiler infrastructure while preserving a language-specific intermediate representation for temporal and ownership analysis.

### Runtime responsibilities

| Component | Responsibility |
|---|---|
| **Task scheduler** | Work stealing, coroutine resumption, cancellation, structured scopes, and a separate pool for explicitly blocking foreign calls. |
| **Readiness poller** | Platform-specific nonblocking sockets, timers, process signals, and supported asynchronous file operations. Named for what it answers rather than for the pattern it implements: "reactor" is the usual word, and in this language a reactor is a graph of state and signals. |
| **Reactive engine** | Mailbox sequencing, turn execution, propagation, stable publication, effect launch, and graph introspection. |
| **Memory services** | Task regions, shared-value counts, reactor-local graph reclamation, and affine-resource finalization on cancellation. |
| **Observability** | Structured traces connecting input sequence, graph recomputation, effects, task spans, queue delay, and allocation. |
| **Supervision** | Panic containment, restart policy, shutdown ordering, and optional restoration from application-defined snapshots. |

### CPU parallelism

```
// Fork-join computation
let results = await parallel {
    for chunk in document.chunks(cpu.count) {
        spawn compute(chunk)
    }
}
```

The parallel region is scoped. Inputs must be immutably borrowed for the duration of the region or moved into workers. Results are owned values returned to the parent. Blocking foreign functions require an explicit `blocking` boundary so they cannot stall the normal task scheduler.

---

## 10 · Worked example

### A small service using all four execution concepts

The following sketch watches a configuration file, exposes current configuration as a signal, opens an HTTP server, makes outbound requests, streams files, and maintains reactive metrics. It is illustrative rather than a frozen syntax proposal.

```
module service

use std.fs
use std.http
use std.json
use std.log
use std.process
use std.time

record Config {
    greeting: String
    upstream: Url
}

record Metrics {
    requests: U64
    mean_latency: Duration
}

reactor App(config_path: Path, initial: Config) {
    source config_changed = fs.watch(config_path).modified

    event reload_requested = Event.once(())
        .merge(config_changed.map(_ => ()))

    event config_loaded = reload_requested.map_task(
        latest,
        task _ => fs.read_json<Config>(config_path)
    )

    export signal config = config_loaded
        .ok()
        .hold(initial)

    export event config_errors = config_loaded.err()

    input request_finished: Duration [
        capacity: 4096,
        overflow: coalesce_latest
    ]

    signal request_count = request_finished.count(from: 0)

    signal latency_average = request_finished
        .scan(
            Ewma.new(weight: 0.2),
            (average, duration) => average.add(duration)
        )
        .map(average => average.value)

    export signal metrics = Metrics {
        requests: request_count,
        mean_latency: latency_average
    }
}

task fn main() -> Result<()>
    uses {
        fs.read, fs.write, fs.watch,
        net.listen, net.connect,
        clock, process.signals, logging
    }
{
    let config_path = Path("./config.json")
    let initial = await fs.read_json<Config>(config_path)?

    let app = spawn reactor App(config_path, initial)
    let server = await http.listen("0.0.0.0:8080")?

    scope {
        spawn {
            for await error in app.config_errors.flow(
                capacity: 32,
                overflow: coalesce_latest
            ) {
                await log.error("configuration reload failed", error)
            }
        }

        spawn server.serve(
            concurrency: 512,
            handler: task request => handle(app, request)
        )

        await process.shutdown_signal()
    }

    return Ok(())
}

task fn handle(app: App, request: http.Request)
    -> Result<http.Response>
    uses { fs.read, fs.write, net.connect, clock }
{
    let started = time.monotonic()

    let response = match request.route() {
        GET "/" => {
            let config = app.config.latest()
            http.text(status: 200, body: config.greeting)
        }

        GET "/proxy/{id}" => {
            let config = app.config.latest()
            let id = request.param("id")
            let upstream = await http.get(
                config.upstream / "items" / id
            )?

            http.response(
                status: upstream.status,
                body: upstream.body
            )
        }

        POST "/files/{name}" => {
            let path = safe_child(
                Path("./data"),
                request.param("name")
            )?

            let output = await fs.create(path)?
            await request.body.pipe_to(output)?
            http.empty(status: 204)
        }

        GET "/files/{name}" => {
            let path = safe_child(
                Path("./data"),
                request.param("name")
            )?

            let file = await fs.open(path, Read)?
            http.response(
                status: 200,
                body: file.into_body()
            )
        }

        GET "/metrics" => {
            http.json(
                status: 200,
                value: app.metrics.latest()
            )
        }

        _ => http.text(status: 404, body: "not found")
    }

    await app.request_finished.send(
        time.monotonic() - started
    )

    return Ok(response)
}
```

The example demonstrates the intended division:

- **Values** hold ordinary parsed and domain data.
- **Tasks** perform finite procedures and I/O with structured cancellation.
- **Flows** move bytes under backpressure.
- **Events and signals** define persistent temporal relationships.
- **The reactor** owns mutable temporal state and publishes coherent snapshots.
- **Ownership** determines who closes each body, file, listener, watcher, and message.

---

## 11 · Game-server case study

### A persistent voxel world as a federation of owned reactors

A Minecraft-like server is a useful stress test because it combines fixed-rate simulation, dynamic spatial state, thousands of long-lived relationships, expensive finite computations, persistence, streaming network traffic, and abrupt client failure. The language should not answer this by turning every block or entity into an independently scheduled reactive object. It should use a small number of explicit authority boundaries and apply FRP primarily to coherent derived state.

> **Architectural thesis**
>
> Commands are serialized at the spatial authority that owns the affected state. One pure region step produces the next committed world state and a set of declared consequences. Reactive graphs maintain views, activation sets, circuits, and replication deltas around that state; tasks perform slow or effectful work; flows carry bytes under demand; ownership transfers authority when an entity crosses a boundary.

### The unit of concurrency is a region, not an object

The server is organized as a hierarchy. A process supervisor owns lifecycle and failure policy. Player-session reactors own connection-local state such as authentication, input sequence numbers, negotiated capabilities, rate limits, and outbound budgets. A lightweight world coordinator owns global metadata such as world identity, clock epochs, region placement, and administrative state. Most authoritative simulation lives in **region reactors**, each of which owns a spatial partition containing chunks, block state, entities, scheduled updates, and local gameplay systems.

```
// Abstract authority topology
process supervisor
    ├── world coordinator
    │     ├── region reactor A ── neighbor snapshots ── region reactor B
    │     ├── region reactor C
    │     └── global service reactors: chat, permissions, economy
    ├── player session reactors
    │     └── structured network tasks and outbound flows
    └── storage / generation / pathfinding tasks
          └── results return as versioned reactor inputs
```

| Unit | Role | Description |
|---|---|---|
| Session reactor | Protocol authority | Orders and validates packets, tracks login and capability state, applies rate limits, and routes accepted commands. It does not directly mutate world state. |
| World coordinator | Directory and epochs | Maps positions to region owners, issues simulation epochs, supervises placement, and owns low-frequency global state rather than every block update. |
| Region reactor | Spatial authority | Owns all mutable simulation state in a partition and processes one coherent turn at a time. Different regions run in parallel. |
| Service reactor | Independent authority | Owns systems whose consistency boundary is not spatial: permissions, chat channels, parties, bans, or an economy ledger. |
| Task | Finite expensive work | Loads a chunk, generates terrain, computes a path, compresses packets, or writes a snapshot without entering reactive propagation. |
| `Flow<Bytes>` | Transport | Moves packet and chunk bytes under backpressure. It remains separate from logical world events and cannot grow an implicit unbounded queue. |

A reactor per block would create too much scheduling, mailbox, and graph overhead. A reactor per entity would turn ordinary interactions into distributed transactions. Blocks and entities are usually owned values inside a region's data-oriented tables. They become separate reactors only when they truly need an independent authority and lifetime.

### One region turn is the authoritative simulation unit

The engine gives each active region an explicit simulation clock. For tick `n`, a region consumes the commands accepted for that tick, scheduled updates, completed task results, and the most recently committed border state from neighboring regions. Its simulation step is an ordinary pure function:

```
// Region step
advance :
    RegionState
    × Tick
    × List<AcceptedCommand>
    × NeighborBorders
    → RegionState
    × List<WorldEvent>
    × List<EffectRequest>
```

The result is published as one region version. Reactive projections then update, and effect requests are scheduled only after stabilization. Regions can execute on separate worker threads because their mutable states are disjoint. Within a region, gameplay may still be implemented as deterministic passes over dense component and chunk tables rather than as thousands of callbacks.

A world-wide barrier on every tick would let one slow region stall the whole world. A more scalable default is bounded local synchronization: neighboring regions exchange immutable border snapshots at committed tick boundaries and may be at most a small, declared number of epochs apart. A rule that truly requires same-turn atomicity across a boundary must be routed to one authority or temporarily widen the ownership domain.

### Spatial boundaries use snapshots, messages, and ownership transfer

Most neighboring interaction can use a read-only *halo*: a compact snapshot of blocks, entities, collisions, power, or environmental values near a region edge. A region reads the latest committed halo from its neighbors while advancing its own state. The small latency is explicit and traceable.

When an entity crosses a boundary, the source region performs a handoff:

1. The source removes the entity from ordinary simulation and creates a move-only transfer value containing its authoritative state and transfer epoch.
2. The destination validates and accepts that value during a later turn.
3. The source finalizes the transfer after acknowledgement; timeout or rejection follows a defined recovery policy.

The transfer is not a shared pointer. At every committed point, exactly one region owns the mutable entity aggregate. The same protocol can move a player, vehicle, projectile, or loaded chunk between authorities.

### Reactive state is strongest in views and activation

The simulation's command path remains explicit, but many persistent relationships are naturally reactive. A player's desired chunk set depends on position, view distance, permissions, and currently available chunks. The network needs only the difference when that set changes:

```
// Reactive interest management
signal desired_chunks = combine(
    player.position,
    player.view_distance,
    region.loaded_chunks
).map((position, distance, chunks) =>
    chunks.within(position, distance)
)

event subscription_delta = desired_chunks.changes()
```

The session uses that delta to attach and detach dynamic subscriptions to immutable region publications. Leaving an area disposes its subscriptions and any child graph nodes. The session never obtains a mutable reference into a region.

The same pattern can maintain nearby entities, audible events, scoreboard views, weather exposure, spawn eligibility, active chunks, and operational signals such as region backlog or tick cost.

### Use FRP selectively inside the simulation

Some local systems genuinely resemble reactive networks. A power circuit, portal network, or transport graph has persistent dependencies, topology changes, and delayed feedback. These can be dynamic child graphs owned by the region. A topology change replaces a local subgraph; feedback crosses an explicit tick delay rather than forming an instantaneous cycle.

Other systems are better represented as bounded work queues. Fluids, lighting frontiers, fire, growth, ecology, and AI should process a declared amount of work per tick and reschedule the remainder. FRP can derive the dirty frontier or activation set without requiring every block to be a signal.

### Slow computations are versioned tasks

Chunk loading, terrain generation, compression, pathfinding, and structure searches run outside the region turn over owned work requests or immutable snapshots:

```
// Keyed and bounded work
event loaded_chunks = chunk_requests.map_task(
    keyed(by: request => request.chunk, parallel_keys: 32),
    task request => load_or_generate(
        request.chunk,
        request.generator_version
    )
)

event paths = path_requests.map_task(
    parallel(8),
    task request => pathfind(
        request.navigation_snapshot,
        request.goal
    )
)
```

Each result carries the region, chunk, entity, and state version for which it was computed. The receiving region accepts, rebases, or rejects it during a later turn. No task retains a mutable borrow of the live world while suspended.

### Network replication has several pressure policies

An outbound connection should not have one undifferentiated FIFO. Different classes of information have different semantics:

| Output class | Pressure policy | Examples |
|---|---|---|
| Critical ordered events | Bounded wait; disconnect or fail explicitly on persistent overload. | Login state, inventory confirmations, permission changes, transfer acknowledgements. |
| Replaceable state | Coalesce by entity or field, retaining only the newest value. | Position, velocity, orientation, health display. |
| Incremental world deltas | Merge by chunk and block key; replace a large backlog with a fresh snapshot. | Block changes, entity spawn and despawn, light updates. |
| Bulk data | Demand-driven `Flow<Bytes>` with explicit concurrency and bandwidth budgets. | Initial chunk payloads, resource data, replay downloads. |
| Cosmetic events | Drop oldest or newest according to a declared protocol policy. | Particles, ambient sounds, nonessential animation events. |

Interest-management signals feed this transport layer, but the flow's byte budget determines when values are encoded and sent. A slow client consumes fewer snapshots or is disconnected; it does not force a region graph to retain an unbounded history. A region publishes stable state and never writes a socket during propagation.

### Persistence is staged rather than hidden in gameplay

A world turn may produce journal records, dirty-chunk markers, audit events, and snapshot requests. These are effect descriptions, not direct writes from inside the simulation. The storage layer batches ordinary world changes and periodically writes compact chunk or region snapshots. A region cannot unload until the storage protocol confirms the required durable version.

Not every operation needs the same durability. Movement, ambient simulation, and replaceable entity state may tolerate periodic persistence. Purchases, scarce-item transfers, administrative actions, or player ownership changes may require a stricter staged commit:

```
// Durable command staging
prepare stable result
    → append journal or commit database transaction
    → receive durable acknowledgement
    → publish authoritative result
    → emit network and secondary effects
```

This stricter path could be a library protocol or eventually a distinct durable-reactor primitive. It should remain visible because waiting for durable storage changes latency and failure semantics. The durable projection contains domain state; live signals, watchers, task continuations, and subscriptions are rebuilt after recovery.

### Ownership gives unloading and failure a concrete meaning

A region owns its chunk pages, entity tables, scheduled updates, local circuit graphs, and pending command state. Network encoders and background tasks receive immutable snapshots or moved work items, never mutable aliases into that state. When a region becomes inactive, the coordinator requests a final durable snapshot, the region cancels child tasks, closes event sources, drops its graph arena, and transfers or frees its owned pages.

This makes memory behavior align with game concepts. A loaded region is a resource-owning scope. An active player view is a dynamic subgraph. A generated chunk is a move-only result. An encoded packet is an immutable byte buffer. A disconnected session is a cancelled task tree rather than a collection of callbacks that must each remember to unsubscribe.

### Selected engine tasks and their language paradigms

| Server task | Primary paradigm | Reason |
|---|---|---|
| Accept and supervise a player connection | Structured task scope | The reader, writer, heartbeat, authentication, and resources share one cancellable lifetime. |
| Order and validate player inputs | Session reactor with a bounded mailbox | Sequence numbers, rate limits, and protocol state require serialized mutation. |
| Advance blocks and entities | Pure fixed-tick region step | The result is deterministic from committed state and ordered inputs. |
| Run the world on multiple cores | Parallel isolated region reactors | Spatial ownership removes shared mutable state between most simulation partitions. |
| Maintain player visibility | Signals over incremental maps and sets | Visibility is persistent derived state whose deltas feed replication. |
| Model a power or transport network | Dynamic region-local reactive subgraph | Dependencies, topology, and delayed feedback are intrinsic to the domain. |
| Generate or load a chunk | Keyed bounded task | One computation per chunk should be deduplicated, cancellable, and independent of propagation. |
| Compute mob paths | Parallel task over an immutable snapshot | Expensive work can finish later and be rejected when stale. |
| Cross a region boundary | Move-only ownership-transfer protocol | Exactly one region remains authoritative for the entity. |
| Send world updates | Prioritized backpressured flows | Critical events, replaceable state, deltas, and bulk chunks need different overload policies. |
| Persist world state | Post-turn journal effects and snapshots | I/O never observes partially propagated state, and unload waits for an explicit durable version. |
| Host plugins or mods | Capability-typed systems and tasks | A plugin declares whether it may read files, open sockets, mutate a region, or schedule background work. |

### Overload is an explicit engine policy

Queue depth, oldest-message age, tick duration, dropped cosmetics, coalesced updates, and task backlog should be exported as signals. A control reactor can reduce optional work before correctness is threatened: shrink view distance, defer chunk generation, lower AI or ecology frequency, move a hot region to another worker, or reject new sessions. Inventory mutations, ownership transfers, and other nonreplaceable commands remain reliable and ordered; stale state and cosmetic work degrade first.

### What the case study adds to the language requirements

This application suggests several facilities that are optional in a simple HTTP service but important at game-server scale:

- **Incremental maps and sets** so spatial indexes and subscriptions propagate deltas without rebuilding complete collections.
- **Explicit tick and epoch types** so wall time, simulation time, command sequence, and persistence version cannot be confused.
- **Versioned task results** with standard patterns for accepting, rebasing, or rejecting stale computations.
- **Priority-aware bounded flows** rather than one channel policy for every class of network output.
- **Observable ownership transfers** so tooling can trace where an entity, chunk, socket, or byte buffer currently lives.
- **Durability staging** for the smaller class of commands that must not become visible before storage acknowledges them.
- **Deterministic trace tooling** that reconstructs a region from a snapshot, ordered inputs, task-result events, and tick epochs.

The resulting engine is neither an actor system with one actor per object nor a single enormous FRP graph. It is a federation of coarse owned simulations. FRP maintains the relationships that should remain continuously true; tasks perform finite work; flows manage transport pressure; and ownership makes the location of authority explicit.

---

## 12 · Application fit and adoption rationale

### Use it when the server is maintaining a world

The language should not justify itself by serving a few JSON endpoints. Go, TypeScript, Java, C#, Rust, and many other ecosystems already do that well. Its reason to exist is narrower: long-lived concurrent systems whose state continuously changes in response to many inputs, and whose hardest bugs arise from coordination across time.

> **Defensible positioning**
>
> A native language for continuously running, stateful systems—where many concurrent events must produce coherent state, bounded work, controlled effects, and understandable resource lifetimes. Use it when the server is not merely answering requests; it is maintaining a world.

The "world" need not be spatial. It may be a deployment cluster, a collaborative document, a financial account, a running workflow, a source-code workspace, a connected device fleet, or a set of live user sessions. The common property is that the application maintains an evolving model, derives many consequences from that model, and continuously interacts with unreliable external systems.

### The fit test

The language becomes compelling when several of the following are true:

**Persistent authority**

- Important state lives substantially longer than one request.
- Many independent event sources can affect the same authority.
- Ordering and coherent multi-field updates matter.
- Replaying the same ordered inputs should reproduce the same local result.

**Continuous derivation**

- Many views, subscriptions, alerts, permissions, or indexes derive from shared facts.
- Clients consume changes rather than repeatedly requesting complete snapshots.
- Late task results can become stale and need an explicit acceptance policy.
- The system naturally resembles a living model rather than a sequence of isolated calls.

**Concurrency pressure**

- Cancellation, backpressure, and overload policy matter.
- Many finite tasks run around long-lived state.
- Resources such as sockets, files, bodies, and transactions have nontrivial lifetimes.
- Coordination bugs dominate ordinary business-logic bugs.

**Natural ownership keys**

- State can be partitioned by region, document, account, tenant, device, workflow, room, or another stable key.
- Most mutation can remain local to one authority boundary.
- Cross-boundary work can use messages, immutable snapshots, bounded flows, or explicit ownership transfer.
- Global coordination is exceptional rather than the default path.

When those properties are absent—when a program receives a request, performs one database query, returns JSON, and forgets everything—the language may still work, but it offers little advantage over mature conventional choices.

### The recurring application shape

```
// Stateful service topology
external events
    ↓
bounded input ports
    ↓
owned reactor
    ↓
one atomic reactive turn
    ↓
stable state and derived outputs
    ↓
effect requests
    ↓
concurrent structured tasks
    ↓
results return as later events
```

A reactor is the serialized authority for one local model. Different reactors execute concurrently. Tasks perform finite I/O or computation outside propagation. Flows transfer sequences under demand. Effects begin only after the triggering turn reaches a stable state. This organization does not remove application-specific algorithms; it gives them a predictable execution, ownership, and failure model.

### Strongest application categories

| Category | Shape | Why it fits |
|---|---|---|
| **Control planes** | Reconciliation and desired state | Deployment orchestrators, cluster managers, service discovery, job schedulers, cloud controllers, and device-fleet managers continuously compare desired state with observed state. A managed resource is a natural reactor; drift and health are signals; reconciliation is an explicit serial or keyed task policy. |
| **Games and simulation** | Persistent authoritative worlds | Matches, world regions, player sessions, guilds, and economy partitions provide clear ownership boundaries. Fixed-step simulation remains pure and deterministic, while reactive state maintains visibility, activation, replication, circuits, and operational health. |
| **Collaboration** | Documents and shared workspaces | Editors, whiteboards, design tools, presence systems, and synchronized planning applications maintain long-lived documents with revisions, participants, permissions, cursors, comments, indexes, and client-specific projections. One document or workspace can own the coherent state. |
| **Workflow engines** | Durable processes over unreliable effects | Order fulfillment, payment flows, approvals, claims, onboarding, media pipelines, and agentic workflows react to timers, webhooks, user actions, retries, cancellations, and task completions. One workflow instance is a natural durable reactor. |
| **Developer tools** | Incremental compilers and build services | Watched files derive syntax trees, dependency graphs, types, diagnostics, indexes, and artifacts. The reactive model suits invalidation and coherent snapshots; structured tasks suit parallel parsing, checking, optimization, and code generation. |
| **Stream processing** | Current conclusions over event partitions | Telemetry, alerting, fraud detection, risk calculation, metering, sensor processing, and materialized views consume backpressured flows while maintaining windows, aggregates, sessions, correlations, thresholds, and current health signals. |
| **Network infrastructure** | Gateways, brokers, and protocol services | API gateways, reverse proxies, WebSocket hubs, message brokers, multiplayer relays, and policy points combine many connections with live routing, certificates, rate limits, upstream health, cancellation, and strict memory pressure. Affine bodies and sockets make transport ownership explicit. |
| **Edge and industrial** | Many clocks and long-lived device state | Smart-building controllers, industrial gateways, robotics coordinators, local device hubs, and sensor networks integrate sampling, operator commands, control loops, persistence, network updates, and health reporting. The base runtime targets soft real time rather than hard deadline certification. |
| **Agent runtimes** | Tools, plans, approvals, and budgets | Long-running AI and automation systems coordinate streaming model output, tool calls, concurrent subtasks, retries, human approvals, permissions, cost limits, checkpoints, and cancellation. A reactor can own one run or workspace while tasks execute tools. |
| **Complex SaaS** | Business systems beyond CRUD | Live subscriptions, collaboration, changing organizational permissions, notification rules, schedules, background workflows, and continuous synchronization with external services can justify the model. A simple stateless database wrapper generally does not. |

### Natural reactor boundaries

A useful predictor of fit is whether the application has an obvious ownership key. The clearer the key, the easier it is to gain parallelism without shared mutable state.

| Application | Likely authority boundary | Typical derived state |
|---|---|---|
| Multiplayer world | Region, match, or instance | Visibility, activation, replication, scores |
| Collaborative editor | Document or workspace | Client views, presence, indexes, permissions |
| Workflow engine | Workflow instance | Current phase, eligibility, deadlines, pending effects |
| Device platform | Device or fleet partition | Health, desired configuration, alerts, drift |
| Financial service | Account or portfolio partition | Balances, limits, risk, available actions |
| Chat or presence system | Room or conversation | Membership, delivery sets, unread state, moderation |
| Build system | Workspace or package | Dependency closure, dirty targets, diagnostics |
| Deployment controller | Managed resource | Drift, health, next reconciliation action |
| Logistics platform | Shipment, route, or warehouse | ETA, capacity, exceptions, customer projections |
| Streaming application | Partition key | Windows, sessions, aggregates, alerts |
| Multi-tenant SaaS | Tenant or bounded domain entity | Permissions, notifications, live views |
| Agent system | Run or workspace | Readiness, blockers, budget, allowed actions |

Systems requiring frequent atomic operations across arbitrary boundaries are a weaker fit. They still need database transactions, consensus, sagas, temporary ownership transfer, or a deliberately larger authority boundary. Local reactive consistency does not make distributed transactions disappear.

### Why reach for it instead of an established language?

| Alternative | What it already does well | Why this language might be chosen |
|---|---|---|
| Go | Simple deployment, fast builds, excellent networking, cheap goroutines and channels. | When the program accumulates shared maps, mutexes, ad hoc goroutine lifetimes, unclear channel ownership, stale caches, and implicit queue growth. Reactors add owned state, atomic derivation, structured cancellation, and mandatory pressure policy. |
| Rust | Memory safety, predictable performance, native interoperability, low-level control. | When the dominant problem is coordinating temporal state rather than controlling representation. Reactor isolation offers a higher-level ownership rule: one component owns the mutable graph; others communicate through typed boundaries. |
| TypeScript + RxJS | Rapid iteration, broad web ecosystem, expressive event-stream operators. | When team conventions are no longer enough. The compiler can enforce pure propagation, atomic stabilization, causal feedback, bounded queues, structured subscription lifetimes, valid resource ownership, and explicit task concurrency. |
| Erlang or Elixir | Actors, supervision, fault tolerance, distribution, operational maturity. | When stronger static types, affine resources, native layouts, potential zero-copy transfer, deterministic intra-component derivation, and backpressured byte streams matter. This language must still develop equally serious supervision before competing broadly. |
| Java, Kotlin, or C# | Deep server ecosystems, databases, debuggers, profilers, mature frameworks. | When futures, event buses, actors, reactive libraries, lifecycle frameworks, and concurrency annotations still leave one fragmented architecture. The proposed model unifies those concerns, at the cost of ecosystem depth. |
| Functional and synchronous FRP systems | Strong temporal semantics, mathematical models, deterministic propagation. | When production server ergonomics are equally important: direct HTTP and file APIs, ordinary task procedures, native deployment, resource ownership, familiar records and enums, and mainstream package workflows. |

The language is intentionally more opinionated than Rust or Go. It trades some generality for a simpler architecture: finite work belongs in tasks; long-lived mutable temporal state belongs in reactors; byte and row sequences belong in flows; and cross-reactor communication is owned, immutable, or bounded.

### Poor fits and explicit non-claims

- **Simple stateless APIs.** A request that validates input, performs one query, returns JSON, and retains no meaningful state gains little from FRP or reactors. Mature mainstream frameworks remain the faster choice.
- **One-shot scripts.** File renaming, shell automation, small migrations, and quick integrations favor languages with immediate scripting workflows unless this ecosystem later develops an excellent script mode.
- **Numerical and ML kernels.** The architecture does not inherently provide tensor compilation, GPU kernels, scientific libraries, SIMD optimization, or notebook workflows. It may orchestrate such work through specialized libraries.
- **Kernels and tiny firmware.** The general runtime assumes tasks, reactors, graph memory, and operating-system services. Kernels, bootloaders, drivers, and severely constrained devices need a lower-level or freestanding profile.
- **Hard real-time control.** Glitch-free turns do not imply bounded wall-clock response. Hard deadlines require bounded allocation, propagation and queue latency, static scheduling analysis, and explicit priority behavior.
- **Globally coupled distributed state.** The model creates deterministic local islands, not one atomic graph across a cluster. Systems requiring constant global coordination still pay consensus and communication costs.

### Why this is a language feature rather than only a framework

A library can imitate the surface vocabulary—`event.map`, `signal.combine`, `reactor.spawn`—but only the language and compiler can reliably enforce the interactions among reactivity, suspension, ownership, effects, and queues. The compiler can know:

- whether code executes during a reactive turn and therefore must remain pure and non-suspending;
- which effects a task may perform and which capability authorizes them;
- which reactor owns a value and whether a reference crosses an invalid boundary;
- whether a feedback cycle lacks a delay or other temporal boundary;
- whether a task closure captures borrowed state that may outlive its owner;
- whether a cross-reactor flow or mailbox has an explicit pressure policy;
- whether a resource is moved, shared, borrowed, or consumed exactly once; and
- whether generated macro code adds hidden effects, tasks, queues, or reactive topology.

Those semantics also enable tools that conventional debuggers rarely provide:

```
// Semantic tooling
tool graph MyService
    show reactive dependencies and dynamic branches

tool ownership MyService
    show reactors, task scopes, resources, and transfers

tool queues MyService
    show capacity, occupancy, age, drops, and backpressure

tool trace --input 8492 Region14
    explain which state changed, what recomputed,
    which effects were requested, and why
```

A runtime trace should be able to say that an input entered a particular reactor, updated one authoritative field, recomputed a visible set, emitted a delta, scheduled two tasks, and published a numbered stable version. The semantics become operationally valuable only when they remain inspectable.

### The adoption bar

Semantic elegance is insufficient. A credible server language must arrive with enough practical depth that teams do not spend their time rebuilding basic infrastructure. At minimum, the ecosystem needs:

- **Server foundations** — HTTP/1.1, HTTP/2, WebSockets, TLS, TCP and UDP, files, processes, timers, DNS, JSON, and binary serialization.
- **Data systems** — Database drivers, pools, transactions, migrations, caches, message systems, and clear ownership conventions for borrowed or streamed results.
- **Operations** — Structured logging, tracing, metrics, profiling, panic isolation, supervision, health checks, graceful shutdown, and resource-leak diagnostics.
- **Developer workflow** — Fast builds, a package manager, reproducible dependencies, editor support, formatter, linter, tests, virtual clocks, deterministic event injection, and native deployment.
- **Interoperability** — A stable C ABI, safe wrappers for foreign resources, blocking annotations, thread-safety declarations, and a practical path to existing libraries.
- **Semantic observability** — Graph inspection, turn traces, queue dashboards, cancellation trees, resource ownership views, and explanations for why a signal changed.

### Likely first adopters

The earliest users are likely to be engineers who already build an informal version of this architecture inside another language: a custom actor runtime, event streams, immutable models, task scheduling, subscriptions, effect queues, backpressure conventions, and ownership rules held together by discipline.

That points toward multiplayer server engineers, infrastructure-controller authors, compiler and build-tool developers, collaborative-application teams, workflow-engine authors, IoT platform engineers, real-time backend developers, and teams maintaining internal event-processing frameworks. The language's strongest promise to them is not novelty for its own sake:

> **Adoption argument**
>
> Stop rebuilding a partial, unenforced version of this architecture inside every sufficiently complicated server. Make coherent state, owned authority, bounded work, structured effects, and temporal observability the default execution model.

---

## 13 · Novelty and related work

### A plausible novel synthesis, not a claim of isolated invention

None of the ingredients is unprecedented. FRP has a long history of behaviors, events, and temporal composition.[^1] ReactiveML integrates a synchronous reactive model directly into an ML-like language.[^3] REScala has explored transactional, thread-safe reactive propagation with strong consistency guarantees.[^5] Stella separates imperative actors from pure reactors.[^4] Lingua Franca develops deterministic reactor-oriented coordination.[^6] Verona investigates concurrent ownership,[^7] Pony co-designs actors, reference capabilities, and collection,[^8] and Koka explores typed effects and handlers.[^9]

The possible novelty lies in treating these concerns as one server-oriented semantic system:

> **Proposed contribution**
>
> Ownership does not merely control memory. It identifies the reactive consistency boundary, the unit of serialized mutation, the domain of local graph reclamation, and the permitted forms of parallel communication. Effects are structurally excluded from propagation and launched only after a stable turn. Streaming and queue pressure are first-class rather than library conventions.

### What distinguishes the proposal

| Area | Common approach | Proposed approach |
|---|---|---|
| FRP and I/O | Effects occur inside subscriptions or callbacks. | Turn propagation is pure; effect requests start after stabilization. |
| Concurrency | Shared state, arbitrary threads, or purely actor-style messages. | Structured tasks for procedures; reactors for temporal state; owned communication between them. |
| Memory | One tracing heap or uniform lexical ownership. | Ownership for values and resources; local arenas for dynamic reactive topology. |
| Streaming | Events and byte streams share one abstraction. | Backpressured flows are distinct from logical reactor events. |
| Scheduling | Flattening and cancellation policy hidden in operators. | `serial`, `parallel`, `latest`, and `keyed` are explicit semantics. |
| Macros | Token-level code generation may hide runtime behavior. | Core reactivity is built in; ecosystem macros are typed, sandboxed, and graph-visible. |

### What would make the novelty credible

A compelling language contribution requires more than a feature list. A small formal core should establish at least:

1. **Memory safety:** no invalid borrow, use-after-free, double close, or use of a transferred resource.
2. **Data-race freedom:** mutable reactor-owned state cannot be accessed concurrently.
3. **Glitch freedom:** reactive expressions observe coherent graph states.
4. **Turn determinism:** the same state and ordered input produce the same stable state and effect descriptions.
5. **Effect isolation:** external I/O cannot occur during partial propagation.
6. **Structured cleanup:** leaving a scope cancels descendants and releases affine resources.
7. **Causality:** every feedback cycle crosses an explicit temporal boundary.
8. **Queue accountability:** each asynchronous boundary has a finite or demand-driven storage policy.

A systematic literature review may reveal a closer precedent than those identified here. The responsible claim is therefore that this is a **plausibly novel synthesis with a clear research thesis**, not that every mechanism is new.

---

## 14 · Open design questions

### The unresolved tensions are the interesting part

**How strict should pure turns be?**

Forbidding suspension and I/O is straightforward. Forbidding all potentially long computation is harder. A compiler cannot generally prove a function finishes quickly. Options include requiring total functions in signal expressions, using cost annotations, imposing cooperative budgets, or accepting that "non-blocking" is partly a discipline enforced by tooling and runtime warnings.

*v0 answers this with a theorem rather than a discipline, and only because it can.* The subset has no `while`, no `for`, and no `loop`, so recursion is the only way a pure function can fail to return; one pass over the call graph reachable from a node body rejects it, and every turn is then provably terminating with no annotation burden and no runtime budget. The answer expires the day loops arrive, and should be replaced rather than extended when they do — at which point the options above become live again.

**What is the exact relationship between state and signals?**

One model exposes explicit reactor state and treats signals as derived views. Another permits stateful signal operators such as `scan` throughout the graph. The latter is expressive but can make durable snapshotting and schema evolution harder. A practical language may distinguish durable state cells from ephemeral graph state.

**Can a reactor turn use parallel cores?**

Independent pure subgraphs can theoretically recompute in parallel while preserving deterministic results. The initial runtime should likely execute a turn serially for clarity, then add compiler-scheduled parallel propagation after profiling demonstrates value. Cross-reactor parallelism already offers a simpler source of scale.

**How should exported signals be observed?**

`latest()` can return an immutable published snapshot without entering the reactor. Stronger reads may need a message and response to ensure ordering relative to prior sends. The language should distinguish stale-tolerant observation from synchronized queries rather than leave that difference implicit. v0 implements the stale-tolerant half only: `latest` reads the last published snapshot, and the synchronized read remains open.

**How much of ownership should users see?**

Rust demonstrates the power and cost of explicit ownership. This language could simplify common server code through task-local regions, immutable-by-default records, move inference, and constrained reactor boundaries. The danger is either producing Rust-level complexity plus FRP complexity, or hiding so much that performance and lifetime become mysterious.

**What is durable?**

Serializing a live graph with closures and sources is undesirable. A reactor should expose an application-defined durable state projection, and the runtime should rebuild ephemeral graph structure after recovery. Whether event sourcing, snapshots, or external databases are standard patterns rather than core semantics remains open.

**How are time and clocks represented?**

Wall-clock time, monotonic time, timers, and logical reactor sequence are distinct. The first version should avoid pretending they are one universal signal. Timers create inputs; monotonic durations support deadlines; a reactor's turn number supports ordering and tracing. Typed clock domains could be a later extension.

**How does foreign code participate?**

FFI calls need declarations covering blocking behavior, thread safety, ownership transfer, callbacks, and effect capabilities. Safe wrappers must make foreign resources affine and route callbacks through task or reactor inputs rather than permit arbitrary graph mutation.

---

## 15 · Implementation and evaluation path

### Prove the semantic center before building the ecosystem

**Phase 1: executable reference semantics.** Build a small interpreter with ordinary immutable values, tasks, events, signals, stateful operators, one reactor, and a deterministic turn trace. The aim is to settle propagation, causality, dynamic switching, effect requests, and cancellation—not performance.

**Phase 2: minimal native server runtime.** Add ahead-of-time compilation, an M:N task scheduler, timers, TCP, HTTP, files, flows, structured scopes, and affine resources. Keep ownership conservative: move-only resources, immutable sharing, and reactor isolation before a sophisticated borrow checker.

**Phase 3: ownership and local graph reclamation.** Introduce borrowing, task-local regions, cross-reactor transfer rules, and reactor-local graph arenas. Measure the cost of reference counting, region promotion, dynamic graph switching, and local tracing.

**Phase 4: effects, persistence patterns, and tooling.** Add capability inference, test handlers, graph visualization, turn tracing, queue inspection, and application-defined durable snapshots. Develop standard patterns for transactional outboxes and replay without making them magical.

**Phase 5: constrained metaprogramming.** Begin with derives and HTTP/schema generation. Add hygienic syntax and typed procedural macros only after the semantic APIs they manipulate are stable.

### Evaluation criteria

| Criterion | What to measure |
|---|---|
| **Correctness** | Property tests for glitch freedom, deterministic turns, cancellation cleanup, queue bounds, and dynamic subgraph disposal. |
| **Performance** | Throughput, tail latency, task scheduling cost, cross-reactor message cost, propagation cost, and memory overhead. |
| **Predictability** | Pause distributions, maximum mailbox memory, resource lifetime traces, and behavior under overload. |
| **Ergonomics** | Code size, diagnostic quality, learning studies, and comparison with idiomatic Go, Rust async, and library-based reactive implementations. |
| **Toolability** | Whether developers can explain why a signal changed, which input caused it, which effects followed, and where values are retained. |
| **Expressiveness** | HTTP services, caches, configuration, streaming proxies, background workers, stateful protocols, and dynamic subscriptions without escape hatches. |

### Representative benchmark applications

A useful evaluation suite would include a static-file and reverse-proxy server; a configuration-driven API gateway; a multi-tenant cache with keyed serialization; a websocket collaboration service; a streaming log processor; a durable job coordinator; and a partitioned voxel-world server. Together these test different mixtures of I/O, reactive state, dynamic topology, backpressure, ownership transfer, fixed-step simulation, spatial partitioning, and overload.

---

## Conclusion

### A language organized around stable turns and owned boundaries

The most promising version of this idea is not a language in which everything is a signal. It is a language that recognizes several distinct forms of time and work, and gives each one precise semantics.

Tasks describe finite, effectful procedures. Flows transfer sequences under demand. Events represent discrete occurrences. Signals represent current temporal values. Reactors own mutable temporal state and process each input as an atomic stabilization. Ownership controls values and resources; isolation controls parallel mutation; local arenas manage dynamic graph topology; bounded queues make pressure visible; effect capabilities describe authority; and typed macros eventually remove ecosystem boilerplate without defining the language's reactive semantics.

The design's strongest thesis is that these mechanisms should not be independent features. They should be co-designed so that one boundary—the owned reactor—simultaneously explains consistency, concurrency, effects, cleanup, observability, and memory reclamation.

This is plausibly a new and useful language design space. Its value would not come from combining fashionable features, but from making server programs easier to reason about at the exact points where current systems become confusing: state propagation, asynchronous completion, cancellation, ownership, and overload.

*The language remains intentionally unnamed. The next useful artifact is not branding or a full grammar, but a small executable semantics that can demonstrate one reactor, one task runtime, one ownership boundary, and one honest HTTP service.*

---

## Selected references

### Prior work informing the proposal

[^1]: Conal Elliott and Paul Hudak. "Functional Reactive Animation." ICFP 1997. [Project page and paper](https://conal.net/papers/icfp97/).

[^2]: ReactiveX. "ReactiveX: An API for asynchronous programming with observable streams." [Official introduction](https://reactivex.io/intro.html).

[^3]: ReactiveML. "ReactiveML Manual." The project describes a synchronous reactive model integrated at the language level. [Official documentation](https://reactiveml.github.io/documentation.html).

[^4]: Sam Van den Vonder, Thierry Renaux, Bjarno Oeyen, Joeri De Koster, and Wolfgang De Meuter. "Tackling the Awkward Squad for Reactive Programming: The Actor–Reactor Model." ECOOP 2020. [Paper](https://soft.vub.ac.be/~svdvonde/papers/ecoop2020-tackling-the-awkward-squad-the-actor-reactor-model.pdf).

[^5]: Joscha Drechsler, Ragnar Mogk, Guido Salvaneschi, and Mira Mezini. "Thread-Safe Reactive Programming." OOPSLA 2018. [REScala project and publication summary](https://programming-group.com/projects/rescala).

[^6]: Lingua Franca. Reactor-oriented coordination for deterministic concurrent and time-sensitive systems. [Official project site](https://www.lf-lang.org/).

[^7]: Project Verona. Research programming language for concurrent ownership. [Official project site](https://microsoft.github.io/verona/).

[^8]: Sylvan Clebsch, Juliana Franco, Sophia Drossopoulou, Albert Mingkun Yang, Tobias Wrigstad, and Jan Vitek. "Orca: GC and Type System Co-Design for Actor Languages." OOPSLA 2017. [Paper](https://www.ponylang.io/media/papers/orca_gc_and_type_system_co-design_for_actor_languages.pdf).

[^9]: Koka. A functional-style language with effect types and handlers. [Official language book](https://koka-lang.github.io/koka/doc/book.html).

[^10]: The Rust Reference. "Macros" and "Procedural Macros." [Official reference](https://doc.rust-lang.org/reference/macros.html).

[^11]: Scala 3 Documentation. "Scala 3 Macros." [Official guide](https://docs.scala-lang.org/scala3/guides/macros/macros.html).
