//! Snapshots of what the checker says when a program is wrong.
//!
//! Every file in `examples/type-errors/`, `examples/reactor-errors/`, and
//! `examples/ownership-errors/` must parse cleanly and then fail to check, so that each snapshot is
//! a type diagnostic rather than a syntax one. The point is not that these programs are rejected —
//! it is that the wording stays deliberate.

use std::path::{Path, PathBuf};

use norn_syntax::{SourceFile, parse, render_all};

#[test]
fn type_errors_are_reported() {
    rejected("type-errors");
}

/// The reactor rules, one file per rule. `cycle.norn` is the one worth reading first: it is the
/// working example with a single token changed, which makes the diagnostic and the fix the same
/// artifact.
#[test]
fn reactor_errors_are_reported() {
    rejected("reactor-errors");
}

/// The ownership rules. Ordinary values copy; only affine values — resources, tasks, and
/// aggregates reaching one — move, so these snapshots are mostly about whether the wording tells
/// you where the value went and how to keep it.
#[test]
fn ownership_errors_are_reported() {
    rejected("ownership-errors");
}

fn rejected(directory: &str) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(directory);
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|err| panic!("reading {}: {err}", dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "norn"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no examples found in {directory}");

    for path in files {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).unwrap();
        let file = SourceFile::new(&name, text.clone());

        let parsed = parse(&text);
        assert!(
            parsed.ok(),
            "{name} must be syntactically valid so the snapshot shows a type error:\n{}",
            render_all(&file, &parsed.errors)
        );
        let checked = norn_hir::check(&parsed.module);
        assert!(!checked.ok(), "{name} checked cleanly but should not have");
        check_snapshot(&name, &render_all(&file, &checked.errors));
    }
}

/// Checking must not depend on declaration order: a function may call one declared later, and a
/// struct may hold a type declared after it.
#[test]
fn declaration_order_does_not_matter() {
    let source = "\
fn first() -> Wrapper {
    Wrapper(inner: second())
}

fn second() -> I64 {
    7
}

struct Wrapper {
    inner: I64
}
";
    let parsed = parse(source);
    assert!(parsed.ok());
    let checked = norn_hir::check(&parsed.module);
    assert!(
        checked.ok(),
        "{}",
        render_all(&SourceFile::new("test", source), &checked.errors)
    );
}

/// The three ways a name survives something that looks like a move. Each is a line of `check_moves`
/// that would be invisible if only the rejections were tested: an error corpus cannot show that a
/// correct program is still accepted, and these are the programs most likely to be rejected by
/// accident.
#[test]
fn a_name_survives_what_only_looks_like_a_move() {
    // A branch that leaves the function cannot reach the code after the `if`, so what it moved is
    // not moved there. Without that, every `?` before a close would poison the close.
    accepted(
        "a diverging branch moves nothing downstream",
        "\
task fn main(conn: Connection, bad: Bool) -> () {
    if bad {
        await tcp_close(conn)
        return ()
    }
    await tcp_close(conn)
}
",
    );

    // Assigning a whole name gives it something to own again.
    accepted(
        "reassignment revives a name",
        "\
task fn main(first: Connection, second: Connection) -> () {
    let mut held = first
    await tcp_close(held)
    held = second
    await tcp_close(held)
}
",
    );

    // A pattern takes an aggregate apart. The scrutinee moves whole and the pieces are named, which
    // is the answer the move-out-of-a-field diagnostic points at.
    accepted(
        "a match binding owns the piece it named",
        "\
struct Session {
    conn: Connection
    opened: I64
}

task fn main(session: Session) -> () {
    match session {
        Session(conn: conn, opened: _) => await tcp_close(conn)
    }
}
",
    );

    // Single ownership applies to whole values: a field read copies, however often.
    accepted(
        "a field read copies",
        "\
struct Point {
    x: I64
    y: I64
}

fn main() -> I64 {
    let p = Point(x: 1, y: 2)
    p.x + p.x + p.y
}
",
    );

    // An ordinary value copies, so a match is not its last use and neither is a call.
    accepted(
        "a match on a copyable is not a move",
        "\
enum Journal {
    Empty
    Entry(I64)
}

fn consume(journal: Journal) -> I64 {
    match journal {
        Journal.Empty => 0
        Journal.Entry(seq) => seq
    }
}

fn main() -> I64 {
    let journal = Journal.Entry(7)
    match journal {
        Journal.Empty => 0
        Journal.Entry(seq) => seq
    }
    consume(journal)
}
",
    );

    // The assign-revive idiom, on an ordinary value, in a loop: the name owns again at the
    // bottom of every pass, so the back edge finds nothing missing.
    accepted(
        "a list is rebuilt into its own name inside a loop",
        "\
enum List {
    Nil
    Cons(I64, List)
}

fn main() -> () {
    let mut items = List.Nil
    let mut n = 0
    while n < 3 {
        items = List.Cons(n, items)
        n = n + 1
    }
    print(items)
}
",
    );

    // A `Self` method reads its receiver, so calling it is not a use the next line pays for.
    accepted(
        "a `Self` method leaves its receiver owned",
        "\
trait Describe {
    fn describe(value: Self) -> String
}

struct Config {
    host: String
}

impl Describe for Config {
    fn describe(value: Self) -> String {
        value.host
    }
}

fn main() -> () {
    let config = Config(host: \"localhost\")
    print(config.describe())
    print(config.describe())
}
",
    );

    // Printing reads — the documented answer to `print(p); print(p)` is that it was never a
    // question: reads are unmarked, and take nothing.
    accepted(
        "printing reads, however often",
        "\
struct Point {
    x: I64
    y: I64
}

fn main() -> () {
    let p = Point(x: 1, y: 2)
    print(p)
    print(p)
    print(p)
}
",
    );
}

/// The `Slots` spelling (BOOTSTRAP §8 item 5): a copyable slab, legal wherever plain data is —
/// parameters, returns, and a template's own fields, where the element is a bare parameter.
#[test]
fn slots_is_plain_data() {
    accepted(
        "a slab passes, returns, and copies",
        "\
fn pass_along(s: Slots<I64>) -> Slots<I64> {
    let kept = s
    print(kept)
    return s
}

fn main() -> () {
}
",
    );

    accepted(
        "a template holds a slab of its own parameter",
        "\
struct Buffer<T> {
    storage: Slots<T>
    len: I64
}

fn occupancy(buf: Buffer<I64>) -> I64 {
    buf.len
}

fn main() -> () {
}
",
    );
}

/// The slots builtins' legal surface: a slab built from the expectation, read anywhere, and
/// written through a `Mut` position — including a field chain rooted at a `mut` parameter, the
/// shape `std/buf`'s `push` is made of.
#[test]
fn slots_builtins_check() {
    accepted(
        "the whole surface on a local slab",
        "\
fn main() -> () {
    let mut s: Slots<I64> = slots_new(4)
    slots_set(s, 0, 7)
    print(slots_len(s))
    match slots_get(s, 0) {
        Some(v) => print(v)
        None => print(0)
    }
    match slots_take(s, 0) {
        Some(v) => print(v)
        None => print(0)
    }
}
",
    );

    accepted(
        "a write op reaches through a mut parameter's field",
        "\
struct Buffer {
    storage: Slots<I64>
    len: I64
}

fn push(buf: mut Buffer, value: I64) -> () {
    let at = buf.len
    slots_set(buf.storage, at, value)
    buf = Buffer(storage: buf.storage, len: at + 1)
}

fn main() -> () {
    let mut buf = Buffer(storage: slots_new(4), len: 0)
    push(buf, 7)
    print(buf.len)
}
",
    );

    accepted(
        "a template builds its own slab",
        "\
struct Buffer<T> {
    storage: Slots<T>
    len: I64
}

fn empty<T>() -> Buffer<T> {
    let storage: Slots<T> = slots_new(0)
    return Buffer(storage: storage, len: 0)
}

fn main() -> () {
    let buf: Buffer<I64> = empty()
    print(buf.len)
}
",
    );
}

/// The read half of the modes doctrine (BOOTSTRAP §8 item 5): field access and `match` on an
/// owned value, spelled plainly, because reads are unmarked and an ordinary value copies.
#[test]
fn a_read_is_unmarked() {
    // A parameter is a read: matching an ordinary value in it costs the caller nothing.
    accepted(
        "a match in a read parameter takes nothing from the caller",
        "\
enum Verdict {
    Pass
    Fail(String)
}

fn describe(verdict: Verdict) -> String {
    match verdict {
        Verdict.Pass => \"pass\"
        Verdict.Fail(reason) => reason
    }
}

fn main() -> () {
    let verdict = Verdict.Fail(\"missing\")
    print(describe(verdict))
    print(describe(verdict))
}
",
    );

    // Deconstructing an *affine* value is a consuming use, so a parameter that matches one
    // infers `sink` — per instance, which is what closes the old template-time-only gap — and
    // the caller hands the value over.
    accepted(
        "a match on an affine parameter flips it to sink",
        "\
enum Carrier {
    Empty
    Wrapped(Connection)
}

task fn close_carried(carrier: Carrier) -> () {
    match carrier {
        Carrier.Empty => ()
        Carrier.Wrapped(conn) => await tcp_close(conn)
    }
}

task fn main(carrier: Carrier) -> () {
    await close_carried(carrier)
}
",
    );

    // A scalar keeps the scalar's rule wherever it sits: a catch-all arm is what completes it.
    accepted(
        "a match on an owned scalar keeps the catch-all rule",
        "\
fn describe(n: I64) -> String {
    match n {
        0 => \"zero\"
        _ => \"nonzero\"
    }
}
",
    );

    // A field read in a read parameter: two calls on one value, nothing marked anywhere.
    accepted(
        "a field read in a read parameter takes nothing",
        "\
struct Config {
    host: String
    port: I64
}

fn port(config: Config) -> I64 {
    config.port
}

fn main() -> () {
    let config = Config(host: \"localhost\", port: 80)
    print(port(config))
    print(port(config))
}
",
    );
}

/// Receivers read by default: a `Self` method leaves its receiver with the caller, through the
/// concrete path and the bounded-generic stub path alike.
#[test]
fn a_receiver_reads_by_default() {
    accepted(
        "a `Self` method is declared, implemented, and called twice",
        "\
trait Describe {
    fn describe(value: Self) -> String
}

struct Config {
    host: String
}

impl Describe for Config {
    fn describe(value: Self) -> String {
        value.host
    }
}

fn show<T: Describe>(x: T) -> String {
    x.describe()
}

fn main() -> () {
    let config = Config(host: \"localhost\")
    print(config.describe())
    print(config.describe())
    print(show(config))
}
",
    );
}

/// Parameter modes (BOOTSTRAP §8 item 5): reads are unmarked, `sink` consumes, and the mode is
/// inferred from the body where it is not written. Pinned inline ahead of the corpus migration —
/// the corpus is still `&`-spelled, and these are the spellings that replace it.
#[test]
fn modes_make_reads_unmarked() {
    // The headline ergonomic win: an owned affine argument at a read-mode position survives the
    // call, so a resource can be handed to a reader without `&` and still be closed afterwards.
    accepted(
        "an owned resource passed to a reader is still owned after the call",
        "\
task fn watch(conn: Connection) -> () {
    let data = await tcp_read(conn)
    ()
}

task fn main(conn: Connection) -> () {
    await watch(conn)
    await tcp_close(conn)
}
",
    );

    // Sink inference propagates through calls: `wrap` never touches a socket builtin, but it
    // hands the connection to `close_it`, which closes — two hops from the consumption fact.
    accepted(
        "sink inference reaches through a two-hop chain",
        "\
task fn close_it(conn: Connection) -> () {
    await tcp_close(conn)
}

task fn wrap(conn: Connection) -> () {
    await close_it(conn)
}

task fn main(conn: Connection) -> () {
    await wrap(conn)
}
",
    );

    // `sink Self`: the trait declares the consuming receiver, the impl spells the same mode,
    // and a call site hands the receiver over.
    accepted(
        "a `sink Self` method is declared, implemented, and called",
        "\
trait Consume {
    fn finish(value: sink Self) -> I64
}

struct Job {
    id: I64
}

impl Consume for Job {
    fn finish(value: sink Self) -> I64 {
        value.id
    }
}

fn main() -> () {
    let job = Job(id: 1)
    print(job.finish())
}
",
    );
}

/// The `mut` wave's declaration half: a `mut` parameter is assignable in its own body — the
/// callee's copy is what the writeback returns — and the mode column copies through generic
/// instantiation like any written mode. Call-site enforcement is the wave's next commit.
#[test]
fn mut_parameters_are_declared() {
    accepted(
        "a `mut` parameter is assignable in its body",
        "\
fn bump(count: mut I64) -> () {
    count = count + 1
}

fn main() -> () {
    let mut total = 0
    bump(total)
    print(total)
}
",
    );

    accepted(
        "a generic template declares `mut` and instantiates",
        "\
fn reset<T>(slot: mut T, value: T) -> () {
    slot = value
}

fn main() -> () {
    let mut n = 3
    reset(n, 0)
    print(n)
}
",
    );
}

/// The call-site half: a `mut` argument is a place — a `mut` variable or a chain of its fields —
/// a `mut` parameter forwards, and exclusivity only bites when the call writes the repeated root.
#[test]
fn mut_arguments_are_places() {
    accepted(
        "a field chain rooted at a `mut` variable is a writeback home",
        "\
struct Point {
    x: I64
    y: I64
}

fn bump(count: mut I64) -> () {
    count = count + 1
}

fn main() -> () {
    let mut point = Point(x: 1, y: 2)
    bump(point.x)
    print(point.x)
}
",
    );

    accepted(
        "a `mut` parameter forwards at a `mut` position",
        "\
fn bump(count: mut I64) -> () {
    count = count + 1
}

fn twice(count: mut I64) -> () {
    bump(count)
    bump(count)
}

fn main() -> () {
    let mut total = 0
    twice(total)
    print(total)
}
",
    );

    accepted(
        "the same root at two read positions is not aliasing a call can act on",
        "\
fn add(a: I64, b: I64) -> I64 {
    a + b
}

fn main() -> () {
    let n = 21
    print(add(n, n))
}
",
    );
}

/// Generic *types* land ahead of the corpus that dogfoods them — std/list and the run example
/// arrive later in the item 7 wave — so the acceptance side is pinned here: instantiation by
/// annotation, by expectation, by field inference, through patterns, and inside reactor state.
#[test]
fn generic_types_are_accepted() {
    accepted(
        "a cons list instantiates, grows, and matches",
        "\
enum List<T> {
    Nil
    Cons(T, List<T>)
}

fn main() {
    let mut items: List<I64> = List.Nil
    items = List.Cons(1, items)
    match items {
        List.Nil => print(\"empty\")
        List.Cons(head, _) => print(head)
    }
}
",
    );

    // No annotation anywhere: the second field's synthesised type is what settles `B`.
    accepted(
        "field inference settles a template's parameters",
        "\
struct Pair<A, B> {
    first: A
    second: B
}

fn main() {
    let pair = Pair(first: 1, second: \"x\")
    print(pair.second)
}
",
    );

    // A self-referential nesting: `Tree<I64>` needs `List<Tree<I64>>`, which needs `Tree<I64>`
    // again — the two-phase register-then-fill is what lets this converge.
    accepted(
        "a self-referential instance dedups to itself",
        "\
enum List<T> {
    Nil
    Cons(T, List<T>)
}

struct Tree<T> {
    value: T
    children: List<Tree<T>>
}

fn main() {
    let tree = Tree(value: 7, children: List.Nil)
    print(tree.value)
}
",
    );

    // A generic calling a generic at a type built from its own parameter: the inner call is a
    // symbolic instance inside the template, resolved per-instance during monomorphization.
    accepted(
        "generics calling generics compose through instances",
        "\
enum List<T> {
    Nil
    Cons(T, List<T>)
}

fn prepend<T>(value: T, rest: List<T>) -> List<T> {
    List.Cons(value, rest)
}

fn double_wrap<T>(value: T) -> List<List<T>> {
    prepend(prepend(value, List.Nil), List.Nil)
}

fn main() {
    match double_wrap(3) {
        List.Cons(inner, _) => match inner {
            List.Cons(value, _) => print(value)
            List.Nil => print(\"empty\")
        }
        List.Nil => print(\"empty\")
    }
}
",
    );

    // The `state journal: List<Delta>` shape: the member's type resolves after the fill drain,
    // so the eager affinity question `reactor_ty` asks sees real fields.
    accepted(
        "reactor state holds a generic instance",
        "\
enum List<T> {
    Nil
    Cons(T, List<T>)
}

reactor Journal() {
    state journal: List<I64> = List.Nil

    on record(entry: I64) [capacity: 4, overflow: reject] {
        journal = List.Cons(entry, journal)
    }

    export signal history = journal
}
",
    );
}

/// Bounds open capabilities on an opaque `T`: `==` through the seeded `Eq`, a method through a
/// declared trait, and both together — including the propagation rule, where a template
/// satisfies a callee's bound by declaring it rather than by anything concrete.
#[test]
fn bounds_open_capabilities() {
    accepted(
        "Eq and Display bounds compose, and propagate by declaration",
        "\
trait Display {
    fn to_string(value: Self) -> String
}

impl Display for I64 {
    fn to_string(value: Self) -> String {
        \"int\"
    }
}

impl Display for Bool {
    fn to_string(value: Self) -> String {
        \"bool\"
    }
}

fn describe<T: Eq + Display>(value: T, fallback: T) -> String {
    if value == fallback {
        \"fallback\"
    } else {
        value.to_string()
    }
}

fn shout<T: Eq + Display>(value: T, fallback: T) -> String {
    describe(value, fallback) + \"!\"
}

fn main() {
    print(describe(7, 0))
    print(shout(true, false))
}
",
    );
}

/// Traits land mid-wave, ahead of std/list's `join<T: Display>` dogfood, so the acceptance side
/// is pinned here: both call spellings, conformance through `Self`, and a method beside a free
/// function of the same name.
#[test]
fn trait_methods_resolve() {
    // The dotted-path spelling (`p.to_string()`) and the field-callee spelling
    // (`p.x.to_string()` — the receiver is itself a projection) resolve through one resolver.
    // The impl's `to_string` delegating to the free `to_string` is not a recursion, because an
    // impl's functions live in no namespace.
    accepted(
        "both method spellings resolve, beside a free function of the same name",
        "\
trait Display {
    fn to_string(value: Self) -> String
}

struct Point {
    x: I64
    y: I64
}

fn to_string(n: I64) -> String {
    \"n\"
}

impl Display for Point {
    fn to_string(value: Self) -> String {
        \"(\" + to_string(value.x) + \", \" + value.y.to_string() + \")\"
    }
}

impl Display for I64 {
    fn to_string(value: Self) -> String {
        to_string(value)
    }
}

fn main() {
    let p = Point(x: 3, y: 4)
    print(p.to_string())
    print(42.to_string())
}
",
    );

    // A method with parameters beyond the receiver: the rewrite prepends the receiver and the
    // written arguments fill the rest, named or positional.
    accepted(
        "a method takes arguments after its receiver",
        "\
trait Scale {
    fn scaled(value: Self, factor: I64) -> I64
}

impl Scale for I64 {
    fn scaled(value: Self, factor: I64) -> I64 {
        value * factor
    }
}

fn main() {
    print(6.scaled(7))
    print(6.scaled(factor: 7))
}
",
    );
}

fn accepted(what: &str, source: &str) {
    let parsed = parse(source);
    assert!(parsed.ok(), "{what}: did not parse");
    let checked = norn_hir::check(&parsed.module);
    assert!(
        checked.ok(),
        "{what}:\n{}",
        render_all(&SourceFile::new("test", source), &checked.errors)
    );
}

/// A diagnostic should say what is wrong once, not once per expression that touched the bad value.
#[test]
fn capabilities_are_inferred() {
    // The everyday spelling: nothing is written, and the authority a body reaches is worked out.
    accepted(
        "a task fn needs no clause to call a builtin that wants authority",
        "\
task fn main() -> () {
    await sleep(1)
}
",
    );

    // Inference reaches through calls, which is the whole reason the clause was ceremony: only
    // `nap` touches a builtin, and `main` two hops up gets the capability all the same.
    accepted(
        "capabilities propagate up a call chain",
        "\
task fn nap() -> () {
    await sleep(1)
}

task fn wrap() -> () {
    await nap()
}

task fn main() -> () {
    await wrap()
}
",
    );

    // A written clause is an assertion, and one that matches the inferred set is simply true.
    accepted(
        "a written clause that matches the body is accepted",
        "\
task fn main() -> ()
    uses { clock }
{
    await sleep(1)
}
",
    );

    // The empty clause is a real spelling — the assertion that a task reaches nothing at all.
    accepted(
        "`uses { }` asserts the empty set",
        "\
task fn main() -> ()
    uses { }
{
    print(\"nothing the world needs authority for\")
}
",
    );

    // Recursion is exactly what a fixpoint is for: `drain` reads its own set while computing it,
    // and the sweep that follows sees the growth. No clause has to be written to break the loop.
    accepted(
        "a recursive task fn infers its own set",
        "\
task fn drain(left: I64) -> () {
    if left > 0 {
        await sleep(1)
        await drain(left - 1)
    }
}

task fn main() -> ()
    uses { clock }
{
    await drain(3)
}
",
    );

    // Through a generic instance: the set is a per-instance fact, inferred on the concrete body
    // monomorphization produced, the way a parameter mode is.
    accepted(
        "capabilities reach through a generic instance",
        "\
task fn pause<T>(value: T) -> T {
    await sleep(1)
    value
}

task fn main() -> ()
    uses { clock }
{
    let held = await pause<I64>(7)
    print(held)
}
",
    );

    // Up through a reactor: the handler is where `after` names the task, the reactor's set is its
    // members', and the spawner reaches all of it through the handle.
    accepted(
        "a spawner reaches what the reactor it spawns reaches",
        "\
reactor Beeper(every: I64) {
    input rang: () [capacity: 8, overflow: reject]

    state rings: I64 = 0

    on rang() {
        rings = rings + 1
        after beep(every)
    }

    export signal count = rings
}

task fn beep(every: I64) -> () {
    await sleep(every)
}

task fn main() -> ()
    uses { clock }
{
    scope {
        let beeper = spawn reactor Beeper(every: 10)
        await send(beeper.rang, ())
    }
}
",
    );
}

/// Rejection, inline: the program must fail to check and the first thing said about it must be
/// the thing under test. Beside `accepted` because half of these rules are only visible from the
/// side that refuses.
fn refused(what: &str, source: &str, needle: &str) {
    let parsed = parse(source);
    assert!(parsed.ok(), "{what}: did not parse");
    let checked = norn_hir::check(&parsed.module);
    assert!(!checked.ok(), "{what}: checked cleanly");
    let rendered = render_all(&SourceFile::new("test", source), &checked.errors);
    assert!(
        rendered.contains(needle),
        "{what}: no diagnostic said {needle:?}\n{rendered}"
    );
}

/// Traits over reactor handles, and `task` members. Two halves of one wave because each is the
/// other's first consumer: a handle abstraction that cannot `send` teaches a model the language
/// does not have.
#[test]
fn traits_carry_tasks_and_reactors() {
    // A `task` member, implemented and awaited. The receiver reads, so `bed` survives the call.
    accepted(
        "a trait member may be a task",
        "\
trait Rest {
    task fn rest(value: Self) -> ()
}

struct Bed {
    size: I64
}

impl Rest for Bed {
    task fn rest(value: Self) -> () {
        await sleep(value.size)
    }
}

task fn main() -> ()
    uses { clock }
{
    let bed = Bed(size: 1)
    await bed.rest()
    print(bed.size)
}
",
    );

    // The capability crosses the impl with no new code: `mono_callee` rewrites the stub to the
    // method that runs, so the instance body carries a real edge and the fixpoint walks it.
    accepted(
        "a task method's capability reaches its caller through a bound",
        "\
trait Rest {
    task fn rest(value: Self) -> ()
}

struct Bed {
    size: I64
}

impl Rest for Bed {
    task fn rest(value: Self) -> () {
        await sleep(value.size)
    }
}

task fn nap<T: Rest>(value: T) -> () {
    await value.rest()
}

task fn main() -> ()
    uses { clock }
{
    await nap(Bed(size: 1))
}
",
    );

    // And the assertion is held to it, transitively — the half that would be silent if the set
    // stopped at the trait's bodiless signature.
    refused(
        "an empty clause cannot cover a task method that sleeps",
        "\
trait Rest {
    task fn rest(value: Self) -> ()
}

struct Bed {
    size: I64
}

impl Rest for Bed {
    task fn rest(value: Self) -> () {
        await sleep(value.size)
    }
}

task fn main() -> ()
    uses { }
{
    let bed = Bed(size: 1)
    await bed.rest()
}
",
        "`main` does not declare the capability `clock`",
    );

    // The receiver the whitelist used to drop: a handle is an ordinary value, and an impl on one
    // reaches exactly the inputs and exported signals any other holder does.
    accepted(
        "a reactor handle implements a trait",
        "\
trait Health {
    fn ok(handle: Self) -> Bool
}

reactor Gate(limit: I64) {
    input opened: () [capacity: 4, overflow: reject]

    state accepted: I64 = 0

    on opened() {
        accepted = accepted + 1
    }

    export signal healthy = accepted <= limit
}

impl Health for Gate {
    fn ok(handle: Self) -> Bool {
        latest(handle.healthy)
    }
}

task fn main() -> () {
    let gate = spawn reactor Gate(limit: 2)
    print(gate.ok())
}
",
    );

    // Static polymorphism over two unrelated reactors: one written call, two instances, each
    // resolved to its own impl. A bound is not a type, so nothing here is heterogeneous.
    accepted(
        "one generic call resolves a different reactor impl per instance",
        "\
trait Feed {
    task fn poke(handle: Self) -> ()
}

reactor Gate() {
    input opened: () [capacity: 4, overflow: reject]

    state accepted: I64 = 0

    on opened() {
        accepted = accepted + 1
    }

    export signal count = accepted
}

reactor Pump() {
    input filled: () [capacity: 4, overflow: reject]

    state level: I64 = 0

    on filled() {
        level = level + 1
    }

    export signal count = level
}

impl Feed for Gate {
    task fn poke(handle: Self) -> () {
        await send(handle.opened, ())
    }
}

impl Feed for Pump {
    task fn poke(handle: Self) -> () {
        await send(handle.filled, ())
    }
}

task fn drive<T: Feed>(handle: T) -> () {
    await handle.poke()
}

task fn main() -> () {
    let gate = spawn reactor Gate()
    let pump = spawn reactor Pump()
    await drive(gate)
    await drive(pump)
    print(latest(gate.count) + latest(pump.count))
}
",
    );

    // A one-shot handle contract. `sink` is assertive on a copyable value, so the name dies at the
    // call even though a handle is nothing but a number — which is the only way to say "this
    // handle is spent" at all.
    accepted(
        "a `sink Self` method spends a reactor handle",
        "\
trait Shutdown {
    task fn stop(handle: sink Self) -> ()
}

reactor Gate() {
    input closed: () [capacity: 4, overflow: reject]

    state released: I64 = 0

    on closed() {
        released = released + 1
    }

    export signal count = released
}

impl Shutdown for Gate {
    task fn stop(handle: sink Self) -> () {
        await send(handle.closed, ())
    }
}

task fn main() -> () {
    let gate = spawn reactor Gate()
    await gate.stop()
    print(\"spent\")
}
",
    );
}

#[test]
fn one_mistake_reports_once() {
    let source = "\
fn main() -> I64 {
    let value = missing()
    value + value + value
}
";
    let parsed = parse(source);
    let checked = norn_hir::check(&parsed.module);
    assert_eq!(checked.errors.len(), 1, "an unknown name cascaded");
}

fn check_snapshot(name: &str, actual: &str) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/snapshots");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.snap"));

    if std::env::var("NORN_BLESS").is_ok() {
        std::fs::write(&path, actual).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&path).unwrap_or_else(|_| {
        panic!(
            "missing snapshot {}\nrerun with NORN_BLESS=1 to create it\n\n{actual}",
            path.display()
        )
    });
    if expected != actual {
        panic!(
            "snapshot {} does not match\nrerun with NORN_BLESS=1 to update it\n\n--- expected ---\n{expected}\n--- actual ---\n{actual}",
            path.display()
        );
    }
}
