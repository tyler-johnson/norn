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

/// The ownership rules. `&` is one character, and getting it wrong in either direction is one
/// character from correct, so these snapshots are mostly about whether the wording tells you which
/// way the value was going.
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
task fn main(conn: Connection, bad: Bool) -> ()
    uses { net.io }
{
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
task fn main(first: Connection, second: Connection) -> ()
    uses { net.io }
{
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

task fn main(session: Session) -> ()
    uses { net.io }
{
    match session {
        Session(conn: conn, opened: _) => await tcp_close(conn)
    }
}
",
    );
}

/// The read half of borrowing (BOOTSTRAP §8 item 6c): field access and `match` reach through a
/// `&`, and what a pattern binds is an owned copy. Pinned inline because the corpus that dogfoods
/// these lands with the corpus migration, and the rules should hold before it does.
#[test]
fn a_borrow_reads_without_taking() {
    // A borrowed scrutinee with payload bindings: the pattern types against the pointee, and the
    // bindings are owned copies.
    accepted(
        "a match reaches through a borrowed parameter",
        "\
enum Verdict {
    Pass
    Fail(String)
}

fn describe(verdict: &Verdict) -> String {
    match verdict {
        Verdict.Pass => \"pass\"
        Verdict.Fail(reason) => reason
    }
}
",
    );

    // `match &x` on an owned local reads it, so the name is still there afterwards.
    accepted(
        "a match through `&` leaves the value owned",
        "\
enum Verdict {
    Pass
    Fail(String)
}

fn main() -> () {
    let verdict = Verdict.Fail(\"missing\")
    match &verdict {
        Verdict.Pass => print(\"pass\")
        Verdict.Fail(reason) => print(reason)
    }
    match verdict {
        Verdict.Pass => print(\"pass\")
        Verdict.Fail(reason) => print(reason)
    }
}
",
    );

    // One top-level peel is provably enough for nested patterns — a `Ty::Ref` is unspellable in
    // any field — so exhaustiveness still resolves at OPTION under the borrow.
    accepted(
        "a nested pattern under a borrow is exhaustive at the pointee",
        "\
enum List<T> {
    Nil
    Cons(T, List<T>)
}

fn first(maybe: &Option<List<I64>>) -> I64 {
    match maybe {
        Some(List.Cons(head, _)) => head
        Some(List.Nil) => 0
        None => -1
    }
}
",
    );

    // A scalar behind a borrow keeps the scalar's rule: a catch-all arm is what completes it.
    accepted(
        "a match on a borrowed scalar keeps the catch-all rule",
        "\
fn describe(n: &I64) -> String {
    match n {
        0 => \"zero\"
        _ => \"nonzero\"
    }
}
",
    );

    // Field access reads through a borrowed struct.
    accepted(
        "a field read reaches through a borrowed parameter",
        "\
struct Config {
    host: String
    port: I64
}

fn port(config: &Config) -> I64 {
    config.port
}
",
    );
}

/// `&Self` receivers: a trait may declare that a method only reads, the impl spells the same
/// mode, and the call site auto-borrows an owned receiver — so the name survives the call, pinned
/// here ahead of the flip that makes the difference observable. The generic case pins the
/// stub/mono interaction: the stub's identity stays the owned Self while its parameter carries
/// the `Ref`.
#[test]
fn a_borrowed_receiver_leaves_the_value_owned() {
    accepted(
        "a `&Self` method is declared, implemented, and called twice",
        "\
trait Describe {
    fn describe(value: &Self) -> String
}

struct Config {
    host: String
}

impl Describe for Config {
    fn describe(value: &Self) -> String {
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
