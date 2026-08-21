//! The M1 execution corpus.
//!
//! Every file in `examples/run/` must check, lower, and execute. The snapshot holds both the
//! lowered IR and the program's output, so a change to lowering and a change to behaviour are
//! visible in the same diff — which is the pairing M5 will need when a native backend has to
//! produce the same output from the same blocks.
//!
//! Set `NORN_BLESS=1` to rewrite the snapshots, then read the diff before committing it.

mod common;

use std::path::{Path, PathBuf};

use norn_nir::{Captured, lower, print, run};
use norn_syntax::parse;

#[test]
fn programs_lower_and_run() {
    let mut checked = 0;
    for path in norn_files(&run_dir()) {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let (nir, main) = common::build(&path);
        let mut out = Captured::default();
        let value =
            run(&nir, main, &mut out).unwrap_or_else(|trap| panic!("{name} trapped: {trap}"));

        let mut snapshot = format!("=== nir ===\n{}", print(&nir));
        snapshot.push_str("=== output ===\n");
        for line in &out.lines {
            snapshot.push_str(line);
            snapshot.push('\n');
        }
        snapshot.push_str(&format!(
            "=== result ===\n{}\n",
            norn_nir::interp::render(&nir, &value)
        ));
        check_snapshot(&name, &snapshot);
        checked += 1;
    }
    assert!(checked > 0, "no runnable examples found");
}

/// Lowering must be a function of the HIR alone: running the same program twice, and lowering it
/// twice, must give the same blocks and the same output. This is the property the M5 differential
/// test extends across two execution engines rather than two runs of one.
#[test]
fn lowering_and_execution_are_deterministic() {
    for path in norn_files(&run_dir()) {
        let (first, main) = common::build(&path);
        let (second, _) = common::build(&path);
        assert_eq!(
            print(&first),
            print(&second),
            "{} lowered differently",
            path.display()
        );

        let mut a = Captured::default();
        let mut b = Captured::default();
        let one = run(&first, main, &mut a).expect("runs");
        let two = run(&second, main, &mut b).expect("runs");
        assert_eq!(
            a.lines,
            b.lines,
            "{} produced different output",
            path.display()
        );
        assert_eq!(one, two, "{} produced a different result", path.display());
    }
}

/// A gap a pattern leaves inside a constructor is not caught by the top-level exhaustiveness
/// check, so the program must trap rather than fall through silently.
#[test]
fn an_unmatched_value_traps() {
    let source = "\
enum Inner {
    A
    B
}

enum Outer {
    Wrap(Inner)
}

fn pick(value: Outer) -> I64 {
    match value {
        Outer.Wrap(Inner.A) => 1
    }
}

fn main() -> I64 {
    pick(Outer.Wrap(Inner.B))
}
";
    let parsed = parse(source);
    assert!(parsed.ok());
    let checked = norn_hir::check(&parsed.module);
    assert!(checked.ok(), "the nested gap is not a compile error yet");
    let nir = lower(&checked.program);
    let main = checked.program.main.unwrap();
    let mut out = Captured::default();
    let trap = run(&nir, main.index(), &mut out).expect_err("should trap");
    assert_eq!(trap.message, "no match arm applied");
    assert_eq!(trap.function, "pick");
}

/// The `mut` wave's writeback semantics (BOOTSTRAP §8 item 5), inline until the corpus example
/// arrives with the codegen commit: the callee's copy lands in the caller's place when the call
/// returns — a bare local, a nested field chain, forwarding through two frames, a loop — and a
/// copy taken before the call keeps its value, because the writeback copies on write.
#[test]
fn mut_parameters_write_back() {
    let source = "\
struct Point {
    x: I64
    y: I64
}

struct Nested {
    at: Point
}

fn bump(count: mut I64) -> () {
    count = count + 1
}

fn twice(count: mut I64) -> () {
    bump(count)
    bump(count)
}

fn main() -> I64 {
    let mut total = 0
    bump(total)
    twice(total)
    let mut n = 0
    while n < 3 {
        bump(total)
        n = n + 1
    }
    let mut spot = Nested(at: Point(x: 10, y: 20))
    let kept = spot
    bump(spot.at.x)
    total * 10000 + spot.at.x * 100 + kept.at.x
}
";
    let parsed = parse(source);
    assert!(parsed.ok());
    let checked = norn_hir::check(&parsed.module);
    assert!(checked.ok(), "{:?}", checked.errors);
    let nir = lower(&checked.program);
    let printed = print(&nir);
    assert!(printed.contains("mut _"), "no `mut` operand printed:\n{printed}");
    let main = checked.program.main.unwrap();
    let mut out = Captured::default();
    let value = run(&nir, main.index(), &mut out).expect("runs");
    // total 0 → 6 across the calls and the loop; spot.at.x 10 → 11; kept untouched at 10.
    assert_eq!(norn_nir::interp::render(&nir, &value), "61110");
}

#[test]
fn division_by_zero_traps() {
    let source = "fn main() -> I64 {\n    let zero = 0\n    10 / zero\n}\n";
    let parsed = parse(source);
    let checked = norn_hir::check(&parsed.module);
    assert!(checked.ok());
    let nir = lower(&checked.program);
    let mut out = Captured::default();
    let trap = run(&nir, checked.program.main.unwrap().index(), &mut out).expect_err("should trap");
    assert_eq!(trap.message, "divide by zero");
}

fn run_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/run")
}

fn norn_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|err| panic!("reading {}: {err}", dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "norn"))
        .collect();
    files.sort();
    files
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
