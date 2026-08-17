//! The M2 task corpus.
//!
//! Every file in `examples/tasks/` is checked, lowered, and run under the virtual clock with the
//! trace recorded. The snapshot holds the lowered IR, the program's output, and the event trace
//! together, so a lowering change and a scheduling change appear in the same diff — and so that
//! "this program suspends here and is cancelled there" is an assertion rather than a belief.
//!
//! Set `NORN_BLESS=1` to rewrite the snapshots, then read the diff before committing it.

use std::path::{Path, PathBuf};

use norn_nir::{Captured, Config, execute, lower, print};
use norn_syntax::{SourceFile, parse, render_all};

#[test]
fn tasks_run_and_trace() {
    let mut checked = 0;
    for path in norn_files(&tasks_dir()) {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let (nir, main) = build(&path);

        let mut out = Captured::default();
        let outcome = execute(&nir, main, &mut out, Config::deterministic());
        let value = match outcome.value {
            Ok(value) => norn_nir::interp::render(&nir, &value),
            Err(trap) => panic!("{name} trapped: {trap}"),
        };

        let mut snapshot = format!("=== nir ===\n{}", print(&nir));
        snapshot.push_str("=== output ===\n");
        for line in &out.lines {
            snapshot.push_str(line);
            snapshot.push('\n');
        }
        snapshot.push_str(&format!("=== result ===\n{value}\n"));
        snapshot.push_str(&format!("=== trace ===\n{}", outcome.trace));
        check_snapshot(&name, &snapshot);
        checked += 1;
    }
    assert!(checked > 0, "no task examples found");
}

/// The virtual clock is only worth having if it makes a run reproducible, so every example is run
/// twice and its trace compared with itself. This is the property M5's differential oracle extends
/// across two execution engines rather than two runs of one.
#[test]
fn traces_are_reproducible() {
    for path in norn_files(&tasks_dir()) {
        let (nir, main) = build(&path);
        let mut first_out = Captured::default();
        let first = execute(&nir, main, &mut first_out, Config::deterministic());
        let mut second_out = Captured::default();
        let second = execute(&nir, main, &mut second_out, Config::deterministic());
        assert_eq!(
            first.trace,
            second.trace,
            "{} traced differently on a second run",
            path.display()
        );
        assert_eq!(
            first_out.lines,
            second_out.lines,
            "{} printed differently on a second run",
            path.display()
        );
    }
}

/// A scope that never waits still joins: leaving it cancels a child that has not run a single
/// instruction yet. Structured concurrency is about the scope's extent, not about giving every
/// child a turn.
#[test]
fn a_scope_that_awaits_nothing_still_cancels_its_child() {
    let source = "\
task fn child() -> ()
    uses { clock }
{
    await sleep(1000)
}

task fn main() -> ()
    uses { clock }
{
    scope {
        spawn child()
    }
    print(\"the scope waited for nothing\")
}
";
    let parsed = parse(source);
    let checked = norn_hir::check(&parsed.module);
    assert!(
        checked.ok(),
        "{}",
        render_all(&SourceFile::new("test", source), &checked.errors)
    );
    let nir = lower(&checked.program);
    let mut out = Captured::default();
    let outcome = execute(
        &nir,
        checked.program.main.unwrap().index(),
        &mut out,
        Config::deterministic(),
    );
    // The scope has nothing to wait for, so it cancels the child at once and the program finishes.
    assert!(outcome.value.is_ok(), "the scope should not have blocked");
    assert_eq!(out.lines, vec!["the scope waited for nothing".to_string()]);
    assert!(
        outcome.trace.contains("t1 cancel"),
        "the child should have been cancelled:\n{}",
        outcome.trace
    );
}

fn build(path: &Path) -> (norn_nir::Program, usize) {
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    let text = std::fs::read_to_string(path).unwrap();
    let file = SourceFile::new(&name, text.clone());

    let parsed = parse(&text);
    assert!(
        parsed.ok(),
        "{name} failed to parse:\n{}",
        render_all(&file, &parsed.errors)
    );
    let checked = norn_hir::check(&parsed.module);
    assert!(
        checked.ok(),
        "{name} failed to check:\n{}",
        render_all(&file, &checked.errors)
    );
    let main = checked
        .program
        .main
        .unwrap_or_else(|| panic!("{name} has no `main`"));
    (lower(&checked.program), main.index())
}

fn tasks_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/tasks")
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
