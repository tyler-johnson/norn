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
/// record may hold a type declared after it.
#[test]
fn declaration_order_does_not_matter() {
    let source = "\
fn first() -> Wrapper {
    #Wrapper(inner: second())
}

fn second() -> I64 {
    7
}

record Wrapper {
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
