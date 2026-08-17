//! The M0 snapshot corpus.
//!
//! Every file in `examples/` must parse cleanly, and every file in `examples/errors/` must not.
//! For each, the s-expression dump and the canonical rendering are compared against a committed
//! snapshot. Set `NORN_BLESS=1` to rewrite the snapshots after an intentional change, then read
//! the diff before committing it.
//!
//! Each clean example is also checked for print idempotence, which is the operative definition of
//! round-tripping for a tree that does not retain comments or layout.

use std::path::{Path, PathBuf};

use norn_syntax::{SourceFile, dump, parse, print, render_all};

#[test]
fn examples_parse_and_round_trip() {
    let mut checked = 0;
    for path in norn_files(&examples_dir()) {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).unwrap();
        let file = SourceFile::new(&name, text.clone());
        let parsed = parse(&text);

        assert!(
            parsed.ok(),
            "{name} failed to parse:\n{}",
            render_all(&file, &parsed.errors)
        );

        let canonical = print::module(&parsed.module);
        let reparsed = parse(&canonical);
        let recanonical = SourceFile::new(format!("{name} (canonical)"), canonical.clone());
        assert!(
            reparsed.ok(),
            "canonical form of {name} failed to parse:\n{}\n--- canonical form ---\n{canonical}",
            render_all(&recanonical, &reparsed.errors)
        );
        assert_eq!(
            canonical,
            print::module(&reparsed.module),
            "printing {name} is not idempotent"
        );
        assert_eq!(
            dump::module(&parsed.module),
            dump::module(&reparsed.module),
            "the canonical form of {name} parses to a different tree"
        );

        let snapshot = format!(
            "=== ast ===\n{}\n=== canonical ===\n{canonical}",
            dump::module(&parsed.module)
        );
        check_snapshot(&name, &snapshot);
        checked += 1;
    }
    assert!(checked > 0, "no examples found");
}

#[test]
fn error_examples_report_diagnostics() {
    let mut checked = 0;
    for path in norn_files(&examples_dir().join("errors")) {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).unwrap();
        let file = SourceFile::new(&name, text.clone());
        let parsed = parse(&text);

        assert!(!parsed.ok(), "errors/{name} parsed cleanly but should not have");
        check_snapshot(&format!("errors-{name}"), &render_all(&file, &parsed.errors));
        checked += 1;
    }
    assert!(checked > 0, "no error examples found");
}

/// The parser must terminate and stay within bounds on arbitrary input, including truncations of
/// valid programs, which is where an unguarded lookahead usually shows up first.
#[test]
fn truncations_do_not_panic() {
    for path in norn_files(&examples_dir()) {
        let text = std::fs::read_to_string(&path).unwrap();
        for end in 0..text.len() {
            if text.is_char_boundary(end) {
                let _ = parse(&text[..end]);
            }
        }
    }
}

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

fn snapshot_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/snapshots")
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
    let dir = snapshot_dir();
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
