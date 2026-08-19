//! `std/flow`'s `pipe` under the interpreter: a file flows into a file, and the trace closes
//! what it opens.
//!
//! The program is written into the test's tmp directory because it needs absolute paths — the
//! same source runs here, under the codegen twin, and inside `norn build`'s cache, and a
//! cwd-relative fixture would mean three different working directories to agree on. The fixture
//! is 10,000 bytes, so the transfer takes three `flow_next` chunks (4096 + 4096 + 1808) — but
//! that shape is now internal to the std loop rather than traced: the per-chunk `pipe` lines
//! died with the `pipe_to` builtin, and what the trace asserts is the eager closes.
//!
//! Mid-pipe cancellation is not testable here: a file-backed flow is always ready, so the whole
//! transfer completes in a single resumption and there is no suspension point to cancel at. That
//! claim is exercised by the HTTP file-server tests, where a request body parks the transfer.

mod common;

use std::path::{Path, PathBuf};

use norn_nir::{Captured, Config, execute};

#[test]
fn a_file_flows_into_a_file() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("pipe-interp");
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join("source.bin");
    let dst = dir.join("copy.bin");
    let fixture: Vec<u8> = (0..10_000u32).map(|i| (i % 251) as u8).collect();
    std::fs::write(&src, &fixture).unwrap();

    let entry = dir.join("pipe.norn");
    std::fs::write(&entry, program(&src, &dst)).unwrap();
    let (nir, main) = common::build(&entry);
    let mut out = Captured::default();
    let outcome = execute(&nir, main, &mut out, Config::deterministic());
    if let Err(trap) = outcome.value {
        panic!("the pipe program trapped: {trap}");
    }

    assert_eq!(out.lines, vec!["10000".to_string()], "{}", outcome.trace);
    assert_eq!(
        std::fs::read(&dst).unwrap(),
        fixture,
        "the copy differs from the source"
    );

    let trace = &outcome.trace;
    let opened = resources(trace, "open");
    let closed = resources(trace, "close");
    assert_eq!(opened.len(), 2, "expected a flow and a file:\n{trace}");
    assert_eq!(opened, closed, "a resource was left open:\n{trace}");

    // The paths never reach the output or the trace, so both are stable enough to pin.
    let mut snapshot = String::from("=== output ===\n");
    for line in &out.lines {
        snapshot.push_str(line);
        snapshot.push('\n');
    }
    snapshot.push_str(&format!("=== trace ===\n{trace}"));
    check_snapshot("pipe", &snapshot);
}

/// The done-when program: open a flow over a file, create a sink, and let `std/flow` move the
/// bytes. Both handles are consumed by `pipe` — naming either afterwards would be a move error.
fn program(src: &Path, dst: &Path) -> String {
    format!(
        r#"import {{ pipe }} from "std/flow"

task fn main() -> Result<(), IoError>
    uses {{ fs.read, fs.write }}
{{
    let flow = await flow_of_file("{}")?
    let sink = await file_create("{}")?
    let moved = await pipe(flow, sink)?
    print(moved)
    Ok(())
}}
"#,
        src.display(),
        dst.display()
    )
}

/// The resource handles named by one kind of trace event, in the order they appear.
fn resources(trace: &str, verb: &str) -> Vec<String> {
    let mut found: Vec<String> = trace
        .lines()
        .filter_map(|line| {
            let mut fields = line.split_whitespace().skip(2);
            (fields.next() == Some(verb)).then(|| fields.next().unwrap_or_default().to_string())
        })
        .collect();
    found.sort();
    found
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
