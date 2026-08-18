//! The differential oracle: M5's done-when.
//!
//! Every deterministic example runs under both engines — the interpreter in-process, the native
//! binary as a child with `--trace --virtual-clock` — and their stdout, stderr, and exit codes
//! must match byte for byte. The stderr comparison is the byte-identical-turn-trace claim of
//! `BOOTSTRAP.md` §5, plus the trap and error conventions around it.
//!
//! Nothing here reads or writes snapshots, so `NORN_BLESS` cannot bless the two engines into
//! agreement: the interpreter's fresh output is always the expectation.

mod common;

use std::path::Path;
use std::process::Command;

use norn_hir::hir::EnumId;
use norn_nir::{Captured, Config, Outcome, Value, execute};

#[test]
fn run_examples_match() {
    corpus("run", &[]);
}

#[test]
fn task_examples_match() {
    corpus("tasks", &[]);
}

#[test]
fn reactor_examples_match() {
    // `server.norn` binds a real socket on an OS-chosen port; `tests/server.rs` drives it live.
    corpus("reactors", &["server.norn"]);
}

/// Trap paths carry the tightest coupling between the two engines — the messages interpolate
/// `{:?}` of the value and operator enums — so they get their own corpus rather than waiting for
/// an example to hit one.
#[test]
fn traps_match() {
    let programs: &[(&str, &str)] = &[
        (
            "divide-by-zero",
            "fn main() -> I64 {\n    let zero = 0\n    7 / zero\n}\n",
        ),
        (
            "remainder-by-zero",
            "fn main() -> I64 {\n    let zero = 0\n    7 % zero\n}\n",
        ),
        (
            // Exhaustiveness is checked on top-level variants only (BOOTSTRAP.md §5 M1), so a gap
            // inside a nested pattern is a runtime trap both engines must word identically.
            "nested-gap",
            "enum Wrap {\n    One(Option<I64>)\n}\n\nfn main() -> I64 {\n    match Wrap.One(None) {\n        Wrap.One(Some(v)) => v\n    }\n}\n",
        ),
        (
            // The bounds are values, so the checker cannot rule the range out; the trap text
            // interpolates all three numbers and both engines must agree on every byte.
            "bytes-slice-range",
            "fn main() -> () {\n    let cut = bytes_slice(bytes(\"abc\"), 1, 9)\n    print(cut)\n}\n",
        ),
        (
            "byte-index-range",
            "fn main() -> () {\n    let data = bytes(\"abc\")\n    print(data[9])\n}\n",
        ),
        (
            "byte-index-negative",
            "fn main() -> () {\n    let data = bytes(\"abc\")\n    print(data[0 - 1])\n}\n",
        ),
    ];
    for (name, source) in programs {
        let (nir, main) = common::build_source(name, source);
        differ(&nir, main, name);
    }
}

fn corpus(dir: &str, live: &[&str]) {
    let mut checked = 0;
    for path in common::examples(dir) {
        let file = path.file_name().unwrap().to_string_lossy().to_string();
        if live.contains(&file.as_str()) {
            continue;
        }
        let name = format!(
            "{dir}-{}",
            Path::new(&file).file_stem().unwrap().to_string_lossy()
        );
        let (nir, main) = common::build(&path);
        differ(&nir, main, &name);
        checked += 1;
    }
    assert!(checked > 0, "no examples found in {dir}");
}

fn differ(nir: &norn_nir::Program, main: usize, name: &str) {
    let mut out = Captured::default();
    let outcome = execute(nir, main, &mut out, Config::deterministic());
    let (stdout, stderr, exit) = expected(nir, &out, &outcome);

    let binary = common::native(nir, main, name);
    let got = Command::new(&binary)
        .args(["--trace", "--virtual-clock"])
        .output()
        .unwrap_or_else(|err| panic!("running {}: {err}", binary.display()));

    assert_eq!(
        String::from_utf8_lossy(&got.stdout),
        stdout,
        "{name}: stdout differs between the engines"
    );
    assert_eq!(
        String::from_utf8_lossy(&got.stderr),
        stderr,
        "{name}: stderr differs between the engines"
    );
    assert_eq!(
        got.status.code(),
        Some(exit),
        "{name}: exit code differs between the engines"
    );
}

/// What `norn run --trace --virtual-clock` would print for this outcome — the conventions of
/// `cmd_run` (`crates/norn/src/main.rs`), which the generated `main` also mirrors.
fn expected(nir: &norn_nir::Program, out: &Captured, outcome: &Outcome) -> (String, String, i32) {
    let mut stdout = String::new();
    for line in &out.lines {
        stdout.push_str(line);
        stdout.push('\n');
    }
    let mut stderr = outcome.trace.clone();
    match &outcome.value {
        Ok(value) => {
            let result = match value {
                Value::Variant(enum_id, tag, fields) if *enum_id == EnumId::RESULT.index() => {
                    if *tag == EnumId::ERR {
                        stderr.push_str(&format!(
                            "error: {}\n",
                            norn_nir::interp::render(nir, &fields[0])
                        ));
                        return (stdout, stderr, 1);
                    }
                    fields[0].clone()
                }
                value => value.clone(),
            };
            if !matches!(result, Value::Unit) {
                stdout.push_str(&format!("{}\n", norn_nir::interp::render(nir, &result)));
            }
            (stdout, stderr, 0)
        }
        Err(trap) => {
            stderr.push_str(&format!("norn: trapped: {trap}\n"));
            (stdout, stderr, 1)
        }
    }
}
