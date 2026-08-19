//! The differential oracle over the multi-file example: the interpreter's output is the
//! expectation, and the native binary must match it byte for byte — stdout, stderr, exit code.
//!
//! This is `differential.rs` with the loader in front: nothing about lowering or codegen knows
//! that the program came from three files, and this test is what keeps that true.

mod common;

use std::path::Path;
use std::process::Command;

use norn_nir::{Captured, Config, Value, execute};

#[test]
fn the_modules_example_matches() {
    let entry = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/modules/main.norn");
    let (nir, main) = common::build(&entry);

    let mut out = Captured::default();
    let outcome = execute(&nir, main, &mut out, Config::deterministic());
    let mut stdout = String::new();
    for line in &out.lines {
        stdout.push_str(line);
        stdout.push('\n');
    }
    let value = outcome.value.expect("the modules example runs");
    assert!(
        matches!(value, Value::Unit),
        "the modules example returns ()"
    );

    let binary = common::native(&nir, main, "modules-main");
    let got = Command::new(&binary)
        .args(["--trace", "--virtual-clock"])
        .output()
        .unwrap_or_else(|err| panic!("running {}: {err}", binary.display()));

    assert_eq!(
        String::from_utf8_lossy(&got.stdout),
        stdout,
        "stdout differs between the engines"
    );
    assert_eq!(
        String::from_utf8_lossy(&got.stderr),
        outcome.trace,
        "stderr differs between the engines"
    );
    assert_eq!(got.status.code(), Some(0), "exit code differs");
}
