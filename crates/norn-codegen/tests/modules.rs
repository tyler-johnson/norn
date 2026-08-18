//! The differential oracle over the multi-file example: the interpreter's output is the
//! expectation, and the native binary must match it byte for byte — stdout, stderr, exit code.
//!
//! This is `differential.rs` with the loader in front: nothing about lowering or codegen knows
//! that the program came from three files, and this test is what keeps that true.

mod common;

use std::path::Path;
use std::process::Command;

use norn_hir::ModuleInput;
use norn_nir::{Captured, Config, Value, execute};
use norn_syntax::render_all;

#[test]
fn the_modules_example_matches() {
    let (nir, main) = build();

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

fn build() -> (norn_nir::Program, usize) {
    let entry = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/modules/main.norn");
    let mut read = |key: &str| std::fs::read_to_string(key);
    let loaded = norn_hir::load(&entry.display().to_string(), &mut read).expect("entry reads");
    assert!(loaded.ok(), "loading the modules example failed");
    let inputs: Vec<ModuleInput> = loaded
        .modules
        .iter()
        .map(|module| ModuleInput {
            name: module.name.clone(),
            key: module.key.clone(),
            module: &module.module,
        })
        .collect();
    let checked = norn_hir::check_modules(&inputs);
    assert!(
        checked.ok(),
        "checking failed:\n{}",
        loaded
            .modules
            .iter()
            .zip(&checked.errors)
            .map(|(module, errors)| render_all(&module.file, errors))
            .collect::<Vec<_>>()
            .join("\n")
    );
    let main = checked.program.main.expect("the entry module has a `main`");
    (norn_nir::lower(&checked.program), main.index())
}
