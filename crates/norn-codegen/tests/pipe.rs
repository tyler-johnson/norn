//! `std/flow`'s `pipe` as a native binary, held byte for byte against the interpreter.
//!
//! The twin of `crates/norn-nir/tests/pipe.rs`: the same program — absolute paths formatted in
//! and the source written to the tmp directory, because three run contexts share it and would
//! not share a working directory — run under both engines with `--trace --virtual-clock`, and
//! stdout, stderr, and the exit code must match exactly. File I/O is deterministic under the
//! virtual clock, so unlike the socket tests this one gets the full differential treatment.

mod common;

use std::path::PathBuf;
use std::process::Command;

use norn_nir::{Captured, Config, execute};

#[test]
fn the_native_pipe_matches_the_interpreter() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("pipe-native");
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join("source.bin");
    let dst = dir.join("copy.bin");
    let fixture: Vec<u8> = (0..10_000u32).map(|i| (i % 251) as u8).collect();
    std::fs::write(&src, &fixture).unwrap();

    let source = format!(
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
    );

    let entry = dir.join("pipe.norn");
    std::fs::write(&entry, &source).unwrap();
    let (nir, main) = common::build(&entry);
    let mut out = Captured::default();
    let outcome = execute(&nir, main, &mut out, Config::deterministic());
    if let Err(trap) = &outcome.value {
        panic!("the pipe program trapped under the interpreter: {trap}");
    }
    let mut stdout = String::new();
    for line in &out.lines {
        stdout.push_str(line);
        stdout.push('\n');
    }
    std::fs::remove_file(&dst).unwrap();

    let binary = common::native(&nir, main, "pipe");
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
    assert_eq!(got.status.code(), Some(0), "the native pipe failed");
    assert_eq!(
        std::fs::read(&dst).unwrap(),
        fixture,
        "the native copy differs from the source"
    );
}
