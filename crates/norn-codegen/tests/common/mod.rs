//! Shared between the differential oracle and the native live tests: the front half of the
//! pipeline, and a `norn build` aimed at the test-private cache under `CARGO_TARGET_TMPDIR` so the
//! runtime rlib is compiled once per suite and `~/.cache` is never touched.

#![allow(dead_code)]

use std::path::{Path, PathBuf};

use norn_syntax::{SourceFile, parse, render_all};

pub fn build(path: &Path) -> (norn_nir::Program, usize) {
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    let text = std::fs::read_to_string(path).unwrap();
    build_source(&name, &text)
}

pub fn build_source(name: &str, source: &str) -> (norn_nir::Program, usize) {
    let file = SourceFile::new(name, source.to_string());
    let parsed = parse(source);
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
    (norn_nir::lower(&checked.program), main.index())
}

/// Compile `nir` to a native binary named after the test and return its path.
pub fn native(nir: &norn_nir::Program, main: usize, name: &str) -> PathBuf {
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));
    let out = tmp.join(format!("bin-{name}"));
    let options = norn_codegen::BuildOptions {
        out: out.clone(),
        cache_dir: Some(tmp.join("cache")),
        emit_rust: false,
        rustc: None,
    };
    norn_codegen::build(nir, main, &options).unwrap_or_else(|err| panic!("building {name}: {err}"));
    out
}

pub fn examples(dir: &str) -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(dir);
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|err| panic!("reading {}: {err}", dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "norn"))
        .collect();
    files.sort();
    files
}
