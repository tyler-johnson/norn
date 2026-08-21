//! Shared between the differential oracle and the native live tests: the front half of the
//! pipeline, and a `norn build` aimed at the test-private cache under `CARGO_TARGET_TMPDIR` so the
//! runtime rlib is compiled once per suite and `~/.cache` is never touched.

#![allow(dead_code)]

use std::path::{Path, PathBuf};

use norn_hir::ModuleInput;
use norn_syntax::render_all;

/// Load, check, and lower the module graph rooted at `path` — the loader in front, so an example
/// that gains an `import` needs no harness change.
pub fn build(path: &Path) -> (norn_nir::Program, usize) {
    let entry = path.display().to_string();
    let mut read = |key: &str| std::fs::read_to_string(key);
    lower_loaded(
        &entry,
        norn_hir::load(&entry, &mut read).unwrap_or_else(|err| panic!("{err}")),
    )
}

fn lower_loaded(entry: &str, loaded: norn_hir::Loaded) -> (norn_nir::Program, usize) {
    assert!(
        loaded.ok(),
        "{entry} failed to load:\n{}",
        loaded
            .errors
            .iter()
            .map(|(index, diagnostic)| norn_syntax::render(
                &loaded.modules[*index].file,
                diagnostic
            ))
            .collect::<Vec<_>>()
            .join("\n")
    );
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
        "{entry} failed to check:\n{}",
        loaded
            .modules
            .iter()
            .zip(&checked.errors)
            .map(|(module, errors)| render_all(&module.file, errors))
            .collect::<Vec<_>>()
            .join("\n")
    );
    let main = checked
        .program
        .main
        .unwrap_or_else(|| panic!("{entry} has no `main`"));
    (norn_nir::lower(&checked.program), main.index())
}

/// Check and lower an in-memory module — for generated programs and inline trap programs, which
/// have no file of their own. Still routed through the loader, against an in-memory entry, so an
/// inline program may import std modules.
pub fn build_source(name: &str, source: &str) -> (norn_nir::Program, usize) {
    let entry = format!("{name}.norn");
    let mut read = |key: &str| {
        if key == entry {
            Ok(source.to_string())
        } else {
            std::fs::read_to_string(key)
        }
    };
    lower_loaded(
        &entry,
        norn_hir::load(&entry, &mut read).unwrap_or_else(|err| panic!("{err}")),
    )
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
