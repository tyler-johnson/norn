//! The shared front end for the interpreter's test suites: every example builds through the
//! loader, so an example that gains an `import` — a user module or `std/…` — needs no harness
//! change. Snapshot names stay derived from the path's basename by the callers, not from the
//! module name, which the loader makes a full path.

#![allow(dead_code)]

use std::path::Path;

use norn_hir::ModuleInput;
use norn_syntax::{SourceFile, parse, render_all};

/// Load, check, and lower the module graph rooted at `path`.
pub fn build(path: &Path) -> (norn_nir::Program, usize) {
    let entry = path.display().to_string();
    let mut read = |key: &str| std::fs::read_to_string(key);
    let loaded = norn_hir::load(&entry, &mut read).unwrap_or_else(|err| panic!("{err}"));
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

/// Parse, check, and lower a single in-memory module — for generated programs, which have no file
/// for the loader to root a graph at.
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
