//! The multi-file pipeline: loader → checker → NIR → execution, snapshotted.
//!
//! `examples/modules/` is the worked example — an entry file importing a library and a
//! subdirectory module — and this test is what pins that the whole graph lowers to one program
//! whose output is deterministic. Set `NORN_BLESS=1` to rewrite the snapshot, then read the diff.

use std::path::{Path, PathBuf};

use norn_hir::ModuleInput;
use norn_nir::{Captured, Config, execute, lower, print};
use norn_syntax::render_all;

#[test]
fn the_modules_example_loads_lowers_and_runs() {
    let (nir, main) = build();

    let mut out = Captured::default();
    let outcome = execute(&nir, main, &mut out, Config::deterministic());
    let value = match outcome.value {
        Ok(value) => norn_nir::interp::render(&nir, &value),
        Err(trap) => panic!("modules example trapped: {trap}"),
    };

    let mut snapshot = format!("=== nir ===\n{}", print(&nir));
    snapshot.push_str("=== output ===\n");
    for line in &out.lines {
        snapshot.push_str(line);
        snapshot.push('\n');
    }
    snapshot.push_str(&format!("=== result ===\n{value}\n"));
    check_snapshot("modules-main.norn", &snapshot);
}

/// Discovery order is a function of file contents alone, so loading twice must give the same
/// modules, the same ids, and the same blocks.
#[test]
fn loading_is_deterministic() {
    let (first, _) = build();
    let (second, _) = build();
    assert_eq!(print(&first), print(&second), "loading lowered differently");
}

fn build() -> (norn_nir::Program, usize) {
    let entry = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/modules/main.norn");
    let mut read = |key: &str| std::fs::read_to_string(key);
    let loaded = norn_hir::load(&entry.display().to_string(), &mut read).expect("entry reads");
    assert!(
        loaded.ok(),
        "loading failed:\n{}",
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
    (lower(&checked.program), main.index())
}

fn check_snapshot(name: &str, actual: &str) {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/snapshots");
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
