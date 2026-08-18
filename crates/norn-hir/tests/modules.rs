//! The module system, checked in memory: named imports, export enforcement, and the path policy
//! import specifiers answer to.
//!
//! Every test hands `check_modules` a list of (name, source) pairs where the name doubles as the
//! resolution key — `("main.norn", …)` imports `("fmt.norn", …)` as `"./fmt"` — which is exactly
//! the shape the loader produces from disk, minus the disk.

use norn_hir::{CheckedModules, ModuleInput, check_modules};
use norn_syntax::ast;
use norn_syntax::{SourceFile, parse, render_all};

/// Parse and check a program of modules; the first pair is the entry module.
fn check_sources(sources: &[(&str, &str)]) -> CheckedModules {
    let modules: Vec<ast::Module> = sources
        .iter()
        .map(|(name, text)| {
            let parsed = parse(text);
            assert!(
                parsed.ok(),
                "{name} failed to parse:\n{}",
                render_all(&SourceFile::new(*name, *text), &parsed.errors)
            );
            parsed.module
        })
        .collect();
    let inputs: Vec<ModuleInput> = sources
        .iter()
        .zip(&modules)
        .map(|((name, _), module)| ModuleInput {
            name: name.to_string(),
            key: name.to_string(),
            module,
        })
        .collect();
    check_modules(&inputs)
}

/// Every diagnostic, rendered against its own file.
fn rendered(sources: &[(&str, &str)]) -> String {
    let checked = check_sources(sources);
    checked
        .errors
        .iter()
        .zip(sources)
        .map(|(errors, (name, text))| render_all(&SourceFile::new(*name, *text), errors))
        .collect::<Vec<_>>()
        .join("\n")
}

fn assert_ok(sources: &[(&str, &str)]) -> CheckedModules {
    let checked = check_sources(sources);
    assert!(
        checked.ok(),
        "expected a clean check:\n{}",
        rendered(sources)
    );
    checked
}

const FMT: &str = "\
export fn digits(n: I64) -> I64 {
    if n < 10 { 1 } else { 2 }
}

export struct Config {
    width: I64
}

export enum Shape {
    Empty
    Dot(I64)
}

fn secret() -> I64 {
    42
}
";

// ---------------------------------------------------------------- what imports bind

#[test]
fn a_named_import_binds_a_function() {
    let checked = assert_ok(&[
        (
            "main.norn",
            "import { digits } from \"./fmt\"\n\nfn main() -> I64 {\n    digits(123)\n}\n",
        ),
        ("fmt.norn", FMT),
    ]);
    // The imported function displays with its file's stem; the entry `main` stays bare.
    assert!(checked.program.fns.iter().any(|f| f.name == "fmt.digits"));
    assert!(checked.program.fns.iter().any(|f| f.name == "main"));
}

#[test]
fn a_named_import_binds_a_struct_in_every_position() {
    assert_ok(&[
        (
            "main.norn",
            "import { Config } from \"./fmt\"\n\nfn width(config: Config) -> I64 {\n    match config {\n        Config(width: w) => w\n    }\n}\n\nfn main() -> I64 {\n    width(Config(width: 3))\n}\n",
        ),
        ("fmt.norn", FMT),
    ]);
}

#[test]
fn a_named_import_binds_an_enum() {
    assert_ok(&[
        (
            "main.norn",
            "import { Shape } from \"./fmt\"\n\nfn main() -> I64 {\n    match Shape.Dot(2) {\n        Shape.Empty => 0\n        Shape.Dot(n) => n\n    }\n}\n",
        ),
        ("fmt.norn", FMT),
    ]);
}

#[test]
fn a_named_import_binds_a_reactor() {
    assert_ok(&[
        (
            "main.norn",
            "import { Gate } from \"./gate\"\n\ntask fn main() -> () {\n    scope {\n        let gate = spawn reactor Gate(limit: 8)\n        await send(gate.opened, ())\n    }\n}\n",
        ),
        (
            "gate.norn",
            "export reactor Gate(limit: I64) {\n    input opened: () [capacity: 1, overflow: reject]\n    state n: I64 = 0\n    on opened() {\n        n = n + 1\n    }\n    export signal open = n\n}\n",
        ),
    ]);
}

#[test]
fn an_import_may_be_renamed_with_as() {
    assert_ok(&[
        (
            "main.norn",
            "import { digits as d, Config as C } from \"./fmt\"\n\nfn main() -> I64 {\n    d(C(width: 40).width)\n}\n",
        ),
        ("fmt.norn", FMT),
    ]);
}

#[test]
fn one_file_may_be_imported_on_two_lines() {
    // The same specifier twice is not an error; only the same *name* twice is.
    assert_ok(&[
        (
            "main.norn",
            "import { digits } from \"./fmt\"\nimport { Config } from \"./fmt\"\n\nfn main() -> I64 {\n    digits(Config(width: 7).width)\n}\n",
        ),
        ("fmt.norn", FMT),
    ]);
}

// ---------------------------------------------------------------- what imports refuse

#[test]
fn an_unknown_name_says_so() {
    let out = rendered(&[
        (
            "main.norn",
            "import { nope } from \"./fmt\"\n\nfn main() {}\n",
        ),
        ("fmt.norn", FMT),
    ]);
    assert!(out.contains("`nope` is not defined in `./fmt`"), "{out}");
    assert!(out.contains("fmt.norn declares no `nope`"), "{out}");
}

#[test]
fn an_unexported_name_is_private() {
    let out = rendered(&[
        (
            "main.norn",
            "import { secret } from \"./fmt\"\n\nfn main() {}\n",
        ),
        ("fmt.norn", FMT),
    ]);
    assert!(out.contains("`secret` is not exported by `./fmt`"), "{out}");
    assert!(out.contains("private to its file"), "{out}");
    assert!(
        out.contains("the function is declared in fmt.norn; write `export` before it"),
        "{out}"
    );
}

#[test]
fn an_import_may_not_shadow_a_local_declaration() {
    let out = rendered(&[
        (
            "main.norn",
            "import { digits } from \"./fmt\"\n\nfn digits(n: I64) -> I64 {\n    n\n}\n\nfn main() {}\n",
        ),
        ("fmt.norn", FMT),
    ]);
    assert!(
        out.contains("the imported name `digits` is already taken"),
        "{out}"
    );
    assert!(out.contains("declared in this file"), "{out}");
    assert!(out.contains("rename the import with `as`"), "{out}");
}

#[test]
fn two_imports_of_one_name_collide() {
    let out = rendered(&[
        (
            "main.norn",
            "import { digits } from \"./fmt\"\nimport { digits } from \"./fmt\"\n\nfn main() {}\n",
        ),
        ("fmt.norn", FMT),
    ]);
    assert!(out.contains("bound by an earlier import"), "{out}");
}

#[test]
fn an_alias_may_not_take_a_prelude_name() {
    let out = rendered(&[
        (
            "main.norn",
            "import { digits as Option, Config as Err } from \"./fmt\"\n\nfn main() {}\n",
        ),
        ("fmt.norn", FMT),
    ]);
    assert!(
        out.contains("the imported name `Option` is already taken"),
        "{out}"
    );
    assert!(out.contains("a built-in type"), "{out}");
    assert!(
        out.contains("the imported name `Err` is already taken"),
        "{out}"
    );
    assert!(out.contains("a built-in constructor"), "{out}");
}

// ---------------------------------------------------------------- specifier policy

#[test]
fn a_bare_specifier_is_the_std_lane() {
    let out = rendered(&[(
        "main.norn",
        "import { read } from \"std/fs\"\n\nfn main() {}\n",
    )]);
    assert!(
        out.contains("`std/fs` is reserved for the standard library"),
        "{out}"
    );
}

#[test]
fn a_written_extension_is_refused() {
    let out = rendered(&[
        (
            "main.norn",
            "import { digits } from \"./fmt.norn\"\n\nfn main() {}\n",
        ),
        ("fmt.norn", FMT),
    ]);
    assert!(out.contains("the `.norn` extension is implied"), "{out}");
    assert!(out.contains("write `\"./fmt\"`"), "{out}");
}

#[test]
fn a_file_cannot_import_itself() {
    let out = rendered(&[(
        "main.norn",
        "import { digits } from \"./main\"\n\nexport fn digits(n: I64) -> I64 {\n    n\n}\n\nfn main() {}\n",
    )]);
    assert!(out.contains("a file cannot import itself"), "{out}");
}

#[test]
fn an_unknown_module_key_says_where_it_looked() {
    let out = rendered(&[(
        "main.norn",
        "import { digits } from \"./nope\"\n\nfn main() {}\n",
    )]);
    assert!(out.contains("cannot find module `./nope`"), "{out}");
    assert!(out.contains("expected a module at `nope.norn`"), "{out}");
}

// ---------------------------------------------------------------- cycles and entry identity

#[test]
fn mutual_recursion_crosses_files() {
    // The import graph has a cycle and so does the call graph; neither is an error — there are no
    // module initialisers, so there is no order for the import cycle to violate, and recursion is
    // only forbidden where a turn can reach it.
    assert_ok(&[
        (
            "a.norn",
            "import { pong } from \"./b\"\n\nexport fn ping(n: I64) -> I64 {\n    if n == 0 {\n        0\n    } else {\n        pong(n - 1)\n    }\n}\n\nfn main() -> I64 {\n    ping(3)\n}\n",
        ),
        (
            "b.norn",
            "import { ping } from \"./a\"\n\nexport fn pong(n: I64) -> I64 {\n    ping(n)\n}\n",
        ),
    ]);
}

#[test]
fn a_type_level_import_cycle_checks_clean() {
    assert_ok(&[
        (
            "a.norn",
            "import { Wrap } from \"./b\"\n\nexport struct Core {\n    id: I64\n}\n\nfn main() -> I64 {\n    Wrap(core: Core(id: 1)).core.id\n}\n",
        ),
        (
            "b.norn",
            "import { Core } from \"./a\"\n\nexport struct Wrap {\n    core: Core\n}\n",
        ),
    ]);
}

#[test]
fn an_imported_main_is_an_ordinary_function() {
    let checked = assert_ok(&[
        (
            "main.norn",
            "import { helper } from \"./lib\"\n\nfn main() -> I64 {\n    helper()\n}\n",
        ),
        (
            "lib.norn",
            "export fn helper() -> I64 {\n    main() + 1\n}\n\nfn main() -> I64 {\n    6\n}\n",
        ),
    ]);
    let main = checked.program.main.expect("the entry module has a main");
    assert_eq!(checked.program.fns[main.index()].name, "main");
    // The library's `main` is present, prefixed, and not the entry point.
    assert!(checked.program.fns.iter().any(|f| f.name == "lib.main"));
}

#[test]
fn entry_module_diagnostics_match_the_single_file_checker() {
    // The entry module is module zero, unprefixed: a one-file program must not be able to tell
    // `check_modules` from `check`.
    let source = "fn main() -> I64 {\n    \"seven\"\n}\n";
    let parsed = parse(source);
    assert!(parsed.ok());
    let single = norn_hir::check(&parsed.module);
    let multi = check_sources(&[("main.norn", source)]);
    let single_rendered = render_all(&SourceFile::new("main.norn", source), &single.errors);
    let multi_rendered = render_all(&SourceFile::new("main.norn", source), &multi.errors[0]);
    assert_eq!(single_rendered, multi_rendered);
    assert!(!single.ok());
}
