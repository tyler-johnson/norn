//! The `norn` compiler driver.
//!
//! The verbs follow the pipeline: `parse` stops after syntax, `check` after types, `nir` after
//! lowering, `run` executes, and `build` compiles to a native binary. Later milestones add
//! `trace` (see `BOOTSTRAP.md` §5).

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use norn_syntax::{SourceFile, dump, parse, print, render_all};

const USAGE: &str = "\
norn — the Norn compiler

usage:
    norn parse [options] <file>...    check syntax
    norn check <file>...              resolve names and check types
    norn nir <file>                   print the lowered IR
    norn graph <file> [Name]          print a reactor's dependency graph
    norn run [options] <file>         check, lower, and execute `main`
    norn build [options] <file>       compile to a native binary
    norn fmt [--check] <file>...      rewrite files in canonical form
    norn --version
    norn --help

parse options:
    --dump      print the abstract syntax tree as s-expressions
    --print     print the parsed program in canonical form

run options:
    --trace           write the runtime event trace to stderr
    --virtual-clock   jump to the next deadline instead of sleeping, so a run
                      that only waits on timers is instant and deterministic

build options:
    -o <path>         where to write the binary (default: ./<stem>)
    --emit-rust       keep the generated Rust beside the binary, as <path>.rs
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(code) => code,
        Err(message) => {
            if !message.is_empty() {
                eprintln!("norn: {message}");
            }
            ExitCode::FAILURE
        }
    }
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    let Some(first) = args.first() else {
        print!("{USAGE}");
        return Ok(ExitCode::SUCCESS);
    };

    match first.as_str() {
        "--help" | "-h" | "help" => {
            print!("{USAGE}");
            Ok(ExitCode::SUCCESS)
        }
        "--version" | "-V" => {
            println!("norn {}", env!("CARGO_PKG_VERSION"));
            Ok(ExitCode::SUCCESS)
        }
        "parse" => cmd_parse(&args[1..]),
        "check" => cmd_check(&args[1..]),
        "nir" => cmd_nir(&args[1..]),
        "graph" => cmd_graph(&args[1..]),
        "run" => cmd_run(&args[1..]),
        "build" => cmd_build(&args[1..]),
        "fmt" => cmd_fmt(&args[1..]),
        other => Err(format!("unknown command `{other}`\n\n{USAGE}")),
    }
}

fn cmd_parse(args: &[String]) -> Result<ExitCode, String> {
    let mut dump_ast = false;
    let mut print_canonical = false;
    let mut paths = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--dump" => dump_ast = true,
            "--print" => print_canonical = true,
            flag if flag.starts_with('-') => return Err(format!("unknown option `{flag}`")),
            path => paths.push(PathBuf::from(path)),
        }
    }
    if paths.is_empty() {
        return Err("expected at least one file to parse".into());
    }

    let mut failed = false;
    for path in &paths {
        let file = read(path)?;
        let parsed = parse(&file.text);
        if !parsed.errors.is_empty() {
            eprint!("{}", render_all(&file, &parsed.errors));
            failed = true;
            continue;
        }
        if dump_ast {
            print!("{}", dump::module(&parsed.module));
        }
        if print_canonical {
            print!("{}", print::module(&parsed.module));
        }
        if !dump_ast && !print_canonical && paths.len() > 1 {
            println!("{}: ok", file.name);
        }
    }
    Ok(if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}

fn cmd_check(args: &[String]) -> Result<ExitCode, String> {
    let paths = plain_paths(args)?;
    let mut failed = false;
    for path in &paths {
        let file = read(path)?;
        if front_end(&file).is_none() {
            failed = true;
        } else if paths.len() > 1 {
            println!("{}: ok", file.name);
        }
    }
    Ok(if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}

fn cmd_nir(args: &[String]) -> Result<ExitCode, String> {
    let paths = plain_paths(args)?;
    let [path] = &paths[..] else {
        return Err("expected exactly one file".into());
    };
    let file = read(path)?;
    let Some(program) = front_end(&file) else {
        return Ok(ExitCode::FAILURE);
    };
    print!("{}", norn_nir::print(&norn_nir::lower(&program)));
    Ok(ExitCode::SUCCESS)
}

/// Print the propagation plan the runtime will consume.
///
/// From NIR rather than from HIR, deliberately: printing the same table the turn loop walks is what
/// makes "the plan is the artifact" a claim anyone can check, rather than two renderings of one idea
/// that might drift.
fn cmd_graph(args: &[String]) -> Result<ExitCode, String> {
    let paths = plain_paths(args)?;
    let (path, wanted) = match &paths[..] {
        [path] => (path, None),
        [path, name] => (path, Some(name.display().to_string())),
        _ => return Err("expected a file and an optional reactor name".into()),
    };
    let file = read(path)?;
    let Some(hir) = front_end(&file) else {
        return Ok(ExitCode::FAILURE);
    };
    let program = norn_nir::lower(&hir);
    if program.reactors.is_empty() {
        return Err(format!("{}: no reactors", file.name));
    }
    if let Some(wanted) = &wanted
        && !program.reactors.iter().any(|r| r.name == *wanted)
    {
        let known: Vec<&str> = program.reactors.iter().map(|r| r.name.as_str()).collect();
        return Err(format!(
            "{}: no reactor `{wanted}`; this file has {}",
            file.name,
            known.join(", ")
        ));
    }
    print!("{}", norn_nir::print_graph(&program, wanted.as_deref()));
    Ok(ExitCode::SUCCESS)
}

fn cmd_run(args: &[String]) -> Result<ExitCode, String> {
    let mut trace = false;
    let mut virtual_clock = false;
    let mut paths = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--trace" => trace = true,
            "--virtual-clock" => virtual_clock = true,
            flag if flag.starts_with('-') => return Err(format!("unknown option `{flag}`")),
            path => paths.push(PathBuf::from(path)),
        }
    }
    let [path] = &paths[..] else {
        return Err("expected exactly one file".into());
    };
    let file = read(path)?;
    let Some(hir) = front_end(&file) else {
        return Ok(ExitCode::FAILURE);
    };

    let main = entry_of(&hir, &file)?;

    let program = norn_nir::lower(&hir);
    // A `task fn main` runs as the root task of a runtime; a plain one is a task that never parks.
    let config = norn_nir::Config {
        clock: if virtual_clock {
            norn_nir::Clock::simulated()
        } else {
            norn_nir::Clock::real()
        },
        trace,
    };
    let mut out = norn_nir::Stdout;
    let outcome = norn_nir::execute(&program, main.index(), &mut out, config);
    if trace {
        eprint!("{}", outcome.trace);
    }
    match outcome.value {
        Ok(value) => {
            // A `main` returning a `Result` reports rather than prints: `Err` is a failed run,
            // and the `Ok` wrapper is ceremony the reader does not need to see.
            let result = match &value {
                norn_nir::Value::Variant(enum_id, tag, fields)
                    if *enum_id == norn_hir::hir::EnumId::RESULT.index() =>
                {
                    if *tag == norn_hir::hir::EnumId::ERR {
                        eprintln!("error: {}", norn_nir::interp::render(&program, &fields[0]));
                        return Ok(ExitCode::FAILURE);
                    }
                    fields[0].clone()
                }
                value => value.clone(),
            };
            if !matches!(result, norn_nir::Value::Unit) {
                println!("{}", norn_nir::interp::render(&program, &result));
            }
            Ok(ExitCode::SUCCESS)
        }
        Err(trap) => {
            eprintln!("norn: trapped: {trap}");
            Ok(ExitCode::FAILURE)
        }
    }
}

fn cmd_build(args: &[String]) -> Result<ExitCode, String> {
    let mut out: Option<PathBuf> = None;
    let mut emit_rust = false;
    let mut paths = Vec::new();
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "-o" => {
                index += 1;
                let path = args.get(index).ok_or("`-o` expects a path")?;
                out = Some(PathBuf::from(path));
            }
            "--emit-rust" => emit_rust = true,
            flag if flag.starts_with('-') => return Err(format!("unknown option `{flag}`")),
            path => paths.push(PathBuf::from(path)),
        }
        index += 1;
    }
    let [path] = &paths[..] else {
        return Err("expected exactly one file".into());
    };
    let file = read(path)?;
    let Some(hir) = front_end(&file) else {
        return Ok(ExitCode::FAILURE);
    };
    let main = entry_of(&hir, &file)?;

    let program = norn_nir::lower(&hir);
    let out = match out {
        Some(out) => out,
        None => path
            .file_stem()
            .map(PathBuf::from)
            .ok_or_else(|| format!("cannot derive an output name from `{}`", path.display()))?,
    };
    let options = norn_codegen::BuildOptions {
        out,
        cache_dir: None,
        emit_rust,
        rustc: None,
    };
    norn_codegen::build(&program, main.index(), &options)?;
    Ok(ExitCode::SUCCESS)
}

/// The function `run` and `build` start from: `main`, which must exist and take nothing.
fn entry_of(hir: &norn_hir::Program, file: &SourceFile) -> Result<norn_hir::hir::FnId, String> {
    let Some(main) = hir.main else {
        return Err(format!("{}: no `main` function to run", file.name));
    };
    if hir.fns[main.index()].params != 0 {
        return Err(format!("{}: `main` cannot take parameters", file.name));
    }
    Ok(main)
}

/// Parse and check one file, printing any diagnostics. `None` means it did not get through.
fn front_end(file: &SourceFile) -> Option<norn_hir::Program> {
    let parsed = parse(&file.text);
    if !parsed.errors.is_empty() {
        eprint!("{}", render_all(file, &parsed.errors));
        return None;
    }
    let checked = norn_hir::check(&parsed.module);
    if !checked.errors.is_empty() {
        eprint!("{}", render_all(file, &checked.errors));
        return None;
    }
    Some(checked.program)
}

fn cmd_fmt(args: &[String]) -> Result<ExitCode, String> {
    let mut check = false;
    let mut paths = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--check" => check = true,
            flag if flag.starts_with('-') => return Err(format!("unknown option `{flag}`")),
            path => paths.push(PathBuf::from(path)),
        }
    }
    if paths.is_empty() {
        return Err("expected at least one file to format".into());
    }

    let mut failed = false;
    for path in &paths {
        let file = read(path)?;
        let parsed = parse(&file.text);
        if !parsed.errors.is_empty() {
            eprint!("{}", render_all(&file, &parsed.errors));
            failed = true;
            continue;
        }
        let canonical = print::module(&parsed.module);
        if canonical == file.text {
            continue;
        }
        if check {
            eprintln!("{}: not in canonical form", file.name);
            failed = true;
        } else if let Err(err) = std::fs::write(path, &canonical) {
            return Err(format!("{}: {err}", path.display()));
        }
    }
    Ok(if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}

fn plain_paths(args: &[String]) -> Result<Vec<PathBuf>, String> {
    let mut paths = Vec::new();
    for arg in args {
        if arg.starts_with('-') {
            return Err(format!("unknown option `{arg}`"));
        }
        paths.push(PathBuf::from(arg));
    }
    if paths.is_empty() {
        return Err("expected at least one file".into());
    }
    Ok(paths)
}

fn read(path: &Path) -> Result<SourceFile, String> {
    let text = std::fs::read_to_string(path).map_err(|err| format!("{}: {err}", path.display()))?;
    Ok(SourceFile::new(path.display().to_string(), text))
}
