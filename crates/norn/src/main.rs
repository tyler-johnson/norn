//! The `norn` compiler driver.
//!
//! At M0 the only stage that exists is parsing, so the only verbs are `parse` and `fmt`. Later
//! milestones add `run`, `build`, `graph`, and `trace` (see `BOOTSTRAP.md` §5).

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use norn_syntax::{SourceFile, dump, parse, print, render_all};

const USAGE: &str = "\
norn — the Norn compiler

usage:
    norn parse [options] <file>...    check syntax
    norn fmt [--check] <file>...      rewrite files in canonical form
    norn --version
    norn --help

parse options:
    --dump      print the abstract syntax tree as s-expressions
    --print     print the parsed program in canonical form
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            if !message.is_empty() {
                eprintln!("norn: {message}");
            }
            ExitCode::FAILURE
        }
    }
}

fn run(args: &[String]) -> Result<(), String> {
    let Some(first) = args.first() else {
        print!("{USAGE}");
        return Ok(());
    };

    match first.as_str() {
        "--help" | "-h" | "help" => {
            print!("{USAGE}");
            Ok(())
        }
        "--version" | "-V" => {
            println!("norn {}", env!("CARGO_PKG_VERSION"));
            Ok(())
        }
        "parse" => cmd_parse(&args[1..]),
        "fmt" => cmd_fmt(&args[1..]),
        other => Err(format!("unknown command `{other}`\n\n{USAGE}")),
    }
}

fn cmd_parse(args: &[String]) -> Result<(), String> {
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
    if failed { Err(String::new()) } else { Ok(()) }
}

fn cmd_fmt(args: &[String]) -> Result<(), String> {
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
    if failed { Err(String::new()) } else { Ok(()) }
}

fn read(path: &Path) -> Result<SourceFile, String> {
    let text = std::fs::read_to_string(path).map_err(|err| format!("{}: {err}", path.display()))?;
    Ok(SourceFile::new(path.display().to_string(), text))
}
