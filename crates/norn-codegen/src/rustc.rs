//! The `rustc` driver: turn generated source into a binary.
//!
//! Two invocations, no cargo. The embedded `norn-rt` sources are written into a cache directory
//! and compiled to an rlib once per (toolchain, flags, sources) hash; every program build after
//! that is a single `rustc --extern norn_rt=…`. The rlib is renamed into place atomically, so
//! concurrent builds race harmlessly — worst case duplicate work, never a torn rlib.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::rt_sources::RT_SOURCES;

pub struct BuildOptions {
    /// Where the binary goes.
    pub out: PathBuf,
    /// Overrides `$NORN_CACHE_DIR`, `$XDG_CACHE_HOME/norn`, `$HOME/.cache/norn`.
    pub cache_dir: Option<PathBuf>,
    /// Keep the generated source beside the binary, as `<out>.rs`.
    pub emit_rust: bool,
    /// Overrides `$NORN_RUSTC`, then `rustc` on `PATH`.
    pub rustc: Option<PathBuf>,
}

/// One set of flags for the runtime and the program: the differential oracle should test the
/// compiler that ships, not a faster variant of it.
const FLAGS: &[&str] = &["--edition", "2024", "-O", "-Cdebuginfo=0"];

/// Compile `source` against the embedded runtime and link it into `options.out`.
pub fn compile(source: &str, options: &BuildOptions) -> Result<(), String> {
    let rustc = options
        .rustc
        .clone()
        .or_else(|| std::env::var_os("NORN_RUSTC").map(PathBuf::from))
        .unwrap_or_else(|| PathBuf::from("rustc"));
    let version = Command::new(&rustc).arg("-vV").output().map_err(|err| {
        format!(
            "`build` needs `rustc` (1.97+) — running `{}` failed: {err}",
            rustc.display()
        )
    })?;
    if !version.status.success() {
        return Err(format!(
            "`{} -vV` failed:\n{}",
            rustc.display(),
            String::from_utf8_lossy(&version.stderr)
        ));
    }

    let cache = cache_root(options)?;
    let rlib = runtime_rlib(&rustc, &version.stdout, &cache)?;

    // The generated source lives in a throwaway directory unless the caller wants to keep it —
    // and it is always kept when the compile fails, because that failure is a norn bug and the
    // source is the evidence.
    let (source_path, scratch) = if options.emit_rust {
        (options.out.with_extension("rs"), None)
    } else {
        static UNIQUE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let unique = UNIQUE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = cache.join(format!("prog-{}-{unique}", std::process::id()));
        fs::create_dir_all(&dir).map_err(|err| format!("creating `{}`: {err}", dir.display()))?;
        (dir.join("main.rs"), Some(dir))
    };
    fs::write(&source_path, source)
        .map_err(|err| format!("writing `{}`: {err}", source_path.display()))?;

    let output = Command::new(&rustc)
        .args(FLAGS)
        .args(["--crate-name", &crate_name(&options.out)])
        .arg("--extern")
        .arg(format!("norn_rt={}", rlib.display()))
        .arg(&source_path)
        .arg("-o")
        .arg(&options.out)
        .output()
        .map_err(|err| format!("running `{}`: {err}", rustc.display()))?;
    if !output.status.success() {
        return Err(format!(
            "internal: the generated Rust failed to compile — this is a bug in norn\n{}\nthe generated source is kept at `{}`",
            String::from_utf8_lossy(&output.stderr).trim_end(),
            source_path.display()
        ));
    }
    if let Some(dir) = scratch {
        let _ = fs::remove_dir_all(dir);
    }
    Ok(())
}

/// The runtime rlib for this toolchain, building it if this is the first time.
fn runtime_rlib(rustc: &Path, version: &[u8], cache: &Path) -> Result<PathBuf, String> {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    fnv(&mut hash, version);
    for flag in FLAGS {
        fnv(&mut hash, flag.as_bytes());
    }
    for (name, contents) in RT_SOURCES {
        fnv(&mut hash, name.as_bytes());
        fnv(&mut hash, contents.as_bytes());
    }

    let dir = cache.join(format!("rt-{hash:016x}"));
    let rlib = dir.join("libnorn_rt.rlib");
    if rlib.exists() {
        return Ok(rlib);
    }

    // Sources and intermediates live in a scratch directory private to this invocation — unique
    // per process *and* per call, because parallel tests build concurrently from one pid — and
    // only the finished rlib is renamed into place. Concurrent builds duplicate work; they never
    // read each other's half-written files.
    static UNIQUE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let unique = UNIQUE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let scratch = cache.join(format!("rt-build-{}-{unique}", std::process::id()));
    let src = scratch.join("src");
    fs::create_dir_all(&src).map_err(|err| format!("creating `{}`: {err}", src.display()))?;
    for (name, contents) in RT_SOURCES {
        let path = src.join(name);
        fs::write(&path, contents).map_err(|err| format!("writing `{}`: {err}", path.display()))?;
    }
    let staged = scratch.join("libnorn_rt.rlib");
    let output = Command::new(rustc)
        .args(FLAGS)
        .args(["--crate-type", "rlib", "--crate-name", "norn_rt"])
        .arg(src.join("lib.rs"))
        .arg("-o")
        .arg(&staged)
        .output()
        .map_err(|err| format!("running `{}`: {err}", rustc.display()))?;
    if !output.status.success() {
        return Err(format!(
            "compiling the runtime failed — is `{}` a current stable rustc (1.97+)?\n{}",
            rustc.display(),
            String::from_utf8_lossy(&output.stderr).trim_end()
        ));
    }
    fs::create_dir_all(&dir).map_err(|err| format!("creating `{}`: {err}", dir.display()))?;
    fs::rename(&staged, &rlib).map_err(|err| format!("installing `{}`: {err}", rlib.display()))?;
    let _ = fs::remove_dir_all(&scratch);
    Ok(rlib)
}

fn cache_root(options: &BuildOptions) -> Result<PathBuf, String> {
    if let Some(dir) = &options.cache_dir {
        return Ok(dir.clone());
    }
    if let Some(dir) = std::env::var_os("NORN_CACHE_DIR")
        && !dir.is_empty()
    {
        return Ok(PathBuf::from(dir));
    }
    if let Some(dir) = std::env::var_os("XDG_CACHE_HOME")
        && !dir.is_empty()
    {
        return Ok(PathBuf::from(dir).join("norn"));
    }
    if let Some(home) = std::env::var_os("HOME")
        && !home.is_empty()
    {
        return Ok(PathBuf::from(home).join(".cache").join("norn"));
    }
    Err("no cache directory: set NORN_CACHE_DIR or HOME".into())
}

/// A crate name `rustc` will accept, derived from the output's file stem.
fn crate_name(out: &Path) -> String {
    let stem = out.file_stem().and_then(|s| s.to_str()).unwrap_or("");
    let mut name: String = stem
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    if name.is_empty() || name.starts_with(|c: char| c.is_ascii_digit()) {
        name.insert(0, '_');
    }
    if name == "norn_rt" {
        // The one name the program cannot take: it is already the runtime's.
        name.push('_');
    }
    name
}

fn fnv(hash: &mut u64, bytes: &[u8]) {
    for byte in bytes {
        *hash ^= *byte as u64;
        *hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
}
