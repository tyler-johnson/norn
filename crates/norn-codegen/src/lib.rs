//! NIR → restricted Rust → `rustc` → binary.
//!
//! The backend of BOOTSTRAP.md §5's M5. `emit` prints one Rust source file per program: a static
//! prelude porting the interpreter's value semantics, then the program's blocks as state machines.
//! `rustc` (the module) links it against the embedded copy of `norn-rt` — the same runtime the
//! interpreter runs on, which is what makes the two engines' turn traces byte-identical by
//! construction rather than by comparison.

mod emit;
mod rt_sources;
mod rustc;
mod types;

pub use emit::generate;
pub use rustc::BuildOptions;

/// The runtime prelude carried into every generated program. `emit` writes it between the header
/// and the per-program part; `tests/prelude.rs` compiles it standalone against stub tables so a
/// prelude that no longer compiles fails this crate's tests, not the first `norn build`.
pub const PRELUDE: &str = include_str!("prelude.rs");

/// Generate, compile, and link `program` into `options.out`.
pub fn build(
    program: &norn_nir::Program,
    main: usize,
    options: &BuildOptions,
) -> Result<(), String> {
    rustc::compile(&emit::generate(program, main), options)
}
