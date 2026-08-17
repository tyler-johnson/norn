//! The lowered Norn IR and its interpreter.
//!
//! `norn-hir` produces a typed tree; this crate flattens it into basic blocks and runs them. The
//! same blocks are what M5's native backend will emit code for, and the interpreter exists partly
//! to be the thing that backend is differentially tested against.

pub mod interp;
pub mod lower;
pub mod nir;

pub use interp::{Captured, Output, Stdout, Trap, Value, run};
pub use lower::lower;
pub use nir::{Program, print};
