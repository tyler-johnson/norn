//! Name resolution and type checking for Norn.
//!
//! This crate turns the spanned AST from `norn-syntax` into a typed HIR: every name resolved to an
//! index, every expression given a type. Flattening to basic blocks is `norn-nir`'s job.

pub mod check;
pub mod hir;

pub use check::{Checked, check};
pub use hir::{Program, Ty};
