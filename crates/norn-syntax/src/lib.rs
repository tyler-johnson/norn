//! Front end for the Norn language: tokenizer, parser, spanned AST, and the two renderings the
//! snapshot corpus is built from.
//!
//! This crate has no opinion about meaning. Name resolution, types, reactive analysis, and
//! lowering arrive in `norn-hir` and `norn-nir`; see `BOOTSTRAP.md`.

pub mod ast;
pub mod diag;
pub mod dump;
pub mod lex;
pub mod parse;
pub mod print;
pub mod span;

pub use ast::Module;
pub use diag::{Diagnostic, render, render_all};
pub use parse::{Parsed, parse};
pub use span::{SourceFile, Span};
