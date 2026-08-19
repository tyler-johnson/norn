//! The standard library, carried inside the compiler.
//!
//! Bare `std/…` specifiers resolve here rather than to the filesystem: each entry is an ordinary
//! Norn source file from the repository's top-level `std/` directory, embedded at compile time so
//! a `norn` binary needs no checkout to find its own standard library. Cargo tracks `include_str!`
//! paths, so editing a std module rebuilds this crate. Being ordinary Norn is the point — one
//! implementation, executed by both engines, differentially tested like any user file.

/// Every standard-library module, as `(import specifier, contents)`. Keys are the specifiers
/// verbatim — extensionless, which is what keeps them disjoint from file keys, whose relative
/// resolution always appends `.norn`.
pub const STD: &[(&str, &str)] = &[
    ("std/fmt", include_str!("../../../std/fmt.norn")),
    ("std/time", include_str!("../../../std/time.norn")),
    ("std/bytes", include_str!("../../../std/bytes.norn")),
];

/// The text of the standard-library module `key` names, if there is one.
pub fn source(key: &str) -> Option<&'static str> {
    STD.iter()
        .find(|(name, _)| *name == key)
        .map(|(_, text)| *text)
}

/// What there is, for the miss diagnostics: "`std/fmt`", comma-separated as the table grows.
pub fn catalogue() -> String {
    STD.iter()
        .map(|(key, _)| format!("`{key}`"))
        .collect::<Vec<_>>()
        .join(", ")
}
