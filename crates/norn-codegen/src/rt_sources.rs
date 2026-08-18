//! The runtime, carried inside the compiler.
//!
//! `norn build` must link generated code against `norn-rt` without assuming a checkout of this
//! repository exists on the machine running it. The sources are embedded here at compile time and
//! written back out into the build cache, where one `rustc` invocation turns them into an rlib that
//! is reused until either they or the toolchain change. Cargo tracks `include_str!` paths, so
//! editing the runtime rebuilds this crate and changes the hash.

/// Every source file of `norn-rt`, as `(path relative to the crate's src/, contents)`.
pub const RT_SOURCES: &[(&str, &str)] = &[
    ("lib.rs", include_str!("../../norn-rt/src/lib.rs")),
    ("clock.rs", include_str!("../../norn-rt/src/clock.rs")),
    ("graph.rs", include_str!("../../norn-rt/src/graph.rs")),
    ("http.rs", include_str!("../../norn-rt/src/http.rs")),
    ("poll.rs", include_str!("../../norn-rt/src/poll.rs")),
    ("scope.rs", include_str!("../../norn-rt/src/scope.rs")),
    ("task.rs", include_str!("../../norn-rt/src/task.rs")),
    ("timer.rs", include_str!("../../norn-rt/src/timer.rs")),
    ("trace.rs", include_str!("../../norn-rt/src/trace.rs")),
];
