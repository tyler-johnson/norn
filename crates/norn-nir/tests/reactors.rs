//! The M3 reactor corpus.
//!
//! Mirrors `tasks.rs` exactly, with a `=== graph ===` section between the IR and the output: the
//! propagation plan is the artifact this milestone exists to produce, so it is snapshotted beside
//! the trace that walks it. A change to either shows up in one diff.
//!
//! `server.norn` is excluded — it binds a real socket and is driven by a real client, so it lives
//! in `server.rs` where a nondeterministic port cannot become a golden file.
//!
//! Set `NORN_BLESS=1` to rewrite the snapshots, then read the diff before committing it.

mod common;

use std::path::{Path, PathBuf};

use norn_nir::nir::NodeKind;
use norn_nir::{Captured, Config, execute, print, print_graph};

/// Driven by a real socket, so it is checked and lowered here but run in `server.rs`.
const LIVE: &[&str] = &["server.norn"];

#[test]
fn reactors_run_and_trace() {
    let mut checked = 0;
    for path in golden_files() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let (nir, main) = common::build(&path);

        let mut out = Captured::default();
        let outcome = execute(&nir, main, &mut out, Config::deterministic());
        let value = match outcome.value {
            Ok(value) => norn_nir::interp::render(&nir, &value),
            Err(trap) => panic!("{name} trapped: {trap}"),
        };

        let mut snapshot = format!("=== nir ===\n{}", print(&nir));
        snapshot.push_str(&format!("=== graph ===\n{}", print_graph(&nir, None)));
        snapshot.push_str("=== output ===\n");
        for line in &out.lines {
            snapshot.push_str(line);
            snapshot.push('\n');
        }
        snapshot.push_str(&format!("=== result ===\n{value}\n"));
        snapshot.push_str(&format!("=== trace ===\n{}", outcome.trace));
        check_snapshot(&name, &snapshot);
        checked += 1;
    }
    assert!(checked > 0, "no reactor examples found");
}

/// The claim the whole milestone rests on, so it is run rather than read.
///
/// This is what catches a nondeterministic graph order the day it is introduced — a `HashMap`
/// iterated during graph construction would pass every other test here and fail this one.
#[test]
fn traces_are_reproducible() {
    for path in golden_files() {
        let (nir, main) = common::build(&path);
        let mut first_out = Captured::default();
        let first = execute(&nir, main, &mut first_out, Config::deterministic());
        let mut second_out = Captured::default();
        let second = execute(&nir, main, &mut second_out, Config::deterministic());
        assert_eq!(
            first.trace,
            second.trace,
            "{} traced differently on a second run",
            path.display()
        );
        assert_eq!(
            first_out.lines,
            second_out.lines,
            "{} printed differently on a second run",
            path.display()
        );
    }
}

/// Glitch freedom, read off the trace rather than off the output.
///
/// A turn recomputes each affected node exactly once and publishes exactly once, at the end. That
/// is what rules out a reader seeing a `Snapshot` whose `accepted` and `open` disagree: `snapshot`
/// is a diamond over `opened` — reachable both directly and through `open` — and a graph that
/// recomputed it twice, or published between the two, would show it here.
#[test]
fn a_turn_updates_each_node_once_and_publishes_once() {
    for path in golden_files() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let (nir, main) = common::build(&path);
        let mut out = Captured::default();
        let outcome = execute(&nir, main, &mut out, Config::deterministic());

        let mut updated: Vec<&str> = Vec::new();
        let mut published = 0;
        let mut turns = 0;
        // Every line between one `turn` and the next belongs to that turn: the runtime never
        // interleaves two, which is what the sequence numbers are there to make checkable.
        for line in outcome.trace.lines().chain(["-- turn end"]) {
            let Some(what) = line.split_whitespace().nth(2) else {
                continue;
            };
            match what {
                "turn" => {
                    if turns > 0 {
                        assert_eq!(published, 1, "{name}: a turn published {published} times");
                    }
                    turns += 1;
                    updated.clear();
                    published = 0;
                }
                "commit" | "recompute" if turns > 0 => {
                    let node = line.split_whitespace().nth(3).unwrap_or_default();
                    assert!(
                        published == 0,
                        "{name}: `{node}` was updated after the snapshot was published"
                    );
                    assert!(
                        !updated.contains(&node),
                        "{name}: `{node}` was updated twice in one turn"
                    );
                    updated.push(node);
                }
                "publish" if turns > 0 => published += 1,
                _ => {}
            }
        }
        assert!(turns > 0, "{name}: no turns ran");
        assert_eq!(
            published, 1,
            "{name}: the last turn published {published} times"
        );
    }
}

/// Effects start strictly after the snapshot they were requested in is published.
///
/// Not "usually" and not "in the current implementation": the requests sit in a local `Vec` that
/// nothing in the propagation loop can reach, so there is no code path by which an effect observes
/// an intermediate graph. This is that structural fact, checked.
#[test]
fn effects_start_after_the_publish_of_their_turn() {
    for path in golden_files() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let (nir, main) = common::build(&path);
        let mut out = Captured::default();
        let outcome = execute(&nir, main, &mut out, Config::deterministic());

        let mut published_since_turn = false;
        for line in outcome.trace.lines() {
            match line.split_whitespace().nth(2) {
                Some("turn") => published_since_turn = false,
                Some("publish") => published_since_turn = true,
                Some("effect") => assert!(
                    published_since_turn,
                    "{name}: an effect started before its turn published:\n{}",
                    outcome.trace
                ),
                _ => {}
            }
        }
    }
}

/// Two invariants asserted directly rather than inferred from a trace.
///
/// A trace shows what one run did; these say what every run could do. `order` being a valid
/// topological sort is what makes one propagation pass a fixed point, and each plan being a
/// subsequence of `order` is what makes a plan a *pruning* of it rather than a second ordering that
/// happens to agree today. The second is the invariant a future optimisation is most likely to
/// break silently.
#[test]
fn the_plan_is_well_formed() {
    for path in all_files() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let (nir, _) = common::build(&path);
        for reactor in &nir.reactors {
            let mut placed = vec![usize::MAX; reactor.nodes.len()];
            for (position, &node) in reactor.order.iter().enumerate() {
                placed[node] = position;
            }
            assert_eq!(
                reactor.order.len(),
                reactor.nodes.len(),
                "{name}: `{}` orders {} of {} nodes",
                reactor.name,
                reactor.order.len(),
                reactor.nodes.len()
            );
            for (node, def) in reactor.nodes.iter().enumerate() {
                for &dep in &def.deps {
                    assert!(
                        placed[dep] < placed[node],
                        "{name}: `{}` puts `{}` before its dependency `{}`",
                        reactor.name,
                        def.name,
                        reactor.nodes[dep].name
                    );
                }
            }
            for input in &reactor.inputs {
                assert!(
                    is_subsequence(&input.plan, &reactor.order),
                    "{name}: `{}`'s plan for `{}` is not a subsequence of the order",
                    reactor.name,
                    input.name
                );
            }
        }
    }
}

/// Slot indices follow *source* order, not topological order.
///
/// A slot index is the shape of the durable state projection `DESIGN.md` §14 asks for, so adding a
/// derived signal must not renumber persisted state. Topological order would: a new signal between
/// two state cells could move either of them.
#[test]
fn slots_are_numbered_in_source_order() {
    for path in all_files() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let (nir, _) = common::build(&path);
        for reactor in &nir.reactors {
            let mut previous = None;
            for (slot, &node) in reactor.slots.iter().enumerate() {
                assert_eq!(
                    reactor.nodes[node].kind.slot(),
                    Some(slot),
                    "{name}: `{}` disagrees with itself about slot {slot}",
                    reactor.name
                );
                if let Some(previous) = previous {
                    assert!(
                        previous < node,
                        "{name}: `{}` numbers its slots out of declaration order",
                        reactor.name
                    );
                }
                previous = Some(node);
            }
        }
    }
}

/// Nothing a turn runs may reach a suspension point, a spawn, or an impure builtin.
///
/// `lower` already verifies this and panics if it fails, so reaching the end of this test at all is
/// the assertion. It is written out anyway because "the lowering checks it" is the kind of claim
/// that quietly stops being true when the verifier is made conditional.
#[test]
fn every_node_body_is_pure() {
    for path in all_files() {
        let (nir, _) = common::build(&path);
        for reactor in &nir.reactors {
            for node in &reactor.nodes {
                if let NodeKind::Signal { body } = node.kind {
                    assert!(
                        matches!(nir.fns[body].kind, norn_nir::nir::FnKind::Plain),
                        "a node body is a task"
                    );
                }
            }
        }
    }
}

fn is_subsequence(plan: &[usize], order: &[usize]) -> bool {
    let mut cursor = order.iter();
    plan.iter().all(|node| cursor.any(|next| next == node))
}

fn reactors_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/reactors")
}

fn all_files() -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(reactors_dir())
        .unwrap_or_else(|err| panic!("reading {}: {err}", reactors_dir().display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "norn"))
        .collect();
    files.sort();
    files
}

fn golden_files() -> Vec<PathBuf> {
    all_files()
        .into_iter()
        .filter(|path| {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            !LIVE.contains(&name.as_str())
        })
        .collect()
}

fn check_snapshot(name: &str, actual: &str) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/snapshots");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.snap"));

    if std::env::var("NORN_BLESS").is_ok() {
        std::fs::write(&path, actual).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&path).unwrap_or_else(|_| {
        panic!(
            "missing snapshot {}\nrerun with NORN_BLESS=1 to create it\n\n{actual}",
            path.display()
        )
    });
    if expected != actual {
        panic!(
            "snapshot {} does not match\nrerun with NORN_BLESS=1 to update it\n\n--- expected ---\n{expected}\n--- actual ---\n{actual}",
            path.display()
        );
    }
}
