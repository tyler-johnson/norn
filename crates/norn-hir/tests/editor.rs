//! The editor grammar is part of the language's surface, and it is the one part no compiler test
//! touches: a keyword added to the lexer and forgotten in `norn.tmLanguage.json` renders as a plain
//! identifier, and nothing fails. These tests close that gap by asserting that every word the front
//! end knows appears in some alternation in the grammar.
//!
//! They check membership, not placement — a keyword listed under the wrong scope still colours,
//! just not the colour it should. That is a judgement call, and a test would only be re-asserting
//! whatever the grammar already says.

use std::path::{Path, PathBuf};

use norn_hir::hir::Builtin;
use norn_syntax::lex::{Kw, RESERVED};

#[test]
fn every_keyword_is_in_the_grammar() {
    let grammar = grammar();
    for kw in Kw::ALL {
        let word = kw.text();
        assert!(
            listed(&grammar, word),
            "`{word}` is a keyword but no alternation in {} mentions it",
            grammar_path().display()
        );
    }
}

#[test]
fn every_reserved_word_is_in_the_grammar() {
    // A reserved word is a hard error in the lexer, so the grammar marks it `invalid.illegal` —
    // the editor should say "you cannot name something this" before the compiler has to.
    let grammar = grammar();
    for word in RESERVED {
        assert!(
            listed(&grammar, word),
            "`{word}` is reserved but no alternation in {} mentions it",
            grammar_path().display()
        );
    }
}

#[test]
fn every_builtin_is_in_the_grammar() {
    let grammar = grammar();
    for builtin in Builtin::ALL {
        let name = builtin.name();
        assert!(
            listed(&grammar, name),
            "`{name}` is a builtin but no alternation in {} mentions it",
            grammar_path().display()
        );
    }
}

/// A TextMate grammar is ordered: the first rule that matches at a position wins, and a generic
/// rule placed too early silently swallows what a specific one meant to claim. Nothing about that
/// shows up as an error — the text just colours wrongly — so the orderings the grammar depends on
/// are asserted here.
///
/// Every pair below is a bug that has actually been possible. `-> settled` in an `after` statement
/// really did colour as a return type until `#after-stmt` was moved ahead of `#return-type`.
#[test]
fn specific_rules_precede_the_generic_ones_they_would_lose_to() {
    let order = top_level_patterns();
    let position = |name: &str| {
        order
            .iter()
            .position(|found| found == name)
            .unwrap_or_else(|| panic!("{name} is not in the grammar's top-level patterns"))
    };
    let precedes = [
        (
            "#after-stmt",
            "#return-type",
            "the name after `->` in an `after` statement is an input, not a return type",
        ),
        (
            "#reactor-decl",
            "#call",
            "`Gate` in `reactor Gate(…)` is a declaration, not a call",
        ),
        (
            "#spawn-reactor",
            "#call",
            "`Gate` in `spawn reactor Gate(…)` names a reactor, not a function",
        ),
        (
            "#on-decl",
            "#call",
            "`opened` in `on opened(…)` is the input being answered, not a call",
        ),
        (
            "#member-typed",
            "#member-plain",
            "the annotated form of a member has to be tried before the bare one",
        ),
        (
            "#member-typed",
            "#keywords",
            "`input`/`state`/`signal` carry a name and a type position, which the bare keyword rule does not",
        ),
        (
            "#queue-clause",
            "#call",
            "`capacity:` inside a queue clause is an attribute, not a named argument",
        ),
    ];
    for (earlier, later, why) in precedes {
        assert!(
            position(earlier) < position(later),
            "{earlier} must come before {later} in {}: {why}",
            grammar_path().display()
        );
    }
}

/// The `#name` includes of the grammar's top-level `patterns`, in order.
///
/// Read by slicing rather than parsing, because the workspace has no dependencies and a JSON
/// parser is not worth acquiring for one test. The top-level array is everything between the first
/// `"patterns"` key and `"repository"`, which is the only place the two can be confused.
fn top_level_patterns() -> Vec<String> {
    let grammar = grammar();
    let start = grammar
        .find("\"patterns\"")
        .expect("the grammar has top-level patterns");
    let end = grammar[start..]
        .find("\"repository\"")
        .map(|at| start + at)
        .unwrap_or(grammar.len());
    let patterns = &grammar[start..end];
    patterns
        .match_indices("\"#")
        .map(|(at, _)| {
            let rest = &patterns[at + 1..];
            let close = rest.find('"').expect("an include name is quoted");
            rest[..close].to_string()
        })
        .collect()
}

#[test]
fn the_extension_claims_norn_files() {
    let manifest = read(&editor_dir().join("package.json"));
    assert!(manifest.contains("\".norn\""), "no `.norn` extension");
    assert!(
        manifest.contains("\"source.norn\""),
        "the grammar is not wired to a scope name"
    );
    // The scope name in the manifest has to be the one the grammar declares, or the grammar is
    // shipped and never applied.
    assert!(
        grammar().contains("\"scopeName\": \"source.norn\""),
        "the grammar declares a different scope name"
    );
}

/// True when `word` appears as a branch of a regex alternation: `(?:word|…)`, `(…|word|…)`, or
/// `(…|word)`. Bare containment would pass on a comment mentioning the word in prose, which is
/// exactly the false negative these tests exist to avoid.
fn listed(grammar: &str, word: &str) -> bool {
    grammar.match_indices(word).any(|(at, _)| {
        let before = grammar[..at].chars().next_back();
        let after = grammar[at + word.len()..].chars().next();
        matches!(before, Some('(' | ':' | '|')) && matches!(after, Some('|' | ')'))
    })
}

fn grammar() -> String {
    read(&grammar_path())
}

fn grammar_path() -> PathBuf {
    editor_dir().join("syntaxes/norn.tmLanguage.json")
}

fn editor_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../editors/vscode")
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|err| panic!("reading {}: {err}", path.display()))
}
