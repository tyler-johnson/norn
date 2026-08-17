//! Targeted tests for the grammar's ambiguous corners.
//!
//! The snapshot corpus proves whole files parse; these pin down the specific decisions — layout
//! sensitivity, `await`/`?` associativity, speculative type arguments, and record-literal
//! disambiguation — that a future change could silently reverse.

use norn_syntax::ast::{Item, StmtKind};
use norn_syntax::{SourceFile, dump, parse, print, render_all};

/// Parse a whole module and return its s-expression dump, asserting it was clean.
fn ast(source: &str) -> String {
    let parsed = parse(source);
    assert!(
        parsed.ok(),
        "unexpected parse error:\n{}",
        render_all(&SourceFile::new("test", source), &parsed.errors)
    );
    dump::module(&parsed.module)
}

/// Parse a single expression by wrapping it in a function body, and dump just that expression.
fn expr(source: &str) -> String {
    let wrapped = format!("fn main() {{\n    let x = {source}\n}}\n");
    let parsed = parse(&wrapped);
    assert!(
        parsed.ok(),
        "unexpected parse error:\n{}",
        render_all(&SourceFile::new("test", &wrapped), &parsed.errors)
    );
    let Some(Item::Fn(decl)) = parsed.module.items.first() else {
        panic!("expected one function");
    };
    let Some(StmtKind::Let { value, .. }) = decl.body.stmts.first().map(|s| &s.kind) else {
        panic!("expected a `let` statement");
    };
    // Collapse the dump's line wrapping: these tests are about structure, not layout.
    dump::expr(value).split_whitespace().collect::<Vec<_>>().join(" ")
}

fn errors(source: &str) -> String {
    let parsed = parse(source);
    assert!(!parsed.ok(), "expected a parse error, got none");
    render_all(&SourceFile::new("test", source), &parsed.errors)
}

#[test]
fn await_binds_before_try() {
    // `await f()?` awaits the task, then propagates the failure of its result.
    assert_eq!(expr("await f()?"), "(try (await (call (path f))))");
}

#[test]
fn await_covers_the_whole_postfix_chain() {
    // The awaited value is `http.get(url).timeout(d)`, not `http.get`.
    assert_eq!(
        expr("await http.get(url).timeout(d)"),
        "(await (call (field (call (path http.get) (arg (path url))) timeout) (arg (path d))))"
    );
}

#[test]
fn comparison_is_not_a_generic_call() {
    let dumped = expr("a < b");
    assert!(dumped.contains("(binary <"), "{dumped}");
}

#[test]
fn type_arguments_are_accepted_when_a_call_follows() {
    let dumped = expr("response.json<Profile>(limit)");
    assert!(dumped.contains("(type-args Profile)"), "{dumped}");
}

#[test]
fn a_failed_type_argument_attempt_leaves_no_diagnostic() {
    // The speculative parse must roll back its errors along with its position.
    let parsed = parse("fn main() {\n    let x = a < b\n}\n");
    assert!(parsed.ok(), "speculative parse leaked a diagnostic");
}

#[test]
fn a_dot_continues_a_chain_across_a_line_break() {
    let dumped = ast("fn main() {\n    let x = a\n        .b()\n        .c()\n}\n");
    assert_eq!(dumped.matches("(call").count(), 2, "{dumped}");
}

#[test]
fn a_paren_on_a_fresh_line_is_not_a_call() {
    // Otherwise `let x = f` followed by a parenthesised statement would silently become `f(...)`.
    let dumped = ast("fn main() {\n    let x = f\n    (b)\n}\n");
    assert!(!dumped.contains("(call"), "{dumped}");
}

#[test]
fn statements_need_a_line_break() {
    assert!(errors("fn main() {\n    let a = 1 let b = 2\n}\n").contains("expected a line break"));
}

#[test]
fn a_semicolon_is_reported_as_a_separator_mistake() {
    assert!(errors("fn main() {\n    let a = 1;\n}\n").contains("not `;`"));
}

#[test]
fn an_uppercase_name_before_a_brace_is_a_record_literal() {
    assert!(expr("Point { x: 1, y: 2 }").starts_with("(record Point"));
}

#[test]
fn a_scrutinee_never_starts_a_record_literal() {
    // `match config { ... }` must read as a match over `config`, not a literal of type `config`.
    let dumped = ast("fn main() {\n    match config {\n        _ => 1\n    }\n}\n");
    assert!(dumped.contains("(match (path config)"), "{dumped}");
}

#[test]
fn a_record_literal_scrutinee_survives_a_round_trip() {
    let source = "fn main() {\n    match Point { x: 1 } {\n        _ => 1\n    }\n}\n";
    let parsed = parse(source);
    // Parsed as `match Point` with a block body — which is a syntax error, not a record literal.
    assert!(!parsed.ok());

    let parenthesised = "fn main() {\n    match (Point { x: 1 }) {\n        _ => 1\n    }\n}\n";
    let parsed = parse(parenthesised);
    assert!(parsed.ok());
    let printed = print::module(&parsed.module);
    assert!(printed.contains("match (Point { x: 1 })"), "{printed}");
    assert!(parse(&printed).ok(), "the printer dropped the required parentheses");
}

#[test]
fn reserved_words_explain_themselves() {
    let rendered = errors("fn main() {\n    let reactor = 1\n}\n");
    assert!(rendered.contains("reserved for a later milestone"), "{rendered}");
}

#[test]
fn a_float_is_only_a_float_with_a_digit_after_the_dot() {
    assert_eq!(expr("2.seconds"), "(field (int 2) seconds)");
    assert_eq!(expr("2.5"), "(float 2.5)");
}

#[test]
fn spans_point_at_the_offending_token() {
    let source = "fn main() {\n    let a = 1 let b = 2\n}\n";
    let parsed = parse(source);
    let span = parsed.errors[0].span;
    assert_eq!(&source[span.start as usize..span.end as usize], "let");
}

#[test]
fn recovery_reaches_later_declarations() {
    let parsed = parse("fn broken( {\n}\n\nfn fine() -> I64 {\n    return 1\n}\n");
    assert!(!parsed.ok());
    let names: Vec<_> = parsed
        .module
        .items
        .iter()
        .map(|item| match item {
            norn_syntax::ast::Item::Fn(decl) => decl.name.name.clone(),
            _ => String::new(),
        })
        .collect();
    assert_eq!(names, vec!["fine"]);
}

#[test]
fn an_empty_file_is_an_empty_module() {
    assert_eq!(ast("").trim(), "(module)");
}
