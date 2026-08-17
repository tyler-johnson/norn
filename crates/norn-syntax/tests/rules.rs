//! Targeted tests for the grammar's ambiguous corners.
//!
//! The snapshot corpus proves whole files parse; these pin down the specific decisions — layout
//! sensitivity, `await`/`?` associativity, speculative type arguments, and the `#` that separates
//! a data constructor from a call — that a future change could silently reverse.

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
    dump::expr(value)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
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
fn a_constructor_is_marked_and_a_call_is_not() {
    assert_eq!(expr("#User(id: 7)"), "(construct User (arg id (int 7)))");
    assert_eq!(expr("user(id: 7)"), "(call (path user) (arg id (int 7)))");
}

#[test]
fn capitalization_carries_no_meaning() {
    // The same spelling parses the same way in either case; only the `#` decides.
    assert_eq!(expr("#point(x: 1)"), "(construct point (arg x (int 1)))");
    assert_eq!(expr("Point(x: 1)"), "(call (path Point) (arg x (int 1)))");
}

#[test]
fn a_unit_constructor_needs_no_parentheses() {
    assert_eq!(
        expr("#LoadError.NotFound"),
        "(construct LoadError.NotFound)"
    );
    // `#Foo()` means the same thing, and the printer settles on the shorter form.
    let parsed = parse("fn main() {\n    let x = #Foo()\n}\n");
    assert!(parsed.ok());
    assert!(print::module(&parsed.module).contains("let x = #Foo\n"));
}

#[test]
fn a_brace_always_opens_a_block() {
    // No scrutinee restriction is needed, because nothing else claims a brace.
    let dumped = ast("fn main() {\n    match config {\n        _ => 1\n    }\n}\n");
    assert!(dumped.contains("(match (path config)"), "{dumped}");

    // A constructor in scrutinee position needs no parentheses to survive.
    let source = "fn main() {\n    match #Point(x: 1) {\n        _ => 1\n    }\n}\n";
    let parsed = parse(source);
    assert!(parsed.ok());
    let printed = print::module(&parsed.module);
    assert!(printed.contains("match #Point(x: 1) {"), "{printed}");
    assert_eq!(printed, print::module(&parse(&printed).module));
}

#[test]
fn a_brace_after_an_expression_explains_itself() {
    // What a Rust or Go reader writes first.
    let rendered = errors("fn main() {\n    let user = User { id: 7 }\n}\n");
    assert!(
        rendered.contains("a brace always opens a block"),
        "{rendered}"
    );
    assert!(rendered.contains("#Name(field: value)"), "{rendered}");
}

#[test]
fn a_bare_name_in_a_pattern_binds_whatever_its_case() {
    let dumped =
        ast("fn main() {\n    match x {\n        NotFound => 1\n        other => 2\n    }\n}\n");
    assert!(dumped.contains("(bind NotFound)"), "{dumped}");
    assert!(dumped.contains("(bind other)"), "{dumped}");
}

#[test]
fn a_dotted_pattern_must_be_marked() {
    let rendered =
        errors("fn main() {\n    match x {\n        LoadError.NotFound => 1\n    }\n}\n");
    assert!(
        rendered.contains("a bare name in a pattern binds"),
        "{rendered}"
    );
    assert!(rendered.contains("#LoadError.NotFound"), "{rendered}");
}

#[test]
fn patterns_mirror_construction() {
    let dumped = ast(
        "fn main() {\n    match e {\n        #E.Io(code: 404, msg) => msg\n        #E.Io(..) => \"x\"\n    }\n}\n",
    );
    assert!(
        dumped.contains("(construct E.Io (arg code (int 404)) (arg (bind msg)))"),
        "{dumped}"
    );
    assert!(dumped.contains("(construct E.Io ..)"), "{dumped}");
}

#[test]
fn reserved_words_explain_themselves() {
    let rendered = errors("fn main() {\n    let reactor = 1\n}\n");
    assert!(
        rendered.contains("reserved for a later milestone"),
        "{rendered}"
    );
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
