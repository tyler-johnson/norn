//! Targeted tests for the grammar's ambiguous corners.
//!
//! The snapshot corpus proves whole files parse; these pin down the specific decisions — layout
//! sensitivity, `await`/`?` associativity, speculative type arguments, and the shape rules that
//! keep spelling out of the grammar — that a future change could silently reverse.

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
fn construction_is_spelled_like_a_call() {
    // `User(id: 7)` builds and `user(id: 7)` calls, and the grammar cannot tell — both are
    // calls here, and name resolution in the checker is what separates them.
    assert_eq!(expr("User(id: 7)"), "(call (path User) (arg id (int 7)))");
    assert_eq!(expr("user(id: 7)"), "(call (path user) (arg id (int 7)))");
}

#[test]
fn capitalization_carries_no_meaning() {
    // The same spelling parses the same way in either case; resolution, not case, decides
    // what a call names.
    assert_eq!(expr("point(x: 1)"), "(call (path point) (arg x (int 1)))");
    assert_eq!(expr("Point(x: 1)"), "(call (path Point) (arg x (int 1)))");
}

#[test]
fn the_constructor_sigil_is_gone() {
    // `#` marked a data constructor before construction was spelled like a call. It is not a
    // token any more, and a leftover one is an ordinary lexer error.
    assert!(
        errors("fn main() {\n    let x = #User(id: 7)\n}\n").contains("unexpected character `#`")
    );
}

#[test]
fn a_unit_variant_pattern_needs_no_parentheses() {
    // `E.NotFound()` and `E.NotFound` mean the same thing, and the printer settles on the
    // shorter form.
    let parsed =
        parse("fn main() {\n    match e {\n        E.NotFound() => 1\n        _ => 2\n    }\n}\n");
    assert!(parsed.ok());
    assert!(print::module(&parsed.module).contains("E.NotFound => 1"));
    // A lone name keeps its `()`: bare, it would be a binding rather than a constructor.
    let parsed =
        parse("fn main() {\n    match e {\n        Foo() => 1\n        _ => 2\n    }\n}\n");
    assert!(parsed.ok());
    assert!(print::module(&parsed.module).contains("Foo() => 1"));
}

#[test]
fn a_brace_always_opens_a_block() {
    // No scrutinee restriction is needed, because nothing else claims a brace.
    let dumped = ast("fn main() {\n    match config {\n        _ => 1\n    }\n}\n");
    assert!(dumped.contains("(match (path config)"), "{dumped}");

    // A constructor in scrutinee position needs no parentheses to survive.
    let source = "fn main() {\n    match Point(x: 1) {\n        _ => 1\n    }\n}\n";
    let parsed = parse(source);
    assert!(parsed.ok());
    let printed = print::module(&parsed.module);
    assert!(printed.contains("match Point(x: 1) {"), "{printed}");
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
    assert!(rendered.contains("Name(field: value)"), "{rendered}");
}

#[test]
fn a_bare_name_in_a_pattern_binds_whatever_its_case() {
    let dumped =
        ast("fn main() {\n    match x {\n        NotFound => 1\n        other => 2\n    }\n}\n");
    assert!(dumped.contains("(bind NotFound)"), "{dumped}");
    assert!(dumped.contains("(bind other)"), "{dumped}");
}

#[test]
fn a_dotted_pattern_matches_a_constructor() {
    // The shape is the whole distinction: a bare name binds, a dotted one matches.
    let dumped = ast(
        "fn main() {\n    match x {\n        LoadError.NotFound => 1\n        _ => 2\n    }\n}\n",
    );
    assert!(
        dumped.contains("(construct LoadError.NotFound)"),
        "{dumped}"
    );
}

#[test]
fn patterns_mirror_construction() {
    let dumped = ast(
        "fn main() {\n    match e {\n        E.Io(code: 404, msg) => msg\n        E.Io(..) => \"x\"\n    }\n}\n",
    );
    assert!(
        dumped.contains("(construct E.Io (arg code (int 404)) (arg (bind msg)))"),
        "{dumped}"
    );
    assert!(dumped.contains("(construct E.Io ..)"), "{dumped}");
}

#[test]
fn reserved_words_explain_themselves() {
    let rendered = errors("fn main() {\n    let event = 1\n}\n");
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

#[test]
fn a_named_import_lists_its_items() {
    let dumped = ast("import { digits, pad as p } from \"./fmt\"\n");
    assert!(
        dumped.contains("(import \"./fmt\" (item digits) (item pad p))"),
        "{dumped}"
    );
}

#[test]
fn a_namespace_import_binds_one_name() {
    let dumped = ast("import * as fmt from \"./fmt\"\n");
    assert!(dumped.contains("(import \"./fmt\" (star fmt))"), "{dumped}");
}

#[test]
fn an_import_list_may_span_lines() {
    let dumped = ast("import {\n    digits\n    pad as p,\n} from \"./fmt\"\n");
    assert!(
        dumped.contains("(import \"./fmt\" (item digits) (item pad p))"),
        "{dumped}"
    );
}

#[test]
fn imports_round_trip() {
    let source = "import { digits, pad as p } from \"./fmt\"\nimport * as strings from \"./util/strings\"\n\nfn main() {}\n";
    let parsed = parse(source);
    assert!(parsed.ok(), "{}", errors(source));
    assert_eq!(print::module(&parsed.module), source);
}

#[test]
fn an_import_without_a_clause_teaches_both_forms() {
    let rendered = errors("import fmt from \"./fmt\"\n");
    assert!(
        rendered.contains("expected an import list or `* as` after `import`"),
        "{rendered}"
    );
    assert!(rendered.contains("import * as fmt from"), "{rendered}");
}

#[test]
fn an_import_without_from_teaches_the_shape() {
    // The habit being caught is the old dotted `use std.fs` spelling: no `from`, no string.
    let rendered = errors("import { digits } of \"./fmt\"\n");
    assert!(
        rendered.contains("expected `from \"…\"` naming the module's file"),
        "{rendered}"
    );
    let rendered = errors("import { digits } from fmt\n");
    assert!(
        rendered.contains("expected `from \"…\"` naming the module's file"),
        "{rendered}"
    );
}

#[test]
fn an_empty_import_list_is_refused() {
    let rendered = errors("import {} from \"./fmt\"\n");
    assert!(
        rendered.contains("an import list cannot be empty"),
        "{rendered}"
    );
}

#[test]
fn recovery_passes_a_broken_import() {
    let parsed = parse("import { from \"./fmt\"\n\nfn fine() -> I64 {\n    return 1\n}\n");
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
fn from_is_not_a_keyword() {
    // ES treats `from` contextually and so does Norn: `matching.norn` binds `from` and `to` as
    // pattern variables, and an import must not take the word away from them.
    let dumped =
        ast("fn main() {\n    match x {\n        Range(from, to) => from + to\n    }\n}\n");
    assert!(dumped.contains("(bind from)"), "{dumped}");
    assert!(dumped.contains("(bind to)"), "{dumped}");
    let dumped = ast("fn main() {\n    let from = 1\n    let x = from\n}\n");
    assert!(dumped.contains("(let from"), "{dumped}");
}

#[test]
fn a_module_header_teaches_its_replacement() {
    // `module` is no longer a keyword, so the old header is a bare identifier where a declaration
    // was expected — and the diagnostic says what replaced it.
    let rendered = errors("module fmt\n\nfn main() {}\n");
    assert!(
        rendered.contains("a file no longer opens with `module …`"),
        "{rendered}"
    );
    // The word itself is an ordinary identifier now.
    let dumped = ast("fn main() {\n    let module = 1\n    let x = module\n}\n");
    assert!(dumped.contains("(let module"), "{dumped}");
}

#[test]
fn a_use_declaration_teaches_the_import_spelling() {
    let rendered = errors("use std.fs\n\nfn main() {}\n");
    assert!(
        rendered.contains("imports are spelled `import { name } from \"./file\"`"),
        "{rendered}"
    );
    // `use` is an ordinary identifier now; only the `uses { … }` clause keeps its keyword.
    let dumped = ast("fn main() {\n    let use = 1\n    let x = use\n}\n");
    assert!(dumped.contains("(let use"), "{dumped}");
}

#[test]
fn export_marks_each_kind_of_declaration() {
    let dumped = ast(
        "export struct P {\n    x: I64\n}\n\nexport enum E {\n    A\n}\n\nexport fn f() {}\n\nexport task fn t() {}\n\nexport reactor R() {\n    input go: () [capacity: 1, overflow: reject]\n    on go() {}\n}\n",
    );
    assert!(dumped.contains("(struct P export"), "{dumped}");
    assert!(dumped.contains("(enum E export"), "{dumped}");
    assert!(dumped.contains("(fn f export"), "{dumped}");
    assert!(dumped.contains("(fn t export task"), "{dumped}");
    assert!(dumped.contains("(reactor R export"), "{dumped}");
}

#[test]
fn export_round_trips() {
    let source = "export struct P {\n    x: I64\n}\n\nexport task fn t() {}\n";
    let parsed = parse(source);
    assert!(parsed.ok(), "{}", errors(source));
    assert_eq!(print::module(&parsed.module), source);
}

#[test]
fn a_top_level_export_signal_is_pointed_home() {
    let rendered = errors("export signal open = 1\n");
    assert!(
        rendered.contains("`export signal` lives inside a reactor"),
        "{rendered}"
    );
}

#[test]
fn export_prefixes_only_declarations() {
    let rendered = errors("export let x = 1\n");
    assert!(
        rendered.contains("`export` prefixes `fn`, `task fn`, `struct`, `enum`, and `reactor`"),
        "{rendered}"
    );
}

#[test]
fn an_exported_signal_still_parses_inside_a_reactor() {
    // The member spelling predates file-level `export`; adding the top-level arm must not steal it.
    let dumped = ast(
        "reactor Gate() {\n    input go: () [capacity: 1, overflow: reject]\n    state n: I64 = 0\n    on go() {\n        n = n + 1\n    }\n    export signal open = n\n}\n",
    );
    assert!(dumped.contains("(signal open export"), "{dumped}");
}

#[test]
fn spawn_takes_a_whole_call() {
    // Not just the callee: `spawn f(x)` starts `f(x)`, and nothing else would be worth writing.
    assert_eq!(
        expr("spawn serve(listener)"),
        "(spawn (call (path serve) (arg (path listener))))"
    );
}

#[test]
fn a_scope_is_an_expression() {
    // It has a value — its body's — so it may sit anywhere an expression may, including as the
    // body of a match arm.
    let dumped = ast(
        "task fn main() {\n    match x {\n        _ => scope {\n            spawn f()\n        }\n    }\n}\n",
    );
    assert!(dumped.contains("(arm _ (scope (block (spawn"), "{dumped}");
}

#[test]
fn scope_and_spawn_round_trip() {
    let source =
        "task fn main() {\n    scope {\n        spawn worker()\n        await done()\n    }\n}\n";
    let parsed = parse(source);
    assert!(parsed.ok(), "{}", errors(source));
    assert_eq!(print::module(&parsed.module), source);
}

#[test]
fn loops_dump_their_shapes() {
    assert_eq!(
        expr("while ready { step() }"),
        "(while (path ready) (block (call (path step))))"
    );
    assert_eq!(expr("loop { step() }"), "(loop (block (call (path step))))");
    assert_eq!(expr("loop { break }"), "(loop (block (break)))");
    assert_eq!(expr("loop { break 5 }"), "(loop (block (break (int 5))))");
    assert_eq!(expr("loop { continue }"), "(loop (block (continue)))");
}

#[test]
fn a_break_value_does_not_cross_a_line_break() {
    // Like `return`: the expression on the next line is its own statement, not the break's value.
    let dumped = ast("fn f() {\n    loop {\n        break\n        step()\n    }\n}\n")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert!(dumped.contains("(break) (call (path step))"), "{dumped}");
}

#[test]
fn a_comma_ends_a_bare_break_in_a_match_arm() {
    // Match arms separate by comma-or-newline, so `break,` on one line must leave the comma to the
    // arm list rather than swallowing it as the start of a value.
    let dumped = expr("loop { match poll() { Err(_) => break, Ok(v) => v } }");
    assert!(
        dumped.contains("(arm (construct Err (arg _)) (break))"),
        "{dumped}"
    );
}

#[test]
fn a_break_value_ends_at_a_comma_too() {
    let dumped = expr("loop { match poll() { Err(_) => break 0, Ok(v) => v } }");
    assert!(dumped.contains("(break (int 0))"), "{dumped}");
}

#[test]
fn loops_round_trip() {
    let source = "fn f() -> I64 {\n    let mut n = 3\n    while n > 0 {\n        n = n - 1\n    }\n    loop {\n        if n == 0 {\n            break\n        }\n        continue\n    }\n    loop {\n        break n\n    }\n}\n";
    let parsed = parse(source);
    assert!(parsed.ok(), "{}", errors(source));
    let canonical = print::module(&parsed.module);
    assert_eq!(canonical, source);
    assert_eq!(
        dump::module(&parsed.module),
        dump::module(&parse(&canonical).module),
        "the canonical form parses to a different tree"
    );
}
