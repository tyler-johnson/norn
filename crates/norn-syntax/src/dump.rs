//! S-expression dump of the AST, used as the structural half of the snapshot corpus.
//!
//! Spans are deliberately omitted. The canonical printer already exercises structure, and byte
//! offsets in a golden file would churn on every unrelated whitespace edit for no added coverage.

use crate::ast::*;

/// A node renders inline when it is small and holds only atoms; otherwise one child per line.
enum Node {
    Atom(String),
    List(String, Vec<Node>),
}

const WIDTH: usize = 84;

impl Node {
    /// The whole subtree on one line.
    fn inline(&self) -> String {
        match self {
            Node::Atom(text) => text.clone(),
            Node::List(head, children) => {
                let mut out = format!("({head}");
                for child in children {
                    out.push(' ');
                    out.push_str(&child.inline());
                }
                out.push(')');
                out
            }
        }
    }

    fn render(&self, indent: usize, out: &mut String) {
        let flat = self.inline();
        if indent + flat.len() <= WIDTH {
            out.push_str(&flat);
            return;
        }
        let Node::List(head, children) = self else {
            out.push_str(&flat);
            return;
        };
        // Leading atoms are names — `(fn greet`, `(record User` — and stay on the head line.
        let leading = children.iter().take_while(|c| matches!(c, Node::Atom(_))).count();
        out.push_str(&format!("({head}"));
        for child in &children[..leading] {
            out.push(' ');
            out.push_str(&child.inline());
        }
        let pad = " ".repeat(indent + 2);
        for child in &children[leading..] {
            out.push('\n');
            out.push_str(&pad);
            child.render(indent + 2, out);
        }
        out.push(')');
    }
}

fn atom(text: impl Into<String>) -> Node {
    Node::Atom(text.into())
}

fn list(head: impl Into<String>, children: Vec<Node>) -> Node {
    Node::List(head.into(), children)
}

pub fn module(module: &Module) -> String {
    let mut children = Vec::new();
    if let Some(name) = &module.name {
        children.push(list("module-name", vec![atom(name.text())]));
    }
    for decl in &module.uses {
        children.push(list("use", vec![atom(decl.path.text())]));
    }
    for item in &module.items {
        children.push(dump_item(item));
    }
    let mut out = String::new();
    list("module", children).render(0, &mut out);
    out.push('\n');
    out
}

/// Dump a single expression. Used by tests that pin down one grammar decision at a time.
pub fn expr(expr: &Expr) -> String {
    let mut out = String::new();
    dump_expr(expr).render(0, &mut out);
    out
}

fn dump_item(item: &Item) -> Node {
    match item {
        Item::Record(decl) => {
            let mut children = vec![atom(&decl.name.name)];
            for field in &decl.fields {
                children.push(list(
                    "field",
                    vec![atom(&field.name.name), dump_type(&field.ty)],
                ));
            }
            list("record", children)
        }
        Item::Enum(decl) => {
            let mut children = vec![atom(&decl.name.name)];
            for variant in &decl.variants {
                let mut parts = vec![atom(&variant.name.name)];
                match &variant.payload {
                    VariantPayload::Unit => {}
                    VariantPayload::Tuple(types) => {
                        parts.push(list("tuple", types.iter().map(dump_type).collect()));
                    }
                    VariantPayload::Record(fields) => {
                        parts.push(list(
                            "fields",
                            fields
                                .iter()
                                .map(|f| {
                                    list("field", vec![atom(&f.name.name), dump_type(&f.ty)])
                                })
                                .collect(),
                        ));
                    }
                }
                children.push(list("variant", parts));
            }
            list("enum", children)
        }
        Item::Fn(decl) => {
            let mut children = vec![atom(&decl.name.name)];
            if decl.is_task {
                children.push(atom("task"));
            }
            children.push(list(
                "params",
                decl.params
                    .iter()
                    .map(|p| list("param", vec![atom(&p.name.name), dump_type(&p.ty)]))
                    .collect(),
            ));
            if let Some(ret) = &decl.ret {
                children.push(list("ret", vec![dump_type(ret)]));
            }
            if !decl.uses.is_empty() {
                children.push(list(
                    "uses",
                    decl.uses.iter().map(|p| atom(p.text())).collect(),
                ));
            }
            children.push(dump_block(&decl.body));
            list("fn", children)
        }
    }
}

fn dump_type(ty: &Type) -> Node {
    match &ty.kind {
        TypeKind::Unit => atom("unit"),
        TypeKind::Path { path, args } if args.is_empty() => atom(path.text()),
        TypeKind::Path { path, args } => {
            let mut children = vec![atom(path.text())];
            children.extend(args.iter().map(dump_type));
            list("ty", children)
        }
        TypeKind::Ref { mutable, inner } => {
            list(if *mutable { "ref-mut" } else { "ref" }, vec![dump_type(inner)])
        }
    }
}

fn dump_block(block: &Block) -> Node {
    list("block", block.stmts.iter().map(dump_stmt).collect())
}

fn dump_stmt(stmt: &Stmt) -> Node {
    match &stmt.kind {
        StmtKind::Let { mutable, name, ty, value } => {
            let mut children = vec![atom(&name.name)];
            if *mutable {
                children.push(atom("mut"));
            }
            if let Some(ty) = ty {
                children.push(list("ty", vec![dump_type(ty)]));
            }
            children.push(dump_expr(value));
            list("let", children)
        }
        StmtKind::Assign { target, value } => {
            list("assign", vec![dump_expr(target), dump_expr(value)])
        }
        StmtKind::Return(None) => list("return", vec![]),
        StmtKind::Return(Some(value)) => list("return", vec![dump_expr(value)]),
        StmtKind::Expr(expr) => dump_expr(expr),
    }
}

fn dump_expr(expr: &Expr) -> Node {
    match &expr.kind {
        ExprKind::Unit => atom("unit"),
        ExprKind::Int(v) => list("int", vec![atom(v.to_string())]),
        ExprKind::Float(v) => list("float", vec![atom(format!("{v:?}"))]),
        ExprKind::Str(v) => list("str", vec![atom(format!("{v:?}"))]),
        ExprKind::Bool(v) => list("bool", vec![atom(v.to_string())]),
        ExprKind::Path(path) => list("path", vec![atom(path.text())]),
        ExprKind::Unary { op, expr } => {
            list("unary", vec![atom(op.text().trim()), dump_expr(expr)])
        }
        ExprKind::Binary { op, lhs, rhs } => {
            list("binary", vec![atom(op.text()), dump_expr(lhs), dump_expr(rhs)])
        }
        ExprKind::Field { base, name } => {
            list("field", vec![dump_expr(base), atom(&name.name)])
        }
        ExprKind::Index { base, index } => {
            list("index", vec![dump_expr(base), dump_expr(index)])
        }
        ExprKind::Call { callee, type_args, args } => {
            let mut children = vec![dump_expr(callee)];
            if !type_args.is_empty() {
                children.push(list("type-args", type_args.iter().map(dump_type).collect()));
            }
            for arg in args {
                children.push(match &arg.name {
                    Some(name) => list("arg", vec![atom(&name.name), dump_expr(&arg.value)]),
                    None => list("arg", vec![dump_expr(&arg.value)]),
                });
            }
            list("call", children)
        }
        ExprKind::Record { path, fields } => {
            let mut children = vec![atom(path.text())];
            for field in fields {
                children.push(list(
                    "field",
                    vec![atom(&field.name.name), dump_expr(&field.value)],
                ));
            }
            list("record", children)
        }
        ExprKind::Await(inner) => list("await", vec![dump_expr(inner)]),
        ExprKind::Try(inner) => list("try", vec![dump_expr(inner)]),
        ExprKind::Block(block) => dump_block(block),
        ExprKind::If { cond, then, els } => {
            let mut children = vec![dump_expr(cond), dump_block(then)];
            if let Some(els) = els {
                children.push(list("else", vec![dump_expr(els)]));
            }
            list("if", children)
        }
        ExprKind::Match { scrutinee, arms } => {
            let mut children = vec![dump_expr(scrutinee)];
            for arm in arms {
                let mut parts = vec![dump_pat(&arm.pat)];
                if let Some(guard) = &arm.guard {
                    parts.push(list("guard", vec![dump_expr(guard)]));
                }
                parts.push(dump_expr(&arm.body));
                children.push(list("arm", parts));
            }
            list("match", children)
        }
        ExprKind::Lambda { is_task, params, body } => {
            let mut children = Vec::new();
            if *is_task {
                children.push(atom("task"));
            }
            children.push(list("params", params.iter().map(dump_pat).collect()));
            children.push(dump_expr(body));
            list("lambda", children)
        }
    }
}

fn dump_pat(pat: &Pat) -> Node {
    match &pat.kind {
        PatKind::Wild => atom("_"),
        PatKind::Binding(ident) => list("bind", vec![atom(&ident.name)]),
        PatKind::Int(v) => list("int", vec![atom(v.to_string())]),
        PatKind::Str(v) => list("str", vec![atom(format!("{v:?}"))]),
        PatKind::Bool(v) => list("bool", vec![atom(v.to_string())]),
        PatKind::Path(path) => list("variant", vec![atom(path.text())]),
        PatKind::Tuple { path, elems } => {
            let mut children = vec![atom(path.text())];
            children.extend(elems.iter().map(dump_pat));
            list("variant", children)
        }
        PatKind::Record { path, fields, rest } => {
            let mut children = vec![atom(path.text())];
            for field in fields {
                children.push(match &field.pat {
                    Some(inner) => list("field", vec![atom(&field.name.name), dump_pat(inner)]),
                    None => list("field", vec![atom(&field.name.name)]),
                });
            }
            if *rest {
                children.push(atom(".."));
            }
            list("variant-record", children)
        }
        PatKind::Or(alts) => list("or", alts.iter().map(dump_pat).collect()),
    }
}
