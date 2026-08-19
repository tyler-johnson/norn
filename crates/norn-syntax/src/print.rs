//! Canonical source rendering.
//!
//! The AST is not lossless, so this is a normaliser rather than a formatter: comments and original
//! layout are gone. What it guarantees is idempotence — `print(parse(print(parse(s))))` equals
//! `print(parse(s))` — which is the property the snapshot corpus checks, and which fails loudly
//! whenever the printer and parser disagree about how a construct nests.

use crate::ast::*;

const INDENT: &str = "    ";

/// Precedence used to decide where parentheses are required. Higher binds tighter.
const ATOM: u8 = 100;
const UNARY: u8 = 20;
const LAMBDA: u8 = 0;

pub fn module(module: &Module) -> String {
    let mut out = String::new();
    if !module.imports.is_empty() {
        if !out.is_empty() {
            out.push('\n');
        }
        for decl in &module.imports {
            out.push_str(&print_import(decl));
        }
    }
    for item in &module.items {
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(&print_item(item));
    }
    out
}

/// One line whichever form it takes; the specifier is re-escaped through the same string printing
/// every literal gets.
fn print_import(decl: &ImportDecl) -> String {
    let specifier = print_string(&decl.specifier);
    match &decl.kind {
        ImportKind::Named(items) => {
            let items: Vec<_> = items
                .iter()
                .map(|item| match &item.alias {
                    Some(alias) => format!("{} as {}", item.name.name, alias.name),
                    None => item.name.name.clone(),
                })
                .collect();
            format!("import {{ {} }} from {specifier}\n", items.join(", "))
        }
        ImportKind::Namespace(name) => format!("import * as {} from {specifier}\n", name.name),
    }
}

/// The declared type parameters, or nothing at all when there are none — which is what keeps
/// every existing snapshot byte-identical.
fn print_type_params(params: &[TypeParam]) -> String {
    if params.is_empty() {
        return String::new();
    }
    let rendered: Vec<String> = params
        .iter()
        .map(|param| {
            if param.bounds.is_empty() {
                param.name.name.clone()
            } else {
                let bounds: Vec<_> = param.bounds.iter().map(|b| b.text()).collect();
                format!("{}: {}", param.name.name, bounds.join(" + "))
            }
        })
        .collect();
    format!("<{}>", rendered.join(", "))
}

fn print_item(item: &Item) -> String {
    match item {
        Item::Struct(decl) => {
            let export = if decl.exported.is_some() {
                "export "
            } else {
                ""
            };
            let mut out = format!(
                "{export}struct {}{} {{\n",
                decl.name.name,
                print_type_params(&decl.type_params)
            );
            for field in &decl.fields {
                out.push_str(&format!(
                    "{INDENT}{}: {}\n",
                    field.name.name,
                    print_type(&field.ty)
                ));
            }
            out.push_str("}\n");
            out
        }
        Item::Enum(decl) => {
            let export = if decl.exported.is_some() {
                "export "
            } else {
                ""
            };
            let mut out = format!(
                "{export}enum {}{} {{\n",
                decl.name.name,
                print_type_params(&decl.type_params)
            );
            for variant in &decl.variants {
                out.push_str(INDENT);
                out.push_str(&variant.name.name);
                match &variant.payload {
                    VariantPayload::Unit => {}
                    VariantPayload::Tuple(types) => {
                        let types: Vec<_> = types.iter().map(print_type).collect();
                        out.push_str(&format!("({})", types.join(", ")));
                    }
                    VariantPayload::Struct(fields) => {
                        let fields: Vec<_> = fields
                            .iter()
                            .map(|f| format!("{}: {}", f.name.name, print_type(&f.ty)))
                            .collect();
                        out.push_str(&format!(" {{ {} }}", fields.join(", ")));
                    }
                }
                out.push('\n');
            }
            out.push_str("}\n");
            out
        }
        Item::Fn(decl) => {
            let mut out = print_fn(decl, 0);
            out.push('\n');
            out
        }
        Item::Trait(decl) => {
            let export = if decl.exported.is_some() {
                "export "
            } else {
                ""
            };
            let mut out = format!(
                "{export}trait {}{} {{\n",
                decl.name.name,
                print_type_params(&decl.type_params)
            );
            for member in &decl.members {
                out.push_str(&print_fn_sig(member, 1));
                out.push('\n');
            }
            out.push_str("}\n");
            out
        }
        Item::Impl(decl) => {
            let mut out = format!(
                "impl{} {} for {} {{\n",
                print_type_params(&decl.type_params),
                decl.trait_path.text(),
                print_type(&decl.receiver)
            );
            for (index, decl) in decl.fns.iter().enumerate() {
                if index > 0 {
                    out.push('\n');
                }
                out.push_str(&print_fn(decl, 1));
                out.push('\n');
            }
            out.push_str("}\n");
            out
        }
        Item::Reactor(decl) => {
            let params: Vec<_> = decl
                .params
                .iter()
                .map(|p| format!("{}: {}", p.name.name, print_type(&p.ty)))
                .collect();
            let export = if decl.exported.is_some() {
                "export "
            } else {
                ""
            };
            let mut out = format!("{export}reactor {}({})", decl.name.name, params.join(", "));
            if decl.uses.is_empty() {
                out.push(' ');
            } else {
                let caps: Vec<_> = decl.uses.iter().map(|p| p.text()).collect();
                out.push_str(&format!("\n{INDENT}uses {{ {} }}\n", caps.join(", ")));
            }
            out.push_str("{\n");
            for member in &decl.members {
                out.push_str(INDENT);
                out.push_str(&print_member(member));
                out.push('\n');
            }
            out.push_str("}\n");
            out
        }
    }
}

/// A whole function at the given indent — at 0 a top-level item, at 1 an `impl` member. The
/// leading pad is included; the trailing newline is the caller's.
fn print_fn(decl: &FnDecl, indent: usize) -> String {
    let pad = INDENT.repeat(indent);
    let mut out = pad.clone();
    if decl.exported.is_some() {
        out.push_str("export ");
    }
    out.push_str(&print_fn_head(
        decl.is_task,
        &decl.name.name,
        &decl.type_params,
        &decl.params,
        decl.ret.as_ref(),
    ));
    if decl.uses.is_empty() {
        out.push(' ');
    } else {
        let caps: Vec<_> = decl.uses.iter().map(|p| p.text()).collect();
        out.push_str(&format!(
            "\n{pad}{INDENT}uses {{ {} }}\n{pad}",
            caps.join(", ")
        ));
    }
    out.push_str(&print_block(&decl.body, indent));
    out
}

/// A trait member: the head of a function with nothing after it.
fn print_fn_sig(sig: &FnSig, indent: usize) -> String {
    let pad = INDENT.repeat(indent);
    let mut out = pad.clone();
    out.push_str(&print_fn_head(
        sig.is_task,
        &sig.name.name,
        &sig.type_params,
        &sig.params,
        sig.ret.as_ref(),
    ));
    if !sig.uses.is_empty() {
        let caps: Vec<_> = sig.uses.iter().map(|p| p.text()).collect();
        out.push_str(&format!("\n{pad}{INDENT}uses {{ {} }}", caps.join(", ")));
    }
    out
}

/// `task fn name<T>(a: T) -> T` — everything a declaration and a signature spell the same way.
fn print_fn_head(
    is_task: bool,
    name: &str,
    type_params: &[TypeParam],
    params: &[Param],
    ret: Option<&Type>,
) -> String {
    let mut out = String::new();
    if is_task {
        out.push_str("task ");
    }
    let params: Vec<_> = params
        .iter()
        .map(|p| format!("{}: {}", p.name.name, print_type(&p.ty)))
        .collect();
    out.push_str(&format!(
        "fn {name}{}({})",
        print_type_params(type_params),
        params.join(", ")
    ));
    if let Some(ret) = ret {
        out.push_str(&format!(" -> {}", print_type(ret)));
    }
    out
}

fn print_member(member: &Member) -> String {
    match &member.kind {
        MemberKind::Input { name, ty, queue } => format!(
            "input {}: {} [capacity: {}, overflow: {}]",
            name.name,
            print_type(ty),
            print_expr(&queue.capacity, 1, LAMBDA),
            queue.overflow.name
        ),
        MemberKind::State { name, ty, init } => format!(
            "state {}: {} = {}",
            name.name,
            print_type(ty),
            print_expr(init, 1, LAMBDA)
        ),
        MemberKind::Signal {
            exported,
            name,
            ty,
            body,
        } => {
            let mut out = String::new();
            if *exported {
                out.push_str("export ");
            }
            out.push_str(&format!("signal {}", name.name));
            if let Some(ty) = ty {
                out.push_str(&format!(": {}", print_type(ty)));
            }
            out.push_str(&format!(" = {}", print_expr(body, 1, LAMBDA)));
            out
        }
        MemberKind::On {
            input,
            params,
            queue,
            body,
        } => {
            let params: Vec<_> = params
                .iter()
                .map(|p| match &p.ty {
                    Some(ty) => format!("{}: {}", p.name.name, print_type(ty)),
                    None => p.name.name.clone(),
                })
                .collect();
            // The queue clause is what distinguishes the merged form from the split one, so it is
            // printed rather than normalised away: `norn fmt` must not rewrite one form as the
            // other.
            let queue = match queue {
                Some(queue) => format!(
                    " [capacity: {}, overflow: {}]",
                    print_expr(&queue.capacity, 1, LAMBDA),
                    queue.overflow.name
                ),
                None => String::new(),
            };
            format!(
                "on {}({}){} {}",
                input.name,
                params.join(", "),
                queue,
                print_block(body, 1)
            )
        }
    }
}

pub fn print_type(ty: &Type) -> String {
    match &ty.kind {
        TypeKind::Unit => "()".into(),
        TypeKind::Path { path, args } => {
            if args.is_empty() {
                path.text()
            } else {
                let args: Vec<_> = args.iter().map(print_type).collect();
                format!("{}<{}>", path.text(), args.join(", "))
            }
        }
        TypeKind::Ref { mutable, inner } => {
            format!(
                "&{}{}",
                if *mutable { "mut " } else { "" },
                print_type(inner)
            )
        }
    }
}

fn print_block(block: &Block, indent: usize) -> String {
    if block.stmts.is_empty() {
        return "{}".into();
    }
    let pad = INDENT.repeat(indent);
    let inner = INDENT.repeat(indent + 1);
    let mut out = String::from("{\n");
    for stmt in &block.stmts {
        out.push_str(&inner);
        out.push_str(&print_stmt(stmt, indent + 1));
        out.push('\n');
    }
    out.push_str(&pad);
    out.push('}');
    out
}

fn print_stmt(stmt: &Stmt, indent: usize) -> String {
    match &stmt.kind {
        StmtKind::Let {
            mutable,
            name,
            ty,
            value,
        } => {
            let mut out = String::from("let ");
            if *mutable {
                out.push_str("mut ");
            }
            out.push_str(&name.name);
            if let Some(ty) = ty {
                out.push_str(&format!(": {}", print_type(ty)));
            }
            out.push_str(&format!(" = {}", print_expr(value, indent, LAMBDA)));
            out
        }
        StmtKind::Assign { target, value } => {
            format!(
                "{} = {}",
                print_expr(target, indent, ATOM),
                print_expr(value, indent, LAMBDA)
            )
        }
        StmtKind::Return(None) => "return".into(),
        StmtKind::Return(Some(value)) => {
            format!("return {}", print_expr(value, indent, LAMBDA))
        }
        StmtKind::After { task, returns } => {
            let mut out = format!("after {}", print_expr(task, indent, LAMBDA));
            if let Some(name) = returns {
                out.push_str(&format!(" -> {}", name.name));
            }
            out
        }
        StmtKind::Expr(expr) => print_expr(expr, indent, LAMBDA),
    }
}

/// Render `expr`, parenthesising it when its precedence is below `min` — the precedence its
/// syntactic position requires.
fn print_expr(expr: &Expr, indent: usize, min: u8) -> String {
    let text = print_expr_bare(expr, indent);
    if precedence(expr) < min {
        format!("({text})")
    } else {
        text
    }
}

fn precedence(expr: &Expr) -> u8 {
    match &expr.kind {
        ExprKind::Binary { op, .. } => binding_power(*op),
        ExprKind::Unary { .. } | ExprKind::Await(_) | ExprKind::Spawn(_) => UNARY,
        ExprKind::Lambda { .. } => LAMBDA,
        _ => ATOM,
    }
}

fn binding_power(op: BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 3,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 5,
        BinOp::Add | BinOp::Sub => 7,
        BinOp::Mul | BinOp::Div | BinOp::Rem => 9,
    }
}

fn print_expr_bare(expr: &Expr, indent: usize) -> String {
    match &expr.kind {
        ExprKind::Unit => "()".into(),
        ExprKind::Int(v) => v.to_string(),
        ExprKind::Float(v) => print_float(*v),
        ExprKind::Str(v) => print_string(v),
        ExprKind::Bool(v) => v.to_string(),
        ExprKind::Path(path) => path.text(),
        ExprKind::Unary { op, expr } => {
            format!("{}{}", op.text(), print_expr(expr, indent, UNARY))
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let bp = binding_power(*op);
            format!(
                "{} {} {}",
                print_expr(lhs, indent, bp),
                op.text(),
                print_expr(rhs, indent, bp + 1)
            )
        }
        ExprKind::Field { base, name } => {
            format!("{}.{}", print_expr(base, indent, ATOM), name.name)
        }
        ExprKind::Index { base, index } => {
            format!(
                "{}[{}]",
                print_expr(base, indent, ATOM),
                print_expr(index, indent, LAMBDA)
            )
        }
        ExprKind::Call {
            callee,
            type_args,
            args,
        } => {
            let type_args = if type_args.is_empty() {
                String::new()
            } else {
                let printed: Vec<_> = type_args.iter().map(print_type).collect();
                format!("<{}>", printed.join(", "))
            };
            let args: Vec<_> = args
                .iter()
                .map(|arg| match &arg.name {
                    Some(name) => {
                        format!("{}: {}", name.name, print_expr(&arg.value, indent, LAMBDA))
                    }
                    None => print_expr(&arg.value, indent, LAMBDA),
                })
                .collect();
            format!(
                "{}{type_args}({})",
                print_expr(callee, indent, ATOM),
                args.join(", ")
            )
        }
        ExprKind::Await(inner) => format!("await {}", print_expr(inner, indent, UNARY)),
        ExprKind::Scope(block) => format!("scope {}", print_block(block, indent)),
        ExprKind::Spawn(inner) => format!("spawn {}", print_expr(inner, indent, UNARY)),
        ExprKind::SpawnReactor { path, args } => {
            let args: Vec<_> = args
                .iter()
                .map(|arg| match &arg.name {
                    Some(name) => {
                        format!("{}: {}", name.name, print_expr(&arg.value, indent, LAMBDA))
                    }
                    None => print_expr(&arg.value, indent, LAMBDA),
                })
                .collect();
            format!("spawn reactor {}({})", path.text(), args.join(", "))
        }
        // `await f()?` already parses as `(await f())?`, so the parentheses would be noise.
        ExprKind::Try(inner) if matches!(inner.kind, ExprKind::Await(_)) => {
            format!("{}?", print_expr_bare(inner, indent))
        }
        ExprKind::Try(inner) => format!("{}?", print_expr(inner, indent, ATOM)),
        ExprKind::Block(block) => print_block(block, indent),
        ExprKind::If { cond, then, els } => {
            let mut out = format!(
                "if {} {}",
                print_expr(cond, indent, LAMBDA),
                print_block(then, indent)
            );
            if let Some(els) = els {
                match &els.kind {
                    ExprKind::Block(block) => {
                        out.push_str(&format!(" else {}", print_block(block, indent)))
                    }
                    _ => out.push_str(&format!(" else {}", print_expr_bare(els, indent))),
                }
            }
            out
        }
        ExprKind::While { cond, body } => {
            format!(
                "while {} {}",
                print_expr(cond, indent, LAMBDA),
                print_block(body, indent)
            )
        }
        ExprKind::Loop { body } => format!("loop {}", print_block(body, indent)),
        ExprKind::Break { value: None } => "break".into(),
        ExprKind::Break { value: Some(value) } => {
            format!("break {}", print_expr(value, indent, LAMBDA))
        }
        ExprKind::Continue => "continue".into(),
        ExprKind::Match { scrutinee, arms } => {
            let pad = INDENT.repeat(indent);
            let inner = INDENT.repeat(indent + 1);
            let mut out = format!("match {} {{\n", print_expr(scrutinee, indent, LAMBDA));
            for arm in arms {
                out.push_str(&inner);
                out.push_str(&print_pat(&arm.pat));
                if let Some(guard) = &arm.guard {
                    out.push_str(&format!(" if {}", print_expr(guard, indent + 1, LAMBDA)));
                }
                out.push_str(&format!(
                    " => {}\n",
                    print_expr(&arm.body, indent + 1, LAMBDA)
                ));
            }
            out.push_str(&pad);
            out.push('}');
            out
        }
        ExprKind::Lambda {
            is_task,
            params,
            body,
        } => {
            let params: Vec<_> = params.iter().map(print_pat).collect();
            let head = if params.len() == 1 && !params[0].contains(',') {
                params.into_iter().next().unwrap()
            } else {
                format!("({})", params.join(", "))
            };
            let task = if *is_task { "task " } else { "" };
            format!("{task}{head} => {}", print_expr(body, indent, LAMBDA))
        }
    }
}

fn print_pat(pat: &Pat) -> String {
    match &pat.kind {
        PatKind::Wild => "_".into(),
        PatKind::Binding(ident) => ident.name.clone(),
        PatKind::Int(v) => v.to_string(),
        PatKind::Str(v) => print_string(v),
        PatKind::Bool(v) => v.to_string(),
        PatKind::Construct { path, args, rest } => {
            let mut parts: Vec<String> = args
                .iter()
                .map(|arg| match &arg.name {
                    Some(name) => format!("{}: {}", name.name, print_pat(&arg.pat)),
                    None => print_pat(&arg.pat),
                })
                .collect();
            if *rest {
                parts.push("..".into());
            }
            if parts.is_empty() {
                // A dotted path is a constructor on its own; a lone name needs its `()` kept,
                // because bare it would re-parse as a binding.
                return if path.segments.len() == 1 {
                    format!("{}()", path.text())
                } else {
                    path.text()
                };
            }
            format!("{}({})", path.text(), parts.join(", "))
        }
        PatKind::Or(alts) => alts.iter().map(print_pat).collect::<Vec<_>>().join(" | "),
    }
}

fn print_string(value: &str) -> String {
    let mut out = String::from("\"");
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Always render a fraction so the value reparses as a float rather than an integer.
fn print_float(value: f64) -> String {
    let text = format!("{value}");
    if text.contains(['.', 'e', 'E', 'n', 'i']) {
        text
    } else {
        format!("{text}.0")
    }
}
