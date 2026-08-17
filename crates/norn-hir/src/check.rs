//! Name resolution and type checking: AST in, typed HIR out.
//!
//! The checker is bidirectional. `check_expr` takes the type its position demands, when there is
//! one, and falls back to synthesising a type when there is not. That is what lets `#None` and
//! `#Err(e)` work without inference variables: the expectation supplies the argument the
//! expression cannot know on its own, and where no expectation exists the checker says so rather
//! than guessing.
//!
//! Everything the grammar admits but v0 does not implement — tasks, `await`, methods, generic
//! arguments, first-class functions — is rejected here, by name, with the milestone that will
//! provide it.

use std::collections::HashMap;

use norn_syntax::ast;
use norn_syntax::{Diagnostic, Span};

use crate::hir::*;

pub struct Checked {
    pub program: Program,
    pub errors: Vec<Diagnostic>,
}

impl Checked {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
}

pub fn check(module: &ast::Module) -> Checked {
    let mut checker = Checker::new();
    checker.run(module);
    let Checker {
        program,
        mut errors,
        ..
    } = checker;
    // Report in source order rather than stage order, as the parser does: signatures are resolved
    // before any body is checked, and what that finds should not float to the top of the list.
    errors.sort_by_key(|diagnostic| diagnostic.span.start);
    Checked { program, errors }
}

/// What a name at the head of a path refers to.
enum TypeName {
    Record(RecordId),
    Enum(EnumId),
    Builtin(Ty),
}

struct Checker {
    program: Program,
    errors: Vec<Diagnostic>,
    types: HashMap<String, TypeName>,
    fns: HashMap<String, FnId>,
    /// Signatures, resolved before any body is checked so that functions may call one another
    /// regardless of declaration order.
    signatures: Vec<(Vec<(String, Ty)>, Ty)>,
    locals: Vec<LocalDef>,
    scopes: Vec<Vec<(String, LocalId)>>,
    ret: Ty,
    /// The function being checked: its name for diagnostics, whether it is a `task fn`, and what it
    /// declared it uses. Capability checking happens where a task is *built*, because an awaiting
    /// function cannot see a `Task<T>`'s provenance.
    fn_name: String,
    in_task: bool,
    uses: Vec<Capability>,
    /// How many `scope { … }` expressions enclose the expression being checked. Reset per function,
    /// which is what makes "inside a scope in the same function" the rule `spawn` enforces.
    scope_depth: usize,
}

impl Checker {
    fn new() -> Checker {
        // `Option` and `Result` are seeded as ordinary enums so that construction, matching, and
        // lowering treat them exactly like a user enum. Only their type arguments are special.
        let span = Span::new(0, 0);
        let option = EnumDef {
            name: "Option".into(),
            variants: vec![
                VariantDef {
                    name: "None".into(),
                    fields: vec![],
                    positional: true,
                    span,
                },
                VariantDef {
                    name: "Some".into(),
                    fields: vec![FieldDef {
                        name: "0".into(),
                        ty: Ty::Error,
                        span,
                    }],
                    positional: true,
                    span,
                },
            ],
            span,
        };
        let result = EnumDef {
            name: "Result".into(),
            variants: vec![
                VariantDef {
                    name: "Ok".into(),
                    fields: vec![FieldDef {
                        name: "0".into(),
                        ty: Ty::Error,
                        span,
                    }],
                    positional: true,
                    span,
                },
                VariantDef {
                    name: "Err".into(),
                    fields: vec![FieldDef {
                        name: "0".into(),
                        ty: Ty::Error,
                        span,
                    }],
                    positional: true,
                    span,
                },
            ],
            span,
        };
        // `IoError` is seeded beside them: the socket builtins have to fail with something, and a
        // failure type the language cannot name is not a failure type.
        let io_error = EnumDef {
            name: "IoError".into(),
            variants: io_error::VARIANTS
                .iter()
                .map(|(name, fields)| VariantDef {
                    name: (*name).into(),
                    fields: (0..*fields)
                        .map(|index| FieldDef {
                            name: index.to_string(),
                            ty: Ty::Str,
                            span,
                        })
                        .collect(),
                    positional: true,
                    span,
                })
                .collect(),
            span,
        };
        Checker {
            program: Program {
                records: Vec::new(),
                enums: vec![option, result, io_error],
                fns: Vec::new(),
                main: None,
            },
            errors: Vec::new(),
            types: HashMap::new(),
            fns: HashMap::new(),
            signatures: Vec::new(),
            locals: Vec::new(),
            scopes: Vec::new(),
            ret: Ty::Unit,
            fn_name: String::new(),
            in_task: false,
            uses: Vec::new(),
            scope_depth: 0,
        }
    }

    fn error(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(Diagnostic::new(span, message));
    }

    fn push(&mut self, diagnostic: Diagnostic) {
        self.errors.push(diagnostic);
    }

    // ---------------------------------------------------------------- program

    fn run(&mut self, module: &ast::Module) {
        if let Some(decl) = module.uses.first() {
            self.push(
                Diagnostic::new(decl.span, "`use` has nothing to import yet")
                    .label("no module system")
                    .note("modules and imports arrive with the standard library; see BOOTSTRAP.md"),
            );
        }

        self.declare_types(module);
        self.define_types(module);
        self.declare_fns(module);
        self.check_fns(module);
    }

    /// Pass one: every type name exists before any type is resolved, so declarations may refer to
    /// one another in any order.
    fn declare_types(&mut self, module: &ast::Module) {
        self.types.insert("I64".into(), TypeName::Builtin(Ty::I64));
        self.types.insert("F64".into(), TypeName::Builtin(Ty::F64));
        self.types
            .insert("Bool".into(), TypeName::Builtin(Ty::Bool));
        self.types
            .insert("String".into(), TypeName::Builtin(Ty::Str));
        self.types.insert(
            "Listener".into(),
            TypeName::Builtin(Ty::Resource(Resource::Listener)),
        );
        self.types.insert(
            "Connection".into(),
            TypeName::Builtin(Ty::Resource(Resource::Connection)),
        );
        self.types
            .insert("IoError".into(), TypeName::Enum(EnumId::IO_ERROR));

        for item in &module.items {
            let (name, span) = match item {
                ast::Item::Record(decl) => (&decl.name, decl.span),
                ast::Item::Enum(decl) => (&decl.name, decl.span),
                ast::Item::Fn(_) => continue,
            };
            if self.types.contains_key(&name.name) {
                self.push(
                    Diagnostic::new(name.span, format!("`{}` is declared twice", name.name))
                        .label("duplicate type"),
                );
                continue;
            }
            let resolved = match item {
                ast::Item::Record(decl) => {
                    let id = RecordId(self.program.records.len() as u32);
                    self.program.records.push(RecordDef {
                        name: decl.name.name.clone(),
                        fields: Vec::new(),
                        span,
                    });
                    TypeName::Record(id)
                }
                ast::Item::Enum(decl) => {
                    let id = EnumId(self.program.enums.len() as u32);
                    self.program.enums.push(EnumDef {
                        name: decl.name.name.clone(),
                        variants: Vec::new(),
                        span,
                    });
                    TypeName::Enum(id)
                }
                ast::Item::Fn(_) => unreachable!(),
            };
            self.types.insert(name.name.clone(), resolved);
        }
    }

    /// Pass two: fill in field and payload types.
    fn define_types(&mut self, module: &ast::Module) {
        for item in &module.items {
            match item {
                ast::Item::Record(decl) => {
                    let Some(TypeName::Record(id)) = self.types.get(&decl.name.name) else {
                        continue;
                    };
                    let id = *id;
                    let mut fields = Vec::new();
                    for field in &decl.fields {
                        if fields.iter().any(|f: &FieldDef| f.name == field.name.name) {
                            self.error(
                                field.name.span,
                                format!("field `{}` is declared twice", field.name.name),
                            );
                            continue;
                        }
                        let ty = self.resolve_ty(&field.ty);
                        fields.push(FieldDef {
                            name: field.name.name.clone(),
                            ty,
                            span: field.span,
                        });
                    }
                    self.program.records[id.index()].fields = fields;
                }
                ast::Item::Enum(decl) => {
                    let Some(TypeName::Enum(id)) = self.types.get(&decl.name.name) else {
                        continue;
                    };
                    let id = *id;
                    let mut variants = Vec::new();
                    for variant in &decl.variants {
                        let (fields, positional) = match &variant.payload {
                            ast::VariantPayload::Unit => (Vec::new(), true),
                            ast::VariantPayload::Tuple(types) => {
                                let fields = types
                                    .iter()
                                    .enumerate()
                                    .map(|(i, ty)| FieldDef {
                                        name: i.to_string(),
                                        ty: self.resolve_ty(ty),
                                        span: ty.span,
                                    })
                                    .collect();
                                (fields, true)
                            }
                            ast::VariantPayload::Record(decls) => {
                                let fields = decls
                                    .iter()
                                    .map(|f| FieldDef {
                                        name: f.name.name.clone(),
                                        ty: self.resolve_ty(&f.ty),
                                        span: f.span,
                                    })
                                    .collect();
                                (fields, false)
                            }
                        };
                        variants.push(VariantDef {
                            name: variant.name.name.clone(),
                            fields,
                            positional,
                            span: variant.span,
                        });
                    }
                    self.program.enums[id.index()].variants = variants;
                }
                ast::Item::Fn(_) => {}
            }
        }
    }

    fn declare_fns(&mut self, module: &ast::Module) {
        for item in &module.items {
            let ast::Item::Fn(decl) = item else { continue };
            if Builtin::from_name(&decl.name.name).is_some() {
                self.push(
                    Diagnostic::new(
                        decl.name.span,
                        format!("`{}` is a built-in function", decl.name.name),
                    )
                    .label("cannot be redefined"),
                );
                continue;
            }
            if self.fns.contains_key(&decl.name.name) {
                self.push(
                    Diagnostic::new(
                        decl.name.span,
                        format!("`{}` is declared twice", decl.name.name),
                    )
                    .label("duplicate function"),
                );
                continue;
            }
            let params: Vec<(String, Ty)> = decl
                .params
                .iter()
                .map(|p| (p.name.name.clone(), self.resolve_ty(&p.ty)))
                .collect();
            let ret = decl.ret.as_ref().map_or(Ty::Unit, |ty| self.resolve_ty(ty));
            let uses = self.capabilities(decl);
            let id = FnId(self.program.fns.len() as u32);
            self.fns.insert(decl.name.name.clone(), id);
            self.signatures.push((params.clone(), ret.clone()));
            self.program.fns.push(FnDef {
                name: decl.name.name.clone(),
                is_task: decl.is_task,
                uses,
                params: params.len(),
                locals: Vec::new(),
                ret,
                body: Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span: decl.span,
                },
                span: decl.span,
            });
            if decl.name.name == "main" {
                self.program.main = Some(id);
            }
        }
    }

    /// Resolve a `uses { … }` list. The vocabulary is closed, so an unknown name is an error that
    /// says what the three are rather than a capability nobody grants.
    fn capabilities(&mut self, decl: &ast::FnDecl) -> Vec<Capability> {
        let mut resolved = Vec::new();
        for path in &decl.uses {
            let name = path.text();
            match Capability::from_name(&name) {
                Some(capability) => {
                    if !resolved.contains(&capability) {
                        resolved.push(capability);
                    }
                }
                None => {
                    let known: Vec<&str> = Capability::ALL.iter().map(|c| c.name()).collect();
                    self.push(
                        Diagnostic::new(path.span, format!("unknown capability `{name}`"))
                            .label("not a capability v0 knows")
                            .note(format!("the vocabulary is fixed: {}", known.join(", "))),
                    );
                }
            }
        }
        resolved.sort();
        resolved
    }

    fn check_fns(&mut self, module: &ast::Module) {
        for item in &module.items {
            let ast::Item::Fn(decl) = item else { continue };
            let Some(&id) = self.fns.get(&decl.name.name) else {
                continue;
            };
            if self.program.fns[id.index()].name != decl.name.name {
                continue;
            }
            if !decl.is_task && !decl.uses.is_empty() {
                // The parser already rejects `uses` on a non-task function, so this is unreachable
                // in practice; keeping it means the checker never silently ignores a capability.
                self.error(decl.span, "capabilities are only meaningful on a `task fn`");
            }

            let (params, ret) = self.signatures[id.index()].clone();
            self.locals = Vec::new();
            self.scopes = vec![Vec::new()];
            self.ret = ret.clone();
            self.fn_name = decl.name.name.clone();
            self.in_task = decl.is_task;
            self.uses = self.program.fns[id.index()].uses.clone();
            self.scope_depth = 0;
            for ((name, ty), param) in params.iter().zip(&decl.params) {
                self.declare_local(name.clone(), ty.clone(), false, param.name.span);
            }
            let body = self.check_block(&decl.body, Some(&ret), decl.body.span);
            let locals = std::mem::take(&mut self.locals);
            self.program.fns[id.index()].locals = locals;
            self.program.fns[id.index()].body = body;
        }
    }

    // ---------------------------------------------------------------- types

    fn resolve_ty(&mut self, ty: &ast::Type) -> Ty {
        match &ty.kind {
            ast::TypeKind::Unit => Ty::Unit,
            // A borrow is transparent in v0. The distinction becomes real in M4, when ownership
            // arrives; until then `&T` and `T` denote the same values.
            ast::TypeKind::Ref { inner, .. } => self.resolve_ty(inner),
            ast::TypeKind::Path { path, args } => {
                if path.segments.len() != 1 {
                    self.error(path.span, format!("unknown type `{}`", path.text()));
                    return Ty::Error;
                }
                let name = &path.last().name;
                match name.as_str() {
                    "Option" => {
                        return match self.type_args(name, args, 1, ty.span) {
                            Some(mut args) => Ty::Option(Box::new(args.remove(0))),
                            None => Ty::Error,
                        };
                    }
                    "Result" => {
                        return match self.type_args(name, args, 2, ty.span) {
                            Some(mut args) => {
                                let ok = args.remove(0);
                                let err = args.remove(0);
                                Ty::Result(Box::new(ok), Box::new(err))
                            }
                            None => Ty::Error,
                        };
                    }
                    "Task" => {
                        return match self.type_args(name, args, 1, ty.span) {
                            Some(mut args) => Ty::Task(Box::new(args.remove(0))),
                            None => Ty::Error,
                        };
                    }
                    _ => {}
                }
                if !args.is_empty() {
                    self.push(
                        Diagnostic::new(ty.span, format!("`{name}` takes no type arguments"))
                            .note("user-defined generics arrive after M6; see BOOTSTRAP.md §8"),
                    );
                    return Ty::Error;
                }
                match self.types.get(name) {
                    Some(TypeName::Builtin(ty)) => ty.clone(),
                    Some(TypeName::Record(id)) => Ty::Record(*id),
                    Some(TypeName::Enum(id)) => Ty::Enum(*id),
                    None => {
                        self.error(path.span, format!("unknown type `{name}`"));
                        Ty::Error
                    }
                }
            }
        }
    }

    fn type_args(
        &mut self,
        name: &str,
        args: &[ast::Type],
        want: usize,
        span: Span,
    ) -> Option<Vec<Ty>> {
        if args.len() != want {
            let plural = if want == 1 { "argument" } else { "arguments" };
            self.push(
                Diagnostic::new(
                    span,
                    format!("`{name}` takes {want} type {plural}, found {}", args.len()),
                )
                .note(match name {
                    "Result" => {
                        "write both, as in `Result<Config, LoadError>` — there is no default error type"
                    }
                    "Task" => "write the value the task produces, as in `Task<()>`",
                    _ => "write the element type, as in `Option<I64>`",
                }),
            );
            return None;
        }
        Some(args.iter().map(|ty| self.resolve_ty(ty)).collect())
    }

    // ---------------------------------------------------------------- locals

    fn declare_local(&mut self, name: String, ty: Ty, mutable: bool, span: Span) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalDef {
            name: name.clone(),
            ty,
            mutable,
            span,
        });
        self.scopes
            .last_mut()
            .expect("a scope is open")
            .push((name, id));
        id
    }

    fn lookup_local(&self, name: &str) -> Option<LocalId> {
        self.scopes.iter().rev().find_map(|scope| {
            scope
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, id)| *id)
        })
    }

    // ---------------------------------------------------------------- expressions

    /// Report a mismatch unless `found` fits `expected`.
    fn expect(&mut self, found: Expr, expected: Option<&Ty>, span: Span) -> Expr {
        if let Some(expected) = expected
            && !found.ty.fits(expected)
        {
            // A task where its own result was wanted is a missing `await`, and saying so is worth
            // more than reporting the shapes that differ.
            if let Ty::Task(produced) = &found.ty
                && produced.fits(expected)
            {
                self.discarded_task(span);
                return self.error_expr(span);
            }
            let message = format!(
                "expected {}, found {}",
                self.program.ty_name(expected),
                self.program.ty_name(&found.ty)
            );
            self.error(span, message);
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        found
    }

    fn check_expr(&mut self, expr: &ast::Expr, expected: Option<&Ty>) -> Expr {
        let span = expr.span;
        let checked = match &expr.kind {
            ast::ExprKind::Unit => Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span,
            },
            ast::ExprKind::Int(v) => Expr {
                kind: ExprKind::Int(*v),
                ty: Ty::I64,
                span,
            },
            ast::ExprKind::Float(v) => Expr {
                kind: ExprKind::Float(*v),
                ty: Ty::F64,
                span,
            },
            ast::ExprKind::Str(v) => Expr {
                kind: ExprKind::Str(v.clone()),
                ty: Ty::Str,
                span,
            },
            ast::ExprKind::Bool(v) => Expr {
                kind: ExprKind::Bool(*v),
                ty: Ty::Bool,
                span,
            },
            ast::ExprKind::Path(path) => self.check_path(path),
            ast::ExprKind::Field { base, name } => {
                let base = self.check_expr(base, None);
                self.field_access(base, name, span)
            }
            ast::ExprKind::Unary { op, expr: inner } => self.check_unary(*op, inner, span),
            ast::ExprKind::Binary { op, lhs, rhs } => self.check_binary(*op, lhs, rhs, span),
            ast::ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.check_call(callee, type_args, args, span),
            ast::ExprKind::Construct { path, args } => {
                self.check_construct(path, args, expected, span)
            }
            ast::ExprKind::Block(block) => self.check_block(block, expected, span),
            ast::ExprKind::If { cond, then, els } => self.check_if(cond, then, els, expected, span),
            ast::ExprKind::Match { scrutinee, arms } => {
                self.check_match(scrutinee, arms, expected, span)
            }
            ast::ExprKind::Try(inner) => self.check_try(inner, span),
            ast::ExprKind::Index { .. } => {
                self.push(
                    Diagnostic::new(span, "indexing is not available yet")
                        .note("collections arrive with the standard library"),
                );
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
            ast::ExprKind::Await(inner) => self.check_await(inner, span),
            ast::ExprKind::Scope(block) => self.check_scope(block, expected, span),
            ast::ExprKind::Spawn(inner) => self.check_spawn(inner, span),
            ast::ExprKind::Lambda { .. } => {
                self.push(
                    Diagnostic::new(span, "functions are not values yet")
                        .label("lambda")
                        .note("closures arrive alongside the reactive operators in M3"),
                );
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
        };
        // A construct that consulted the expectation itself has already reported any mismatch.
        if matches!(checked.kind, ExprKind::Error) {
            return checked;
        }
        self.expect(checked, expected, span)
    }

    // ---------------------------------------------------------------- tasks

    fn error_expr(&self, span: Span) -> Expr {
        Expr {
            kind: ExprKind::Error,
            ty: Ty::Error,
            span,
        }
    }

    /// Whether the running function may create a task at all, and whether it declared the authority
    /// the task it is creating needs. Both questions belong here, at the point of creation: once a
    /// `Task<T>` is a value, nothing downstream can tell what it will do.
    fn require_task_authority(&mut self, what: &str, needs: &[Capability], span: Span) -> bool {
        if !self.in_task {
            let message = format!(
                "only a `task fn` can create a task, and `{}` is not one",
                self.fn_name
            );
            self.push(
                Diagnostic::new(span, message)
                    .label(format!("`{what}` builds a task"))
                    .note("mark the enclosing function `task fn`"),
            );
            return false;
        }
        let mut authorised = true;
        for capability in needs {
            if !self.uses.contains(capability) {
                let message = format!(
                    "`{}` does not declare the capability `{}`",
                    self.fn_name,
                    capability.name()
                );
                self.push(
                    Diagnostic::new(span, message)
                        .label(format!("`{what}` uses it"))
                        .note("a task's `uses { … }` set must cover every task it creates")
                        .note(format!(
                            "add it: `uses {{ {} }}`",
                            self.uses
                                .iter()
                                .chain(std::iter::once(capability))
                                .map(|c| c.name())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )),
                );
                authorised = false;
            }
        }
        authorised
    }

    /// A task that is built and dropped does nothing at all, which is the obvious first bug
    /// laziness invites. It is worth a diagnostic rather than a silent no-op.
    fn discarded_task(&mut self, span: Span) {
        self.push(
            Diagnostic::new(span, "this builds a task and then discards it")
                .label("the task never runs")
                .note("`await` it to run it here, or `spawn` it to run it in a scope"),
        );
    }

    fn check_await(&mut self, inner: &ast::Expr, span: Span) -> Expr {
        if !self.in_task {
            self.push(
                Diagnostic::new(span, "`await` is only available inside a `task fn`")
                    .label("only a task may suspend")
                    .note("mark the enclosing function `task fn`"),
            );
            return self.error_expr(span);
        }
        // The operand synthesises rather than being checked against `Task<expected>`. Every task
        // value in v0 comes from a call, which knows its own type, and synthesising lets `await`
        // report what it was actually handed instead of a shape mismatch two layers down.
        let task = self.check_expr(inner, None);
        if task.ty.is_error() {
            return self.error_expr(span);
        }
        let Ty::Task(produced) = &task.ty else {
            let message = format!(
                "`await` applies to a task, not {}",
                self.program.ty_name(&task.ty)
            );
            self.push(
                Diagnostic::new(span, message)
                    .label("not a task")
                    .note("a task comes from calling a `task fn`, and nothing else in v0"),
            );
            return self.error_expr(span);
        };
        let ty = (**produced).clone();
        Expr {
            kind: ExprKind::Await {
                expr: Box::new(task),
            },
            ty,
            span,
        }
    }

    fn check_scope(&mut self, block: &ast::Block, expected: Option<&Ty>, span: Span) -> Expr {
        if !self.in_task {
            self.push(
                Diagnostic::new(span, "a `scope` is only available inside a `task fn`")
                    .label("only a task may start other tasks")
                    .note("mark the enclosing function `task fn`"),
            );
            return self.error_expr(span);
        }
        self.scope_depth += 1;
        let body = self.check_block(block, expected, block.span);
        self.scope_depth -= 1;
        let ty = body.ty.clone();
        Expr {
            kind: ExprKind::Scope {
                body: Box::new(body),
            },
            ty,
            span,
        }
    }

    fn check_spawn(&mut self, inner: &ast::Expr, span: Span) -> Expr {
        if !self.in_task {
            self.push(
                Diagnostic::new(span, "`spawn` is only available inside a `task fn`")
                    .label("only a task may start other tasks")
                    .note("mark the enclosing function `task fn`"),
            );
            return self.error_expr(span);
        }
        if self.scope_depth == 0 {
            self.push(
                Diagnostic::new(span, "`spawn` must appear inside a `scope`")
                    .label("nothing here would cancel or join it")
                    .note("wrap it in `scope { … }`: a spawned task may not outlive the scope that started it"),
            );
            return self.error_expr(span);
        }
        let task = self.check_expr(inner, None);
        if task.ty.is_error() {
            return self.error_expr(span);
        }
        match &task.ty {
            Ty::Task(produced) if **produced == Ty::Unit => {}
            Ty::Task(produced) => {
                let message = format!(
                    "`spawn` needs a task that produces (), and this one produces {}",
                    self.program.ty_name(produced)
                );
                self.push(
                    Diagnostic::new(span, message)
                        .label("nothing would receive the value")
                        .note("there are no task handles in v0, so a spawned task has to say what happens to its own result"),
                );
                return self.error_expr(span);
            }
            other => {
                let message = format!(
                    "`spawn` applies to a task, not {}",
                    self.program.ty_name(other)
                );
                self.push(Diagnostic::new(span, message).label("not a task"));
                return self.error_expr(span);
            }
        }
        Expr {
            kind: ExprKind::Spawn {
                expr: Box::new(task),
            },
            ty: Ty::Unit,
            span,
        }
    }

    fn check_path(&mut self, path: &ast::Path) -> Expr {
        let span = path.span;
        let head = &path.segments[0];
        let Some(local) = self.lookup_local(&head.name) else {
            if path.segments.len() == 1 && self.fns.contains_key(&head.name) {
                self.push(
                    Diagnostic::new(span, "functions are not values yet")
                        .label(format!("`{}` can only be called", head.name))
                        .note("first-class functions arrive with closures in M3"),
                );
            } else {
                self.error(span, format!("unknown name `{}`", head.name));
            }
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };

        // A dotted expression is a local followed by field projections. Deciding that here is what
        // lets the grammar keep `a.b.c` as one node.
        let mut expr = Expr {
            kind: ExprKind::Local(local),
            ty: self.locals[local.index()].ty.clone(),
            span: head.span,
        };
        for segment in &path.segments[1..] {
            expr = self.field_access(expr, segment, head.span.to(segment.span));
        }
        expr
    }

    fn field_access(&mut self, base: Expr, name: &ast::Ident, span: Span) -> Expr {
        if base.ty.is_error() {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let Ty::Record(id) = base.ty else {
            let message = format!("{} has no fields", self.program.ty_name(&base.ty));
            self.push(
                Diagnostic::new(span, message).label(format!("`{}` accessed here", name.name)),
            );
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let Some((index, field)) = self.program.records[id.index()].field(&name.name) else {
            let record = self.program.records[id.index()].name.clone();
            self.push(
                Diagnostic::new(
                    name.span,
                    format!("`{record}` has no field `{}`", name.name),
                )
                .label("unknown field"),
            );
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let ty = field.ty.clone();
        Expr {
            kind: ExprKind::Field {
                base: Box::new(base),
                index,
            },
            ty,
            span,
        }
    }

    fn check_unary(&mut self, op: ast::UnOp, inner: &ast::Expr, span: Span) -> Expr {
        // `&` and `&mut` are transparent until M4 introduces ownership.
        if matches!(op, ast::UnOp::Ref | ast::UnOp::RefMut) {
            return self.check_expr(inner, None);
        }
        let inner = self.check_expr(inner, None);
        if inner.ty.is_error() {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let (hir_op, ty) = match (op, &inner.ty) {
            (ast::UnOp::Neg, Ty::I64) => (UnOp::Neg, Ty::I64),
            (ast::UnOp::Neg, Ty::F64) => (UnOp::Neg, Ty::F64),
            (ast::UnOp::Not, Ty::Bool) => (UnOp::Not, Ty::Bool),
            (op, ty) => {
                let message = format!(
                    "`{}` does not apply to {}",
                    op.text().trim(),
                    self.program.ty_name(ty)
                );
                self.error(span, message);
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
        };
        Expr {
            kind: ExprKind::Unary {
                op: hir_op,
                expr: Box::new(inner),
            },
            ty,
            span,
        }
    }

    fn check_binary(
        &mut self,
        op: ast::BinOp,
        lhs: &ast::Expr,
        rhs: &ast::Expr,
        span: Span,
    ) -> Expr {
        if matches!(op, ast::BinOp::And | ast::BinOp::Or) {
            let lhs = self.check_expr(lhs, Some(&Ty::Bool));
            let rhs = self.check_expr(rhs, Some(&Ty::Bool));
            return Expr {
                kind: ExprKind::ShortCircuit {
                    and: op == ast::BinOp::And,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                ty: Ty::Bool,
                span,
            };
        }

        let lhs = self.check_expr(lhs, None);
        let rhs = self.check_expr(rhs, Some(&lhs.ty));
        if lhs.ty.is_error() || rhs.ty.is_error() {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }

        use ast::BinOp as A;
        let operand = &lhs.ty;
        let resolved = match op {
            A::Add => match operand {
                Ty::I64 => Some((BinOp::AddInt, Ty::I64)),
                Ty::F64 => Some((BinOp::AddFloat, Ty::F64)),
                Ty::Str => Some((BinOp::Concat, Ty::Str)),
                _ => None,
            },
            A::Sub => match operand {
                Ty::I64 => Some((BinOp::SubInt, Ty::I64)),
                Ty::F64 => Some((BinOp::SubFloat, Ty::F64)),
                _ => None,
            },
            A::Mul => match operand {
                Ty::I64 => Some((BinOp::MulInt, Ty::I64)),
                Ty::F64 => Some((BinOp::MulFloat, Ty::F64)),
                _ => None,
            },
            A::Div => match operand {
                Ty::I64 => Some((BinOp::DivInt, Ty::I64)),
                Ty::F64 => Some((BinOp::DivFloat, Ty::F64)),
                _ => None,
            },
            A::Rem => match operand {
                Ty::I64 => Some((BinOp::RemInt, Ty::I64)),
                Ty::F64 => Some((BinOp::RemFloat, Ty::F64)),
                _ => None,
            },
            A::Eq | A::Ne => match operand {
                Ty::I64 | Ty::F64 | Ty::Bool | Ty::Str => {
                    Some((if op == A::Eq { BinOp::Eq } else { BinOp::Ne }, Ty::Bool))
                }
                _ => None,
            },
            A::Lt | A::Le | A::Gt | A::Ge => match operand {
                Ty::I64 | Ty::F64 | Ty::Str => {
                    let hir_op = match op {
                        A::Lt => BinOp::Lt,
                        A::Le => BinOp::Le,
                        A::Gt => BinOp::Gt,
                        _ => BinOp::Ge,
                    };
                    Some((hir_op, Ty::Bool))
                }
                _ => None,
            },
            A::And | A::Or => unreachable!("handled above"),
        };

        let Some((hir_op, ty)) = resolved else {
            let message = format!(
                "`{}` does not apply to {}",
                op.text(),
                self.program.ty_name(operand)
            );
            let mut diagnostic = Diagnostic::new(span, message);
            if matches!(op, A::Eq | A::Ne) {
                diagnostic = diagnostic.note(
                    "structural equality on records and enums is not derived yet; match instead",
                );
            }
            self.push(diagnostic);
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        Expr {
            kind: ExprKind::Binary {
                op: hir_op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty,
            span,
        }
    }

    fn check_call(
        &mut self,
        callee: &ast::Expr,
        type_args: &[ast::Type],
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
        if !type_args.is_empty() {
            self.push(
                Diagnostic::new(span, "explicit type arguments are not available yet")
                    .note("generics arrive after M6; see BOOTSTRAP.md §8"),
            );
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let ast::ExprKind::Path(path) = &callee.kind else {
            self.push(
                Diagnostic::new(callee.span, "only a named function can be called")
                    .note("methods and function values arrive in M3"),
            );
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        if path.segments.len() != 1 {
            self.error(path.span, format!("unknown function `{}`", path.text()));
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let name = &path.last().name;

        if let Some(builtin) = Builtin::from_name(name) {
            return self.check_builtin(builtin, args, span);
        }

        let Some(&id) = self.fns.get(name) else {
            self.error(path.span, format!("unknown function `{name}`"));
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let (params, ret) = self.signatures[id.index()].clone();
        let param_names: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
        let Some(order) = self.argument_order(&param_names, args, name, "parameter", span) else {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };

        let mut checked = Vec::with_capacity(params.len());
        for (index, (_, ty)) in params.iter().enumerate() {
            let arg = &args[order[index]];
            checked.push(self.check_expr(&arg.value, Some(ty)));
        }

        // Calling a `task fn` builds a task; it does not run one. That is why the capability check
        // happens here rather than at the `await`.
        let ty = if self.program.fns[id.index()].is_task {
            let needs = self.program.fns[id.index()].uses.clone();
            self.require_task_authority(name, &needs, span);
            Ty::Task(Box::new(ret))
        } else {
            ret
        };
        Expr {
            kind: ExprKind::Call {
                callee: id,
                args: checked,
            },
            ty,
            span,
        }
    }

    fn check_builtin(&mut self, builtin: Builtin, args: &[ast::Arg], span: Span) -> Expr {
        let (params, ret) = builtin.signature();
        let name = builtin.name();
        if args.len() != params.len() || args.iter().any(|arg| arg.name.is_some()) {
            let message = format!(
                "`{name}` takes {} positional argument{}",
                params.len(),
                if params.len() == 1 { "" } else { "s" }
            );
            self.error(span, message);
            return self.error_expr(span);
        }
        if builtin.is_task() && !self.require_task_authority(name, builtin.capabilities(), span) {
            return self.error_expr(span);
        }

        let mut checked = Vec::with_capacity(params.len());
        for (arg, param) in args.iter().zip(&params) {
            // `print` is the one builtin that takes a value of any type at all, spelled as an
            // expectation of `Ty::Error`, which every type fits.
            let wanted = if param.is_error() { None } else { Some(param) };
            checked.push(self.check_expr(&arg.value, wanted));
        }
        Expr {
            kind: ExprKind::Builtin {
                builtin,
                args: checked,
            },
            ty: ret,
            span,
        }
    }

    /// Map declaration order onto the order the arguments were written. Arguments are either all
    /// positional or all named; mixing the two is rejected rather than given a precedence rule.
    fn argument_order(
        &mut self,
        names: &[String],
        args: &[ast::Arg],
        subject: &str,
        noun: &str,
        span: Span,
    ) -> Option<Vec<usize>> {
        let named = args.iter().filter(|a| a.name.is_some()).count();
        if named != 0 && named != args.len() {
            self.push(
                Diagnostic::new(span, "arguments are either all named or all positional").note(
                    "mixing the two forms would need a precedence rule nobody should have to learn",
                ),
            );
            return None;
        }

        if named == 0 {
            if args.len() != names.len() {
                let message = format!(
                    "`{subject}` takes {} {noun}{}, found {}",
                    names.len(),
                    if names.len() == 1 { "" } else { "s" },
                    args.len()
                );
                self.error(span, message);
                return None;
            }
            return Some((0..args.len()).collect());
        }

        let mut order = vec![usize::MAX; names.len()];
        let mut failed = false;
        for (position, arg) in args.iter().enumerate() {
            let name = arg.name.as_ref().expect("all arguments are named");
            let Some(index) = names.iter().position(|n| *n == name.name) else {
                self.push(
                    Diagnostic::new(
                        name.span,
                        format!("`{subject}` has no {noun} named `{}`", name.name),
                    )
                    .label(format!("unknown {noun}")),
                );
                failed = true;
                continue;
            };
            if order[index] != usize::MAX {
                self.error(name.span, format!("`{}` is given twice", name.name));
                failed = true;
                continue;
            }
            order[index] = position;
        }
        let missing: Vec<&str> = order
            .iter()
            .enumerate()
            .filter(|(_, p)| **p == usize::MAX)
            .map(|(i, _)| names[i].as_str())
            .collect();
        if !missing.is_empty() {
            let message = format!(
                "missing {noun}{}: {}",
                if missing.len() == 1 { "" } else { "s" },
                missing.join(", ")
            );
            self.error(span, message);
            failed = true;
        }
        if failed { None } else { Some(order) }
    }

    fn check_construct(
        &mut self,
        path: &ast::Path,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        // The built-in constructors need the expectation to supply the argument they cannot see.
        if path.segments.len() == 1 {
            match path.last().name.as_str() {
                "None" | "Some" => return self.check_option(path, args, expected, span),
                "Ok" | "Err" => return self.check_result(path, args, expected, span),
                _ => {}
            }
        }

        match path.segments.len() {
            1 => {
                let name = &path.last().name;
                match self.types.get(name) {
                    Some(TypeName::Record(id)) => {
                        let id = *id;
                        self.construct_record(id, args, span)
                    }
                    Some(TypeName::Enum(_)) => {
                        self.push(
                            Diagnostic::new(span, format!("`{name}` is an enum"))
                                .note("name the variant too, as in `#LoadError.NotFound`"),
                        );
                        Expr {
                            kind: ExprKind::Error,
                            ty: Ty::Error,
                            span,
                        }
                    }
                    _ => {
                        self.error(span, format!("unknown record `{name}`"));
                        Expr {
                            kind: ExprKind::Error,
                            ty: Ty::Error,
                            span,
                        }
                    }
                }
            }
            2 => {
                let enum_name = &path.segments[0].name;
                let variant_name = &path.segments[1].name;
                let Some(TypeName::Enum(id)) = self.types.get(enum_name) else {
                    self.error(path.segments[0].span, format!("unknown enum `{enum_name}`"));
                    return Expr {
                        kind: ExprKind::Error,
                        ty: Ty::Error,
                        span,
                    };
                };
                let id = *id;
                let Some((index, _)) = self.program.enums[id.index()].variant(variant_name) else {
                    let message = format!("`{enum_name}` has no variant `{variant_name}`");
                    self.push(
                        Diagnostic::new(path.segments[1].span, message).label("unknown variant"),
                    );
                    return Expr {
                        kind: ExprKind::Error,
                        ty: Ty::Error,
                        span,
                    };
                };
                self.construct_variant(id, index, args, Ty::Enum(id), span)
            }
            _ => {
                self.error(span, format!("unknown constructor `{}`", path.text()));
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
        }
    }

    fn check_option(
        &mut self,
        path: &ast::Path,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let some = path.last().name == "Some";
        let inner_expected = match expected {
            Some(Ty::Option(inner)) => Some((**inner).clone()),
            Some(other) if !other.is_error() => {
                let message = format!("expected {}, found Option", self.program.ty_name(other));
                self.error(span, message);
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
            _ => None,
        };

        if !some {
            if !args.is_empty() {
                self.error(span, "`#None` takes no arguments");
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
            let Some(inner) = inner_expected else {
                return self.uninferable(span, "#None", "Option<I64>");
            };
            return Expr {
                kind: ExprKind::Construct {
                    ctor: Ctor::Variant(EnumId::OPTION, EnumId::NONE),
                    args: Vec::new(),
                },
                ty: Ty::Option(Box::new(inner)),
                span,
            };
        }

        if args.len() != 1 || args[0].name.is_some() {
            self.error(span, "`#Some` takes one positional argument");
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let value = self.check_expr(&args[0].value, inner_expected.as_ref());
        let inner = inner_expected.unwrap_or_else(|| value.ty.clone());
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Variant(EnumId::OPTION, EnumId::SOME),
                args: vec![value],
            },
            ty: Ty::Option(Box::new(inner)),
            span,
        }
    }

    fn check_result(
        &mut self,
        path: &ast::Path,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let is_ok = path.last().name == "Ok";
        let parts = match expected {
            Some(Ty::Result(ok, err)) => Some(((**ok).clone(), (**err).clone())),
            Some(other) if !other.is_error() => {
                let message = format!("expected {}, found Result", self.program.ty_name(other));
                self.error(span, message);
                return Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                };
            }
            _ => None,
        };

        let name = if is_ok { "#Ok" } else { "#Err" };
        if args.len() != 1 || args[0].name.is_some() {
            self.error(span, format!("`{name}` takes one positional argument"));
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let side = parts
            .as_ref()
            .map(|(ok, err)| if is_ok { ok.clone() } else { err.clone() });
        let value = self.check_expr(&args[0].value, side.as_ref());

        let (ok, err) = match parts {
            Some(parts) => parts,
            None if is_ok => {
                return self.uninferable(span, name, "Result<I64, LoadError>");
            }
            None => return self.uninferable(span, name, "Result<I64, LoadError>"),
        };
        let variant = if is_ok { EnumId::OK } else { EnumId::ERR };
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Variant(EnumId::RESULT, variant),
                args: vec![value],
            },
            ty: Ty::Result(Box::new(ok), Box::new(err)),
            span,
        }
    }

    fn uninferable(&mut self, span: Span, what: &str, example: &str) -> Expr {
        self.push(
            Diagnostic::new(span, format!("cannot tell what type `{what}` builds here"))
                .label("no expected type at this position")
                .note(format!(
                    "annotate the binding or the return type, as in `let x: {example} = …`"
                )),
        );
        Expr {
            kind: ExprKind::Error,
            ty: Ty::Error,
            span,
        }
    }

    fn construct_record(&mut self, id: RecordId, args: &[ast::Arg], span: Span) -> Expr {
        let record = &self.program.records[id.index()];
        let name = record.name.clone();
        let names: Vec<String> = record.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = record.fields.iter().map(|f| f.ty.clone()).collect();
        let Some(order) = self.argument_order(&names, args, &name, "field", span) else {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let mut checked = Vec::with_capacity(types.len());
        for (index, ty) in types.iter().enumerate() {
            checked.push(self.check_expr(&args[order[index]].value, Some(ty)));
        }
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Record(id),
                args: checked,
            },
            ty: Ty::Record(id),
            span,
        }
    }

    fn construct_variant(
        &mut self,
        id: EnumId,
        index: usize,
        args: &[ast::Arg],
        ty: Ty,
        span: Span,
    ) -> Expr {
        let variant = &self.program.enums[id.index()].variants[index];
        let subject = format!("{}.{}", self.program.enums[id.index()].name, variant.name);
        let names: Vec<String> = variant.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = variant.fields.iter().map(|f| f.ty.clone()).collect();
        let Some(order) = self.argument_order(&names, args, &subject, "field", span) else {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        };
        let mut checked = Vec::with_capacity(types.len());
        for (i, field_ty) in types.iter().enumerate() {
            checked.push(self.check_expr(&args[order[i]].value, Some(field_ty)));
        }
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Variant(id, index),
                args: checked,
            },
            ty,
            span,
        }
    }

    // ---------------------------------------------------------------- blocks and control flow

    fn check_block(&mut self, block: &ast::Block, expected: Option<&Ty>, span: Span) -> Expr {
        self.scopes.push(Vec::new());

        // A trailing expression statement is the block's value. Everything before it is a
        // statement whose value is discarded.
        let tail_index = match block.stmts.last() {
            Some(ast::Stmt {
                kind: ast::StmtKind::Expr(_),
                ..
            }) => Some(block.stmts.len() - 1),
            _ => None,
        };

        let mut stmts = Vec::new();
        let mut diverges = false;
        for (index, stmt) in block.stmts.iter().enumerate() {
            if Some(index) == tail_index {
                break;
            }
            let checked = self.check_stmt(stmt);
            if let StmtKind::Expr(expr) | StmtKind::Let { value: expr, .. } = &checked.kind
                && expr.ty == Ty::Never
            {
                diverges = true;
            }
            if let StmtKind::Expr(expr) = &checked.kind
                && matches!(expr.ty, Ty::Task(_))
            {
                self.discarded_task(stmt.span);
            }
            stmts.push(checked);
        }

        let tail = tail_index.map(|index| {
            let ast::StmtKind::Expr(expr) = &block.stmts[index].kind else {
                unreachable!()
            };
            Box::new(self.check_expr(expr, expected))
        });

        self.scopes.pop();

        let ty = match &tail {
            Some(tail) => tail.ty.clone(),
            None if diverges => Ty::Never,
            None => Ty::Unit,
        };
        Expr {
            kind: ExprKind::Block { stmts, tail },
            ty,
            span,
        }
    }

    fn check_stmt(&mut self, stmt: &ast::Stmt) -> Stmt {
        let span = stmt.span;
        let kind = match &stmt.kind {
            ast::StmtKind::Let {
                mutable,
                name,
                ty,
                value,
            } => {
                let declared = ty.as_ref().map(|ty| self.resolve_ty(ty));
                let value = self.check_expr(value, declared.as_ref());
                let ty = declared.unwrap_or_else(|| match &value.ty {
                    Ty::Never => Ty::Unit,
                    ty => ty.clone(),
                });
                let local = self.declare_local(name.name.clone(), ty, *mutable, name.span);
                StmtKind::Let { local, value }
            }
            ast::StmtKind::Assign { target, value } => {
                let place = self.check_expr(target, None);
                self.check_assignable(&place, target.span);
                let value = self.check_expr(value, Some(&place.ty));
                StmtKind::Assign { place, value }
            }
            ast::StmtKind::Return(value) => {
                let ret = self.ret.clone();
                let value = match value {
                    Some(expr) => Some(Box::new(self.check_expr(expr, Some(&ret)))),
                    None => {
                        if !Ty::Unit.fits(&ret) {
                            let message =
                                format!("expected {}, found ()", self.program.ty_name(&ret));
                            self.error(span, message);
                        }
                        None
                    }
                };
                StmtKind::Expr(Expr {
                    kind: ExprKind::Return { value },
                    ty: Ty::Never,
                    span,
                })
            }
            ast::StmtKind::Expr(expr) => StmtKind::Expr(self.check_expr(expr, None)),
        };
        Stmt { kind, span }
    }

    /// An assignment target must be a local, or a chain of fields rooted at one, and that local
    /// must be `mut`.
    fn check_assignable(&mut self, place: &Expr, span: Span) {
        let mut cursor = place;
        loop {
            match &cursor.kind {
                ExprKind::Local(id) => {
                    let local = &self.locals[id.index()];
                    if !local.mutable {
                        let name = local.name.clone();
                        self.push(
                            Diagnostic::new(span, format!("`{name}` is not declared `mut`"))
                                .label("cannot assign")
                                .note(format!("declare it as `let mut {name} = …`")),
                        );
                    }
                    return;
                }
                ExprKind::Field { base, .. } => cursor = base,
                ExprKind::Error => return,
                _ => {
                    self.error(span, "only a variable or one of its fields can be assigned");
                    return;
                }
            }
        }
    }

    fn check_if(
        &mut self,
        cond: &ast::Expr,
        then: &ast::Block,
        els: &Option<Box<ast::Expr>>,
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let cond = self.check_expr(cond, Some(&Ty::Bool));
        let then = self.check_block(then, expected, then.span);
        let els = match els {
            Some(els) => {
                let expected = match expected {
                    Some(ty) => Some(ty.clone()),
                    None if then.ty != Ty::Never => Some(then.ty.clone()),
                    None => None,
                };
                Some(Box::new(self.check_expr(els, expected.as_ref())))
            }
            None => {
                if !then.ty.fits(&Ty::Unit) {
                    let message = format!(
                        "an `if` without an `else` must produce (), found {}",
                        self.program.ty_name(&then.ty)
                    );
                    self.error(span, message);
                }
                None
            }
        };
        let ty = match (&els, &then.ty) {
            (None, _) => Ty::Unit,
            (Some(els), Ty::Never) => els.ty.clone(),
            (Some(_), ty) => ty.clone(),
        };
        Expr {
            kind: ExprKind::If {
                cond: Box::new(cond),
                then: Box::new(then),
                els,
            },
            ty,
            span,
        }
    }

    fn check_match(
        &mut self,
        scrutinee: &ast::Expr,
        arms: &[ast::Arm],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let scrutinee = self.check_expr(scrutinee, None);
        let scrutinee_ty = scrutinee.ty.clone();
        if arms.is_empty() {
            self.error(span, "a `match` needs at least one arm");
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }

        let mut checked = Vec::with_capacity(arms.len());
        let mut result: Option<Ty> = expected.cloned();
        for arm in arms {
            self.scopes.push(Vec::new());
            let pat = self.check_pat(&arm.pat, &scrutinee_ty);
            let guard = arm
                .guard
                .as_ref()
                .map(|g| self.check_expr(g, Some(&Ty::Bool)));
            let body = self.check_expr(&arm.body, result.as_ref());
            self.scopes.pop();
            if result.is_none() && body.ty != Ty::Never && !body.ty.is_error() {
                result = Some(body.ty.clone());
            }
            checked.push(Arm {
                pat,
                guard,
                body,
                span: arm.span,
            });
        }

        self.check_exhaustive(&checked, &scrutinee_ty, span);
        let ty = result.unwrap_or(Ty::Never);
        Expr {
            kind: ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms: checked,
            },
            ty,
            span,
        }
    }

    /// Top-level coverage only: an arm names a variant, or it is irrefutable. Gaps hidden inside a
    /// nested pattern are not detected here and trap at runtime instead — a full usefulness
    /// algorithm can arrive with the rest of the pattern work.
    fn check_exhaustive(&mut self, arms: &[Arm], scrutinee: &Ty, span: Span) {
        if scrutinee.is_error() || *scrutinee == Ty::Never {
            return;
        }

        let mut covered = Vec::new();
        for arm in arms {
            if arm.guard.is_some() {
                continue;
            }
            let mut collect = |pat: &Pat| match &pat.kind {
                PatKind::Wild | PatKind::Bind(_) => covered.push(usize::MAX),
                PatKind::Variant { variant, .. } => covered.push(*variant),
                PatKind::Record { .. } => covered.push(usize::MAX),
                _ => {}
            };
            match &arm.pat.kind {
                PatKind::Or(alts) => alts.iter().for_each(&mut collect),
                _ => collect(&arm.pat),
            }
        }
        if covered.contains(&usize::MAX) {
            return;
        }

        let (enum_id, name) = match scrutinee {
            Ty::Enum(id) => (*id, self.program.enums[id.index()].name.clone()),
            Ty::Option(_) => (EnumId::OPTION, "Option".to_string()),
            Ty::Result(_, _) => (EnumId::RESULT, "Result".to_string()),
            other => {
                let message = format!(
                    "this `match` on {} needs a catch-all arm",
                    self.program.ty_name(other)
                );
                self.push(Diagnostic::new(span, message).note("add `_ => …`"));
                return;
            }
        };

        let missing: Vec<String> = self.program.enums[enum_id.index()]
            .variants
            .iter()
            .enumerate()
            .filter(|(index, _)| !covered.contains(index))
            .map(|(_, variant)| format!("#{name}.{}", variant.name))
            .collect();
        if !missing.is_empty() {
            self.push(
                Diagnostic::new(
                    span,
                    format!("this `match` does not cover {}", missing.join(", ")),
                )
                .label("not exhaustive")
                .note("add the missing arms, or a `_ => …` catch-all"),
            );
        }
    }

    fn check_try(&mut self, inner: &ast::Expr, span: Span) -> Expr {
        let inner = self.check_expr(inner, None);
        if inner.ty.is_error() {
            return Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            };
        }
        let ret = self.ret.clone();
        match (&inner.ty, &ret) {
            (Ty::Result(ok, err), Ty::Result(_, ret_err)) => {
                if err != ret_err {
                    let message = format!(
                        "this fails with {}, but the function fails with {}",
                        self.program.ty_name(err),
                        self.program.ty_name(ret_err)
                    );
                    self.push(Diagnostic::new(span, message).note(
                        "there is no automatic error conversion; match and rebuild the error",
                    ));
                    return Expr {
                        kind: ExprKind::Error,
                        ty: Ty::Error,
                        span,
                    };
                }
                let ty = (**ok).clone();
                Expr {
                    kind: ExprKind::Try {
                        expr: Box::new(inner),
                        enum_id: EnumId::RESULT,
                    },
                    ty,
                    span,
                }
            }
            (Ty::Option(some), Ty::Option(_)) => {
                let ty = (**some).clone();
                Expr {
                    kind: ExprKind::Try {
                        expr: Box::new(inner),
                        enum_id: EnumId::OPTION,
                    },
                    ty,
                    span,
                }
            }
            (Ty::Result(_, _) | Ty::Option(_), ret) => {
                let message = format!(
                    "`?` needs the function to return the same shape, but it returns {}",
                    self.program.ty_name(ret)
                );
                self.push(Diagnostic::new(span, message).label("cannot propagate here"));
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
            (other, _) => {
                let message = format!(
                    "`?` applies to Result and Option, not {}",
                    self.program.ty_name(other)
                );
                self.error(span, message);
                Expr {
                    kind: ExprKind::Error,
                    ty: Ty::Error,
                    span,
                }
            }
        }
    }

    // ---------------------------------------------------------------- patterns

    fn check_pat(&mut self, pat: &ast::Pat, ty: &Ty) -> Pat {
        let span = pat.span;
        match &pat.kind {
            ast::PatKind::Wild => Pat {
                kind: PatKind::Wild,
                span,
            },
            ast::PatKind::Binding(name) => {
                let local = self.declare_local(name.name.clone(), ty.clone(), false, name.span);
                Pat {
                    kind: PatKind::Bind(local),
                    span,
                }
            }
            ast::PatKind::Int(v) => {
                self.expect_pat_ty(&Ty::I64, ty, span);
                Pat {
                    kind: PatKind::Int(*v),
                    span,
                }
            }
            ast::PatKind::Str(v) => {
                self.expect_pat_ty(&Ty::Str, ty, span);
                Pat {
                    kind: PatKind::Str(v.clone()),
                    span,
                }
            }
            ast::PatKind::Bool(v) => {
                self.expect_pat_ty(&Ty::Bool, ty, span);
                Pat {
                    kind: PatKind::Bool(*v),
                    span,
                }
            }
            ast::PatKind::Or(alts) => {
                let checked: Vec<Pat> = alts.iter().map(|alt| self.check_pat(alt, ty)).collect();
                if checked.iter().any(binds_anything) {
                    self.push(
                        Diagnostic::new(span, "an alternative pattern may not bind names yet")
                            .note("each alternative would have to bind the same names; write separate arms"),
                    );
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                }
                Pat {
                    kind: PatKind::Or(checked),
                    span,
                }
            }
            ast::PatKind::Construct { path, args, rest } => {
                self.check_construct_pat(path, args, *rest, ty, span)
            }
        }
    }

    fn expect_pat_ty(&mut self, found: &Ty, expected: &Ty, span: Span) {
        if !found.fits(expected) {
            let message = format!(
                "this pattern matches {}, but the value is {}",
                self.program.ty_name(found),
                self.program.ty_name(expected)
            );
            self.error(span, message);
        }
    }

    fn check_construct_pat(
        &mut self,
        path: &ast::Path,
        args: &[ast::PatArg],
        rest: bool,
        ty: &Ty,
        span: Span,
    ) -> Pat {
        // Resolve the constructor against the type being matched, so `#Some(x)` and `#Ok(x)` need
        // no qualification and pick up their payload type from the scrutinee.
        let resolved = match (path.segments.len(), path.last().name.as_str(), ty) {
            (1, "None", Ty::Option(_)) => Some((EnumId::OPTION, EnumId::NONE, Vec::new())),
            (1, "Some", Ty::Option(inner)) => {
                Some((EnumId::OPTION, EnumId::SOME, vec![(**inner).clone()]))
            }
            (1, "Ok", Ty::Result(ok, _)) => {
                Some((EnumId::RESULT, EnumId::OK, vec![(**ok).clone()]))
            }
            (1, "Err", Ty::Result(_, err)) => {
                Some((EnumId::RESULT, EnumId::ERR, vec![(**err).clone()]))
            }
            _ => None,
        };

        if let Some((enum_id, variant, types)) = resolved {
            let names: Vec<String> = (0..types.len()).map(|i| i.to_string()).collect();
            let name = format!("#{}", path.text());
            let Some(sub) = self.pat_args(&names, &types, args, rest, &name, span) else {
                return Pat {
                    kind: PatKind::Error,
                    span,
                };
            };
            return Pat {
                kind: PatKind::Variant {
                    enum_id,
                    variant,
                    args: sub,
                },
                span,
            };
        }

        match path.segments.len() {
            1 => {
                let name = path.last().name.clone();
                if matches!(name.as_str(), "None" | "Some" | "Ok" | "Err") {
                    let message = format!(
                        "`#{name}` matches Option or Result, but the value is {}",
                        self.program.ty_name(ty)
                    );
                    self.error(span, message);
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                }
                let Some(TypeName::Record(id)) = self.types.get(&name) else {
                    self.error(span, format!("unknown record `{name}`"));
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                let id = *id;
                self.expect_pat_ty(&Ty::Record(id), ty, span);
                let record = &self.program.records[id.index()];
                let names: Vec<String> = record.fields.iter().map(|f| f.name.clone()).collect();
                let types: Vec<Ty> = record.fields.iter().map(|f| f.ty.clone()).collect();
                let Some(sub) = self.pat_args(&names, &types, args, rest, &name, span) else {
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                Pat {
                    kind: PatKind::Record {
                        record: id,
                        args: sub,
                    },
                    span,
                }
            }
            2 => {
                let enum_name = path.segments[0].name.clone();
                let variant_name = path.segments[1].name.clone();
                let Some(TypeName::Enum(id)) = self.types.get(&enum_name) else {
                    self.error(path.segments[0].span, format!("unknown enum `{enum_name}`"));
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                let id = *id;
                self.expect_pat_ty(&Ty::Enum(id), ty, span);
                let Some((index, variant)) = self.program.enums[id.index()].variant(&variant_name)
                else {
                    let message = format!("`{enum_name}` has no variant `{variant_name}`");
                    self.push(
                        Diagnostic::new(path.segments[1].span, message).label("unknown variant"),
                    );
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                let names: Vec<String> = variant.fields.iter().map(|f| f.name.clone()).collect();
                let types: Vec<Ty> = variant.fields.iter().map(|f| f.ty.clone()).collect();
                let subject = format!("{enum_name}.{variant_name}");
                let Some(sub) = self.pat_args(&names, &types, args, rest, &subject, span) else {
                    return Pat {
                        kind: PatKind::Error,
                        span,
                    };
                };
                Pat {
                    kind: PatKind::Variant {
                        enum_id: id,
                        variant: index,
                        args: sub,
                    },
                    span,
                }
            }
            _ => {
                self.error(span, format!("unknown constructor `{}`", path.text()));
                Pat {
                    kind: PatKind::Error,
                    span,
                }
            }
        }
    }

    /// Expand a constructor pattern's arguments to full arity in declaration order, filling the
    /// gaps `..` leaves with wildcards.
    fn pat_args(
        &mut self,
        names: &[String],
        types: &[Ty],
        args: &[ast::PatArg],
        rest: bool,
        subject: &str,
        span: Span,
    ) -> Option<Vec<Pat>> {
        let named = args.iter().filter(|a| a.name.is_some()).count();
        if named != 0 && named != args.len() {
            self.error(
                span,
                "pattern arguments are either all named or all positional",
            );
            return None;
        }

        let mut slots: Vec<Option<&ast::Pat>> = vec![None; names.len()];
        if named == 0 {
            if args.len() > names.len() || (args.len() < names.len() && !rest) {
                let message = format!(
                    "`{subject}` has {} field{}, found {}",
                    names.len(),
                    if names.len() == 1 { "" } else { "s" },
                    args.len()
                );
                let mut diagnostic = Diagnostic::new(span, message);
                if args.len() < names.len() {
                    diagnostic = diagnostic.note("write `..` to ignore the rest");
                }
                self.push(diagnostic);
                return None;
            }
            for (slot, arg) in slots.iter_mut().zip(args) {
                *slot = Some(&arg.pat);
            }
        } else {
            for arg in args {
                let name = arg.name.as_ref().expect("all arguments are named");
                let Some(index) = names.iter().position(|n| *n == name.name) else {
                    self.push(
                        Diagnostic::new(
                            name.span,
                            format!("`{subject}` has no field named `{}`", name.name),
                        )
                        .label("unknown field"),
                    );
                    return None;
                };
                if slots[index].is_some() {
                    self.error(name.span, format!("`{}` is matched twice", name.name));
                    return None;
                }
                slots[index] = Some(&arg.pat);
            }
            if !rest && slots.iter().any(Option::is_none) {
                let missing: Vec<&str> = slots
                    .iter()
                    .enumerate()
                    .filter(|(_, slot)| slot.is_none())
                    .map(|(i, _)| names[i].as_str())
                    .collect();
                self.push(
                    Diagnostic::new(span, format!("missing fields: {}", missing.join(", ")))
                        .note("write `..` to ignore the rest"),
                );
                return None;
            }
        }

        Some(
            slots
                .into_iter()
                .zip(types)
                .map(|(slot, ty)| match slot {
                    Some(pat) => self.check_pat(pat, ty),
                    None => Pat {
                        kind: PatKind::Wild,
                        span,
                    },
                })
                .collect(),
        )
    }
}

fn binds_anything(pat: &Pat) -> bool {
    match &pat.kind {
        PatKind::Bind(_) => true,
        PatKind::Variant { args, .. } | PatKind::Record { args, .. } => {
            args.iter().any(binds_anything)
        }
        PatKind::Or(alts) => alts.iter().any(binds_anything),
        _ => false,
    }
}
