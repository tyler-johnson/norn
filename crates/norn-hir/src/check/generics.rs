//! Generic templates and their instances.
//!
//! A declaration with type parameters is a template: it lives in the program tables like any
//! other def, `type_params` non-empty, and is never itself the type of a value. Naming it at
//! concrete arguments appends an ordinary monomorphic def — an instance — to the same table, so
//! nothing downstream of the checker learns that generics exist. Types are erased at lowering,
//! which is what makes check-time monomorphization the whole implementation.
//!
//! Everything here is insertion-ordered Vecs with linear-scan dedup and keyed map lookups —
//! never a `HashMap` iteration — so instance ids are a pure function of the AST, the same
//! determinism rule `topological` states for reactor graphs.

use super::*;

/// One instantiation of a generic struct template: which template, at which arguments, and the
/// id the instance was appended under. `module`/`at` record where it was first asked for, which
/// is where a diagnostic about filling it belongs.
pub(super) struct StructInstance {
    pub(super) template: StructId,
    pub(super) args: Vec<Ty>,
    pub(super) id: StructId,
    module: usize,
    at: Span,
}

/// The enum half of `StructInstance`.
pub(super) struct EnumInstance {
    pub(super) template: EnumId,
    pub(super) args: Vec<Ty>,
    pub(super) id: EnumId,
    module: usize,
    at: Span,
}

/// A type instance whose fields still need substituting, queued during `define_types` because
/// the template it copies from may not have its own fields yet. The second field is the
/// substitution depth the fill resumes at.
enum Fill {
    Struct(usize, usize),
    Enum(usize, usize),
}

/// The checker-side registry of generic instantiations.
pub(super) struct Generics {
    struct_instances: Vec<StructInstance>,
    enum_instances: Vec<EnumInstance>,
    /// Instance id → registry index, the reverse direction of the Vecs above. Keyed lookups only.
    struct_meaning: HashMap<StructId, usize>,
    enum_meaning: HashMap<EnumId, usize>,
    /// Pending fills, drained FIFO by `drain_type_fills` through `fill_cursor`.
    fill_queue: Vec<Fill>,
    fill_cursor: usize,
    /// True while `define_types` and its drain run: instances allocated then are filled by the
    /// drain rather than on the spot.
    pub(super) defining_types: bool,
    /// The global instance ceiling has one report in it, not one per instantiation past it.
    cap_reported: bool,
}

impl Generics {
    pub(super) fn new() -> Generics {
        Generics {
            struct_instances: Vec::new(),
            enum_instances: Vec::new(),
            struct_meaning: HashMap::new(),
            enum_meaning: HashMap::new(),
            fill_queue: Vec::new(),
            fill_cursor: 0,
            defining_types: false,
            cap_reported: false,
        }
    }
}

/// Substitution deeper than this is reported rather than followed. A self-referential instance
/// dedups to itself, so only a type that *grows* under substitution can get here.
const INSTANCE_DEPTH: usize = 32;

/// The global ceiling on generic instances — a backstop far above any real program, so a
/// divergence the depth cap misses still terminates with a diagnostic instead of an allocation.
const INSTANCE_CEILING: usize = 4096;

impl Checker {
    /// The identity argument vector of a template: each parameter standing for itself. A mention
    /// of `List<T>` inside `List<T>`'s own declaration instantiates at exactly this vector, and
    /// resolving it to the template id itself is what keeps self-reference from minting an
    /// instance at all.
    pub(super) fn param_identity(params: &[String]) -> Vec<Ty> {
        params
            .iter()
            .enumerate()
            .map(|(index, name)| Ty::Param {
                index: index as u32,
                name: name.clone(),
            })
            .collect()
    }

    /// What a struct id means generically: `(template, arguments)` for an instance, the identity
    /// instance for a template, `None` for an ordinary monomorphic struct.
    pub(super) fn struct_base(&self, id: StructId) -> Option<(StructId, Vec<Ty>)> {
        if let Some(&at) = self.generics.struct_meaning.get(&id) {
            let instance = &self.generics.struct_instances[at];
            return Some((instance.template, instance.args.clone()));
        }
        let def = &self.program.structs[id.index()];
        if def.type_params.is_empty() {
            None
        } else {
            Some((id, Self::param_identity(&def.type_params)))
        }
    }

    /// The enum half of `struct_base`.
    pub(super) fn enum_base(&self, id: EnumId) -> Option<(EnumId, Vec<Ty>)> {
        if let Some(&at) = self.generics.enum_meaning.get(&id) {
            let instance = &self.generics.enum_instances[at];
            return Some((instance.template, instance.args.clone()));
        }
        let def = &self.program.enums[id.index()];
        if def.type_params.is_empty() {
            None
        } else {
            Some((id, Self::param_identity(&def.type_params)))
        }
    }

    /// How an instance displays: `List<I64>`, `Pair<I64, Bool>`. Never a Rust identifier —
    /// codegen writes names as string literals — so the brackets are safe everywhere a name goes.
    fn instance_name(&self, base: &str, args: &[Ty]) -> String {
        let args: Vec<String> = args.iter().map(|arg| self.program.ty_name(arg)).collect();
        format!("{base}<{}>", args.join(", "))
    }

    fn depth_exceeded(&mut self, at: Span) {
        self.push(
            Diagnostic::new(at, "generic instantiation recursed too deeply")
                .label(format!("more than {INSTANCE_DEPTH} levels of substitution"))
                .note("a type that grows with every substitution never converges; check for a type argument that mentions the type it instantiates"),
        );
    }

    /// Whether one more instance may be allocated; the ceiling reports once and then poisons.
    fn instance_budget(&mut self, at: Span) -> bool {
        let count = self.generics.struct_instances.len() + self.generics.enum_instances.len();
        if count < INSTANCE_CEILING {
            return true;
        }
        if !self.generics.cap_reported {
            self.generics.cap_reported = true;
            self.push(
                Diagnostic::new(
                    at,
                    format!("this program needs more than {INSTANCE_CEILING} generic instances"),
                )
                .label("instantiation stopped here")
                .note("a ceiling this size is only ever reached by a type that grows under substitution and never converges"),
            );
        }
        false
    }

    /// Instantiate a struct template at `args`, deduplicating on `(template, args)` so equal
    /// spellings share one id — which derived `Value` equality depends on. Two-phase: the
    /// instance is registered *before* its fields are substituted, so a self-referential type
    /// dedups to itself instead of recursing. `None` means poisoned, already diagnosed.
    pub(super) fn instantiate_struct(
        &mut self,
        template: StructId,
        args: Vec<Ty>,
        at: Span,
        depth: usize,
    ) -> Option<StructId> {
        if args == Self::param_identity(&self.program.structs[template.index()].type_params) {
            return Some(template);
        }
        if let Some(found) = self
            .generics
            .struct_instances
            .iter()
            .find(|instance| instance.template == template && instance.args == args)
        {
            return Some(found.id);
        }
        if depth > INSTANCE_DEPTH {
            self.depth_exceeded(at);
            return None;
        }
        if !self.instance_budget(at) {
            return None;
        }
        let name = self.instance_name(&self.program.structs[template.index()].name.clone(), &args);
        let id = StructId(self.program.structs.len() as u32);
        self.program.structs.push(StructDef {
            name,
            type_params: Vec::new(),
            fields: Vec::new(),
            span: self.program.structs[template.index()].span,
        });
        let index = self.generics.struct_instances.len();
        self.generics.struct_instances.push(StructInstance {
            template,
            args,
            id,
            module: self.current,
            at,
        });
        self.generics.struct_meaning.insert(id, index);
        if self.generics.defining_types {
            self.generics.fill_queue.push(Fill::Struct(index, depth));
        } else {
            self.fill_struct(index, depth);
        }
        Some(id)
    }

    /// The enum half of `instantiate_struct`.
    pub(super) fn instantiate_enum(
        &mut self,
        template: EnumId,
        args: Vec<Ty>,
        at: Span,
        depth: usize,
    ) -> Option<EnumId> {
        if args == Self::param_identity(&self.program.enums[template.index()].type_params) {
            return Some(template);
        }
        if let Some(found) = self
            .generics
            .enum_instances
            .iter()
            .find(|instance| instance.template == template && instance.args == args)
        {
            return Some(found.id);
        }
        if depth > INSTANCE_DEPTH {
            self.depth_exceeded(at);
            return None;
        }
        if !self.instance_budget(at) {
            return None;
        }
        let name = self.instance_name(&self.program.enums[template.index()].name.clone(), &args);
        let id = EnumId(self.program.enums.len() as u32);
        self.program.enums.push(EnumDef {
            name,
            type_params: Vec::new(),
            variants: Vec::new(),
            span: self.program.enums[template.index()].span,
        });
        let index = self.generics.enum_instances.len();
        self.generics.enum_instances.push(EnumInstance {
            template,
            args,
            id,
            module: self.current,
            at,
        });
        self.generics.enum_meaning.insert(id, index);
        if self.generics.defining_types {
            self.generics.fill_queue.push(Fill::Enum(index, depth));
        } else {
            self.fill_enum(index, depth);
        }
        Some(id)
    }

    fn fill_struct(&mut self, index: usize, depth: usize) {
        let (template, args, id, module, at) = {
            let instance = &self.generics.struct_instances[index];
            (
                instance.template,
                instance.args.clone(),
                instance.id,
                instance.module,
                instance.at,
            )
        };
        let fields = self.program.structs[template.index()].fields.clone();
        // Diagnostics raised while filling — a depth overrun in a nested argument — belong to
        // the file that first asked for the instance.
        let outer = std::mem::replace(&mut self.current, module);
        let fields: Vec<FieldDef> = fields
            .into_iter()
            .map(|mut field| {
                field.ty = self.subst(&field.ty, &args, at, depth + 1);
                field
            })
            .collect();
        self.current = outer;
        self.program.structs[id.index()].fields = fields;
    }

    fn fill_enum(&mut self, index: usize, depth: usize) {
        let (template, args, id, module, at) = {
            let instance = &self.generics.enum_instances[index];
            (
                instance.template,
                instance.args.clone(),
                instance.id,
                instance.module,
                instance.at,
            )
        };
        let variants = self.program.enums[template.index()].variants.clone();
        let outer = std::mem::replace(&mut self.current, module);
        let variants: Vec<VariantDef> = variants
            .into_iter()
            .map(|mut variant| {
                for field in &mut variant.fields {
                    field.ty = self.subst(&field.ty, &args, at, depth + 1);
                }
                variant
            })
            .collect();
        self.current = outer;
        self.program.enums[id.index()].variants = variants;
    }

    /// Drain the fills queued during `define_types`, in the order the instances were asked for.
    /// Filling may queue more — a field of one instance can name another — and the cursor walks
    /// through those too, so after this returns every instance any later pass observes has real
    /// fields. That is what keeps `reactor_ty`'s eager affinity question right for a member like
    /// `state journal: List<Delta>`.
    pub(super) fn drain_type_fills(&mut self) {
        while self.generics.fill_cursor < self.generics.fill_queue.len() {
            let next = self.generics.fill_cursor;
            self.generics.fill_cursor += 1;
            match self.generics.fill_queue[next] {
                Fill::Struct(index, depth) => self.fill_struct(index, depth),
                Fill::Enum(index, depth) => self.fill_enum(index, depth),
            }
        }
        self.generics.defining_types = false;
    }

    /// The one substitution everything shares: parameters to `args`, boxes structurally, a
    /// generic struct or enum re-instantiated at its substituted arguments. Exhaustive over `Ty`
    /// on purpose — a future variant must break the build here, not silently pass through.
    pub(super) fn subst(&mut self, ty: &Ty, args: &[Ty], at: Span, depth: usize) -> Ty {
        match ty {
            Ty::Param { index, .. } => args.get(*index as usize).cloned().unwrap_or(Ty::Error),
            Ty::Option(inner) => Ty::Option(Box::new(self.subst(inner, args, at, depth))),
            Ty::Result(ok, err) => Ty::Result(
                Box::new(self.subst(ok, args, at, depth)),
                Box::new(self.subst(err, args, at, depth)),
            ),
            Ty::Task(inner) => Ty::Task(Box::new(self.subst(inner, args, at, depth))),
            Ty::Ref(inner) => Ty::Ref(Box::new(self.subst(inner, args, at, depth))),
            Ty::Input(inner) => Ty::Input(Box::new(self.subst(inner, args, at, depth))),
            Ty::Signal(inner) => Ty::Signal(Box::new(self.subst(inner, args, at, depth))),
            Ty::Event(inner) => Ty::Event(Box::new(self.subst(inner, args, at, depth))),
            Ty::Struct(id) => match self.struct_base(*id) {
                None => Ty::Struct(*id),
                Some((template, base_args)) => {
                    let new_args: Vec<Ty> = base_args
                        .iter()
                        .map(|arg| self.subst(arg, args, at, depth))
                        .collect();
                    match self.instantiate_struct(template, new_args, at, depth) {
                        Some(instance) => Ty::Struct(instance),
                        None => Ty::Error,
                    }
                }
            },
            Ty::Enum(id) => match self.enum_base(*id) {
                None => Ty::Enum(*id),
                Some((template, base_args)) => {
                    let new_args: Vec<Ty> = base_args
                        .iter()
                        .map(|arg| self.subst(arg, args, at, depth))
                        .collect();
                    match self.instantiate_enum(template, new_args, at, depth) {
                        Some(instance) => Ty::Enum(instance),
                        None => Ty::Error,
                    }
                }
            },
            Ty::Unit
            | Ty::I64
            | Ty::F64
            | Ty::Bool
            | Ty::Str
            | Ty::Bytes
            | Ty::Resource(_)
            | Ty::Reactor(_)
            | Ty::Never
            | Ty::Error => ty.clone(),
        }
    }

    /// Substitute a template-side type through partial `bindings`; an unbound parameter becomes
    /// `Ty::Error`, which is only reached on paths already diagnosed.
    pub(super) fn subst_bindings(&mut self, ty: &Ty, bindings: &[Option<Ty>], at: Span) -> Ty {
        let args: Vec<Ty> = bindings
            .iter()
            .map(|binding| binding.clone().unwrap_or(Ty::Error))
            .collect();
        self.subst(ty, &args, at, 0)
    }

    // ---------------------------------------------------------------- inference

    /// One-way structural match of `found` against a template-side `param` type, binding type
    /// parameters as they are met. First binding wins, and no disagreement is reported here: the
    /// caller re-checks the argument against the fully substituted type afterwards, which is
    /// where a conflict surfaces with both concrete names in hand.
    pub(super) fn solve(&self, param: &Ty, found: &Ty, bindings: &mut [Option<Ty>]) {
        // `Never` teaches nothing; `Error` poisons — binding the mentioned parameters to `Error`
        // is what keeps one bad argument from also being reported as uninferable.
        if matches!(found, Ty::Never) {
            return;
        }
        if found.is_error() {
            self.bind_params(param, bindings, &Ty::Error);
            return;
        }
        // Borrows strip on both sides: `&T` and `T` are the same values, and whether the borrow
        // was right is the re-check's question, not inference's.
        let found = found.owned();
        match (param, found) {
            (Ty::Param { index, .. }, _) => {
                let slot = &mut bindings[*index as usize];
                if slot.is_none() {
                    *slot = Some(found.clone());
                }
            }
            (Ty::Ref(inner), _) => self.solve(inner, found, bindings),
            (Ty::Option(p), Ty::Option(f)) => self.solve(p, f, bindings),
            (Ty::Result(po, pe), Ty::Result(fo, fe)) => {
                self.solve(po, fo, bindings);
                self.solve(pe, fe, bindings);
            }
            (Ty::Task(p), Ty::Task(f)) => self.solve(p, f, bindings),
            (Ty::Input(p), Ty::Input(f)) => self.solve(p, f, bindings),
            (Ty::Signal(p), Ty::Signal(f)) => self.solve(p, f, bindings),
            (Ty::Event(p), Ty::Event(f)) => self.solve(p, f, bindings),
            (Ty::Struct(p), Ty::Struct(f)) => {
                if let (Some((pt, pargs)), Some((ft, fargs))) =
                    (self.struct_base(*p), self.struct_base(*f))
                    && pt == ft
                {
                    for (pa, fa) in pargs.iter().zip(&fargs) {
                        self.solve(pa, fa, bindings);
                    }
                }
            }
            (Ty::Enum(p), Ty::Enum(f)) => {
                if let (Some((pt, pargs)), Some((ft, fargs))) =
                    (self.enum_base(*p), self.enum_base(*f))
                    && pt == ft
                {
                    for (pa, fa) in pargs.iter().zip(&fargs) {
                        self.solve(pa, fa, bindings);
                    }
                }
            }
            _ => {}
        }
    }

    /// Bind every parameter `ty` mentions that is still unbound — the poison direction of
    /// `solve`, and the cleanup after a structural mismatch has been reported.
    pub(super) fn bind_params(&self, ty: &Ty, bindings: &mut [Option<Ty>], to: &Ty) {
        match ty {
            Ty::Param { index, .. } => {
                let slot = &mut bindings[*index as usize];
                if slot.is_none() {
                    *slot = Some(to.clone());
                }
            }
            Ty::Option(inner)
            | Ty::Task(inner)
            | Ty::Ref(inner)
            | Ty::Input(inner)
            | Ty::Signal(inner)
            | Ty::Event(inner) => self.bind_params(inner, bindings, to),
            Ty::Result(ok, err) => {
                self.bind_params(ok, bindings, to);
                self.bind_params(err, bindings, to);
            }
            Ty::Struct(id) => {
                if let Some((_, args)) = self.struct_base(*id) {
                    for arg in &args {
                        self.bind_params(arg, bindings, to);
                    }
                }
            }
            Ty::Enum(id) => {
                if let Some((_, args)) = self.enum_base(*id) {
                    for arg in &args {
                        self.bind_params(arg, bindings, to);
                    }
                }
            }
            Ty::Unit
            | Ty::I64
            | Ty::F64
            | Ty::Bool
            | Ty::Str
            | Ty::Bytes
            | Ty::Resource(_)
            | Ty::Reactor(_)
            | Ty::Never
            | Ty::Error => {}
        }
    }

    /// Whether `ty` mentions a parameter `bindings` has not settled yet.
    pub(super) fn mentions_unbound(&self, ty: &Ty, bindings: &[Option<Ty>]) -> bool {
        match ty {
            Ty::Param { index, .. } => bindings
                .get(*index as usize)
                .is_none_or(|binding| binding.is_none()),
            Ty::Option(inner)
            | Ty::Task(inner)
            | Ty::Ref(inner)
            | Ty::Input(inner)
            | Ty::Signal(inner)
            | Ty::Event(inner) => self.mentions_unbound(inner, bindings),
            Ty::Result(ok, err) => {
                self.mentions_unbound(ok, bindings) || self.mentions_unbound(err, bindings)
            }
            Ty::Struct(id) => self.struct_base(*id).is_some_and(|(_, args)| {
                args.iter().any(|arg| self.mentions_unbound(arg, bindings))
            }),
            Ty::Enum(id) => self.enum_base(*id).is_some_and(|(_, args)| {
                args.iter().any(|arg| self.mentions_unbound(arg, bindings))
            }),
            Ty::Unit
            | Ty::I64
            | Ty::F64
            | Ty::Bool
            | Ty::Str
            | Ty::Bytes
            | Ty::Resource(_)
            | Ty::Reactor(_)
            | Ty::Never
            | Ty::Error => false,
        }
    }

    // ---------------------------------------------------------------- generic construction

    /// Construction of a generic struct template: infer the type arguments — from the
    /// expectation when it names an instance of this template, field by field otherwise — then
    /// instantiate and check against the instance.
    pub(super) fn construct_generic_struct(
        &mut self,
        template: StructId,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let def = &self.program.structs[template.index()];
        let display = def.name.clone();
        let params = def.type_params.clone();
        let names: Vec<String> = def.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = def.fields.iter().map(|f| f.ty.clone()).collect();

        let Some(mut bindings) = self.expectation_bindings(
            &display,
            params.len(),
            expected,
            span,
            |checker, ty| match ty {
                Ty::Struct(id) => checker
                    .struct_base(*id)
                    .filter(|(base, _)| *base == template)
                    .map(|(_, args)| args),
                _ => None,
            },
        ) else {
            return self.error_expr(span);
        };

        let Some(order) = self.argument_order(&names, args, &display, "field", span) else {
            return self.error_expr(span);
        };
        let checked = self.check_template_fields(&types, args, &order, &mut bindings, span);
        let Some(instance_args) = self.settle_bindings(bindings, &params, &display, span) else {
            return self.error_expr(span);
        };
        let Some(instance) = self.instantiate_struct(template, instance_args, span, 0) else {
            return self.error_expr(span);
        };
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Struct(instance),
                args: checked,
            },
            ty: Ty::Struct(instance),
            span,
        }
    }

    /// The variant half of `construct_generic_struct`: `List.Cons(1, rest)`, `List.Nil` against
    /// an expectation.
    pub(super) fn construct_generic_variant(
        &mut self,
        template: EnumId,
        index: usize,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let def = &self.program.enums[template.index()];
        let display = def.name.clone();
        let params = def.type_params.clone();
        let variant = &def.variants[index];
        let subject = format!("{display}.{}", variant.name);
        let names: Vec<String> = variant.fields.iter().map(|f| f.name.clone()).collect();
        let types: Vec<Ty> = variant.fields.iter().map(|f| f.ty.clone()).collect();

        let Some(mut bindings) = self.expectation_bindings(
            &display,
            params.len(),
            expected,
            span,
            |checker, ty| match ty {
                Ty::Enum(id) => checker
                    .enum_base(*id)
                    .filter(|(base, _)| *base == template)
                    .map(|(_, args)| args),
                _ => None,
            },
        ) else {
            return self.error_expr(span);
        };

        let Some(order) = self.argument_order(&names, args, &subject, "field", span) else {
            return self.error_expr(span);
        };
        let checked = self.check_template_fields(&types, args, &order, &mut bindings, span);
        let Some(instance_args) = self.settle_bindings(bindings, &params, &display, span) else {
            return self.error_expr(span);
        };
        let Some(instance) = self.instantiate_enum(template, instance_args, span, 0) else {
            return self.error_expr(span);
        };
        Expr {
            kind: ExprKind::Construct {
                ctor: Ctor::Variant(instance, index),
                args: checked,
            },
            ty: Ty::Enum(instance),
            span,
        }
    }

    /// What the expectation says about a template's arguments: all of them when it names an
    /// instance of this template, nothing when there is no expectation, and a mismatch — the
    /// `check_option` precedent — when it names anything else. `None` means the mismatch was
    /// reported.
    fn expectation_bindings(
        &mut self,
        display: &str,
        count: usize,
        expected: Option<&Ty>,
        span: Span,
        matches: impl Fn(&Checker, &Ty) -> Option<Vec<Ty>>,
    ) -> Option<Vec<Option<Ty>>> {
        match expected {
            Some(ty) => {
                if let Some(args) = matches(self, ty) {
                    return Some(args.into_iter().map(Some).collect());
                }
                // An `Error` expectation was already reported — its annotation failed to
                // resolve — so it poisons the bindings rather than falling through to a
                // second, "cannot tell what type" report.
                if ty.is_error() {
                    return Some(vec![Some(Ty::Error); count]);
                }
                if matches!(ty, Ty::Never) {
                    return Some(vec![None; count]);
                }
                let message = format!("expected {}, found {display}", self.program.ty_name(ty));
                self.error(span, message);
                None
            }
            None => Some(vec![None; count]),
        }
    }

    /// Check each field of a template construction in declaration order. A field whose type is
    /// already settled is checked bidirectionally; one still mentioning an unbound parameter is
    /// synthesised, solved, and then re-checked against what solving settled — which is where a
    /// disagreement between two fields reports with concrete types on both sides.
    fn check_template_fields(
        &mut self,
        types: &[Ty],
        args: &[ast::Arg],
        order: &[usize],
        bindings: &mut Vec<Option<Ty>>,
        span: Span,
    ) -> Vec<Expr> {
        let mut checked = Vec::with_capacity(types.len());
        for (index, field_ty) in types.iter().enumerate() {
            let arg = &args[order[index]];
            if !self.mentions_unbound(field_ty, bindings) {
                let want = self.subst_bindings(field_ty, bindings, span);
                checked.push(self.check_expr(&arg.value, Some(&want)));
                continue;
            }
            let synth = self.check_expr(&arg.value, None);
            self.solve(field_ty, &synth.ty, bindings);
            if self.mentions_unbound(field_ty, bindings) {
                // The argument's shape never reached the parameter: a structural mismatch. The
                // template-side name carries the `T`, which is the honest thing to show.
                let message = format!(
                    "expected {}, found {}",
                    self.program.ty_name(field_ty),
                    self.program.ty_name(&synth.ty)
                );
                self.error(arg.value.span, message);
                self.bind_params(field_ty, bindings, &Ty::Error);
                checked.push(self.error_expr(arg.value.span));
                continue;
            }
            let want = self.subst_bindings(field_ty, bindings, span);
            let at = arg.value.span;
            checked.push(self.expect(synth, Some(&want), at));
        }
        checked
    }

    /// The end of inference: every parameter must have been settled by the expectation or an
    /// argument, or the construction is refused with the parameter named.
    fn settle_bindings(
        &mut self,
        bindings: Vec<Option<Ty>>,
        params: &[String],
        display: &str,
        span: Span,
    ) -> Option<Vec<Ty>> {
        if let Some(unbound) = bindings
            .iter()
            .position(|binding| binding.is_none())
            .map(|index| params[index].clone())
        {
            let example: Vec<&str> = params.iter().map(|_| "I64").collect();
            self.push(
                Diagnostic::new(
                    span,
                    format!(
                        "cannot tell what type `{unbound}` is in this construction of `{display}`"
                    ),
                )
                .label("no argument or expectation pins it down")
                .note(format!(
                    "annotate the binding, as in `let x: {display}<{}> = …`",
                    example.join(", ")
                )),
            );
            return None;
        }
        Some(bindings.into_iter().flatten().collect())
    }
}
