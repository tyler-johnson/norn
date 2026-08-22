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

/// One instantiation of a generic function. `symbolic` marks arguments that still mention a type
/// parameter: such an instance stands inside another template's body as the pending-instantiation
/// marker, is resolved per-instance during monomorphization, and is never queued or executed
/// itself. `depth` is how many instantiations of remapping deep the request was made — the
/// polymorphic-recursion fuse.
pub(super) struct FnInstance {
    pub(super) template: FnId,
    pub(super) args: Vec<Ty>,
    pub(super) id: FnId,
    module: usize,
    at: Span,
    pub(super) symbolic: bool,
    depth: usize,
}

/// A method call on a bounded type parameter: `value.to_string()` where `value: T` and
/// `T: Display`. The stub is a symbolic function — a real id every call site can hold, never
/// executed itself — and monomorphization resolves it to the impl's function once the receiver
/// is concrete. Neutered with the templates.
pub(super) struct TraitCallStub {
    trait_id: TraitId,
    method: String,
    /// Always mentions a type parameter: a concrete receiver resolves at the call site instead.
    receiver: Ty,
    pub(super) id: FnId,
}

/// The checker-side registry of generic instantiations.
pub(super) struct Generics {
    struct_instances: Vec<StructInstance>,
    enum_instances: Vec<EnumInstance>,
    fn_instances: Vec<FnInstance>,
    trait_calls: Vec<TraitCallStub>,
    /// Instance id → registry index, the reverse direction of the Vecs above. Keyed lookups only.
    struct_meaning: HashMap<StructId, usize>,
    enum_meaning: HashMap<EnumId, usize>,
    fn_meaning: HashMap<FnId, usize>,
    trait_call_meaning: HashMap<FnId, usize>,
    /// Pending fills, drained FIFO by `drain_type_fills` through `fill_cursor`.
    fill_queue: Vec<Fill>,
    fill_cursor: usize,
    /// Concrete fn instances whose bodies still need cloning from their template, drained FIFO
    /// by `monomorphize` through `mono_cursor`.
    mono_worklist: Vec<FnId>,
    mono_cursor: usize,
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
            fn_instances: Vec::new(),
            trait_calls: Vec::new(),
            struct_meaning: HashMap::new(),
            enum_meaning: HashMap::new(),
            fn_meaning: HashMap::new(),
            trait_call_meaning: HashMap::new(),
            fill_queue: Vec::new(),
            fill_cursor: 0,
            mono_worklist: Vec::new(),
            mono_cursor: 0,
            defining_types: false,
            cap_reported: false,
        }
    }
}

/// What one monomorphization carries into the clone of a template body: the instance's concrete
/// arguments, where the instance was first asked for, and how deep the remapping chain is.
struct MonoCx {
    args: Vec<Ty>,
    at: Span,
    depth: usize,
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
        // The instance belongs to its template's module: that is where its fields' spans point,
        // and it is the "receiver's module" the orphan rule means for `impl … for List<I64>`.
        self.struct_owner.push(self.struct_owner[template.index()]);
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
        self.enum_owner.push(self.enum_owner[template.index()]);
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
            Ty::Shared(inner) => Ty::Shared(Box::new(self.subst(inner, args, at, depth))),
            Ty::Slots(inner) => Ty::Slots(Box::new(self.subst(inner, args, at, depth))),
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
        match (param, found) {
            (Ty::Param { index, .. }, _) => {
                let slot = &mut bindings[*index as usize];
                if slot.is_none() {
                    *slot = Some(found.clone());
                }
            }
            (Ty::Option(p), Ty::Option(f)) => self.solve(p, f, bindings),
            (Ty::Result(po, pe), Ty::Result(fo, fe)) => {
                self.solve(po, fo, bindings);
                self.solve(pe, fe, bindings);
            }
            (Ty::Task(p), Ty::Task(f)) => self.solve(p, f, bindings),
            (Ty::Shared(p), Ty::Shared(f)) => self.solve(p, f, bindings),
            // Without this arm the catch-all would silently teach nothing through a slab, and
            // `push<T>(buf: mut Buf<T>, …)` could never infer `T` from a `Buf<I64>`.
            (Ty::Slots(p), Ty::Slots(f)) => self.solve(p, f, bindings),
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
            | Ty::Shared(inner)
            | Ty::Slots(inner)
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
            | Ty::Shared(inner)
            | Ty::Slots(inner)
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
        let checked = self.check_inferred_args(&types, args, &order, &mut bindings, span);
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
        let checked = self.check_inferred_args(&types, args, &order, &mut bindings, span);
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

    /// Check the value arguments of a template construction or call in declaration order. One
    /// whose declared type is already settled is checked bidirectionally; one still mentioning
    /// an unbound parameter is synthesised, solved, and then re-checked against what solving
    /// settled — which is where a disagreement between two arguments reports with concrete
    /// types on both sides.
    fn check_inferred_args(
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

    /// Attach the opaque-parameter teaching note when the offending type is a bare `T` — the one
    /// note every operation a parameter cannot do shares.
    pub(super) fn with_opaque_note(&self, diagnostic: Diagnostic, ty: &Ty) -> Diagnostic {
        if let Ty::Param { name, .. } = ty {
            diagnostic.note(format!(
                "`{name}` is opaque inside `{}`: without a bound it can only be moved, stored, matched by binding, or passed on",
                self.fn_name
            ))
        } else {
            diagnostic
        }
    }

    /// The instantiation gate: asked once a generic function's arguments settle, before the
    /// instance is minted. Bounds live on functions alone (struct and enum parameters may not
    /// declare them), which is why type instantiation has no twin of this. Monomorphization asks
    /// nothing either: a symbolic request inside a template was gated here at the template's own
    /// parameters, and the concrete arguments that later substitute them passed their own gate.
    pub(super) fn check_type_param_bounds(&mut self, template: FnId, args: &[Ty], at: Span) {
        let bounds = self.fn_bounds[template.index()].clone();
        if bounds.iter().all(Vec::is_empty) {
            return;
        }
        let display = self.program.fns[template.index()].name.clone();
        let params = self.program.fns[template.index()].type_params.clone();
        for (index, arg) in args.iter().enumerate() {
            for &bound in bounds.get(index).into_iter().flatten() {
                if self.trait_satisfied(bound, arg) {
                    continue;
                }
                let trait_name = self.traits[bound.index()].name.clone();
                let ty = self.program.ty_name(arg);
                let param = &params[index];
                let diagnostic = Diagnostic::new(
                    at,
                    format!(
                        "`{display}` requires `{param}: {trait_name}`, and `{ty}` is not `{trait_name}`"
                    ),
                )
                .label(format!("`{param}` is `{ty}` here"));
                let diagnostic = if bound == TraitId::EQ {
                    diagnostic.note("`Eq` is compiler-defined: exactly `I64`, `F64`, `Bool`, `String`, and `Bytes` satisfy it until derived equality lands (BOOTSTRAP.md §8 item 9)")
                } else {
                    diagnostic.note(format!(
                        "write `impl {trait_name} for {ty} {{ … }}` in the trait's module or the type's"
                    ))
                };
                self.push(diagnostic);
            }
        }
    }

    /// Whether a type satisfies a bound. A parameter satisfies it by declaring it — propagation
    /// by declaration, never search — `Eq` by membership in the closed scalar set, and anything
    /// else by an impl existing somewhere; receiver-keyed, so no import is consulted.
    fn trait_satisfied(&self, bound: TraitId, ty: &Ty) -> bool {
        match ty {
            Ty::Error => true,
            Ty::Param { index, .. } => self
                .bounds_in_scope
                .get(*index as usize)
                .is_some_and(|declared| declared.contains(&bound)),
            _ if bound == TraitId::EQ => {
                matches!(ty, Ty::I64 | Ty::F64 | Ty::Bool | Ty::Str | Ty::Bytes)
            }
            _ => self
                .impls
                .iter()
                .any(|imp| imp.trait_id == bound && imp.receiver == *ty),
        }
    }

    /// The stub a method call on a bounded `T` compiles to: a symbolic function with the trait
    /// method's signature under `Self := T`, deduplicated on (trait, method, receiver) so every
    /// such call in every template shares one id. Resolved per instance by `mono_callee`.
    pub(super) fn request_trait_call(
        &mut self,
        trait_id: TraitId,
        method: &str,
        receiver: Ty,
        at: Span,
    ) -> FnId {
        if let Some(found) = self.generics.trait_calls.iter().find(|stub| {
            stub.trait_id == trait_id && stub.method == method && stub.receiver == receiver
        }) {
            return found.id;
        }
        let position = self.traits[trait_id.index()]
            .methods
            .iter()
            .position(|m| m.name == method)
            .expect("the caller found the method in this trait");
        let (method_params, method_ret) = {
            let m = &self.traits[trait_id.index()].methods[position];
            (m.params.clone(), m.ret.clone())
        };
        let params: Vec<(String, Ty)> = method_params
            .into_iter()
            .map(|(name, ty)| {
                let ty = self.subst(&ty, std::slice::from_ref(&receiver), at, 0);
                (name, ty)
            })
            .collect();
        let ret = self.subst(&method_ret, std::slice::from_ref(&receiver), at, 0);
        let name = format!(
            "{}.{method} for {}",
            self.traits[trait_id.index()].name,
            self.program.ty_name(&receiver)
        );
        let modes = self.traits[trait_id.index()].methods[position]
            .modes
            .clone();
        // The stub carries the member's `task`, so a call on a bounded `T` types as `Ty::Task`
        // inside the template — where no impl is visible and the trait is the only contract there
        // is. Every impl spells the same word, so the instance agrees by conformance.
        let is_task = self.traits[trait_id.index()].methods[position].is_task;
        let id = FnId(self.program.fns.len() as u32);
        self.fn_owner.push(self.current);
        self.fn_bounds.push(Vec::new());
        self.signatures.push((params.clone(), ret.clone()));
        // The trait's declared modes, pinned like an impl's: a stub is bodiless twice over.
        self.param_modes.push(modes);
        self.mode_pinned.push(vec![true; params.len()]);
        self.declared_uses.push(None);
        self.uses_spans.push(None);
        self.program.fns.push(FnDef {
            name,
            type_params: Vec::new(),
            is_task,
            uses: Vec::new(),
            params: params.len(),
            modes: Vec::new(),
            locals: Vec::new(),
            ret,
            body: Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span: at,
            },
            inert: false,
            span: at,
        });
        let index = self.generics.trait_calls.len();
        self.generics.trait_calls.push(TraitCallStub {
            trait_id,
            method: method.to_string(),
            receiver,
            id,
        });
        self.generics.trait_call_meaning.insert(id, index);
        id
    }

    // ---------------------------------------------------------------- generic functions

    /// What a fn id means generically — `struct_base`'s shape for functions.
    pub(super) fn fn_base(&self, id: FnId) -> Option<(FnId, Vec<Ty>)> {
        if let Some(&at) = self.generics.fn_meaning.get(&id) {
            let instance = &self.generics.fn_instances[at];
            return Some((instance.template, instance.args.clone()));
        }
        let def = &self.program.fns[id.index()];
        if def.type_params.is_empty() {
            None
        } else {
            Some((id, Self::param_identity(&def.type_params)))
        }
    }

    /// Whether a type mentions any type parameter at all, looking through instance arguments.
    pub(super) fn mentions_param(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Param { .. } => true,
            Ty::Option(inner)
            | Ty::Task(inner)
            | Ty::Shared(inner)
            | Ty::Slots(inner)
            | Ty::Input(inner)
            | Ty::Signal(inner)
            | Ty::Event(inner) => self.mentions_param(inner),
            Ty::Result(ok, err) => self.mentions_param(ok) || self.mentions_param(err),
            Ty::Struct(id) => self
                .struct_base(*id)
                .is_some_and(|(_, args)| args.iter().any(|arg| self.mentions_param(arg))),
            Ty::Enum(id) => self
                .enum_base(*id)
                .is_some_and(|(_, args)| args.iter().any(|arg| self.mentions_param(arg))),
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

    /// Instantiate a generic function at `args`: dedup on `(template, args)`, else append a stub
    /// def — program.fns, fn_owner, and signatures pushed in lockstep, the `declare_lifted`
    /// discipline — with the substituted signature. A concrete instance queues for
    /// monomorphization; a symbolic one (arguments still mentioning a parameter) is the
    /// pending-instantiation marker another template's body carries, resolved when *that*
    /// template is monomorphized.
    pub(super) fn request_fn_instance(
        &mut self,
        template: FnId,
        args: Vec<Ty>,
        at: Span,
        depth: usize,
    ) -> FnId {
        if args == Self::param_identity(&self.program.fns[template.index()].type_params) {
            return template;
        }
        if let Some(found) = self
            .generics
            .fn_instances
            .iter()
            .find(|instance| instance.template == template && instance.args == args)
        {
            return found.id;
        }
        // The polymorphic-recursion fuse: a function that calls itself at an ever-growing type
        // requests a fresh instance from inside every instance, and this chain is the one thing
        // the worklist cannot converge on.
        if depth > INSTANCE_DEPTH {
            let display = self.program.fns[template.index()].name.clone();
            self.push(
                Diagnostic::new(
                    at,
                    format!("`{display}` instantiates itself at an ever-deeper type"),
                )
                .label(format!("more than {INSTANCE_DEPTH} instantiations deep"))
                .note("a generic function that calls itself at a bigger type than it was given never stops instantiating; make the recursion reuse the caller's own type parameters"),
            );
            return template;
        }
        if self.generics.fn_instances.len() >= INSTANCE_CEILING {
            if !self.generics.cap_reported {
                self.generics.cap_reported = true;
                self.push(
                    Diagnostic::new(
                        at,
                        format!(
                            "this program needs more than {INSTANCE_CEILING} generic instances"
                        ),
                    )
                    .label("instantiation stopped here")
                    .note("a ceiling this size is only ever reached by an instantiation that never converges"),
                );
            }
            return template;
        }
        let (params, ret) = self.signatures[template.index()].clone();
        let params: Vec<(String, Ty)> = params
            .into_iter()
            .map(|(name, ty)| {
                let ty = self.subst(&ty, &args, at, 0);
                (name, ty)
            })
            .collect();
        let ret = self.subst(&ret, &args, at, 0);
        let name = self.instance_name(&self.program.fns[template.index()].name.clone(), &args);
        let (is_task, span) = {
            let def = &self.program.fns[template.index()];
            (def.is_task, def.span)
        };
        let id = FnId(self.program.fns.len() as u32);
        // Move errors in an instance body carry the template's spans, so they render against the
        // template's file. An instance carries no bounds of its own: they were checked when the
        // arguments settled.
        self.fn_owner.push(self.fn_owner[template.index()]);
        self.fn_bounds.push(Vec::new());
        self.signatures.push((params.clone(), ret.clone()));
        // The template's *written* modes: at every point an instance can be requested, inference
        // has not run, so this row is exactly the written sinks — the rest fills per instance.
        self.param_modes
            .push(self.param_modes[template.index()].clone());
        self.mode_pinned
            .push(self.mode_pinned[template.index()].clone());
        // The template's written clause, spans and all: an instance inherits the assertion the
        // template made, so `infer_uses` checks it once per instance and the span dedupe collapses
        // the report back to the one place it was written.
        self.declared_uses
            .push(self.declared_uses[template.index()].clone());
        self.uses_spans.push(self.uses_spans[template.index()]);
        self.program.fns.push(FnDef {
            name,
            type_params: Vec::new(),
            is_task,
            uses: Vec::new(),
            params: params.len(),
            modes: Vec::new(),
            locals: Vec::new(),
            ret,
            body: Expr {
                kind: ExprKind::Error,
                ty: Ty::Error,
                span,
            },
            inert: false,
            span,
        });
        let symbolic = args.iter().any(|arg| self.mentions_param(arg));
        let index = self.generics.fn_instances.len();
        self.generics.fn_instances.push(FnInstance {
            template,
            args,
            id,
            module: self.current,
            at,
            symbolic,
            depth,
        });
        self.generics.fn_meaning.insert(id, index);
        if !symbolic {
            self.generics.mono_worklist.push(id);
        }
        id
    }

    /// A call to a generic function: settle the type arguments — written explicitly, solved from
    /// the expectation, solved left to right from the arguments — then request the instance and
    /// call it. Task wrapping and the capability check are `call_fn`'s, unchanged.
    pub(super) fn call_generic_fn(
        &mut self,
        template: FnId,
        display: &str,
        explicit: Option<Vec<Ty>>,
        args: &[ast::Arg],
        expected: Option<&Ty>,
        span: Span,
    ) -> Expr {
        let type_params = self.program.fns[template.index()].type_params.clone();
        let is_task = self.program.fns[template.index()].is_task;
        let (params, ret) = self.signatures[template.index()].clone();
        let param_names: Vec<String> = params.iter().map(|(name, _)| name.clone()).collect();
        let Some(order) = self.argument_order(&param_names, args, display, "parameter", span)
        else {
            return self.error_expr(span);
        };

        let mut bindings: Vec<Option<Ty>> = vec![None; type_params.len()];
        match explicit {
            Some(explicit) => {
                if !self.template_arity(display, &type_params, explicit.len(), span) {
                    return self.error_expr(span);
                }
                if explicit.iter().any(Ty::is_error) {
                    return self.error_expr(span);
                }
                bindings = explicit.into_iter().map(Some).collect();
            }
            None => {
                // The expectation solves return-position parameters before any argument is
                // looked at, so `let x: Option<I64> = pick(items)` checks bidirectionally.
                if let Some(expected) = expected {
                    let effective = if is_task {
                        Ty::Task(Box::new(ret.clone()))
                    } else {
                        ret.clone()
                    };
                    self.solve(&effective, expected, &mut bindings);
                }
            }
        }

        let types: Vec<Ty> = params.into_iter().map(|(_, ty)| ty).collect();
        let checked = self.check_inferred_args(&types, args, &order, &mut bindings, span);

        if let Some(unbound) = bindings
            .iter()
            .position(|binding| binding.is_none())
            .map(|index| type_params[index].clone())
        {
            self.push(
                Diagnostic::new(
                    span,
                    format!("cannot tell what type `{unbound}` is in this call of `{display}`"),
                )
                .label("no argument or expectation pins it down")
                .note(format!("say it explicitly, as in `{display}<I64>(…)`")),
            );
            return self.error_expr(span);
        }
        let instance_args: Vec<Ty> = bindings.into_iter().flatten().collect();
        // An `Error` in the settled arguments means a mismatch already reported; minting an
        // instance of it would only cascade.
        if instance_args.iter().any(Ty::is_error) {
            return self.error_expr(span);
        }
        self.check_type_param_bounds(template, &instance_args, span);
        let instance = self.request_fn_instance(template, instance_args, span, 0);
        let ret = self.signatures[instance.index()].1.clone();
        let ty = if is_task {
            self.require_task_context(display, span);
            Ty::Task(Box::new(ret))
        } else {
            ret
        };
        Expr {
            kind: ExprKind::Call {
                callee: instance,
                args: checked,
            },
            ty,
            span,
        }
    }

    /// A written `Struct<…>` in call position — the explicit-argument spelling of a generic
    /// construction. `None` means already diagnosed.
    pub(super) fn explicit_struct_instance(
        &mut self,
        id: StructId,
        args: Vec<Ty>,
        span: Span,
    ) -> Option<StructId> {
        let display = self.program.structs[id.index()].name.clone();
        let params = self.program.structs[id.index()].type_params.clone();
        if params.is_empty() {
            self.no_type_args(&display, span);
            return None;
        }
        if !self.template_arity(&display, &params, args.len(), span) {
            return None;
        }
        if args.iter().any(Ty::is_error) {
            return None;
        }
        self.instantiate_struct(id, args, span, 0)
    }

    /// The enum half of `explicit_struct_instance`.
    pub(super) fn explicit_enum_instance(
        &mut self,
        id: EnumId,
        args: Vec<Ty>,
        span: Span,
    ) -> Option<EnumId> {
        let display = self.program.enums[id.index()].name.clone();
        let params = self.program.enums[id.index()].type_params.clone();
        if params.is_empty() {
            self.no_type_args(&display, span);
            return None;
        }
        if !self.template_arity(&display, &params, args.len(), span) {
            return None;
        }
        if args.iter().any(Ty::is_error) {
            return None;
        }
        self.instantiate_enum(id, args, span, 0)
    }

    // ---------------------------------------------------------------- monomorphization

    /// The pass between `check_fns` and `check_turns`: FIFO-drain the worklist, cloning each
    /// concrete instance's body from its checked template with types substituted and every
    /// generic id remapped. Remapping may enqueue — a generic calling a generic composes here —
    /// and the drain is the fixpoint. Afterwards templates and symbolic instances are neutered:
    /// every executable call site holds a concrete instance id, so they lower as inert dead code.
    pub(super) fn monomorphize(&mut self) {
        while self.generics.mono_cursor < self.generics.mono_worklist.len() {
            let id = self.generics.mono_worklist[self.generics.mono_cursor];
            self.generics.mono_cursor += 1;
            self.mono_instance(id);
        }
        self.neuter_templates();
    }

    fn mono_instance(&mut self, id: FnId) {
        let (template, args, module, at, depth) = {
            let index = self.generics.fn_meaning[&id];
            let instance = &self.generics.fn_instances[index];
            (
                instance.template,
                instance.args.clone(),
                instance.module,
                instance.at,
                instance.depth,
            )
        };
        let outer = std::mem::replace(&mut self.current, module);
        // The template body is moved out for the walk and restored after: `mono_expr` needs
        // `&mut self` for substitution, and the template is read many times over.
        let stub = Expr {
            kind: ExprKind::Error,
            ty: Ty::Error,
            span: at,
        };
        let template_body = std::mem::replace(&mut self.program.fns[template.index()].body, stub);
        let template_locals = std::mem::take(&mut self.program.fns[template.index()].locals);

        let cx = MonoCx { args, at, depth };
        let locals: Vec<LocalDef> = template_locals
            .iter()
            .map(|local| LocalDef {
                name: local.name.clone(),
                ty: self.subst(&local.ty, &cx.args, cx.at, 0),
                mutable: local.mutable,
                role: local.role,
                span: local.span,
            })
            .collect();
        let body = self.mono_expr(&template_body, &cx);

        self.program.fns[template.index()].body = template_body;
        self.program.fns[template.index()].locals = template_locals;
        self.program.fns[id.index()].locals = locals;
        self.program.fns[id.index()].body = body;
        self.current = outer;
    }

    /// Remap a callee through its generic meaning: a symbolic instance carried by a template
    /// body resolves at this instance's arguments, which is how a generic calling a generic
    /// composes. Requests made here run one level deeper — the polymorphic-recursion fuse.
    fn mono_callee(&mut self, callee: FnId, cx: &MonoCx) -> FnId {
        // A trait-call stub resolves through the impls once its receiver is concrete. The gate
        // proved the bound when this instance's arguments settled, so the impl exists; a miss
        // can only follow an already-reported failure, and the neutered stub is inert to keep.
        if let Some(&index) = self.generics.trait_call_meaning.get(&callee) {
            let (trait_id, method, receiver) = {
                let stub = &self.generics.trait_calls[index];
                (stub.trait_id, stub.method.clone(), stub.receiver.clone())
            };
            let receiver = self.subst(&receiver, &cx.args, cx.at, 0);
            return self
                .find_impl_method(trait_id, &method, &receiver)
                .unwrap_or(callee);
        }
        match self.fn_base(callee) {
            None => callee,
            Some((template, base_args)) => {
                let new_args: Vec<Ty> = base_args
                    .iter()
                    .map(|arg| self.subst(arg, &cx.args, cx.at, 0))
                    .collect();
                self.request_fn_instance(template, new_args, cx.at, cx.depth + 1)
            }
        }
    }

    fn mono_struct_id(&mut self, id: StructId, cx: &MonoCx) -> StructId {
        match self.subst(&Ty::Struct(id), &cx.args, cx.at, 0) {
            Ty::Struct(instance) => instance,
            // Poisoned by a cap; the program already carries the diagnostic.
            _ => id,
        }
    }

    fn mono_enum_id(&mut self, id: EnumId, cx: &MonoCx) -> EnumId {
        match self.subst(&Ty::Enum(id), &cx.args, cx.at, 0) {
            Ty::Enum(instance) => instance,
            _ => id,
        }
    }

    /// Deep-clone one checked template expression at the instance's arguments. Exhaustive over
    /// `ExprKind` with no catch-all, so a future variant breaks the build here rather than
    /// silently copying wrong. No `check_expr` runs during this walk — the template was checked
    /// once, and this is a substitution, not a re-check.
    fn mono_expr(&mut self, expr: &Expr, cx: &MonoCx) -> Expr {
        let ty = self.subst(&expr.ty, &cx.args, cx.at, 0);
        let span = expr.span;
        let kind = match &expr.kind {
            ExprKind::Unit => ExprKind::Unit,
            ExprKind::Int(value) => ExprKind::Int(*value),
            ExprKind::Float(value) => ExprKind::Float(*value),
            ExprKind::Str(value) => ExprKind::Str(value.clone()),
            ExprKind::Bool(value) => ExprKind::Bool(*value),
            ExprKind::Local(id) => ExprKind::Local(*id),
            ExprKind::Field { base, index } => ExprKind::Field {
                base: Box::new(self.mono_expr(base, cx)),
                index: *index,
            },
            ExprKind::Unary { op, expr } => ExprKind::Unary {
                op: *op,
                expr: Box::new(self.mono_expr(expr, cx)),
            },
            ExprKind::Binary { op, lhs, rhs } => ExprKind::Binary {
                op: *op,
                lhs: Box::new(self.mono_expr(lhs, cx)),
                rhs: Box::new(self.mono_expr(rhs, cx)),
            },
            ExprKind::ShortCircuit { and, lhs, rhs } => ExprKind::ShortCircuit {
                and: *and,
                lhs: Box::new(self.mono_expr(lhs, cx)),
                rhs: Box::new(self.mono_expr(rhs, cx)),
            },
            ExprKind::Call { callee, args } => ExprKind::Call {
                callee: self.mono_callee(*callee, cx),
                args: args.iter().map(|arg| self.mono_expr(arg, cx)).collect(),
            },
            ExprKind::Builtin { builtin, args } => {
                let args: Vec<Expr> = args.iter().map(|arg| self.mono_expr(arg, cx)).collect();
                // The one re-check in the walk: `shared(x)` at `T = File` is invisible to the
                // template — `Ty::Param` is not affine — and only exists once substituted, so
                // the creation-site refusal has to run again here, at the instantiation site
                // where the user can act.
                if *builtin == Builtin::Shared
                    && let Some(arg) = args.first()
                    && self.program.affine(&arg.ty)
                {
                    self.push(
                        Diagnostic::new(
                            cx.at,
                            format!(
                                "`shared` cannot take {}",
                                self.program.ty_name(&arg.ty)
                            ),
                        )
                        .label("instantiated here with an affine payload")
                        .note("resources and tasks have exactly one owner; share the data, not the handle"),
                    );
                }
                // The same re-check for the slab constructor: `let s: Slots<T> = slots_new(0)` at
                // `T = Connection` is invisible to the template and only exists once substituted,
                // and this is the one expression that could mint a `Slots` of an affine element.
                if *builtin == Builtin::SlotsNew
                    && let Ty::Slots(element) = &ty
                    && self.program.affine(element)
                {
                    self.push(
                        Diagnostic::new(
                            cx.at,
                            format!(
                                "a `Slots` value cannot hold {}",
                                self.program.ty_name(element)
                            ),
                        )
                        .label("instantiated here with an affine element")
                        .note("resources and tasks have exactly one owner; hold the data, not the handle"),
                    );
                }
                ExprKind::Builtin {
                    builtin: *builtin,
                    args,
                }
            }
            ExprKind::Construct { ctor, args } => ExprKind::Construct {
                ctor: match ctor {
                    Ctor::Struct(id) => Ctor::Struct(self.mono_struct_id(*id, cx)),
                    // Tags and field indices are instance-invariant: an instance's variants are
                    // the template's, substituted in place.
                    Ctor::Variant(id, variant) => {
                        Ctor::Variant(self.mono_enum_id(*id, cx), *variant)
                    }
                },
                args: args.iter().map(|arg| self.mono_expr(arg, cx)).collect(),
            },
            ExprKind::Match { scrutinee, arms } => ExprKind::Match {
                scrutinee: Box::new(self.mono_expr(scrutinee, cx)),
                arms: arms
                    .iter()
                    .map(|arm| Arm {
                        pat: self.mono_pat(&arm.pat, cx),
                        guard: arm.guard.as_ref().map(|guard| self.mono_expr(guard, cx)),
                        body: self.mono_expr(&arm.body, cx),
                        span: arm.span,
                    })
                    .collect(),
            },
            ExprKind::If { cond, then, els } => ExprKind::If {
                cond: Box::new(self.mono_expr(cond, cx)),
                then: Box::new(self.mono_expr(then, cx)),
                els: els.as_ref().map(|els| Box::new(self.mono_expr(els, cx))),
            },
            ExprKind::Block { stmts, tail } => ExprKind::Block {
                stmts: stmts.iter().map(|stmt| self.mono_stmt(stmt, cx)).collect(),
                tail: tail.as_ref().map(|tail| Box::new(self.mono_expr(tail, cx))),
            },
            ExprKind::Await { expr } => ExprKind::Await {
                expr: Box::new(self.mono_expr(expr, cx)),
            },
            ExprKind::Scope { body } => ExprKind::Scope {
                body: Box::new(self.mono_expr(body, cx)),
            },
            ExprKind::Spawn { expr } => ExprKind::Spawn {
                expr: Box::new(self.mono_expr(expr, cx)),
            },
            ExprKind::SpawnReactor { reactor, args } => ExprKind::SpawnReactor {
                reactor: *reactor,
                args: args.iter().map(|arg| self.mono_expr(arg, cx)).collect(),
            },
            ExprKind::ReactorInput { reactor, index } => ExprKind::ReactorInput {
                reactor: Box::new(self.mono_expr(reactor, cx)),
                index: *index,
            },
            ExprKind::ReactorExport { reactor, index } => ExprKind::ReactorExport {
                reactor: Box::new(self.mono_expr(reactor, cx)),
                index: *index,
            },
            // Option and Result are never templates, so the enum id copies verbatim.
            ExprKind::Try { expr, enum_id } => ExprKind::Try {
                expr: Box::new(self.mono_expr(expr, cx)),
                enum_id: *enum_id,
            },
            ExprKind::Return { value } => ExprKind::Return {
                value: value
                    .as_ref()
                    .map(|value| Box::new(self.mono_expr(value, cx))),
            },
            ExprKind::While { cond, body } => ExprKind::While {
                cond: Box::new(self.mono_expr(cond, cx)),
                body: Box::new(self.mono_expr(body, cx)),
            },
            ExprKind::Loop { body } => ExprKind::Loop {
                body: Box::new(self.mono_expr(body, cx)),
            },
            ExprKind::Break { value } => ExprKind::Break {
                value: value
                    .as_ref()
                    .map(|value| Box::new(self.mono_expr(value, cx))),
            },
            ExprKind::Continue => ExprKind::Continue,
            ExprKind::Error => ExprKind::Error,
        };
        Expr { kind, ty, span }
    }

    fn mono_stmt(&mut self, stmt: &Stmt, cx: &MonoCx) -> Stmt {
        let kind = match &stmt.kind {
            StmtKind::Let { local, value } => StmtKind::Let {
                local: *local,
                value: self.mono_expr(value, cx),
            },
            StmtKind::Assign { place, value } => StmtKind::Assign {
                place: self.mono_expr(place, cx),
                value: self.mono_expr(value, cx),
            },
            StmtKind::After { task, returns } => StmtKind::After {
                task: self.mono_expr(task, cx),
                returns: *returns,
            },
            StmtKind::Expr(expr) => StmtKind::Expr(self.mono_expr(expr, cx)),
        };
        Stmt {
            kind,
            span: stmt.span,
        }
    }

    fn mono_pat(&mut self, pat: &Pat, cx: &MonoCx) -> Pat {
        let kind = match &pat.kind {
            PatKind::Wild => PatKind::Wild,
            PatKind::Bind(local) => PatKind::Bind(*local),
            PatKind::Int(value) => PatKind::Int(*value),
            PatKind::Str(value) => PatKind::Str(value.clone()),
            PatKind::Bool(value) => PatKind::Bool(*value),
            PatKind::Variant {
                enum_id,
                variant,
                args,
            } => PatKind::Variant {
                enum_id: self.mono_enum_id(*enum_id, cx),
                variant: *variant,
                args: args.iter().map(|arg| self.mono_pat(arg, cx)).collect(),
            },
            PatKind::Struct { strukt, args } => PatKind::Struct {
                strukt: self.mono_struct_id(*strukt, cx),
                args: args.iter().map(|arg| self.mono_pat(arg, cx)).collect(),
            },
            PatKind::Or(alts) => {
                PatKind::Or(alts.iter().map(|alt| self.mono_pat(alt, cx)).collect())
            }
            PatKind::Error => PatKind::Error,
        };
        Pat {
            kind,
            span: pat.span,
        }
    }

    /// After the drain, templates and symbolic instances become inert: a `()` body, locals cut
    /// to the parameters. Nothing executable references them — every call site was remapped —
    /// and neutering before `check_moves` is what makes move checking per-instance: every
    /// executable body has its concrete types by now.
    fn neuter_templates(&mut self) {
        let mut inert: Vec<FnId> = Vec::new();
        for (index, def) in self.program.fns.iter().enumerate() {
            if !def.type_params.is_empty() {
                inert.push(FnId(index as u32));
            }
        }
        for instance in &self.generics.fn_instances {
            if instance.symbolic {
                inert.push(instance.id);
            }
        }
        // Trait-call stubs are symbolic by construction: every executable call site was remapped
        // to an impl's function during the drain.
        for stub in &self.generics.trait_calls {
            inert.push(stub.id);
        }
        for id in inert {
            let def = &mut self.program.fns[id.index()];
            let params = def.params;
            def.locals.truncate(params);
            def.inert = true;
            def.body = Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span: def.span,
            };
        }
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
