//! Traits: declarations, impls, conformance, and method resolution.
//!
//! Traits are a checker-only fact. A trait's methods are ordinary functions appended to
//! `program.fns` — displayed as `fmt.Display.to_string for I64`, entered in no namespace — and
//! every method call is rewritten to a plain call before lowering sees it, so NIR, both engines,
//! and the backend know nothing about any of this.
//!
//! Resolution is receiver-keyed: a method needs no import, because the scan is over every impl
//! in the program in declaration order and the receiver's type is what selects. What keeps that
//! coherent is the one-impl rule — one impl per (trait, receiver) program-wide — and what keeps
//! it honest is the orphan rule: an impl lives in the trait's module or the receiver's, so no
//! third file can change what a pairing means.

use super::*;

/// Index into the checker's trait table.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct TraitId(pub(super) u32);

impl TraitId {
    /// The seeded marker trait: method-less, compiler-defined, satisfied by exactly the scalar
    /// types until derived equality lands with item 9.
    pub(super) const EQ: TraitId = TraitId(0);

    pub(super) fn index(self) -> usize {
        self.0 as usize
    }
}

pub(super) struct TraitDef {
    /// Display name, module-qualified the way functions are: `fmt.Display`.
    pub(super) name: String,
    pub(super) module: usize,
    pub(super) methods: Vec<TraitMethod>,
}

/// One trait member. The receiver is `params[0]`, typed as the reserved `Self` parameter slot.
/// The modes are the trait's to declare — a bodiless contract has nothing to infer from — so
/// every impl inherits them pinned: `sink Self` consumes at every call site, and everything
/// else reads.
pub(super) struct TraitMethod {
    pub(super) name: String,
    pub(super) params: Vec<(String, Ty)>,
    pub(super) modes: Vec<Mode>,
    pub(super) ret: Ty,
}

pub(super) struct ImplDef {
    pub(super) trait_id: TraitId,
    pub(super) receiver: Ty,
    /// One entry per function in the impl block, in written order — `None` where the function
    /// was refused. `check_fns` pairs bodies with these by position, exactly like `fn_of_item`.
    pub(super) methods: Vec<(String, Option<FnId>)>,
    pub(super) module: usize,
    /// Which item in the owning module's AST this impl is.
    pub(super) item: usize,
}

/// The reserved parameter slot `Self` resolves to inside a trait declaration. The index never
/// collides: a trait member has no type parameters of its own, so the slot is the whole scope.
pub(super) fn self_param() -> Ty {
    Ty::Param {
        index: 0,
        name: "Self".into(),
    }
}

/// Equality for signature conformance: `fits` in both directions, so `Ty::Error` from an
/// already-reported failure absorbs rather than erroring twice.
fn same_ty(a: &Ty, b: &Ty) -> bool {
    a.fits(b) && b.fits(a)
}

impl Checker {
    /// Pass: resolve every trait's member signatures, `Self` in scope as the reserved slot.
    /// Runs after `drain_type_fills`, so a member type may mention a generic instance.
    pub(super) fn define_traits(&mut self, module: &ast::Module) {
        for item in &module.items {
            let ast::Item::Trait(decl) = item else {
                continue;
            };
            let Some(&id) = self.ns[self.current].traits.get(&decl.name.name) else {
                continue;
            };
            if !decl.type_params.is_empty() {
                self.push(
                    Diagnostic::new(decl.name.span, "a trait takes no type parameters yet")
                        .label("generic traits are not available")
                        .note("the one type a trait abstracts over is `Self`; traits over more arrive with a later milestone"),
                );
            }
            let mut methods: Vec<TraitMethod> = Vec::new();
            for member in &decl.members {
                if methods.iter().any(|m| m.name == member.name.name) {
                    self.push(
                        Diagnostic::new(
                            member.name.span,
                            format!("`{}` is declared twice", member.name.name),
                        )
                        .label("duplicate member"),
                    );
                    continue;
                }
                if member.is_task {
                    self.push(
                        Diagnostic::new(member.name.span, "a trait member is a plain `fn` for now")
                            .label("`task` on a trait member")
                            .note("task methods and their capability clauses arrive with a later milestone"),
                    );
                    continue;
                }
                if !member.type_params.is_empty() {
                    self.push(
                        Diagnostic::new(
                            member.name.span,
                            format!("`{}` takes no type parameters", member.name.name),
                        )
                        .label("a trait member is not generic")
                        .note("the one type a member abstracts over is `Self`"),
                    );
                    continue;
                }
                self.self_ty = Some(self_param());
                let params: Vec<(String, Ty)> = member
                    .params
                    .iter()
                    .map(|p| (p.name.name.clone(), self.resolve_param_ty(&p.ty)))
                    .collect();
                let (modes, _) = super::item::written_modes(&member.params);
                let ret = member
                    .ret
                    .as_ref()
                    .map_or(Ty::Unit, |ty| self.resolve_ty(ty));
                self.self_ty = None;
                // The receiver mode is the trait's to declare: `Self` reads, `sink Self`
                // consumes. An impl spells the same mode — conformance holds the written
                // signature and modes against the trait's.
                match params.first() {
                    Some((_, first)) if *first == self_param() => {}
                    _ => {
                        self.push(
                            Diagnostic::new(
                                member.span,
                                format!(
                                    "`{}`'s first parameter must be `Self`",
                                    member.name.name
                                ),
                            )
                            .label("no receiver")
                            .note(format!(
                                "the method spelling `value.{}(…)` passes the receiver as the first argument",
                                member.name.name
                            ))
                            .note("a receiver reads by default; a consuming method declares `sink Self`"),
                        );
                        continue;
                    }
                }
                methods.push(TraitMethod {
                    name: member.name.name.clone(),
                    params,
                    modes,
                    ret,
                });
            }
            self.traits[id.index()].methods = methods;
        }
    }

    /// Pass: register every impl — orphan rule, coherence, conformance — and append its
    /// functions to the program tables. Runs after `bind_fn_imports`, so an impl body checked
    /// later may call anything a body can; the functions land after every declared one, which
    /// keeps `program.main` where `declare_fns` put it.
    pub(super) fn declare_impls(&mut self, module: &ast::Module) {
        for (index, item) in module.items.iter().enumerate() {
            let ast::Item::Impl(decl) = item else {
                continue;
            };
            if !decl.type_params.is_empty() {
                self.push(
                    Diagnostic::new(decl.span, "generic impls are not available yet")
                        .label("type parameters on an `impl`")
                        .note("write the impl for each concrete type; `impl<T> … for List<T>` arrives with a later milestone"),
                );
                continue;
            }
            let Some(trait_id) = self.resolve_trait(&decl.trait_path) else {
                continue;
            };
            if trait_id == TraitId::EQ {
                self.push(
                    Diagnostic::new(decl.trait_path.span, "`Eq` cannot be implemented by hand")
                        .label("compiler-defined")
                        .note("exactly `I64`, `F64`, `Bool`, `String`, and `Bytes` are `Eq`; derived equality for your own types arrives with BOOTSTRAP.md §8 item 9"),
                );
                continue;
            }
            let receiver = self.resolve_ty(&decl.receiver);
            if receiver.is_error() {
                continue;
            }
            let receiver_name = self.program.ty_name(&receiver);
            let trait_name = self.traits[trait_id.index()].name.clone();
            let owner = match &receiver {
                Ty::I64 | Ty::F64 | Ty::Bool | Ty::Str | Ty::Bytes => None,
                Ty::Struct(id) => Some(self.struct_owner[id.index()]),
                Ty::Enum(id) => Some(self.enum_owner[id.index()]),
                other => {
                    let name = self.program.ty_name(other);
                    self.push(
                        Diagnostic::new(decl.receiver.span, format!("{name} cannot implement a trait"))
                            .label("not a named type")
                            .note("a trait is implemented for a struct, an enum, or one of `I64`, `F64`, `Bool`, `String`, `Bytes`"),
                    );
                    continue;
                }
            };
            // The orphan rule. Instances carry their template's owner, and the seeded enums
            // carry no module at all, so both land in the builtin arm's rule: only the trait's
            // module may implement for them.
            let trait_module = self.traits[trait_id.index()].module;
            let at_home = self.current == trait_module || owner == Some(self.current);
            if !at_home {
                let mut diagnostic = Diagnostic::new(
                    decl.span,
                    format!(
                        "this impl lives in neither `{trait_name}`'s module nor `{receiver_name}`'s"
                    ),
                )
                .label("an impl travels with its trait or its type");
                diagnostic = if owner.is_none_or(|module| module == usize::MAX) {
                    diagnostic.note(format!(
                        "`{receiver_name}` is built in, so only the module that declares `{trait_name}` may implement it"
                    ))
                } else {
                    diagnostic.note("move it beside the `trait` declaration or beside the type it implements it for")
                };
                self.push(diagnostic);
                continue;
            }
            // Coherence: one impl per (trait, receiver), program-wide. Modules are visited in
            // input order and items in written order, so "the first one wins" is deterministic.
            if let Some(existing) = self
                .impls
                .iter()
                .find(|imp| imp.trait_id == trait_id && same_ty(&imp.receiver, &receiver))
            {
                let file = self.names[existing.module].clone();
                let where_ = if existing.module == self.current {
                    "earlier in this file".to_string()
                } else {
                    format!("in {file}")
                };
                self.push(
                    Diagnostic::new(
                        decl.span,
                        format!("`{trait_name}` is already implemented for `{receiver_name}`"),
                    )
                    .label("second impl")
                    .note(format!(
                        "one impl per trait and type, program-wide; the other is {where_}"
                    )),
                );
                continue;
            }

            let mut methods: Vec<(String, Option<FnId>)> = Vec::new();
            for member in &decl.fns {
                let name = member.name.name.clone();
                if member.is_task {
                    self.push(
                        Diagnostic::new(member.name.span, "a trait member is a plain `fn` for now")
                            .label("`task` on an impl function")
                            .note("task methods and their capability clauses arrive with a later milestone"),
                    );
                    methods.push((name, None));
                    continue;
                }
                if !member.type_params.is_empty() {
                    self.push(
                        Diagnostic::new(
                            member.name.span,
                            format!("`{name}` takes no type parameters"),
                        )
                        .label("an impl function is not generic")
                        .note("its types are fixed by the trait and the receiver"),
                    );
                    methods.push((name, None));
                    continue;
                }
                if methods.iter().any(|(n, _)| *n == name) {
                    self.push(
                        Diagnostic::new(member.name.span, format!("`{name}` is declared twice"))
                            .label("duplicate function"),
                    );
                    methods.push((name, None));
                    continue;
                }
                let Some(position) = self.traits[trait_id.index()]
                    .methods
                    .iter()
                    .position(|m| m.name == name)
                else {
                    self.push(
                        Diagnostic::new(
                            member.name.span,
                            format!("`{trait_name}` has no method `{name}`"),
                        )
                        .label("not in the trait")
                        .note(format!(
                            "an impl provides exactly the trait's methods; `{trait_name}` declares {}",
                            self.method_roster(trait_id)
                        )),
                    );
                    methods.push((name, None));
                    continue;
                };
                // Resolve the written signature with `Self` meaning the receiver, then hold it
                // against the trait's, substituted the same way. Names are the impl's own — the
                // trait fixes the types, and named arguments read off the function that runs.
                self.self_ty = Some(receiver.clone());
                let params: Vec<(String, Ty)> = member
                    .params
                    .iter()
                    .map(|p| (p.name.name.clone(), self.resolve_param_ty(&p.ty)))
                    .collect();
                let (modes, _) = super::item::written_modes(&member.params);
                let ret = member
                    .ret
                    .as_ref()
                    .map_or(Ty::Unit, |ty| self.resolve_ty(ty));
                self.self_ty = None;
                let wanted = &self.traits[trait_id.index()].methods[position];
                let wanted_params: Vec<Ty> = wanted
                    .params
                    .iter()
                    .map(|(_, ty)| ty.clone())
                    .collect::<Vec<_>>()
                    .iter()
                    .map(|ty| self.subst(ty, std::slice::from_ref(&receiver), member.span, 0))
                    .collect();
                let wanted_ret = {
                    let ret = self.traits[trait_id.index()].methods[position].ret.clone();
                    self.subst(&ret, std::slice::from_ref(&receiver), member.span, 0)
                };
                let conforms = params.len() == wanted_params.len()
                    && params
                        .iter()
                        .zip(&wanted_params)
                        .all(|((_, found), wanted)| same_ty(found, wanted))
                    && same_ty(&ret, &wanted_ret);
                if !conforms {
                    let shape: Vec<String> = wanted_params
                        .iter()
                        .map(|ty| self.program.ty_name(ty))
                        .collect();
                    self.push(
                        Diagnostic::new(
                            member.span,
                            format!("the signature of `{name}` does not match `{trait_name}`'s"),
                        )
                        .label("conflicting signature")
                        .note(format!(
                            "for `{receiver_name}`, the trait asks for `fn {name}({}) -> {}`",
                            shape.join(", "),
                            self.program.ty_name(&wanted_ret)
                        )),
                    );
                    methods.push((name, None));
                    continue;
                }
                // Modes conform separately from types: `sink Self` and `Self` name the same
                // type, and what the caller keeps is the half of the contract the mode carries.
                let wanted_modes = self.traits[trait_id.index()].methods[position]
                    .modes
                    .clone();
                if modes != wanted_modes {
                    self.push(
                        Diagnostic::new(
                            member.span,
                            format!(
                                "`{name}` and `{trait_name}`'s declaration disagree about `sink`"
                            ),
                        )
                        .label("conflicting mode")
                        .note("a parameter's mode is the trait's to declare: whether the caller keeps the value is part of the contract, and every impl spells the same one"),
                    );
                    methods.push((name, None));
                    continue;
                }
                let id = FnId(self.program.fns.len() as u32);
                self.fn_owner.push(self.current);
                self.fn_bounds.push(Vec::new());
                self.signatures.push((params.clone(), ret.clone()));
                // Pinned whole: the contract is declared at the trait, so a body that consumes a
                // read parameter is an error `infer_sinks` reports rather than a mode it flips.
                self.param_modes.push(wanted_modes);
                self.mode_pinned.push(vec![true; params.len()]);
                self.program.fns.push(FnDef {
                    name: format!("{trait_name}.{name} for {receiver_name}"),
                    type_params: Vec::new(),
                    is_task: false,
                    uses: Vec::new(),
                    params: params.len(),
                    locals: Vec::new(),
                    ret,
                    body: Expr {
                        kind: ExprKind::Error,
                        ty: Ty::Error,
                        span: member.span,
                    },
                    inert: false,
                    span: member.span,
                });
                methods.push((name, Some(id)));
            }

            // Missing means never written: a member that was written and refused has its own
            // diagnostic, and repeating it as an absence would be noise.
            let missing: Vec<String> = self.traits[trait_id.index()]
                .methods
                .iter()
                .filter(|m| !methods.iter().any(|(n, _)| *n == m.name))
                .map(|m| format!("`{}`", m.name))
                .collect();
            if !missing.is_empty() {
                self.push(
                    Diagnostic::new(
                        decl.span,
                        format!(
                            "`impl {trait_name} for {receiver_name}` does not implement {}",
                            missing.join(", ")
                        ),
                    )
                    .label("incomplete impl")
                    .note("a type implements all of a trait or none of it"),
                );
            }
            self.impls.push(ImplDef {
                trait_id,
                receiver,
                methods,
                module: self.current,
                item: index,
            });
        }
    }

    /// The trait's members, quoted for a diagnostic: "`to_string`" or "`a`, `b`".
    fn method_roster(&self, id: TraitId) -> String {
        let names: Vec<String> = self.traits[id.index()]
            .methods
            .iter()
            .map(|m| format!("`{}`", m.name))
            .collect();
        if names.is_empty() {
            "no methods".to_string()
        } else {
            names.join(", ")
        }
    }

    /// A trait named in an `impl` header (and, once bounds land, in a bound): this file's own
    /// and imported traits by bare name, another module's through a namespace binding.
    pub(super) fn resolve_trait(&mut self, path: &ast::Path) -> Option<TraitId> {
        let head = &path.segments[0];
        if path.segments.len() == 1 {
            if let Some(&id) = self.ns[self.current].traits.get(&head.name) {
                return Some(id);
            }
            let what = match self.ns[self.current].types.get(&head.name) {
                Some(TypeName::Struct(_)) => Some("a struct"),
                Some(TypeName::Enum(_)) => Some("an enum"),
                Some(TypeName::Reactor(_)) => Some("a reactor"),
                Some(TypeName::Builtin(_)) => Some("a built-in type"),
                None => None,
            };
            match what {
                Some(what) => self.push(
                    Diagnostic::new(head.span, format!("`{}` is {what}, not a trait", head.name))
                        .label("a type cannot stand here")
                        .note("a bound (`T: Display`) and an `impl` header both name a trait; a type is what implements one"),
                ),
                None => self.error(head.span, format!("unknown trait `{}`", head.name)),
            }
            return None;
        }
        if path.segments.len() == 2
            && let Some(&target) = self.ns[self.current].namespaces.get(&head.name)
        {
            let member = &path.segments[1];
            let span = head.span.to(member.span);
            let Some(&(kind, exported)) = self.decls[target].get(&member.name) else {
                let file = self.names[target].clone();
                self.push(
                    Diagnostic::new(
                        span,
                        format!("`{}` is not defined in `{}`", member.name, head.name),
                    )
                    .label("unknown name")
                    .note(format!("{file} declares no `{}`", member.name)),
                );
                return None;
            };
            if kind != DeclKind::Trait {
                self.push(
                    Diagnostic::new(
                        span,
                        format!("`{}` is a {}, not a trait", path.text(), kind.describe()),
                    )
                    .label("cannot be implemented"),
                );
                return None;
            }
            if !exported {
                let name = member.name.clone();
                let shown = head.name.clone();
                self.not_exported(&name, &shown, target, span);
                return None;
            }
            return self.ns[target].traits.get(&member.name).copied();
        }
        self.error(path.span, format!("unknown trait `{}`", path.text()));
        None
    }

    // ------------------------------------------------------------- resolution

    /// A method call: `value.to_string()`, whatever expression the value is. One resolver for
    /// both spellings — a dotted path whose head is a local, and a call on a field projection.
    pub(super) fn method_call(
        &mut self,
        receiver: Expr,
        method: &ast::Ident,
        explicit: Option<Vec<Ty>>,
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
        if receiver.ty.is_error() {
            return self.error_expr(span);
        }
        if explicit.is_some() {
            self.push(
                Diagnostic::new(span, format!("`{}` takes no type arguments", method.name))
                    .note("a method's types are fixed by its trait and its receiver"),
            );
            return self.error_expr(span);
        }
        // A reactor handle keeps its own member surface: the answer is the one field access
        // gives, and the teach is which builtin reaches the member.
        if let Ty::Reactor(_) = receiver.ty {
            let member = self.field_access(receiver, method, span);
            match member.ty {
                Ty::Error => return self.error_expr(span),
                Ty::Input(_) => self.push(
                    Diagnostic::new(span, format!("`{}` is an input, not a method", method.name))
                        .label("an input is a mailbox")
                        .note(format!(
                            "put a message in it with `send(handle.{}, …)`",
                            method.name
                        )),
                ),
                _ => self.push(
                    Diagnostic::new(
                        span,
                        format!("`{}` is an exported signal, not a method", method.name),
                    )
                    .label("a signal is read, not called")
                    .note(format!(
                        "read its latest published value with `latest(handle.{})`",
                        method.name
                    )),
                ),
            }
            return self.error_expr(span);
        }
        // A type parameter's methods come from its declared bounds — propagation by declaration,
        // never a search of the impls, because inside the template nothing concrete exists to
        // search. The call becomes a symbolic stub in the fn-instance registry; monomorphization
        // resolves it per instance through `find_impl_method`.
        if let Ty::Param { index, name } = &receiver.ty {
            let bounds = self
                .bounds_in_scope
                .get(*index as usize)
                .cloned()
                .unwrap_or_default();
            if bounds.is_empty() {
                let name = name.clone();
                let diagnostic = Diagnostic::new(span, format!("a bare `{name}` has no methods"))
                    .label(format!("`{}` called on a type parameter", method.name));
                let diagnostic = self.with_opaque_note(diagnostic, &receiver.ty);
                self.push(diagnostic);
                return self.error_expr(span);
            }
            let name = name.clone();
            let candidates: Vec<TraitId> = bounds
                .iter()
                .copied()
                .filter(|id| {
                    self.traits[id.index()]
                        .methods
                        .iter()
                        .any(|m| m.name == method.name)
                })
                .collect();
            return match candidates.as_slice() {
                [] => {
                    let roster: Vec<String> = bounds
                        .iter()
                        .map(|id| format!("`{}`", self.traits[id.index()].name))
                        .collect();
                    self.push(
                        Diagnostic::new(
                            method.span,
                            format!("none of `{name}`'s bounds provides `{}`", method.name),
                        )
                        .label("not in the bounds")
                        .note(format!(
                            "a method on `{name}` must come from a declared bound; here that is {}",
                            roster.join(", ")
                        )),
                    );
                    self.error_expr(span)
                }
                [trait_id] => {
                    let stub =
                        self.request_trait_call(*trait_id, &method.name, receiver.ty.clone(), span);
                    let display = format!("{name}.{}", method.name);
                    self.call_method(stub, &display, receiver, args, span)
                }
                _ => {
                    let mut diagnostic = Diagnostic::new(
                        method.span,
                        format!(
                            "more than one of `{name}`'s bounds provides `{}`",
                            method.name
                        ),
                    )
                    .label("ambiguous method");
                    for trait_id in &candidates {
                        diagnostic = diagnostic.note(format!(
                            "`{}` provides one",
                            self.traits[trait_id.index()].name
                        ));
                    }
                    self.push(diagnostic);
                    self.error_expr(span)
                }
            };
        }

        // The scan: every impl in the program, declaration order, keyed by the receiver's type.
        let candidates: Vec<(TraitId, FnId)> = self
            .impls
            .iter()
            .filter(|imp| same_ty(&imp.receiver, &receiver.ty))
            .filter_map(|imp| {
                imp.methods
                    .iter()
                    .find_map(|(name, id)| (*name == method.name).then_some(*id))
                    .flatten()
                    .map(|id| (imp.trait_id, id))
            })
            .collect();
        let ty_name = self.program.ty_name(&receiver.ty);
        match candidates.as_slice() {
            [] => {
                if let Ty::Struct(id) = &receiver.ty
                    && self.program.structs[id.index()]
                        .field(&method.name)
                        .is_some()
                {
                    self.push(
                        Diagnostic::new(
                            method.span,
                            format!("`{}` is a field of {ty_name}, not a method", method.name),
                        )
                        .label("fields hold values; they cannot be called")
                        .note("an `impl` is what gives a type methods"),
                    );
                    return self.error_expr(span);
                }
                self.push(
                    Diagnostic::new(
                        method.span,
                        format!("{ty_name} has no method `{}`", method.name),
                    )
                    .label("no impl provides it")
                    .note(format!(
                        "a method comes from a trait: an `impl` with a `fn {}` taking {ty_name} is what declares one",
                        method.name
                    )),
                );
                self.error_expr(span)
            }
            [(_, id)] => {
                let id = *id;
                let display = format!("{ty_name}.{}", method.name);
                self.call_method(id, &display, receiver, args, span)
            }
            _ => {
                let mut diagnostic = Diagnostic::new(
                    method.span,
                    format!("{ty_name} has more than one method named `{}`", method.name),
                )
                .label("ambiguous method");
                for (trait_id, _) in &candidates {
                    diagnostic = diagnostic.note(format!(
                        "`{}` provides one",
                        self.traits[trait_id.index()].name
                    ));
                }
                diagnostic = diagnostic
                    .note("methods share one name and functions do not: call the function form the impl delegates to");
                self.push(diagnostic);
                self.error_expr(span)
            }
        }
    }

    /// The impl-provided function behind (trait, method, receiver), if the pairing exists —
    /// what a symbolic trait call resolves to once monomorphization makes its receiver concrete.
    pub(super) fn find_impl_method(
        &self,
        trait_id: TraitId,
        method: &str,
        receiver: &Ty,
    ) -> Option<FnId> {
        self.impls
            .iter()
            .filter(|imp| imp.trait_id == trait_id && imp.receiver == *receiver)
            .find_map(|imp| {
                imp.methods
                    .iter()
                    .find_map(|(name, id)| (name == method).then_some(*id))
                    .flatten()
            })
    }

    /// The rewrite that makes a method a plain call: the receiver becomes the first argument,
    /// and everything after it is checked the way `call_fn` checks arguments. Impl functions are
    /// never generic and never tasks this wave, so neither branch of `call_fn` is needed. The
    /// receiver needs no adaptation: reading is unmarked, and whether the method consumes it is
    /// the mode column's fact, enforced by `check_moves` like any other argument.
    fn call_method(
        &mut self,
        id: FnId,
        display: &str,
        receiver: Expr,
        args: &[ast::Arg],
        span: Span,
    ) -> Expr {
        let (params, ret) = self.signatures[id.index()].clone();
        let names: Vec<String> = params.iter().skip(1).map(|(n, _)| n.clone()).collect();
        let Some(order) = self.argument_order(&names, args, display, "parameter", span) else {
            return self.error_expr(span);
        };
        let mut checked = Vec::with_capacity(params.len());
        checked.push(receiver);
        for (index, (_, ty)) in params.iter().skip(1).enumerate() {
            checked.push(self.check_expr(&args[order[index]].value, Some(ty)));
        }
        Expr {
            kind: ExprKind::Call {
                callee: id,
                args: checked,
            },
            ty: ret,
            span,
        }
    }
}
