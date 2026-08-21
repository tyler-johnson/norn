//! The type registry: every concrete type the program's executable code touches, interned in one
//! fixed walk, plus the Rust spellings the typed backend emits against.
//!
//! Determinism is load-bearing. The registry is rebuilt from the NIR on every generation, and the
//! synthetic enum ids and the declaration order must come out identical every time — so interning
//! is a `Vec` scan (no hashing anywhere), and the walk order is fixed: non-inert functions in id
//! order over locals then return, reactors over params/nodes/inputs, struct then enum fields in
//! id order, then the result type of every task builtin the program uses.
//!
//! The representation rule (BOOTSTRAP §8 item 6a): generated structs and enums are flat Rust
//! types; a field whose type is a named aggregate or an Option/Result instantiation is stored
//! behind `Rc`, and everything else — scalars, handles, the already-`Rc` `Str`/`Bytes`/`Task` —
//! is inline. Copying a value is a memcpy plus refcount bumps, never a deep copy; recursive types
//! (`List`) are legal automatically.

use std::fmt::Write;

use norn_hir::hir::{EnumId, Resource, Ty};
use norn_nir::nir::{
    EnumLayout, Function, Instr, Place, Program, Rvalue, StructLayout, VariantLayout, print_ty,
};

pub struct Registry<'p> {
    program: &'p Program,
    /// One entry per distinct render key, in first-appearance order of the fixed walk. The key
    /// doubles as the renderer-name suffix; the type is any exemplar spelling it (every type
    /// sharing a key shares a representation and a renderer).
    keys: Vec<(String, Ty)>,
    /// Option/Result instantiations in first-appearance order. Entry `k` is the synthetic enum
    /// table id `program.enums.len() + k` — appended after the real enums so one emission path
    /// serves every enum.
    synthetics: Vec<Ty>,
}

impl<'p> Registry<'p> {
    pub fn build(program: &'p Program) -> Registry<'p> {
        let mut registry = Registry {
            program,
            keys: Vec::new(),
            synthetics: Vec::new(),
        };
        for function in program.fns.iter().filter(|f| !f.inert) {
            for ty in &function.tys {
                registry.walk(ty);
            }
            registry.walk(&function.ret);
        }
        for reactor in &program.reactors {
            for ty in &reactor.params {
                registry.walk(ty);
            }
            for node in &reactor.nodes {
                registry.walk(&node.ty);
            }
            for input in &reactor.inputs {
                registry.walk(&input.ty);
            }
        }
        for strukt in &program.structs {
            if !struct_inert(strukt) {
                for field in &strukt.fields {
                    registry.walk(&field.ty);
                }
            }
        }
        for def in &program.enums {
            if !enum_inert(def) {
                for variant in &def.variants {
                    for field in &variant.fields {
                        registry.walk(&field.ty);
                    }
                }
            }
        }
        // The result type of every task builtin the program builds: `poll_task` constructs these
        // instantiations whether or not any local names one.
        for function in program.fns.iter().filter(|f| !f.inert) {
            for block in &function.blocks {
                for instr in &block.instrs {
                    if let Instr::Assign(_, Rvalue::BuiltinTask(builtin, _)) = instr {
                        registry.walk(&builtin.signature().1);
                    }
                }
            }
        }
        registry
    }

    /// Intern `ty` and everything reachable through its structure. Named aggregates are leaves —
    /// the table walk covers their fields, and recursing into them would not terminate on `List`.
    fn walk(&mut self, ty: &Ty) {
        match ty {
            Ty::Unit
            | Ty::I64
            | Ty::F64
            | Ty::Bool
            | Ty::Str
            | Ty::Bytes
            | Ty::Struct(_)
            | Ty::Enum(_)
            | Ty::Resource(_)
            | Ty::Reactor(_) => self.intern(ty),
            Ty::Option(inner) => {
                self.intern_synthetic(ty);
                self.intern(ty);
                self.walk(inner);
            }
            Ty::Result(ok, err) => {
                self.intern_synthetic(ty);
                self.intern(ty);
                self.walk(ok);
                self.walk(err);
            }
            Ty::Task(inner) => {
                self.intern(ty);
                self.walk(inner);
            }
            // A named intern like Task, not a synthetic enum: `Shared<T>` is a pointer, not a
            // variant shape.
            Ty::Shared(inner) => {
                self.intern(ty);
                self.walk(inner);
            }
            // `Slots<T>` likewise: a pointer to its storage, interned by name.
            Ty::Slots(inner) => {
                self.intern(ty);
                self.walk(inner);
            }
            Ty::Input(inner) | Ty::Signal(inner) => {
                self.intern(ty);
                self.walk(inner);
            }
            // No value of these ever exists in executable code: `Never` slots are never written
            // or read, and `Param`/`Error`/`Event` cannot reach a checked, non-inert body.
            Ty::Never | Ty::Param { .. } | Ty::Error | Ty::Event(_) => {}
        }
    }

    fn intern(&mut self, ty: &Ty) {
        let key = self.key(ty);
        if !self.keys.iter().any(|(existing, _)| *existing == key) {
            self.keys.push((key, ty.clone()));
        }
    }

    fn intern_synthetic(&mut self, ty: &Ty) {
        if !self.synthetics.contains(ty) {
            self.synthetics.push(ty.clone());
        }
    }

    /// The synthetic enum table id of an Option/Result instantiation.
    pub fn synthetic_id(&self, ty: &Ty) -> usize {
        let index = self
            .synthetics
            .iter()
            .position(|existing| existing == ty)
            .unwrap_or_else(|| panic!("uninterned instantiation {ty:?}"));
        self.program.enums.len() + index
    }

    /// The renderer-name suffix, shared by every type with the same representation and rendering.
    pub fn key(&self, ty: &Ty) -> String {
        match ty {
            Ty::Unit => "unit".into(),
            Ty::I64 => "i64".into(),
            Ty::F64 => "f64".into(),
            Ty::Bool => "bool".into(),
            Ty::Str => "str".into(),
            Ty::Bytes => "bytes".into(),
            Ty::Struct(id) => format!("s{}", id.index()),
            Ty::Enum(id) => format!("e{}", id.index()),
            Ty::Option(_) | Ty::Result(..) => format!("e{}", self.synthetic_id(ty)),
            Ty::Task(_) => "task".into(),
            // Payload-distinguishing, unlike `task`: the renderer delegates to the payload's, so
            // every instantiation needs its own key. Composes for nesting (`shared_shared_i64`).
            Ty::Shared(inner) => format!("shared_{}", self.key(inner)),
            Ty::Slots(inner) => format!("slots_{}", self.key(inner)),
            Ty::Resource(Resource::Listener) => "res_listener".into(),
            Ty::Resource(Resource::Connection) => "res_connection".into(),
            Ty::Resource(Resource::File) => "res_file".into(),
            Ty::Resource(Resource::Flow) => "res_flow".into(),
            Ty::Reactor(_) => "reactor".into(),
            Ty::Input(_) => "input".into(),
            Ty::Signal(_) => "signal".into(),
            other => panic!("no representation for {other:?}"),
        }
    }

    /// The Rust type of a value in value position — a local, a parameter, a return.
    pub fn repr(&self, ty: &Ty) -> String {
        match ty {
            Ty::Unit => "()".into(),
            Ty::I64 => "i64".into(),
            Ty::F64 => "f64".into(),
            Ty::Bool => "bool".into(),
            Ty::Str => "Rc<str>".into(),
            // The prelude's byte view — buffer, offset, length — so `bytes_slice` is O(1).
            Ty::Bytes => "Bytes".into(),
            Ty::Struct(id) => format!("S{}", id.index()),
            Ty::Enum(id) => format!("E{}", id.index()),
            Ty::Option(_) | Ty::Result(..) => format!("E{}", self.synthetic_id(ty)),
            Ty::Task(_) => "Rc<TaskVal>".into(),
            // Already a pointer, so `boxed()` excludes it: a `Shared` field stores this same
            // `Rc` inline rather than double-boxing.
            Ty::Shared(inner) => format!("Rc<{}>", self.repr(inner)),
            // Already a pointer too — the `Rc` is what makes copying a slab a refcount bump and
            // what the ops' `Rc::make_mut` uniqueness check reads. The element is field-shaped so
            // an aggregate element sits behind one `Rc` of its own.
            Ty::Slots(inner) => format!("Rc<Vec<Option<{}>>>", self.field_repr(inner)),
            // The kind is part of the static type, so the value is the id alone.
            Ty::Resource(_) => "ResourceId".into(),
            Ty::Reactor(_) => "ReactorId".into(),
            Ty::Input(_) | Ty::Signal(_) => "(ReactorId, usize)".into(),
            // A diverging expression's slot: it exists so every temp has one, and no path ever
            // writes or reads it.
            Ty::Never => "()".into(),
            other => panic!("no representation for {other:?}"),
        }
    }

    /// The Rust type of a field in an aggregate — the `Rc` rule's storage position.
    pub fn field_repr(&self, ty: &Ty) -> String {
        if self.boxed(ty) {
            format!("Rc<{}>", self.repr(ty))
        } else {
            self.repr(ty)
        }
    }

    /// Whether the `Rc` rule stores this type behind a pointer in field position.
    pub fn boxed(&self, ty: &Ty) -> bool {
        matches!(
            ty,
            Ty::Struct(_) | Ty::Enum(_) | Ty::Option(_) | Ty::Result(..)
        )
    }

    /// A value-position expression converted to what field position stores.
    pub fn store(&self, ty: &Ty, expr: &str) -> String {
        if self.boxed(ty) {
            format!("Rc::new({expr})")
        } else {
            expr.to_string()
        }
    }

    /// The field types of one variant of an enum type — a table lookup for a declared enum,
    /// structural for an Option/Result instantiation.
    pub fn variant_field_tys(&self, ty: &Ty, variant: usize) -> Vec<Ty> {
        match ty {
            Ty::Enum(id) => self.program.enums[id.index()].variants[variant]
                .fields
                .iter()
                .map(|field| field.ty.clone())
                .collect(),
            Ty::Option(_) | Ty::Result(..) => synthetic_variants(ty)[variant]
                .fields
                .iter()
                .map(|field| field.ty.clone())
                .collect(),
            other => panic!("no variants on {other:?}"),
        }
    }

    pub fn variant_count(&self, ty: &Ty) -> usize {
        match ty {
            Ty::Enum(id) => self.program.enums[id.index()].variants.len(),
            Ty::Option(_) | Ty::Result(..) => 2,
            other => panic!("no variants on {other:?}"),
        }
    }

    /// The type of a projected place in `function`, walking downcasts.
    pub fn ty_of_place(&self, function: &Function, place: &Place) -> Ty {
        self.program.ty_of_place(function, place)
    }

    // ------------------------------------------------------------ declarations

    /// The type section of the generated program: `S{id}`/`E{id}` declarations for every concrete
    /// aggregate, synthetic enums for the Option/Result instantiations, and one `render_*` /
    /// `render_top_*` pair per interned type — a 1:1 transcription of the interpreter's
    /// `render_nested`, resolved per type at generation time.
    pub fn decls(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "// ---------------------------------------------------------------- typed declarations"
        );
        let _ = writeln!(out);
        for (id, strukt) in self.program.structs.iter().enumerate() {
            if struct_inert(strukt) {
                let _ = writeln!(
                    out,
                    "// struct {} #{id} — generic template or symbolic instance, never constructed",
                    strukt.name
                );
                let _ = writeln!(out);
                continue;
            }
            let _ = writeln!(out, "// struct {}", strukt.name);
            let _ = writeln!(out, "#[derive(Clone)]");
            let _ = writeln!(out, "struct S{id} {{");
            for (index, field) in strukt.fields.iter().enumerate() {
                let _ = writeln!(
                    out,
                    "    f{index}: {}, // {}: {}",
                    self.field_repr(&field.ty),
                    field.name,
                    print_ty(self.program, &field.ty)
                );
            }
            let _ = writeln!(out, "}}");
            let _ = writeln!(out);
        }
        for (id, def) in self.program.enums.iter().enumerate() {
            if enum_inert(def) {
                let _ = writeln!(
                    out,
                    "// enum {} #{id} — generic template or symbolic instance, never constructed",
                    def.name
                );
                let _ = writeln!(out);
                continue;
            }
            let _ = writeln!(out, "// enum {}", def.name);
            self.enum_decl(&mut out, id, &def.variants);
        }
        for (index, ty) in self.synthetics.iter().enumerate() {
            let id = self.program.enums.len() + index;
            let _ = writeln!(out, "// {}", print_ty(self.program, ty));
            self.enum_decl(&mut out, id, &synthetic_variants(ty));
        }

        self.boundary(&mut out);

        for (key, ty) in &self.keys {
            self.renderer(&mut out, key, ty);
        }
        out
    }

    /// Every concrete aggregate id in table-then-synthetic order, as `("S3", "S3")`-style
    /// (variant name, payload type) pairs for the boundary enum.
    fn aggregate_names(&self) -> Vec<String> {
        let mut names = Vec::new();
        for (id, strukt) in self.program.structs.iter().enumerate() {
            if !struct_inert(strukt) {
                names.push(format!("S{id}"));
            }
        }
        for (id, def) in self.program.enums.iter().enumerate() {
            if !enum_inert(def) {
                names.push(format!("E{id}"));
            }
        }
        for index in 0..self.synthetics.len() {
            names.push(format!("E{}", self.program.enums.len() + index));
        }
        names
    }

    /// The boundary enum and its wrap/unwrap pairs. `Value` is what crosses the nine runtime
    /// boundaries (`Engine::make`, `Step::Done`, spawn/send/latest, the graph methods); it never
    /// appears inside the call graph, where everything is typed. One variant per concrete
    /// aggregate unconditionally — deriving the set from actual crossings could silently
    /// under-approximate — plus the fixed scalar and handle variants.
    fn boundary(&self, out: &mut String) {
        let _ = writeln!(out, "#[derive(Clone)]");
        let _ = writeln!(out, "enum Value {{");
        let _ = writeln!(out, "    Unit,");
        let _ = writeln!(out, "    Int(i64),");
        let _ = writeln!(out, "    Float(f64),");
        let _ = writeln!(out, "    Bool(bool),");
        let _ = writeln!(out, "    Str(Rc<str>),");
        let _ = writeln!(out, "    Bytes(Bytes),");
        let _ = writeln!(out, "    Task(Rc<TaskVal>),");
        let _ = writeln!(out, "    Resource(ResourceKind, ResourceId),");
        let _ = writeln!(out, "    Reactor(ReactorId),");
        let _ = writeln!(out, "    Input(ReactorId, usize),");
        let _ = writeln!(out, "    Signal(ReactorId, usize),");
        for name in self.aggregate_names() {
            let _ = writeln!(out, "    {name}({name}),");
        }
        // One variant per interned `Shared` instantiation — a shared value crosses the same
        // seams any value does (`send(input, shared(cfg))`), and the payload type differs per
        // instantiation. `keys` is push-ordered by the deterministic walk.
        for (key, ty) in &self.keys {
            if matches!(ty, Ty::Shared(_)) {
                let _ = writeln!(out, "    {}({}),", camel(key), self.repr(ty));
            }
        }
        let _ = writeln!(out, "}}");
        let _ = writeln!(out);

        let mut pair = |key: &str, repr: &str, wrap: &str, unwrap_pat: &str, unwrap_val: &str| {
            let _ = writeln!(out, "fn wrap_{key}(v: {repr}) -> Value {{");
            let _ = writeln!(out, "    {wrap}");
            let _ = writeln!(out, "}}");
            let _ = writeln!(out);
            let _ = writeln!(out, "fn unwrap_{key}(v: Value) -> {repr} {{");
            let _ = writeln!(out, "    match v {{");
            let _ = writeln!(out, "        {unwrap_pat} => {unwrap_val},");
            let _ = writeln!(
                out,
                "        _ => panic!(\"a {key} crossed the boundary as something else\"),"
            );
            let _ = writeln!(out, "    }}");
            let _ = writeln!(out, "}}");
            let _ = writeln!(out);
        };
        pair("unit", "()", "Value::Unit", "Value::Unit", "()");
        pair("i64", "i64", "Value::Int(v)", "Value::Int(v)", "v");
        pair("f64", "f64", "Value::Float(v)", "Value::Float(v)", "v");
        pair("bool", "bool", "Value::Bool(v)", "Value::Bool(v)", "v");
        pair("str", "Rc<str>", "Value::Str(v)", "Value::Str(v)", "v");
        pair("bytes", "Bytes", "Value::Bytes(v)", "Value::Bytes(v)", "v");
        pair(
            "task",
            "Rc<TaskVal>",
            "Value::Task(v)",
            "Value::Task(v)",
            "v",
        );
        for (key, kind) in [
            ("res_listener", "Listener"),
            ("res_connection", "Connection"),
            ("res_file", "File"),
            ("res_flow", "Flow"),
        ] {
            pair(
                key,
                "ResourceId",
                &format!("Value::Resource(ResourceKind::{kind}, v)"),
                // The kind is part of the static type, so unwrapping goes by the id alone.
                "Value::Resource(_, v)",
                "v",
            );
        }
        pair(
            "reactor",
            "ReactorId",
            "Value::Reactor(v)",
            "Value::Reactor(v)",
            "v",
        );
        pair(
            "input",
            "(ReactorId, usize)",
            "Value::Input(v.0, v.1)",
            "Value::Input(a, b)",
            "(a, b)",
        );
        pair(
            "signal",
            "(ReactorId, usize)",
            "Value::Signal(v.0, v.1)",
            "Value::Signal(a, b)",
            "(a, b)",
        );
        for name in self.aggregate_names() {
            let key = name.to_lowercase();
            pair(
                &key,
                &name,
                &format!("Value::{name}(v)"),
                &format!("Value::{name}(v)"),
                "v",
            );
        }
        for (key, ty) in &self.keys {
            if matches!(ty, Ty::Shared(_)) {
                let name = camel(key);
                pair(
                    key,
                    &self.repr(ty),
                    &format!("Value::{name}(v)"),
                    &format!("Value::{name}(v)"),
                    "v",
                );
            }
        }
    }

    fn enum_decl(&self, out: &mut String, id: usize, variants: &[VariantLayout]) {
        let _ = writeln!(out, "#[derive(Clone)]");
        let _ = writeln!(out, "enum E{id} {{");
        for (tag, variant) in variants.iter().enumerate() {
            if variant.fields.is_empty() {
                let _ = writeln!(out, "    V{tag}, // {}", variant.name);
                continue;
            }
            let fields: Vec<String> = variant
                .fields
                .iter()
                .map(|field| self.field_repr(&field.ty))
                .collect();
            let _ = writeln!(
                out,
                "    V{tag}({}), // {}",
                fields.join(", "),
                variant.name
            );
        }
        let _ = writeln!(out, "}}");
        let _ = writeln!(out);
    }

    // ------------------------------------------------------------ renderers

    /// One `render_{key}` and its `render_top_{key}` twin. Every renderer takes a reference to
    /// the value-position representation; at a call on an `Rc`-stored field, deref coercion
    /// bridges the difference.
    fn renderer(&self, out: &mut String, key: &str, ty: &Ty) {
        let repr = self.repr(ty);
        // Only a top-level string renders as its own raw text; everything else renders nested.
        // A `Shared` is transparent at both depths by delegation to the payload's renderer —
        // which is what carries the raw-text rule through `print(shared("hi"))`.
        if matches!(ty, Ty::Str) {
            let _ = writeln!(out, "fn render_top_str(v: &Rc<str>) -> String {{");
            let _ = writeln!(out, "    v.to_string()");
            let _ = writeln!(out, "}}");
        } else if let Ty::Shared(inner) = ty {
            let _ = writeln!(out, "fn render_top_{key}(v: &{repr}) -> String {{");
            let _ = writeln!(out, "    render_top_{}(&**v)", self.key(inner));
            let _ = writeln!(out, "}}");
        } else {
            let _ = writeln!(out, "fn render_top_{key}(v: &{repr}) -> String {{");
            let _ = writeln!(out, "    render_{key}(v)");
            let _ = writeln!(out, "}}");
        }
        let _ = writeln!(out);
        let _ = writeln!(out, "fn render_{key}(v: &{repr}) -> String {{");
        match ty {
            Ty::Unit | Ty::Never => {
                let _ = writeln!(out, "    \"()\".to_string()");
            }
            Ty::I64 | Ty::Bool => {
                let _ = writeln!(out, "    v.to_string()");
            }
            Ty::F64 => {
                let _ = writeln!(out, "    render_float(*v)");
            }
            Ty::Str => {
                let _ = writeln!(out, "    format!(\"{{:?}}\", &**v)");
            }
            Ty::Bytes => {
                let _ = writeln!(out, "    format!(\"<bytes {{}}>\", v.len())");
            }
            Ty::Task(_) => {
                let _ = writeln!(out, "    format!(\"<task {{}}>\", task_name(v))");
            }
            Ty::Resource(resource) => {
                let _ = writeln!(out, "    format!(\"<{} {{v}}>\")", resource.name());
            }
            Ty::Reactor(_) => {
                let _ = writeln!(out, "    format!(\"<reactor {{v}}>\")");
            }
            Ty::Input(_) => {
                let _ = writeln!(out, "    format!(\"<input {{}} of {{}}>\", v.1, v.0)");
            }
            Ty::Signal(_) => {
                let _ = writeln!(out, "    format!(\"<signal {{}} of {{}}>\", v.1, v.0)");
            }
            Ty::Struct(id) => {
                self.struct_renderer(out, &self.program.structs[id.index()]);
            }
            Ty::Enum(id) => {
                let def = &self.program.enums[id.index()];
                let name = format!("{}.", def.name);
                self.variants_renderer(out, &self.repr(ty), &name, &def.variants);
            }
            // Option and Result print unqualified.
            Ty::Option(_) | Ty::Result(..) => {
                self.variants_renderer(out, &self.repr(ty), "", &synthetic_variants(ty));
            }
            Ty::Shared(inner) => {
                let _ = writeln!(out, "    render_{}(&**v)", self.key(inner));
            }
            // The Bytes model: the capacity, not the contents — a slab is storage, and what it
            // holds is the sequence on top of it's business to show.
            Ty::Slots(_) => {
                let _ = writeln!(out, "    format!(\"<slots {{}}>\", v.len())");
            }
            other => panic!("no renderer for {other:?}"),
        }
        let _ = writeln!(out, "}}");
        let _ = writeln!(out);
    }

    fn struct_renderer(&self, out: &mut String, strukt: &StructLayout) {
        if strukt.fields.is_empty() {
            let _ = writeln!(out, "    \"{}()\".to_string()", strukt.name);
            return;
        }
        // Struct fields are always labeled.
        let mut text = format!("{}(", strukt.name);
        let mut args = Vec::new();
        for (index, field) in strukt.fields.iter().enumerate() {
            if index > 0 {
                text.push_str(", ");
            }
            let _ = write!(text, "{}: {{}}", field.name);
            args.push(format!("render_{}(&v.f{index})", self.key(&field.ty)));
        }
        text.push(')');
        let _ = writeln!(out, "    format!({text:?}, {})", args.join(", "));
    }

    /// The match over an enum's variants: a zero-field variant renders bare (no `()`), a named
    /// payload labels its fields, a positional one does not.
    fn variants_renderer(
        &self,
        out: &mut String,
        repr: &str,
        qualifier: &str,
        variants: &[VariantLayout],
    ) {
        let _ = writeln!(out, "    match v {{");
        for (tag, variant) in variants.iter().enumerate() {
            let spelled = format!("{qualifier}{}", variant.name);
            if variant.fields.is_empty() {
                let _ = writeln!(out, "        {repr}::V{tag} => {spelled:?}.to_string(),");
                continue;
            }
            let bindings: Vec<String> = (0..variant.fields.len())
                .map(|index| format!("f{index}"))
                .collect();
            let mut text = format!("{spelled}(");
            let mut args = Vec::new();
            for (index, field) in variant.fields.iter().enumerate() {
                if index > 0 {
                    text.push_str(", ");
                }
                if !variant.positional {
                    let _ = write!(text, "{}: ", field.name);
                }
                text.push_str("{}");
                args.push(format!("render_{}(f{index})", self.key(&field.ty)));
            }
            text.push(')');
            let _ = writeln!(
                out,
                "        {repr}::V{tag}({}) => format!({text:?}, {}),",
                bindings.join(", "),
                args.join(", ")
            );
        }
        let _ = writeln!(out, "    }}");
    }
}

/// Whether a table aggregate is a generic template or symbolic instance rather than a type a
/// value can have. Detected structurally: `Ty::Param` marks a template's own declaration, and
/// `Ty::Error` marks the seeded Option/Result table heads, whose real instantiations are the
/// structural `Ty::Option`/`Ty::Result` spellings.
pub fn struct_inert(strukt: &StructLayout) -> bool {
    strukt.fields.iter().any(|field| unreal(&field.ty))
}

pub fn enum_inert(def: &EnumLayout) -> bool {
    def.variants
        .iter()
        .any(|variant| variant.fields.iter().any(|field| unreal(&field.ty)))
}

/// A boundary variant name from a render key: `shared_s3` → `SharedS3`. Injective because keys
/// are built from a closed alphabet of fixed atoms, and the aggregate convention (`S3` ⇒ key
/// `s3`) inverts through it exactly.
fn camel(key: &str) -> String {
    key.split('_')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

fn unreal(ty: &Ty) -> bool {
    match ty {
        Ty::Param { .. } | Ty::Error => true,
        // Load-bearing recursion: a template field `Shared<T>` is `Shared(Param)`, and without
        // this arm the entry would be walked as real and `key()` would panic on the payload.
        Ty::Option(inner)
        | Ty::Task(inner)
        | Ty::Shared(inner)
        | Ty::Slots(inner)
        | Ty::Input(inner)
        | Ty::Signal(inner)
        | Ty::Event(inner) => unreal(inner),
        Ty::Result(ok, err) => unreal(ok) || unreal(err),
        _ => false,
    }
}

/// The variant layouts of an Option/Result instantiation — the shape the table would hold if the
/// instantiation were a declared enum, so one declaration and rendering path serves both.
fn synthetic_variants(ty: &Ty) -> Vec<VariantLayout> {
    let field = |ty: &Ty| {
        vec![norn_nir::nir::FieldLayout {
            name: "0".into(),
            ty: ty.clone(),
        }]
    };
    match ty {
        Ty::Option(inner) => vec![
            VariantLayout {
                name: "None".into(),
                fields: Vec::new(),
                positional: true,
            },
            VariantLayout {
                name: "Some".into(),
                fields: field(inner),
                positional: true,
            },
        ],
        Ty::Result(ok, err) => vec![
            VariantLayout {
                name: "Ok".into(),
                fields: field(ok),
                positional: true,
            },
            VariantLayout {
                name: "Err".into(),
                fields: field(err),
                positional: true,
            },
        ],
        other => panic!("not an instantiation: {other:?}"),
    }
}

// The tag order of the synthetic variants above mirrors the seeded enums exactly.
const _: () = {
    assert!(EnumId::NONE == 0 && EnumId::SOME == 1);
    assert!(EnumId::OK == 0 && EnumId::ERR == 1);
};
