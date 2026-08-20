//! NIR → restricted Rust.
//!
//! The backend is a printer, and since the typed flip (BOOTSTRAP §8 item 6a) a typed one: every
//! local, parameter, and return is emitted at its NIR type's representation, and the dynamic
//! `Value` survives only as the boundary enum the runtime traffics in. Blocks become match arms,
//! terminators become state assignments, and everything about scheduling, propagation, and
//! tracing is a call into `norn-rt` — the same calls the interpreter makes, in the same order.
//! The turn traces stay byte-identical by comparison now, not by construction: the differential
//! oracle is the referee.
//!
//! One state-numbering scheme carries the whole suspension story: block `b` of a `task fn` is
//! state `2*b`, and state `2*b + 1` re-executes only its terminator. A park leaves the frame at
//! the odd state, so waking re-asks the suspension point; an awaited callee's return value
//! arrives at the same odd state as `resumed: Some(v)`, written typed and jumped past.
//!
//! Locals are `Option<Repr>`: parameters start `Some`, everything else `None`, reads
//! `.clone().unwrap()` (the checker proves initialization; the panic is unreachable), and
//! projected writes copy-on-write through `Rc::make_mut` exactly as the interpreter does.

use std::collections::HashSet;

use norn_hir::hir;
use norn_hir::hir::{Builtin, Ty};
use norn_nir::nir::{
    Const, FnKind, Function, Instr, NodeKind, Operand, Place, Program, Proj, Rvalue, Term,
};

use crate::types::Registry;

/// Which runtime access the surrounding function has. A `task fn` holds a `&mut Cx`; a plain
/// function holds an `Option` it must ask; a handler holds `None` by construction plus the turn
/// accumulator — purity as the absence of the thing every impure arm needs.
#[derive(Clone, Copy, PartialEq)]
enum Ctx {
    Task,
    Plain,
    Handler,
}

impl Ctx {
    /// The expression producing an `Option<&mut Cx>` for a callee.
    fn cx_opt(self) -> &'static str {
        match self {
            Ctx::Task => "Some(&mut *cx)",
            Ctx::Plain | Ctx::Handler => "cx.as_deref_mut()",
        }
    }

    /// A statement binding `cx` for an impure operation, or trapping without one.
    fn cx_stmt(self, what: &str) -> String {
        match self {
            Ctx::Task => "let cx = &mut *cx;".into(),
            Ctx::Plain | Ctx::Handler => format!(
                "let Some(cx) = cx.as_deref_mut() else {{ return Err(impure_trap({what:?})); }};"
            ),
        }
    }

    fn state(self) -> &'static str {
        match self {
            Ctx::Task => "frame.state",
            Ctx::Plain | Ctx::Handler => "block",
        }
    }

    /// The prefix a local lives behind.
    fn locals(self) -> &'static str {
        match self {
            Ctx::Task => "frame.",
            Ctx::Plain | Ctx::Handler => "",
        }
    }

    /// The state number for a transfer to block `b`.
    fn target(self, b: usize) -> usize {
        match self {
            Ctx::Task => 2 * b,
            Ctx::Plain | Ctx::Handler => b,
        }
    }
}

pub fn generate(program: &Program, main: usize) -> String {
    let mut used_builtins: Vec<Builtin> = Vec::new();
    for function in program.fns.iter().filter(|f| !f.inert) {
        for block in &function.blocks {
            for instr in &block.instrs {
                if let Instr::Assign(_, Rvalue::BuiltinTask(builtin, _)) = instr
                    && !used_builtins.contains(builtin)
                {
                    used_builtins.push(*builtin);
                }
            }
        }
    }
    let task_fns: Vec<usize> = program
        .fns
        .iter()
        .enumerate()
        .filter(|(_, f)| !f.inert && f.kind == FnKind::Task)
        .map(|(id, _)| id)
        .collect();
    let emitter = Emitter {
        program,
        registry: Registry::build(program),
        handlers: program
            .reactors
            .iter()
            .flat_map(|reactor| reactor.inputs.iter().map(|input| input.handler))
            .collect(),
        used_builtins,
        task_fns,
        main,
    };
    let mut out = String::new();
    emitter.generate(&mut out);
    out
}

struct Emitter<'p> {
    program: &'p Program,
    registry: Registry<'p>,
    handlers: HashSet<usize>,
    /// Task builtins the program builds, in first-appearance order — the `TaskVal` variants and
    /// `poll_task` arms.
    used_builtins: Vec<Builtin>,
    /// Non-inert `task fn` ids, in id order — the frame and `TaskVal` fn variants.
    task_fns: Vec<usize>,
    main: usize,
}

fn push(out: &mut String, indent: usize, line: &str) {
    for _ in 0..indent {
        out.push_str("    ");
    }
    out.push_str(line);
    out.push('\n');
}

fn push_all(out: &mut String, indent: usize, lines: &[String]) {
    for line in lines {
        push(out, indent, line);
    }
}

impl Emitter<'_> {
    fn generate(&self, out: &mut String) {
        push(
            out,
            0,
            "// Generated by `norn build`. Do not edit: the source of truth is the .norn file.",
        );
        push(out, 0, "#![allow(warnings)]");
        push(out, 0, "");
        push(out, 0, "use std::io;");
        push(out, 0, "use std::process::ExitCode;");
        push(out, 0, "use std::rc::Rc;");
        push(out, 0, "");
        push(out, 0, "use norn_rt::graph::{InputSpec, ReactorSpec};");
        push(out, 0, "use norn_rt::{");
        push(
            out,
            0,
            "    Body, Clock, Config, Cx, Effect, Engine, Graph, Handled, NodeSpec, Overflow, Poll,",
        );
        push(
            out,
            0,
            "    ReactorId, ResourceId, ResourceKind, Runtime, Step, Stdout, Trap, Update,",
        );
        push(out, 0, "};");
        push(out, 0, "");
        out.push_str(crate::PRELUDE);
        push(out, 0, "");
        out.push_str(&self.registry.decls());
        push(out, 0, "");
        self.tasks(out);
        self.tables(out);
        for id in 0..self.program.fns.len() {
            self.function(out, id);
        }
        self.dispatchers(out);
        self.graph(out);
        self.specs(out);
        self.entry(out);
    }

    // ------------------------------------------------------------ types by key

    fn key(&self, ty: &Ty) -> String {
        self.registry.key(ty)
    }

    fn repr(&self, ty: &Ty) -> String {
        self.registry.repr(ty)
    }

    fn place_ty(&self, function: &Function, place: &Place) -> Ty {
        self.registry.ty_of_place(function, place)
    }

    fn operand_ty(&self, function: &Function, operand: &Operand) -> Ty {
        match operand {
            Operand::Const(Const::Unit) => Ty::Unit,
            Operand::Const(Const::Int(_)) => Ty::I64,
            Operand::Const(Const::Float(_)) => Ty::F64,
            Operand::Const(Const::Bool(_)) => Ty::Bool,
            Operand::Const(Const::Str(_)) => Ty::Str,
            Operand::Copy(place) => self.place_ty(function, place),
        }
    }

    // ------------------------------------------------------------ tasks

    /// `TaskVal` and its companions: the typed form of "a computation that has not run".
    fn tasks(&self, out: &mut String) {
        push(
            out,
            0,
            "// ---------------------------------------------------------------- tasks",
        );
        push(out, 0, "");
        push(out, 0, "#[derive(Clone)]");
        push(out, 0, "enum TaskVal {");
        for &id in &self.task_fns {
            let function = &self.program.fns[id];
            let fields: Vec<String> = function.tys[..function.params]
                .iter()
                .map(|ty| self.repr(ty))
                .collect();
            let payload = if fields.is_empty() {
                String::new()
            } else {
                format!("({})", fields.join(", "))
            };
            push(
                out,
                1,
                &format!("F{id}{payload}, // task fn {}", function.name),
            );
        }
        if self.main_is_plain() {
            push(out, 1, "Main, // the plain `main`, run as the root task");
        }
        for &builtin in &self.used_builtins {
            let fields = self.builtin_fields(builtin);
            let payload = if fields.is_empty() {
                String::new()
            } else {
                format!("({})", fields.join(", "))
            };
            push(
                out,
                1,
                &format!("B{builtin:?}{payload}, // builtin {}", builtin.name()),
            );
        }
        push(out, 0, "}");
        push(out, 0, "");

        // task_name
        push(out, 0, "fn task_name(task: &TaskVal) -> &'static str {");
        push(out, 1, "match task {");
        for &id in &self.task_fns {
            push(
                out,
                2,
                &format!(
                    "TaskVal::F{id}{} => FN_NAMES[{id}usize],",
                    self.fn_variant_dots(id)
                ),
            );
        }
        if self.main_is_plain() {
            push(out, 2, "TaskVal::Main => FN_NAMES[MAIN_FN],");
        }
        for &builtin in &self.used_builtins {
            push(
                out,
                2,
                &format!(
                    "TaskVal::B{builtin:?}{} => {:?},",
                    self.builtin_variant_dots(builtin),
                    builtin.name()
                ),
            );
        }
        push(out, 1, "}");
        push(out, 0, "}");
        push(out, 0, "");

        // is_fn_task: what `await` hands to the frame stack rather than to `poll_task`.
        push(out, 0, "fn is_fn_task(task: &TaskVal) -> bool {");
        if self.task_fns.is_empty() {
            push(out, 1, "false");
        } else {
            let patterns: Vec<String> = self
                .task_fns
                .iter()
                .map(|&id| format!("TaskVal::F{id}{}", self.fn_variant_dots(id)))
                .collect();
            push(out, 1, &format!("matches!(task, {})", patterns.join(" | ")));
        }
        push(out, 0, "}");
        push(out, 0, "");

        // moved_resources: the handles a spawned task takes with it, in argument order. Only
        // arguments whose static type is a resource are seen — one buried inside an aggregate
        // stays with the parent, deliberately matching the interpreter's shallow scan.
        push(
            out,
            0,
            "fn moved_resources(task: &TaskVal) -> Vec<ResourceId> {",
        );
        push(out, 1, "match task {");
        for &id in &self.task_fns {
            let function = &self.program.fns[id];
            let moved: Vec<usize> = (0..function.params)
                .filter(|&i| matches!(function.tys[i], Ty::Resource(_)))
                .collect();
            if moved.is_empty() {
                continue;
            }
            let bindings: Vec<String> = (0..function.params)
                .map(|i| {
                    if moved.contains(&i) {
                        format!("a{i}")
                    } else {
                        "_".into()
                    }
                })
                .collect();
            let ids: Vec<String> = moved.iter().map(|i| format!("*a{i}")).collect();
            push(
                out,
                2,
                &format!(
                    "TaskVal::F{id}({}) => vec![{}],",
                    bindings.join(", "),
                    ids.join(", ")
                ),
            );
        }
        for &builtin in &self.used_builtins {
            if builtin == Builtin::Send {
                // The message crosses the boundary wrapped, so the scan the interpreter does on
                // values happens here on the one wrapped argument.
                push(
                    out,
                    2,
                    "TaskVal::BSend(_, message) => match message { Value::Resource(_, id) => vec![*id], _ => Vec::new() },",
                );
                continue;
            }
            let params = builtin.signature().0;
            let moved: Vec<usize> = (0..params.len())
                .filter(|&i| matches!(params[i].0, Ty::Resource(_)))
                .collect();
            if moved.is_empty() {
                continue;
            }
            let bindings: Vec<String> = (0..params.len())
                .map(|i| {
                    if moved.contains(&i) {
                        format!("a{i}")
                    } else {
                        "_".into()
                    }
                })
                .collect();
            let ids: Vec<String> = moved.iter().map(|i| format!("*a{i}")).collect();
            push(
                out,
                2,
                &format!(
                    "TaskVal::B{builtin:?}({}) => vec![{}],",
                    bindings.join(", "),
                    ids.join(", ")
                ),
            );
        }
        push(out, 2, "_ => Vec::new(),");
        push(out, 1, "}");
        push(out, 0, "}");
        push(out, 0, "");

        // push_frame: a task fn value becomes a typed frame directly — no boundary detour.
        push(
            out,
            0,
            "fn push_frame(task: &TaskVal, frames: &mut Vec<Frame>) -> Result<(), Trap> {",
        );
        push(out, 1, "match task {");
        for &id in &self.task_fns {
            let function = &self.program.fns[id];
            let bindings: Vec<String> = (0..function.params).map(|i| format!("a{i}")).collect();
            let args: Vec<String> = bindings.iter().map(|b| format!("{b}.clone()")).collect();
            let pattern = if bindings.is_empty() {
                format!("TaskVal::F{id}")
            } else {
                format!("TaskVal::F{id}({})", bindings.join(", "))
            };
            push(
                out,
                2,
                &format!(
                    "{pattern} => frames.push(Frame::F{id}(frame_f{id}({}))),",
                    args.join(", ")
                ),
            );
        }
        push(
            out,
            2,
            "_ => return Err(Trap::new(\"pushed a frame for a task that is not a task fn\", \"runtime\")),",
        );
        push(out, 1, "}");
        push(out, 1, "Ok(())");
        push(out, 0, "}");
        push(out, 0, "");

        self.io_err(out);
        self.poll_task(out);

        // make_body: how the runtime turns a task value into something it can resume.
        push(
            out,
            0,
            "fn make_body(value: &Value) -> Result<Box<dyn Body<Value>>, Trap> {",
        );
        push(out, 1, "let Value::Task(task) = value else {");
        push(
            out,
            2,
            "return Err(Trap::new(\"started something that is not a task\", \"runtime\"));",
        );
        push(out, 1, "};");
        push(out, 1, "Ok(match &**task {");
        if self.main_is_plain() {
            push(
                out,
                2,
                "TaskVal::Main => Box::new(PlainBody { func: MAIN_FN }),",
            );
        }
        if !self.task_fns.is_empty() {
            let patterns: Vec<String> = self
                .task_fns
                .iter()
                .map(|&id| format!("TaskVal::F{id}{}", self.fn_variant_dots(id)))
                .collect();
            push(out, 2, &format!("{} => {{", patterns.join(" | ")));
            push(out, 3, "let mut frames = Vec::new();");
            push(out, 3, "push_frame(task, &mut frames)?;");
            push(out, 3, "Box::new(FnBody { name: task_name(task), frames })");
            push(out, 2, "}");
        }
        push(out, 2, "_ => Box::new(BuiltinBody { task: task.clone() }),");
        push(out, 1, "})");
        push(out, 0, "}");
        push(out, 0, "");

        push(
            out,
            0,
            "fn spawn_task(cx: &mut Cx<'_, '_, Value>, task: Rc<TaskVal>) -> Result<(), Trap> {",
        );
        push(out, 1, "let moved = moved_resources(&task);");
        push(out, 1, "cx.spawn(Value::Task(task), &moved)?;");
        push(out, 1, "Ok(())");
        push(out, 0, "}");
        push(out, 0, "");
    }

    fn main_is_plain(&self) -> bool {
        self.program.fns[self.main].kind == FnKind::Plain
    }

    /// `(..)` when the fn variant has a payload, nothing when it is a unit variant.
    fn fn_variant_dots(&self, id: usize) -> &'static str {
        if self.program.fns[id].params == 0 {
            ""
        } else {
            "(..)"
        }
    }

    fn builtin_variant_dots(&self, builtin: Builtin) -> &'static str {
        if self.builtin_fields(builtin).is_empty() {
            ""
        } else {
            "(..)"
        }
    }

    /// The typed payload of a builtin's `TaskVal` variant. `send`'s signature is untyped in HIR
    /// (`Ty::Error` twice), so it is spelled here: the input handle, and the message wrapped at
    /// construction.
    fn builtin_fields(&self, builtin: Builtin) -> Vec<String> {
        if builtin == Builtin::Send {
            return vec!["(ReactorId, usize)".into(), "Value".into()];
        }
        builtin
            .signature()
            .0
            .iter()
            .map(|(ty, _)| self.repr(ty))
            .collect()
    }

    /// The io mapping, at its single home: a host error becomes the built-in `IoError`. The
    /// unknown case carries the host's own name for the condition rather than its message, which
    /// varies by platform.
    fn io_err(&self, out: &mut String) {
        push(out, 0, "fn io_err(err: &io::Error) -> E2 {");
        push(out, 1, "use io::ErrorKind as K;");
        push(out, 1, "match err.kind() {");
        push(out, 2, "K::NotFound => E2::V0,");
        push(out, 2, "K::PermissionDenied => E2::V1,");
        push(out, 2, "K::AddrInUse | K::AddrNotAvailable => E2::V2,");
        push(out, 2, "K::ConnectionRefused => E2::V3,");
        push(
            out,
            2,
            "K::ConnectionReset | K::ConnectionAborted | K::NotConnected | K::BrokenPipe | K::WriteZero | K::UnexpectedEof => E2::V4,",
        );
        push(
            out,
            2,
            "other => E2::V5(Rc::from(format!(\"{other:?}\").as_str())),",
        );
        push(out, 1, "}");
        push(out, 0, "}");
        push(out, 0, "");
    }

    /// One arm per used task builtin: ask the runtime, and construct the typed result — the
    /// `Result<T, IoError>` instantiations here are exactly what the awaiting unwrap expects.
    fn poll_task(&self, out: &mut String) {
        push(
            out,
            0,
            "fn poll_task(cx: &mut Cx<'_, '_, Value>, task: &TaskVal) -> Result<Poll<Value>, Trap> {",
        );
        push(out, 1, "Ok(match task {");
        for &builtin in &self.used_builtins {
            for line in self.poll_arm(builtin) {
                push(out, 2, &line);
            }
        }
        push(
            out,
            2,
            "_ => return Err(Trap::new(\"polled a task that is not a builtin\", \"runtime\")),",
        );
        push(out, 1, "})");
        push(out, 0, "}");
        push(out, 0, "");
    }

    /// The typed construction of one fallible outcome: `Ok(binding)` converted into the ok
    /// variant's storage, an io error mapped and boxed into the err variant.
    fn fallible_expr(&self, builtin: Builtin, ok_binding: &str, ok_expr: &str) -> String {
        let Ty::Task(inner) = builtin.signature().1 else {
            panic!("`{}` does not build a task", builtin.name());
        };
        let sid = self.registry.synthetic_id(&inner);
        let ok_ty = &self.registry.variant_field_tys(&inner, 0)[0];
        let stored = self.registry.store(ok_ty, ok_expr);
        format!(
            "wrap_e{sid}(match outcome {{ Ok({ok_binding}) => E{sid}::V0({stored}), Err(err) => E{sid}::V1(Rc::new(io_err(&err))) }})"
        )
    }

    fn poll_arm(&self, builtin: Builtin) -> Vec<String> {
        let ready_fallible = |call: &str, binding: &str, expr: &str| {
            vec![format!(
                "TaskVal::B{builtin:?}(a0) => {{ let outcome = {call}; Poll::Ready({}) }}",
                self.fallible_expr(builtin, binding, expr)
            )]
        };
        let pending_fallible = |call: &str, binding: &str, expr: &str| {
            vec![
                format!(
                    "TaskVal::B{builtin:?}{} => match {call} {{",
                    self.builtin_bindings(builtin)
                ),
                format!(
                    "    Poll::Ready(outcome) => Poll::Ready({}),",
                    self.fallible_expr(builtin, binding, expr)
                ),
                "    Poll::Pending => Poll::Pending,".into(),
                "},".into(),
            ]
        };
        match builtin {
            Builtin::Sleep => vec![
                format!("TaskVal::BSleep(a0) => match cx.sleep(*a0) {{"),
                "    Poll::Ready(()) => Poll::Ready(Value::Unit),".into(),
                "    Poll::Pending => Poll::Pending,".into(),
                "},".into(),
            ],
            // Binding does not block, so this answers at once either way.
            Builtin::TcpListen => ready_fallible("cx.listen(*a0)", "id", "id"),
            Builtin::TcpAccept => pending_fallible("cx.accept(*a0)", "id", "id"),
            Builtin::TcpRead => pending_fallible("cx.read(*a0)", "data", "Bytes::from_vec(data)"),
            Builtin::TcpWrite => pending_fallible("cx.write(*a0, a1.as_slice())", "()", "()"),
            Builtin::TcpClose | Builtin::FileClose | Builtin::FlowClose => vec![format!(
                "TaskVal::B{builtin:?}(a0) => {{ cx.close(*a0); Poll::Ready(Value::Unit) }}"
            )],
            // Creating and opening do not block, so these answer at once either way; neither does
            // writing to a file — a regular file is always ready.
            Builtin::FileCreate => ready_fallible("cx.file_create(a0)", "id", "id"),
            Builtin::FileWrite => {
                vec![format!(
                    "TaskVal::BFileWrite(a0, a1) => {{ let outcome = cx.file_write(*a0, a1.as_slice()); Poll::Ready({}) }}",
                    self.fallible_expr(builtin, "()", "()")
                )]
            }
            Builtin::FlowOfFile => ready_fallible("cx.flow_of_file(a0)", "id", "id"),
            Builtin::FlowNext => {
                pending_fallible("cx.flow_next(*a0)", "chunk", "Bytes::from_vec(chunk)")
            }
            Builtin::Send => vec![
                "TaskVal::BSend(a0, a1) => match cx.send(a0.0, a0.1, a1.clone()) {".into(),
                "    Poll::Ready(()) => Poll::Ready(Value::Unit),".into(),
                "    Poll::Pending => Poll::Pending,".into(),
                "},".into(),
            ],
            other => panic!("`{}` does not build a task", other.name()),
        }
    }

    fn builtin_bindings(&self, builtin: Builtin) -> String {
        let count = self.builtin_fields(builtin).len();
        if count == 0 {
            return String::new();
        }
        let names: Vec<String> = (0..count).map(|i| format!("a{i}")).collect();
        format!("({})", names.join(", "))
    }

    // ------------------------------------------------------------ tables

    fn tables(&self, out: &mut String) {
        push(
            out,
            0,
            "// ---------------------------------------------------------------- program tables",
        );
        push(out, 0, "");
        let names: Vec<String> = self
            .program
            .fns
            .iter()
            .map(|f| format!("{:?}", f.name))
            .collect();
        push(
            out,
            0,
            &format!("static FN_NAMES: &[&str] = &[{}];", names.join(", ")),
        );
        push(
            out,
            0,
            &format!("const MAIN_FN: usize = {}usize;", self.main),
        );
        push(out, 0, "");
    }

    // ------------------------------------------------------------ functions

    fn function(&self, out: &mut String, id: usize) {
        let function = &self.program.fns[id];
        if function.inert {
            push(
                out,
                0,
                &format!(
                    "// inert fn {} #{id} — generic template, symbolic instance, or trait-call stub",
                    function.name
                ),
            );
            push(out, 0, "");
            return;
        }
        match function.kind {
            FnKind::Task => self.task_fn(out, id, function),
            FnKind::Plain if self.handlers.contains(&id) => {
                push(out, 0, &format!("// handler fn {} #{id}", function.name));
                push(
                    out,
                    0,
                    &format!(
                        "fn f{id}(turn: &mut Handled<Value>{}) -> Result<{}, Trap> {{",
                        self.param_list(function),
                        self.repr(&function.ret)
                    ),
                );
                push(out, 1, "let mut cx: Option<&mut Cx<'_, '_, Value>> = None;");
                self.plain_body(out, function, Ctx::Handler);
                push(out, 0, "}");
                push(out, 0, "");
            }
            FnKind::Plain => {
                push(out, 0, &format!("// fn {} #{id}", function.name));
                push(
                    out,
                    0,
                    &format!(
                        "fn f{id}(mut cx: Option<&mut Cx<'_, '_, Value>>{}) -> Result<{}, Trap> {{",
                        self.param_list(function),
                        self.repr(&function.ret)
                    ),
                );
                self.plain_body(out, function, Ctx::Plain);
                push(out, 0, "}");
                push(out, 0, "");
            }
        }
    }

    fn param_list(&self, function: &Function) -> String {
        let mut out = String::new();
        for i in 0..function.params {
            out.push_str(&format!(", a{i}: {}", self.repr(&function.tys[i])));
        }
        out
    }

    /// Locals as `Option<Repr>`: parameters `Some`, the rest `None`. The checker proves every
    /// read is initialized; `rustc`'s definite-assignment cannot see that across the state loop,
    /// and `Option` is what satisfies it without inventing base values for recursive types.
    fn local_decls(&self, function: &Function) -> Vec<String> {
        (0..function.locals.len())
            .map(|i| {
                let repr = self.repr(&function.tys[i]);
                if i < function.params {
                    format!("let mut l{i}: Option<{repr}> = Some(a{i});")
                } else {
                    format!("let mut l{i}: Option<{repr}> = None;")
                }
            })
            .collect()
    }

    /// The shared shape of a function that cannot park: a block variable and one arm per block.
    fn plain_body(&self, out: &mut String, function: &Function, ctx: Ctx) {
        let fname = name_lit(function);
        push_all(out, 1, &self.local_decls(function));
        push(out, 1, "let mut block = 0usize;");
        push(out, 1, "loop {");
        push(out, 2, "match block {");
        for (b, block) in function.blocks.iter().enumerate() {
            let mut body = Vec::new();
            for instr in &block.instrs {
                body.extend(self.instr_lines(function, ctx, instr));
            }
            body.extend(self.term_lines(function, ctx, b, &block.term));
            push(out, 3, &format!("{b}usize => {{"));
            push_all(out, 4, &body);
            push(out, 3, "}");
        }
        push(
            out,
            3,
            &format!("_ => return Err(Trap::new(\"unreachable block\", {fname})),"),
        );
        push(out, 2, "}");
        push(out, 1, "}");
    }

    fn task_fn(&self, out: &mut String, id: usize, function: &Function) {
        let fname = name_lit(function);
        push(out, 0, &format!("// task fn {} #{id}", function.name));
        push(out, 0, &format!("struct FrameF{id} {{"));
        push(out, 1, "state: usize,");
        for i in 0..function.locals.len() {
            push(
                out,
                1,
                &format!("l{i}: Option<{}>,", self.repr(&function.tys[i])),
            );
        }
        push(out, 0, "}");
        push(out, 0, "");
        push(
            out,
            0,
            &format!(
                "fn frame_f{id}({}) -> FrameF{id} {{",
                (0..function.params)
                    .map(|i| format!("a{i}: {}", self.repr(&function.tys[i])))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        );
        push(out, 1, &format!("FrameF{id} {{"));
        push(out, 2, "state: 0usize,");
        for i in 0..function.locals.len() {
            if i < function.params {
                push(out, 2, &format!("l{i}: Some(a{i}),"));
            } else {
                push(out, 2, &format!("l{i}: None,"));
            }
        }
        push(out, 1, "}");
        push(out, 0, "}");
        push(out, 0, "");
        push(
            out,
            0,
            &format!(
                "fn step_f{id}(frame: &mut FrameF{id}, cx: &mut Cx<'_, '_, Value>, mut resumed: Option<Value>) -> Result<Cont, Trap> {{"
            ),
        );
        push(out, 1, "loop {");
        push(out, 2, "match frame.state {");
        for (b, block) in function.blocks.iter().enumerate() {
            let mut body = Vec::new();
            for instr in &block.instrs {
                body.extend(self.instr_lines(function, Ctx::Task, instr));
            }
            let term = self.term_lines(function, Ctx::Task, b, &block.term);
            body.extend(term.iter().cloned());
            push(out, 3, &format!("{}usize => {{", 2 * b));
            push_all(out, 4, &body);
            push(out, 3, "}");
            // The parkable terminators get a second arm that re-executes them alone.
            if matches!(block.term, Term::Await { .. } | Term::ScopeExit { .. }) {
                push(out, 3, &format!("{}usize => {{", 2 * b + 1));
                push_all(out, 4, &term);
                push(out, 3, "}");
            }
        }
        push(
            out,
            3,
            &format!("_ => return Err(Trap::new(\"unreachable state\", {fname})),"),
        );
        push(out, 2, "}");
        push(out, 1, "}");
        push(out, 0, "}");
        push(out, 0, "");
    }

    // ------------------------------------------------------------ instructions

    fn instr_lines(&self, function: &Function, ctx: Ctx, instr: &Instr) -> Vec<String> {
        match instr {
            Instr::Assign(place, rvalue) => {
                let dest_ty = self.place_ty(function, place);
                let expr = self.rvalue_expr(function, ctx, &dest_ty, rvalue);
                vec![
                    format!("let value: {} = {expr};", self.repr(&dest_ty)),
                    self.write_stmt(function, ctx, place, "value"),
                ]
            }
            Instr::ScopeEnter => match ctx {
                Ctx::Task => vec!["cx.scope_enter();".into()],
                _ => vec![format!("{{ {} cx.scope_enter(); }}", ctx.cx_stmt("scope"))],
            },
            Instr::Spawn(operand) => {
                let task = self.operand_expr(function, ctx, operand);
                match ctx {
                    Ctx::Task => vec![format!("spawn_task(cx, {task})?;")],
                    _ => vec![format!(
                        "{{ {} spawn_task(cx, {task})?; }}",
                        ctx.cx_stmt("spawn")
                    )],
                }
            }
            Instr::SpawnReactor {
                dest,
                reactor,
                args,
            } => {
                let wrapped: Vec<String> = args
                    .iter()
                    .zip(&self.program.reactors[*reactor].params)
                    .map(|(arg, ty)| {
                        format!(
                            "wrap_{}({})",
                            self.key(ty),
                            self.operand_expr(function, ctx, arg)
                        )
                    })
                    .collect();
                let create = format!(
                    "cx.create_reactor({reactor}usize, vec![{}])?",
                    wrapped.join(", ")
                );
                let first = match ctx {
                    Ctx::Task => format!("let value: ReactorId = {create};"),
                    _ => format!(
                        "let value: ReactorId = {{ {} {create} }};",
                        ctx.cx_stmt("spawn reactor")
                    ),
                };
                vec![first, self.write_stmt(function, ctx, dest, "value")]
            }
            Instr::SetSlot(slot, operand) => {
                assert!(
                    ctx == Ctx::Handler,
                    "`set slot` outside a handler survived lowering"
                );
                let key = self.key(&self.operand_ty(function, operand));
                vec![format!(
                    "turn.writes.push(({slot}usize, wrap_{key}({})));",
                    self.operand_expr(function, ctx, operand)
                )]
            }
            Instr::Emit { task, returns } => {
                assert!(
                    ctx == Ctx::Handler,
                    "`emit` outside a handler survived lowering"
                );
                vec![format!(
                    "turn.effects.push(Effect {{ task: Value::Task({}), returns: {returns:?} }});",
                    self.operand_expr(function, ctx, task)
                )]
            }
        }
    }

    // ------------------------------------------------------------ terminators

    fn term_lines(&self, function: &Function, ctx: Ctx, b: usize, term: &Term) -> Vec<String> {
        let fname = name_lit(function);
        let state = ctx.state();
        match term {
            Term::Goto(target) => vec![format!("{state} = {}usize;", ctx.target(*target))],
            Term::Branch { cond, then, els } => vec![format!(
                "if {} {{ {state} = {}usize; }} else {{ {state} = {}usize; }}",
                self.operand_expr(function, ctx, cond),
                ctx.target(*then),
                ctx.target(*els)
            )],
            Term::SwitchTag {
                scrutinee,
                cases,
                default,
            } => {
                let ty = self.place_ty(function, scrutinee);
                let ename = self.repr(&ty);
                let count = self.registry.variant_count(&ty);
                let mut lines = vec![format!(
                    "{state} = match {} {{",
                    self.read_place_expr(function, ctx, scrutinee)
                )];
                let mut covered = HashSet::new();
                for (tag, target) in cases {
                    covered.insert(*tag);
                    let dots = if self.registry.variant_field_tys(&ty, *tag).is_empty() {
                        ""
                    } else {
                        "(..)"
                    };
                    lines.push(format!(
                        "    {ename}::V{tag}{dots} => {}usize,",
                        ctx.target(*target)
                    ));
                }
                if covered.len() < count {
                    lines.push(format!("    _ => {}usize,", ctx.target(*default)));
                }
                lines.push("};".into());
                lines
            }
            Term::Return(operand) => {
                let value = self.operand_expr(function, ctx, operand);
                match ctx {
                    Ctx::Task => vec![format!(
                        "return Ok(Cont::Return(wrap_{}({value})));",
                        self.key(&function.ret)
                    )],
                    _ => vec![format!("return Ok({value});")],
                }
            }
            Term::Trap(message) => vec![format!("return Err(Trap::new({message:?}, {fname}));")],
            Term::Await { task, dest, resume } => {
                assert!(
                    ctx == Ctx::Task,
                    "`await` outside a task fn survived lowering"
                );
                let key = self.key(&self.place_ty(function, dest));
                let resume = 2 * resume;
                vec![
                    // A value here is the awaited callee returning: write it and move on. `None`
                    // means execute (or re-ask) the suspension point itself.
                    "if let Some(value) = resumed.take() {".into(),
                    format!(
                        "    {}",
                        self.write_stmt(function, ctx, dest, &format!("unwrap_{key}(value)"))
                    ),
                    format!("    frame.state = {resume}usize;"),
                    "} else {".into(),
                    format!("    frame.state = {}usize;", 2 * b + 1),
                    format!(
                        "    let awaited: Rc<TaskVal> = {};",
                        self.operand_expr(function, ctx, task)
                    ),
                    "    if is_fn_task(&awaited) {".into(),
                    "        return Ok(Cont::AwaitTask(awaited));".into(),
                    "    }".into(),
                    "    match poll_task(cx, &awaited)? {".into(),
                    "        Poll::Ready(value) => {".into(),
                    format!(
                        "            {}",
                        self.write_stmt(function, ctx, dest, &format!("unwrap_{key}(value)"))
                    ),
                    format!("            frame.state = {resume}usize;"),
                    "        }".into(),
                    "        Poll::Pending => return Ok(Cont::Park),".into(),
                    "    }".into(),
                    "}".into(),
                ]
            }
            Term::ScopeExit { resume } => {
                assert!(
                    ctx == Ctx::Task,
                    "`scope exit` outside a task fn survived lowering"
                );
                vec![
                    format!("frame.state = {}usize;", 2 * b + 1),
                    "match cx.scope_exit() {".into(),
                    format!("    Poll::Ready(()) => frame.state = {}usize,", 2 * resume),
                    "    Poll::Pending => return Ok(Cont::Park),".into(),
                    "}".into(),
                ]
            }
        }
    }

    // ------------------------------------------------------------ rvalues

    fn rvalue_expr(&self, function: &Function, ctx: Ctx, dest_ty: &Ty, rvalue: &Rvalue) -> String {
        let fname = name_lit(function);
        match rvalue {
            Rvalue::Use(operand) => self.operand_expr(function, ctx, operand),
            Rvalue::Unary(op, operand) => {
                let value = self.operand_expr(function, ctx, operand);
                match (op, self.operand_ty(function, operand)) {
                    (hir::UnOp::Neg, Ty::I64) => format!("({value}).wrapping_neg()"),
                    (hir::UnOp::Neg, Ty::F64) => format!("-({value})"),
                    (hir::UnOp::Not, Ty::Bool) => format!("!({value})"),
                    (op, ty) => panic!("cannot apply {op:?} to {ty:?}"),
                }
            }
            Rvalue::Binary(op, lhs, rhs) => self.binary_expr(function, ctx, *op, lhs, rhs),
            Rvalue::Call(id, args) => {
                format!(
                    "f{id}({}{})?",
                    ctx.cx_opt(),
                    self.args_list(function, ctx, args)
                )
            }
            Rvalue::Builtin(builtin, args) => {
                self.builtin_expr(function, ctx, dest_ty, *builtin, args, &fname)
            }
            Rvalue::Task(id, args) => {
                if args.is_empty() {
                    format!("Rc::new(TaskVal::F{id})")
                } else {
                    let args: Vec<String> = args
                        .iter()
                        .map(|arg| self.operand_expr(function, ctx, arg))
                        .collect();
                    format!("Rc::new(TaskVal::F{id}({}))", args.join(", "))
                }
            }
            Rvalue::BuiltinTask(builtin, args) => {
                if *builtin == Builtin::Send {
                    let input = self.operand_expr(function, ctx, &args[0]);
                    let message = self.operand_expr(function, ctx, &args[1]);
                    let key = self.key(&self.operand_ty(function, &args[1]));
                    return format!("Rc::new(TaskVal::BSend({input}, wrap_{key}({message})))");
                }
                let args: Vec<String> = args
                    .iter()
                    .map(|arg| self.operand_expr(function, ctx, arg))
                    .collect();
                if args.is_empty() {
                    format!("Rc::new(TaskVal::B{builtin:?})")
                } else {
                    format!("Rc::new(TaskVal::B{builtin:?}({}))", args.join(", "))
                }
            }
            Rvalue::Struct(id, args) => {
                let fields: Vec<String> = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        let field_ty = &self.program.structs[*id].fields[index].ty;
                        format!(
                            "f{index}: {}",
                            self.registry
                                .store(field_ty, &self.operand_expr(function, ctx, arg))
                        )
                    })
                    .collect();
                format!("S{id} {{ {} }}", fields.join(", "))
            }
            Rvalue::Variant(enum_id, variant, args) => {
                // `Option`/`Result` constructions are typed by the destination: the table heads
                // at ids 0 and 1 stand for every instantiation, and the destination's type names
                // which synthetic enum this one builds.
                let ename = if *enum_id == hir::EnumId::OPTION.index()
                    || *enum_id == hir::EnumId::RESULT.index()
                {
                    self.repr(dest_ty)
                } else {
                    format!("E{enum_id}")
                };
                if args.is_empty() {
                    return format!("{ename}::V{variant}");
                }
                let field_tys = self.registry.variant_field_tys(dest_ty, *variant);
                let fields: Vec<String> = args
                    .iter()
                    .zip(&field_tys)
                    .map(|(arg, field_ty)| {
                        self.registry
                            .store(field_ty, &self.operand_expr(function, ctx, arg))
                    })
                    .collect();
                format!("{ename}::V{variant}({})", fields.join(", "))
            }
            Rvalue::ReactorInput(operand, index) => {
                format!(
                    "({}, {index}usize)",
                    self.operand_expr(function, ctx, operand)
                )
            }
            Rvalue::ReactorExport(operand, index) => {
                format!(
                    "({}, {index}usize)",
                    self.operand_expr(function, ctx, operand)
                )
            }
        }
    }

    fn binary_expr(
        &self,
        function: &Function,
        ctx: Ctx,
        op: hir::BinOp,
        lhs: &Operand,
        rhs: &Operand,
    ) -> String {
        use hir::BinOp;
        let fname = name_lit(function);
        let a = self.operand_expr(function, ctx, lhs);
        let b = self.operand_expr(function, ctx, rhs);
        match op {
            BinOp::AddInt => format!("({a}).wrapping_add({b})"),
            BinOp::SubInt => format!("({a}).wrapping_sub({b})"),
            BinOp::MulInt => format!("({a}).wrapping_mul({b})"),
            BinOp::DivInt => format!("div_i64({a}, {b}, {fname})?"),
            BinOp::RemInt => format!("rem_i64({a}, {b}, {fname})?"),
            BinOp::AddFloat => format!("({a}) + ({b})"),
            BinOp::SubFloat => format!("({a}) - ({b})"),
            BinOp::MulFloat => format!("({a}) * ({b})"),
            // No trap: float division and remainder are IEEE, infinities and NaN included.
            BinOp::DivFloat => format!("({a}) / ({b})"),
            BinOp::RemFloat => format!("({a}) % ({b})"),
            BinOp::Concat => match self.operand_ty(function, lhs) {
                Ty::Str => format!("str_concat({a}, {b})"),
                Ty::Bytes => format!("bytes_concat({a}, {b})"),
                other => panic!("concat on {other:?} survived checking"),
            },
            // Eq reaches runtime only on the five comparable scalars, where the representations'
            // own equality is content equality (`Rc<str>` compares contents, the byte view's
            // manual `PartialEq` compares slices, and NaN != NaN falls out of f64).
            BinOp::Eq | BinOp::Ne => {
                let ty = self.operand_ty(function, lhs);
                assert!(
                    matches!(ty, Ty::I64 | Ty::F64 | Ty::Bool | Ty::Str | Ty::Bytes),
                    "equality on {ty:?} survived checking"
                );
                if op == BinOp::Eq {
                    format!("({a}) == ({b})")
                } else {
                    format!("({a}) != ({b})")
                }
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let test = match op {
                    BinOp::Lt => "is_lt",
                    BinOp::Le => "is_le",
                    BinOp::Gt => "is_gt",
                    _ => "is_ge",
                };
                match self.operand_ty(function, lhs) {
                    // Only floats can fail to order; everything else is total.
                    Ty::F64 => format!("cmp_f64({a}, {b}, {fname})?.{test}()"),
                    Ty::I64 | Ty::Str | Ty::Bytes => {
                        format!("({a}).partial_cmp(&({b})).unwrap().{test}()")
                    }
                    other => panic!("ordering on {other:?} survived checking"),
                }
            }
        }
    }

    /// The immediate builtins, inlined per site against typed operands. The task-building ones
    /// are unreachable here — lowering routed them to `Rvalue::BuiltinTask`.
    fn builtin_expr(
        &self,
        function: &Function,
        ctx: Ctx,
        dest_ty: &Ty,
        builtin: Builtin,
        args: &[Operand],
        fname: &str,
    ) -> String {
        let arg = |i: usize| self.operand_expr(function, ctx, &args[i]);
        match builtin {
            Builtin::Print => {
                let key = self.key(&self.operand_ty(function, &args[0]));
                format!(
                    "{{ let text = render_top_{key}(&({})); {} cx.print(&text) }}",
                    arg(0),
                    ctx.cx_stmt("print")
                )
            }
            Builtin::ListenerPort => format!(
                "{{ {} match cx.port({}) {{ Ok(port) => port, Err(err) => return Err(Trap::new(format!(\"`listener_port`: {{}}\", err.kind()), {fname})) }} }}",
                ctx.cx_stmt("listener_port"),
                arg(0)
            ),
            Builtin::FlowLen => format!(
                "{{ {} match cx.flow_len({}) {{ Ok(length) => length, Err(err) => return Err(Trap::new(format!(\"`flow_len`: {{}}\", err.kind()), {fname})) }} }}",
                ctx.cx_stmt("flow_len"),
                arg(0)
            ),
            Builtin::Latest => {
                let key = self.key(dest_ty);
                format!(
                    "{{ let sig = {}; {} match cx.latest(sig.0, sig.1) {{ Some(value) => unwrap_{key}(value), None => return Err(Trap::new(\"`latest` of an export that does not exist\", {fname})) }} }}",
                    arg(0),
                    ctx.cx_stmt("latest")
                )
            }
            // A shared value is one `Rc`; unsharing clones the payload back out — Rc bumps and a
            // memcpy, the ordinary pre-move copy.
            Builtin::Shared => format!("Rc::new({})", arg(0)),
            Builtin::Unshare => format!("(*({})).clone()", arg(0)),
            Builtin::Bytes => format!("Bytes::from_slice(({}).as_bytes())", arg(0)),
            Builtin::BytesLen => format!("(({}).len() as i64)", arg(0)),
            Builtin::BytesSlice => {
                format!("bytes_slice({}, {}, {}, {fname})?", arg(0), arg(1), arg(2))
            }
            Builtin::Byte => format!("byte({}, {fname})?", arg(0)),
            Builtin::BytesAt => format!("bytes_at({}, {}, {fname})?", arg(0), arg(1)),
            Builtin::TextUnchecked => format!("text_unchecked({}, {fname})?", arg(0)),
            task => panic!(
                "`{}` builds a task and cannot be evaluated here",
                task.name()
            ),
        }
    }

    fn args_list(&self, function: &Function, ctx: Ctx, operands: &[Operand]) -> String {
        let mut out = String::new();
        for operand in operands {
            out.push_str(&format!(", {}", self.operand_expr(function, ctx, operand)));
        }
        out
    }

    // ------------------------------------------------------------ places

    fn operand_expr(&self, function: &Function, ctx: Ctx, operand: &Operand) -> String {
        match operand {
            Operand::Const(value) => match value {
                Const::Unit => "()".into(),
                Const::Int(v) if *v == i64::MIN => "i64::MIN".into(),
                Const::Int(v) => format!("{v}i64"),
                // Bit-identical round-tripping: never through decimal.
                Const::Float(v) => format!("f64::from_bits(0x{:016x}u64) /* {v:?} */", v.to_bits()),
                Const::Bool(v) => format!("{v}"),
                Const::Str(v) => format!("Rc::<str>::from({:?})", &**v),
            },
            Operand::Copy(place) => self.read_place_expr(function, ctx, place),
        }
    }

    /// A place read: the local, then the typed projection path — `&`-steps through struct
    /// fields, a match per downcast — with one clone at the end.
    fn read_place_expr(&self, function: &Function, ctx: Ctx, place: &Place) -> String {
        let base = format!("{}l{}", ctx.locals(), place.local);
        if place.proj.is_empty() {
            return format!("{base}.clone().unwrap()");
        }
        let fname = name_lit(function);
        let mut ty = function.tys[place.local].clone();
        let mut out = format!("{{ let cur = {base}.as_ref().unwrap();");
        for proj in &place.proj {
            let step_ty = self.program.ty_of_proj(&ty, proj);
            match proj {
                Proj::Field(index) => {
                    if self.registry.boxed(&step_ty) {
                        out.push_str(&format!(" let cur = &*cur.f{index};"));
                    } else {
                        out.push_str(&format!(" let cur = &cur.f{index};"));
                    }
                }
                Proj::Downcast { variant, field } => {
                    let ename = self.repr(&ty);
                    let arity = self.registry.variant_field_tys(&ty, *variant).len();
                    let bindings: Vec<String> = (0..arity)
                        .map(|i| {
                            if i == *field {
                                format!("f{i}")
                            } else {
                                "_".into()
                            }
                        })
                        .collect();
                    let bound = if self.registry.boxed(&step_ty) {
                        format!("&**f{field}")
                    } else {
                        format!("f{field}")
                    };
                    // The surrounding control flow proved the tag; the other arm is unreachable.
                    out.push_str(&format!(
                        " let cur = match cur {{ {ename}::V{variant}({}) => {bound}, _ => return Err(Trap::new(\"a downcast of an impossible variant\", {fname})) }};",
                        bindings.join(", ")
                    ));
                }
                // A read through a `Shared`: `cur` is `&Rc<Repr>`, and one deref lands `&Repr`.
                Proj::Deref => out.push_str(" let cur = &**cur;"),
            }
            ty = step_ty;
        }
        out.push_str(" cur.clone() }");
        out
    }

    /// A place write. Projected writes are checker-restricted to struct-field chains, and each
    /// `Rc`-stored step copies on write through `Rc::make_mut`, exactly like the interpreter.
    fn write_stmt(&self, function: &Function, ctx: Ctx, place: &Place, value: &str) -> String {
        let base = format!("{}l{}", ctx.locals(), place.local);
        if place.proj.is_empty() {
            return format!("{base} = Some({value});");
        }
        let mut ty = function.tys[place.local].clone();
        let mut out = format!("{{ let cur = {base}.as_mut().unwrap();");
        for (position, proj) in place.proj.iter().enumerate() {
            let Proj::Field(index) = proj else {
                panic!("a write projected through an enum or a shared value");
            };
            let step_ty = self.program.ty_of_proj(&ty, proj);
            if position + 1 == place.proj.len() {
                out.push_str(&format!(
                    " cur.f{index} = {};",
                    self.registry.store(&step_ty, value)
                ));
            } else {
                assert!(
                    self.registry.boxed(&step_ty),
                    "an interior projection step is not an aggregate"
                );
                out.push_str(&format!(" let cur = Rc::make_mut(&mut cur.f{index});"));
            }
            ty = step_ty;
        }
        out.push_str(" }");
        out
    }

    // ------------------------------------------------------------ dispatchers

    fn dispatchers(&self, out: &mut String) {
        // The program-wide frame: one variant per task fn, holding its typed locals.
        if self.task_fns.is_empty() {
            push(out, 0, "enum Frame {}");
        } else {
            push(out, 0, "enum Frame {");
            for &id in &self.task_fns {
                push(out, 1, &format!("F{id}(FrameF{id}),"));
            }
            push(out, 0, "}");
        }
        push(out, 0, "");
        push(
            out,
            0,
            "fn step_frame(frame: &mut Frame, cx: &mut Cx<'_, '_, Value>, resumed: Option<Value>) -> Result<Cont, Trap> {",
        );
        if self.task_fns.is_empty() {
            push(out, 1, "match *frame {}");
        } else {
            push(out, 1, "match frame {");
            for &id in &self.task_fns {
                push(
                    out,
                    2,
                    &format!("Frame::F{id}(frame) => step_f{id}(frame, cx, resumed),"),
                );
            }
            push(out, 1, "}");
        }
        push(out, 0, "}");
        push(out, 0, "");

        push(
            out,
            0,
            "fn call_plain(func: usize, cx: Option<&mut Cx<'_, '_, Value>>) -> Result<Value, Trap> {",
        );
        push(out, 1, "match func {");
        if self.main_is_plain() {
            let ret = &self.program.fns[self.main].ret;
            push(
                out,
                2,
                &format!(
                    "MAIN_FN => Ok(wrap_{}(f{}(cx)?)),",
                    self.key(ret),
                    self.main
                ),
            );
        }
        push(
            out,
            2,
            "_ => Err(Trap::new(\"called a function that is not plain\", \"runtime\")),",
        );
        push(out, 1, "}");
        push(out, 0, "}");
        push(out, 0, "");
    }

    // ------------------------------------------------------------ the graph engine

    fn graph(&self, out: &mut String) {
        for (id, reactor) in self.program.reactors.iter().enumerate() {
            // One pass in slot order, unrolled: parameters come before state, so everything an
            // initialiser can name has a binding by the time it is emitted.
            let mut body = Vec::new();
            let mut ready: HashSet<usize> = HashSet::new();
            let mut stuck = false;
            for &node in &reactor.slots {
                let ty = &reactor.nodes[node].ty;
                match &reactor.nodes[node].kind {
                    NodeKind::Param { index, .. } => {
                        body.push(format!(
                            "let n{node}: {} = unwrap_{}(args.get({index}usize).cloned().ok_or_else(|| Trap::new(\"a reactor was created with too few arguments\", \"runtime\"))?);",
                            self.repr(ty),
                            self.key(ty)
                        ));
                    }
                    NodeKind::State { init, .. } => {
                        if reactor.nodes[node]
                            .deps
                            .iter()
                            .any(|dep| !ready.contains(dep))
                        {
                            // The interpreter traps here at runtime; the generated program traps
                            // in the same place with the same words.
                            body.push(
                                "return Err(Trap::new(\"a state initialiser read a value that is not ready\", \"runtime\"));"
                                    .into(),
                            );
                            stuck = true;
                            break;
                        }
                        let deps: Vec<String> = reactor.nodes[node]
                            .deps
                            .iter()
                            .map(|dep| format!(", n{dep}.clone()"))
                            .collect();
                        body.push(format!(
                            "let n{node}: {} = f{init}(None{})?;",
                            self.repr(ty),
                            deps.join("")
                        ));
                    }
                    NodeKind::Signal { .. } => unreachable!("a signal holds no slot"),
                }
                ready.insert(node);
            }
            if !stuck {
                let slots: Vec<String> = reactor
                    .slots
                    .iter()
                    .map(|node| {
                        format!(
                            "wrap_{}(n{node}.clone())",
                            self.key(&reactor.nodes[*node].ty)
                        )
                    })
                    .collect();
                body.push(format!("Ok(vec![{}])", slots.join(", ")));
            }
            push(out, 0, &format!("// reactor {} #{id}", reactor.name));
            push(
                out,
                0,
                &format!("fn create_r{id}(args: Vec<Value>) -> Result<Vec<Value>, Trap> {{"),
            );
            push_all(out, 1, &body);
            push(out, 0, "}");
            push(out, 0, "");
        }

        let create_arms: Vec<String> = (0..self.program.reactors.len())
            .map(|id| format!("{id}usize => create_r{id}(args),"))
            .collect();
        let mut handle_arms = Vec::new();
        for (id, reactor) in self.program.reactors.iter().enumerate() {
            for (index, input) in reactor.inputs.iter().enumerate() {
                let handler = &self.program.fns[input.handler];
                handle_arms.push(format!("({id}usize, {index}usize) => {{"));
                handle_arms.push(
                    "    let mut turn = Handled { writes: Vec::new(), effects: Vec::new() };"
                        .into(),
                );
                // An input carrying `()` binds nothing, so the handler's arity says whether the
                // message is one of its arguments; the types come from the handler's own locals.
                let mut args = Vec::new();
                let bound = handler.params == reactor.slots.len() + 1;
                if bound {
                    args.push(format!(", unwrap_{}(message)", self.key(&handler.tys[0])));
                }
                let offset = if bound { 1 } else { 0 };
                for slot in 0..reactor.slots.len() {
                    args.push(format!(
                        ", unwrap_{}(slots[{slot}usize].clone())",
                        self.key(&handler.tys[offset + slot])
                    ));
                }
                handle_arms.push(format!(
                    "    f{}(&mut turn{})?;",
                    input.handler,
                    args.join("")
                ));
                handle_arms.push("    Ok(turn)".into());
                handle_arms.push("}".into());
            }
        }
        let mut recompute_arms = Vec::new();
        for (id, reactor) in self.program.reactors.iter().enumerate() {
            for (index, node) in reactor.nodes.iter().enumerate() {
                if let NodeKind::Signal { body } = node.kind {
                    let function = &self.program.fns[body];
                    let deps: Vec<String> = (0..function.params)
                        .map(|i| {
                            format!(
                                ", unwrap_{}(deps[{i}usize].clone())",
                                self.key(&function.tys[i])
                            )
                        })
                        .collect();
                    // Always `Set`: deciding a value is unchanged would need an equality the
                    // trace could observe, and the only pruning v0 does is each input's plan.
                    recompute_arms.push(format!(
                        "({id}usize, {index}usize) => Ok(Update::Set(wrap_{}(f{body}(None{})?))),",
                        self.key(&function.ret),
                        deps.join("")
                    ));
                }
            }
        }

        push(out, 0, "struct Nodes;");
        push(out, 0, "");
        push(out, 0, "impl Graph<Value> for Nodes {");
        push(
            out,
            1,
            "fn create(&self, reactor: usize, args: Vec<Value>) -> Result<Vec<Value>, Trap> {",
        );
        push(out, 2, "match reactor {");
        push_all(out, 3, &create_arms);
        push(
            out,
            3,
            "_ => Err(Trap::new(\"created a reactor that does not exist\", \"runtime\")),",
        );
        push(out, 2, "}");
        push(out, 1, "}");
        push(out, 0, "");
        push(
            out,
            1,
            "fn handle(&self, reactor: usize, input: usize, message: Value, slots: &[Value]) -> Result<Handled<Value>, Trap> {",
        );
        push(out, 2, "match (reactor, input) {");
        push_all(out, 3, &handle_arms);
        push(
            out,
            3,
            "_ => Err(Trap::new(\"a message for an input that does not exist\", \"runtime\")),",
        );
        push(out, 2, "}");
        push(out, 1, "}");
        push(out, 0, "");
        push(
            out,
            1,
            "fn recompute(&self, reactor: usize, node: usize, deps: &[Value]) -> Result<Update<Value>, Trap> {",
        );
        push(out, 2, "match (reactor, node) {");
        push_all(out, 3, &recompute_arms);
        push(
            out,
            3,
            "_ => Err(Trap::new(\"recomputed a node that is not a signal\", \"runtime\")),",
        );
        push(out, 2, "}");
        push(out, 1, "}");
        push(out, 0, "}");
        push(out, 0, "");
    }

    // ------------------------------------------------------------ the plan as data

    fn specs(&self, out: &mut String) {
        let mut body = Vec::new();
        for reactor in &self.program.reactors {
            body.push("ReactorSpec {".to_string());
            body.push(format!("    name: {:?}.to_string(),", reactor.name));
            body.push("    nodes: vec![".into());
            for node in &reactor.nodes {
                body.push(format!(
                    "        NodeSpec {{ name: {:?}.to_string(), deps: vec![{}], slot: {:?} }},",
                    node.name,
                    list(&node.deps),
                    node.kind.slot()
                ));
            }
            body.push("    ],".into());
            body.push(format!("    slots: vec![{}],", list(&reactor.slots)));
            body.push("    inputs: vec![".into());
            for input in &reactor.inputs {
                body.push(format!(
                    "        InputSpec {{ name: {:?}.to_string(), capacity: {}usize, overflow: Overflow::{}, plan: vec![{}] }},",
                    input.name,
                    input.capacity,
                    overflow(input.overflow),
                    list(&input.plan)
                ));
            }
            body.push("    ],".into());
            body.push(format!("    order: vec![{}],", list(&reactor.order)));
            body.push(format!("    exports: vec![{}],", list(&reactor.exports)));
            body.push("},".into());
        }
        push(out, 0, "fn reactor_specs() -> Vec<ReactorSpec> {");
        push(out, 1, "vec![");
        push_all(out, 2, &body);
        push(out, 1, "]");
        push(out, 0, "}");
        push(out, 0, "");
    }

    // ------------------------------------------------------------ entry glue

    fn entry(&self, out: &mut String) {
        push(out, 0, "fn root_task() -> Value {");
        if self.main_is_plain() {
            push(out, 1, "Value::Task(Rc::new(TaskVal::Main))");
        } else {
            push(
                out,
                1,
                &format!("Value::Task(Rc::new(TaskVal::F{}))", self.main),
            );
        }
        push(out, 0, "}");
        push(out, 0, "");

        // main's result convention, typed by main's return: a `Result` reports rather than
        // prints, anything else non-unit prints top-level, exactly as `norn run` does.
        let ret = &self.program.fns[self.main].ret;
        push(out, 0, "fn finish(value: Value) -> ExitCode {");
        match ret {
            Ty::Unit => {
                push(out, 1, "ExitCode::SUCCESS");
            }
            Ty::Result(ok, err) => {
                let sid = self.registry.synthetic_id(ret);
                push(out, 1, &format!("match unwrap_e{sid}(value) {{"));
                push(out, 2, &format!("E{sid}::V1(f0) => {{"));
                push(
                    out,
                    3,
                    &format!(
                        "eprintln!(\"error: {{}}\", render_top_{}(&f0));",
                        self.key(err)
                    ),
                );
                push(out, 3, "ExitCode::FAILURE");
                push(out, 2, "}");
                push(out, 2, &format!("E{sid}::V0(f0) => {{"));
                if !matches!(**ok, Ty::Unit) {
                    push(
                        out,
                        3,
                        &format!("println!(\"{{}}\", render_top_{}(&f0));", self.key(ok)),
                    );
                }
                push(out, 3, "ExitCode::SUCCESS");
                push(out, 2, "}");
                push(out, 1, "}");
            }
            other => {
                let key = self.key(other);
                push(
                    out,
                    1,
                    &format!("println!(\"{{}}\", render_top_{key}(&unwrap_{key}(value)));"),
                );
                push(out, 1, "ExitCode::SUCCESS");
            }
        }
        push(out, 0, "}");
    }
}

/// The declared overflow policy, in the runtime's vocabulary — the same deliberate second spelling
/// as `interp::overflow`.
fn overflow(policy: hir::Overflow) -> &'static str {
    match policy {
        hir::Overflow::Reject => "Reject",
        hir::Overflow::DropOldest => "DropOldest",
        hir::Overflow::DropNewest => "DropNewest",
        hir::Overflow::Wait => "Wait",
    }
}

fn list(items: &[usize]) -> String {
    items
        .iter()
        .map(|item| format!("{item}usize"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn name_lit(function: &Function) -> String {
    format!("{:?}", function.name)
}
