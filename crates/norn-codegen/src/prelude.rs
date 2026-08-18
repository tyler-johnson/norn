// The runtime prelude of every generated program.
//
// This file is not a module of norn-codegen: `lib.rs` carries it as a string and `emit.rs` writes
// it into the generated source ahead of the per-program part. It is a port of the interpreter's
// value semantics — `norn-nir/src/interp.rs`, item for item — and the two must not drift: trap
// messages interpolate `{:?}` of `Value`, `BinOp`, `UnOp`, and builtin names, so a renamed variant
// on either side is a byte difference the differential oracle will catch in stderr.
//
// The restricted-Rust charter (BOOTSTRAP.md §3), as it is interpreted here: structs, enums,
// `match`, loops, `Rc`, and calls into `norn-rt`; no `async`, no trait definitions, no generic
// definitions, and no named lifetimes — `'static` data-section references and the elided `'_` in
// signatures the runtime ABI dictates are the whole of what appears. Implementing `Body<Value>`
// and `Graph<Value>` at the one concrete `Value` is the sanctioned ABI, not a generic definition.
// Everything in this file maps mechanically onto a Cranelift backend.
//
// The emitted header provides the imports: `Rc`, `io`, `ExitCode`, and the `norn_rt` names. The
// per-program part provides, and this file may name freely:
//
//   static STRUCTS: &[StructLayout]         one entry per struct type
//   static ENUMS: &[EnumLayout]             one entry per enum type, seeded ones included
//   static FN_NAMES: &[&str]                every function's name, by id
//   static FN_LOCALS: &[usize]              every function's local count, by id
//   static FN_IS_TASK: &[bool]              whether the function is a `task fn`, by id
//   const MAIN_FN: usize                    the entry point
//   fn step_frame(&mut Frame, &mut Cx) -> Result<Cont, Trap>     dispatch to a task fn's states
//   fn call_plain(usize, Option<&mut Cx>, Vec<Value>) -> Result<Value, Trap>
//   struct Nodes + impl Graph<Value>        the reactor engine
//   fn reactor_specs() -> Vec<ReactorSpec>  the plan, as plain data

// ---------------------------------------------------------------- values

#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    Unit,
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Rc<str>),
    Struct(usize, Rc<Vec<Value>>),
    Variant(usize, usize, Rc<Vec<Value>>),
    Task(Rc<TaskValue>),
    Resource(ResourceKind, ResourceId),
    Reactor(ReactorId),
    Input(ReactorId, usize),
    Signal(ReactorId, usize),
}

#[derive(PartialEq, Debug)]
pub struct TaskValue {
    pub kind: TaskKind,
}

#[derive(PartialEq, Debug)]
pub enum TaskKind {
    Fn(usize, Vec<Value>),
    Builtin(Builtin, Vec<Value>),
}

// The seeded enums sit in fixed slots of the enum table; see `hir::EnumId`.
const ENUM_OPTION: usize = 0;
const ENUM_RESULT: usize = 1;
const ENUM_IO_ERROR: usize = 2;
const TAG_OK: usize = 0;
const TAG_ERR: usize = 1;
const IO_NOT_FOUND: usize = 0;
const IO_DENIED: usize = 1;
const IO_IN_USE: usize = 2;
const IO_REFUSED: usize = 3;
const IO_CLOSED: usize = 4;
const IO_OTHER: usize = 5;

pub struct StructLayout {
    pub name: &'static str,
    pub fields: &'static [&'static str],
}

pub struct EnumLayout {
    pub name: &'static str,
    pub variants: &'static [VariantLayout],
}

pub struct VariantLayout {
    pub name: &'static str,
    pub fields: &'static [&'static str],
    pub positional: bool,
}

// ---------------------------------------------------------------- operators and builtins

// Variant names mirror `hir::BinOp` and `hir::UnOp` exactly: trap messages print them with `{:?}`.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum BinOp {
    AddInt,
    SubInt,
    MulInt,
    DivInt,
    RemInt,
    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,
    RemFloat,
    Concat,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Builtin {
    Print,
    ListenerPort,
    Sleep,
    TcpListen,
    TcpAccept,
    TcpRead,
    TcpWrite,
    TcpClose,
    Send,
    Latest,
}

impl Builtin {
    pub fn name(self) -> &'static str {
        match self {
            Builtin::Print => "print",
            Builtin::ListenerPort => "listener_port",
            Builtin::Sleep => "sleep",
            Builtin::TcpListen => "tcp_listen",
            Builtin::TcpAccept => "tcp_accept",
            Builtin::TcpRead => "tcp_read",
            Builtin::TcpWrite => "tcp_write",
            Builtin::TcpClose => "tcp_close",
            Builtin::Send => "send",
            Builtin::Latest => "latest",
        }
    }
}

// ---------------------------------------------------------------- frames

// A suspended task is a stack of these, innermost last, exactly the interpreter's shape. `state`
// numbers the emitted match arms: `2*b` runs block `b` whole, `2*b + 1` re-executes only its
// terminator, which is how waking re-asks a suspension point without re-running the instructions
// before it.
pub struct Frame {
    pub func: usize,
    pub state: usize,
    pub locals: Vec<Value>,
    // Where this frame's result goes in its caller.
    pub dest: Option<(usize, &'static [usize])>,
}

// What one resumption of a frame produced. `AwaitTask` is the inline call: the caller has already
// set its own resume state, and the driver pushes the callee.
pub enum Cont {
    Return(Value),
    Park,
    AwaitTask {
        func: usize,
        args: Vec<Value>,
        local: usize,
        proj: &'static [usize],
    },
}

fn new_frame(func: usize, args: Vec<Value>, dest: Option<(usize, &'static [usize])>) -> Frame {
    let mut locals = vec![Value::Unit; FN_LOCALS[func]];
    for (slot, value) in locals.iter_mut().zip(args) {
        *slot = value;
    }
    Frame {
        func,
        state: 0,
        locals,
        dest,
    }
}

// Run until the task finishes or suspends. Parking leaves every frame's state where it was, so
// waking re-executes the same suspension point and asks the runtime again.
fn resume_frames(frames: &mut Vec<Frame>, cx: &mut Cx<'_, '_, Value>) -> Result<Step<Value>, Trap> {
    loop {
        let frame = frames
            .last_mut()
            .expect("a running task has at least one frame");
        match step_frame(frame, cx)? {
            Cont::Park => return Ok(Step::Park),
            Cont::AwaitTask {
                func,
                args,
                local,
                proj,
            } => {
                frames.push(new_frame(func, args, Some((local, proj))));
            }
            Cont::Return(value) => {
                let finished = frames.pop().expect("the frame being returned from");
                match (finished.dest, frames.last_mut()) {
                    (Some((local, proj)), Some(caller)) => {
                        write_place(&mut caller.locals, local, proj, value);
                    }
                    // The outermost frame returning is the task finishing.
                    _ => return Ok(Step::Done(value)),
                }
            }
        }
    }
}

// ---------------------------------------------------------------- bodies

pub struct FnBody {
    name: &'static str,
    frames: Vec<Frame>,
}

impl Body<Value> for FnBody {
    fn resume(&mut self, cx: &mut Cx<'_, '_, Value>) -> Step<Value> {
        match resume_frames(&mut self.frames, cx) {
            Ok(step) => step,
            Err(trap) => Step::Trap(trap),
        }
    }

    fn name(&self) -> &str {
        self.name
    }
}

pub struct BuiltinBody {
    builtin: Builtin,
    args: Vec<Value>,
}

impl Body<Value> for BuiltinBody {
    fn resume(&mut self, cx: &mut Cx<'_, '_, Value>) -> Step<Value> {
        match poll_builtin(cx, self.builtin, &self.args) {
            Ok(Poll::Ready(value)) => Step::Done(value),
            Ok(Poll::Pending) => Step::Park,
            Err(trap) => Step::Trap(trap),
        }
    }

    fn name(&self) -> &str {
        self.builtin.name()
    }
}

// A plain function run as a task: it never parks, so one resumption is the whole run. Only `main`
// can arrive here — every other task value is built from a `task fn` or a builtin.
pub struct PlainBody {
    func: usize,
    args: Vec<Value>,
}

impl Body<Value> for PlainBody {
    fn resume(&mut self, cx: &mut Cx<'_, '_, Value>) -> Step<Value> {
        match call_plain(self.func, Some(cx), std::mem::take(&mut self.args)) {
            Ok(value) => Step::Done(value),
            Err(trap) => Step::Trap(trap),
        }
    }

    fn name(&self) -> &str {
        FN_NAMES[self.func]
    }
}

fn make_body(value: &Value) -> Result<Box<dyn Body<Value>>, Trap> {
    let Value::Task(task) = value else {
        return Err(Trap::new("started something that is not a task", "runtime"));
    };
    Ok(match &task.kind {
        TaskKind::Fn(id, args) => {
            if FN_IS_TASK[*id] {
                Box::new(FnBody {
                    name: FN_NAMES[*id],
                    frames: vec![new_frame(*id, args.clone(), None)],
                })
            } else {
                Box::new(PlainBody {
                    func: *id,
                    args: args.clone(),
                })
            }
        }
        TaskKind::Builtin(builtin, args) => Box::new(BuiltinBody {
            builtin: *builtin,
            args: args.clone(),
        }),
    })
}

// ---------------------------------------------------------------- places

fn read_place(locals: &[Value], local: usize, proj: &[usize]) -> Value {
    let mut value = &locals[local];
    for index in proj {
        value = match value {
            Value::Struct(_, fields) | Value::Variant(_, _, fields) => &fields[*index],
            other => return other.clone(),
        };
    }
    value.clone()
}

fn write_place(locals: &mut [Value], local: usize, proj: &[usize], value: Value) {
    let mut slot = &mut locals[local];
    for index in proj {
        slot = match slot {
            Value::Struct(_, fields) | Value::Variant(_, _, fields) => {
                &mut Rc::make_mut(fields)[*index]
            }
            other => {
                *other = value;
                return;
            }
        };
    }
    *slot = value;
}

// ---------------------------------------------------------------- operators

fn unary(op: UnOp, value: Value, func: &str) -> Result<Value, Trap> {
    Ok(match (op, value) {
        (UnOp::Neg, Value::Int(v)) => Value::Int(v.wrapping_neg()),
        (UnOp::Neg, Value::Float(v)) => Value::Float(-v),
        (UnOp::Not, Value::Bool(v)) => Value::Bool(!v),
        (op, value) => {
            return Err(Trap::new(
                format!("cannot apply {op:?} to {value:?}"),
                func,
            ));
        }
    })
}

fn binary(op: BinOp, lhs: Value, rhs: Value, func: &str) -> Result<Value, Trap> {
    use Value::{Bool, Float, Int, Str};
    Ok(match (op, &lhs, &rhs) {
        (BinOp::AddInt, Int(a), Int(b)) => Int(a.wrapping_add(*b)),
        (BinOp::SubInt, Int(a), Int(b)) => Int(a.wrapping_sub(*b)),
        (BinOp::MulInt, Int(a), Int(b)) => Int(a.wrapping_mul(*b)),
        (BinOp::DivInt, Int(_), Int(0)) => {
            return Err(Trap::new("divide by zero", func));
        }
        (BinOp::DivInt, Int(a), Int(b)) => Int(a.wrapping_div(*b)),
        (BinOp::RemInt, Int(_), Int(0)) => {
            return Err(Trap::new("remainder by zero", func));
        }
        (BinOp::RemInt, Int(a), Int(b)) => Int(a.wrapping_rem(*b)),
        (BinOp::AddFloat, Float(a), Float(b)) => Float(a + b),
        (BinOp::SubFloat, Float(a), Float(b)) => Float(a - b),
        (BinOp::MulFloat, Float(a), Float(b)) => Float(a * b),
        (BinOp::DivFloat, Float(a), Float(b)) => Float(a / b),
        (BinOp::RemFloat, Float(a), Float(b)) => Float(a % b),
        (BinOp::Concat, Str(a), Str(b)) => Str(format!("{a}{b}").into()),
        (BinOp::Eq, _, _) => Bool(lhs == rhs),
        (BinOp::Ne, _, _) => Bool(lhs != rhs),
        (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge, _, _) => {
            let ordering = match (&lhs, &rhs) {
                (Int(a), Int(b)) => a.partial_cmp(b),
                (Float(a), Float(b)) => a.partial_cmp(b),
                (Str(a), Str(b)) => a.partial_cmp(b),
                _ => None,
            };
            let Some(ordering) = ordering else {
                return Err(Trap::new(
                    format!("cannot order {lhs:?} and {rhs:?}"),
                    func,
                ));
            };
            Bool(match op {
                BinOp::Lt => ordering.is_lt(),
                BinOp::Le => ordering.is_le(),
                BinOp::Gt => ordering.is_gt(),
                _ => ordering.is_ge(),
            })
        }
        (op, a, b) => {
            return Err(Trap::new(
                format!("cannot apply {op:?} to {a:?} and {b:?}"),
                func,
            ));
        }
    })
}

// ---------------------------------------------------------------- builtins

// Purity's trap of last resort: emitted code in a turn-called function has no `Cx` to hand over,
// so every observable operation is an arm that has to ask for one and cannot get it.
fn impure_trap(what: &str) -> Trap {
    Trap::new(
        format!("`{what}` cannot run during a turn: a reactor node is pure"),
        "turn",
    )
}

// The builtins that produce a value immediately. The ones that produce a task are polled at the
// `await` that runs them.
fn eval_builtin(
    cx: Option<&mut Cx<'_, '_, Value>>,
    builtin: Builtin,
    args: &[Value],
    func: &str,
) -> Result<Value, Trap> {
    Ok(match builtin {
        Builtin::Print => {
            let text = render(&args[0]);
            let Some(cx) = cx else {
                return Err(impure_trap("print"));
            };
            cx.print(&text);
            Value::Unit
        }
        Builtin::ListenerPort => {
            let Value::Resource(_, id) = &args[0] else {
                return Err(Trap::new(
                    "`listener_port` of something that is not a listener",
                    func,
                ));
            };
            let Some(cx) = cx else {
                return Err(impure_trap("listener_port"));
            };
            match cx.port(*id) {
                Ok(port) => Value::Int(port),
                Err(err) => {
                    return Err(Trap::new(format!("`listener_port`: {}", err.kind()), func));
                }
            }
        }
        Builtin::Latest => {
            let Value::Signal(reactor, export) = &args[0] else {
                return Err(Trap::new("`latest` of something that is not a signal", func));
            };
            let (reactor, export) = (*reactor, *export);
            let Some(cx) = cx else {
                return Err(impure_trap("latest"));
            };
            match cx.latest(reactor, export) {
                Some(value) => value,
                None => {
                    return Err(Trap::new("`latest` of an export that does not exist", func));
                }
            }
        }
        task => {
            return Err(Trap::new(
                format!("`{}` builds a task and cannot be evaluated here", task.name()),
                func,
            ));
        }
    })
}

// Ask the runtime for the effect of a task builtin. `Pending` means the task parks and asks again
// when it is woken, which is why nothing here has to remember an operation in flight.
fn poll_builtin(
    cx: &mut Cx<'_, '_, Value>,
    builtin: Builtin,
    args: &[Value],
) -> Result<Poll<Value>, Trap> {
    let name = builtin.name();
    Ok(match builtin {
        Builtin::Sleep => match cx.sleep(integer(name, &args[0])?) {
            Poll::Ready(()) => Poll::Ready(Value::Unit),
            Poll::Pending => Poll::Pending,
        },
        Builtin::TcpListen => Poll::Ready(fallible(
            cx.listen(integer(name, &args[0])?)
                .map(|id| Value::Resource(ResourceKind::Listener, id)),
        )),
        Builtin::TcpAccept => match cx.accept(resource(name, &args[0])?) {
            Poll::Ready(outcome) => Poll::Ready(fallible(
                outcome.map(|id| Value::Resource(ResourceKind::Connection, id)),
            )),
            Poll::Pending => Poll::Pending,
        },
        Builtin::TcpRead => match cx.read(resource(name, &args[0])?) {
            Poll::Ready(outcome) => {
                Poll::Ready(fallible(outcome.map(|text| Value::Str(text.into()))))
            }
            Poll::Pending => Poll::Pending,
        },
        Builtin::TcpWrite => {
            let connection = resource(name, &args[0])?;
            let text = text(name, &args[1])?;
            match cx.write(connection, &text) {
                Poll::Ready(outcome) => Poll::Ready(fallible(outcome.map(|()| Value::Unit))),
                Poll::Pending => Poll::Pending,
            }
        }
        Builtin::TcpClose => {
            cx.close(resource(name, &args[0])?);
            Poll::Ready(Value::Unit)
        }
        Builtin::Send => {
            let Value::Input(reactor, input) = &args[0] else {
                return Err(Trap::new(
                    "`send` to something that is not an input",
                    "runtime",
                ));
            };
            match cx.send(*reactor, *input, args[1].clone()) {
                Poll::Ready(()) => Poll::Ready(Value::Unit),
                Poll::Pending => Poll::Pending,
            }
        }
        plain => {
            return Err(Trap::new(
                format!("`{}` does not build a task", plain.name()),
                "runtime",
            ));
        }
    })
}

fn integer(builtin: &str, value: &Value) -> Result<i64, Trap> {
    match value {
        Value::Int(value) => Ok(*value),
        other => Err(Trap::new(
            format!("`{builtin}` wanted a number, found {other:?}"),
            "runtime",
        )),
    }
}

fn text(builtin: &str, value: &Value) -> Result<String, Trap> {
    match value {
        Value::Str(value) => Ok(value.to_string()),
        other => Err(Trap::new(
            format!("`{builtin}` wanted a string, found {other:?}"),
            "runtime",
        )),
    }
}

fn resource(builtin: &str, value: &Value) -> Result<ResourceId, Trap> {
    match value {
        Value::Resource(_, id) => Ok(*id),
        other => Err(Trap::new(
            format!("`{builtin}` wanted a resource, found {other:?}"),
            "runtime",
        )),
    }
}

// Wrap what a socket operation returned as a `Result<T, IoError>`.
fn fallible(outcome: io::Result<Value>) -> Value {
    let (variant, fields) = match outcome {
        Ok(value) => (TAG_OK, vec![value]),
        Err(err) => (TAG_ERR, vec![io_error_value(&err)]),
    };
    Value::Variant(ENUM_RESULT, variant, Rc::new(fields))
}

// Map a host I/O error onto the built-in `IoError`. The unknown case carries the host's own name
// for the condition rather than its message, which varies by platform.
fn io_error_value(err: &io::Error) -> Value {
    use io::ErrorKind as K;
    let (variant, fields) = match err.kind() {
        K::NotFound => (IO_NOT_FOUND, Vec::new()),
        K::PermissionDenied => (IO_DENIED, Vec::new()),
        K::AddrInUse | K::AddrNotAvailable => (IO_IN_USE, Vec::new()),
        K::ConnectionRefused => (IO_REFUSED, Vec::new()),
        K::ConnectionReset
        | K::ConnectionAborted
        | K::NotConnected
        | K::BrokenPipe
        | K::WriteZero
        | K::UnexpectedEof => (IO_CLOSED, Vec::new()),
        other => (IO_OTHER, vec![Value::Str(format!("{other:?}").into())]),
    };
    Value::Variant(ENUM_IO_ERROR, variant, Rc::new(fields))
}

// ---------------------------------------------------------------- spawning

// The resource handles a spawned task is being given. Only handles passed directly are seen; one
// buried inside a struct stays with the parent, deliberately matching the interpreter.
fn moved_resources(kind: &TaskKind) -> Vec<ResourceId> {
    let args = match kind {
        TaskKind::Fn(_, args) | TaskKind::Builtin(_, args) => args,
    };
    args.iter()
        .filter_map(|arg| match arg {
            Value::Resource(_, id) => Some(*id),
            _ => None,
        })
        .collect()
}

fn spawn_task(cx: &mut Cx<'_, '_, Value>, value: Value, func: &str) -> Result<(), Trap> {
    let Value::Task(task) = &value else {
        return Err(Trap::new("spawned a value that is not a task", func));
    };
    let moved = moved_resources(&task.kind);
    cx.spawn(value, &moved)?;
    Ok(())
}

// ---------------------------------------------------------------- rendering

// Render a value in the surface syntax that would build it. At the top level a string is its own
// text; nested inside an aggregate it is quoted.
fn render(value: &Value) -> String {
    match value {
        Value::Str(v) => v.to_string(),
        other => render_nested(other),
    }
}

fn render_nested(value: &Value) -> String {
    match value {
        Value::Unit => "()".into(),
        Value::Int(v) => v.to_string(),
        Value::Float(v) => {
            let text = format!("{v}");
            if text.contains(['.', 'e', 'E', 'n', 'i']) {
                text
            } else {
                format!("{text}.0")
            }
        }
        Value::Bool(v) => v.to_string(),
        Value::Str(v) => format!("{:?}", &**v),
        Value::Task(task) => {
            let name = match &task.kind {
                TaskKind::Fn(id, _) => FN_NAMES[*id],
                TaskKind::Builtin(builtin, _) => builtin.name(),
            };
            format!("<task {name}>")
        }
        Value::Resource(kind, id) => format!("<{} {id}>", kind.name()),
        Value::Reactor(id) => format!("<reactor {id}>"),
        Value::Input(id, index) => format!("<input {index} of {id}>"),
        Value::Signal(id, index) => format!("<signal {index} of {id}>"),
        Value::Struct(id, fields) => {
            let layout = &STRUCTS[*id];
            let mut out = format!("{}(", layout.name);
            for (index, field) in fields.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!(
                    "{}: {}",
                    layout.fields[index],
                    render_nested(field)
                ));
            }
            out.push(')');
            out
        }
        Value::Variant(enum_id, tag, fields) => {
            let layout = &ENUMS[*enum_id];
            let variant = &layout.variants[*tag];
            // `Option` and `Result` are written unqualified in source, so they print that way.
            let builtin = *enum_id == ENUM_OPTION || *enum_id == ENUM_RESULT;
            let mut out = if builtin {
                variant.name.to_string()
            } else {
                format!("{}.{}", layout.name, variant.name)
            };
            if fields.is_empty() {
                return out;
            }
            out.push('(');
            for (index, field) in fields.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                if !variant.positional {
                    out.push_str(&format!("{}: ", variant.fields[index]));
                }
                out.push_str(&render_nested(field));
            }
            out.push(')');
            out
        }
    }
}

// ---------------------------------------------------------------- entry

// The generated binary's whole interface, mirroring `norn run` byte for byte from the point where
// the front end has finished: the same flags, the same output conventions, the same exit codes.
fn main() -> ExitCode {
    let mut trace = false;
    let mut virtual_clock = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--trace" => trace = true,
            "--virtual-clock" => virtual_clock = true,
            flag if flag.starts_with('-') => {
                eprintln!("norn: unknown option `{flag}`");
                return ExitCode::FAILURE;
            }
            arg => {
                eprintln!("norn: unexpected argument `{arg}`");
                return ExitCode::FAILURE;
            }
        }
    }

    let config = Config {
        clock: if virtual_clock {
            Clock::simulated()
        } else {
            Clock::real()
        },
        trace,
    };
    let mut out = Stdout;
    let engine = Engine {
        make: Box::new(|value: &Value| make_body(value)),
        graph: Box::new(Nodes),
        reactors: reactor_specs(),
    };
    let mut runtime = Runtime::new(config, &mut out, engine);
    let root = Value::Task(Rc::new(TaskValue {
        kind: TaskKind::Fn(MAIN_FN, Vec::new()),
    }));
    let value = runtime.block_on(root);
    if trace {
        eprint!("{}", runtime.trace().render());
    }
    match value {
        Ok(value) => {
            // A `main` returning a `Result` reports rather than prints, exactly as `norn run` does.
            let result = match &value {
                Value::Variant(enum_id, tag, fields) if *enum_id == ENUM_RESULT => {
                    if *tag == TAG_ERR {
                        eprintln!("error: {}", render(&fields[0]));
                        return ExitCode::FAILURE;
                    }
                    fields[0].clone()
                }
                value => value.clone(),
            };
            if !matches!(result, Value::Unit) {
                println!("{}", render(&result));
            }
            ExitCode::SUCCESS
        }
        Err(trap) => {
            eprintln!("norn: trapped: {trap}");
            ExitCode::FAILURE
        }
    }
}
