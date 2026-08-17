//! The NIR interpreter.
//!
//! Calls are managed with an explicit frame stack rather than the host call stack. Nothing in M1
//! needed that — pure functions could recurse on Rust's stack quite happily — but suspension does:
//! a task that parks has to put its frames down somewhere and pick them up later, and resuming is
//! then just picking a `(block, instruction)` back up.
//!
//! Everything about scheduling lives in `norn-rt`. This file supplies one `Body`: given a frame
//! stack and a `Cx`, run until the task finishes or suspends. `await` of a `task fn` pushes a frame
//! exactly like a plain call — an inline task call *is* a call, differing only in that the callee may
//! park — and `await` of a task builtin is where a real suspension happens.

use std::fmt::Write as _;
use std::io;
use std::rc::Rc;

use norn_hir::hir::{BinOp, Builtin, EnumId, UnOp, io_error};
use norn_rt::{Body, Cx, Runtime, Step};

pub use norn_rt::{Captured, Clock, Config, Output, Poll, ResourceId, ResourceKind, Stdout, Trap};

use crate::nir::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    Unit,
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Rc<str>),
    Record(usize, Rc<Vec<Value>>),
    Variant(usize, usize, Rc<Vec<Value>>),
    /// A computation that has not run. `await` and `spawn` are what start it.
    Task(Rc<TaskValue>),
    /// A handle into the runtime's resource table.
    Resource(ResourceKind, ResourceId),
}

#[derive(PartialEq, Debug)]
pub struct TaskValue {
    pub kind: TaskKind,
}

#[derive(PartialEq, Debug)]
pub enum TaskKind {
    Fn(FnId, Vec<Value>),
    Builtin(Builtin, Vec<Value>),
}

struct Frame {
    function: FnId,
    locals: Vec<Value>,
    block: BlockId,
    instr: usize,
    /// Where this frame's result goes in its caller.
    dest: Option<Place>,
}

/// The result of a whole program: what `main` produced, and the trace of how it got there.
pub struct Outcome {
    pub value: Result<Value, Trap>,
    pub trace: String,
}

/// Run `entry` as the root task, with a real clock and no trace.
pub fn run(program: &Program, entry: FnId, out: &mut dyn Output) -> Result<Value, Trap> {
    execute(program, entry, out, Config::default()).value
}

/// Run `entry` as the root task under `config`.
///
/// Every program runs this way, including one whose `main` is an ordinary `fn`: a plain function is
/// a task that never parks, and one execution path is worth more than the two lines it saves.
pub fn execute<'p>(
    program: &'p Program,
    entry: FnId,
    out: &'p mut dyn Output,
    config: Config,
) -> Outcome {
    let root = Value::Task(Rc::new(TaskValue {
        kind: TaskKind::Fn(entry, Vec::new()),
    }));
    let mut runtime = Runtime::new(config, out, move |value| body(program, value));
    let value = runtime.block_on(root);
    Outcome {
        value,
        trace: runtime.trace().render(),
    }
}

/// Turn a task value into something the runtime can resume. The runtime asks for this whenever a
/// task is spawned; it cannot interpret a task value itself.
fn body<'p>(program: &'p Program, value: &Value) -> Result<Box<dyn Body<Value> + 'p>, Trap> {
    let Value::Task(task) = value else {
        return Err(Trap::new("started something that is not a task", "runtime"));
    };
    Ok(match &task.kind {
        TaskKind::Fn(id, args) => Box::new(TaskBody {
            program,
            name: program.fns[*id].name.clone(),
            state: State::Frames(vec![new_frame(program, *id, args.clone(), None)]),
        }),
        TaskKind::Builtin(builtin, args) => Box::new(TaskBody {
            program,
            name: builtin.name().to_string(),
            state: State::Builtin(*builtin, args.clone()),
        }),
    })
}

struct TaskBody<'p> {
    program: &'p Program,
    name: String,
    state: State,
}

enum State {
    /// A `task fn` body: a stack of frames, innermost last.
    Frames(Vec<Frame>),
    /// A task builtin started on its own, with no Norn code around it.
    Builtin(Builtin, Vec<Value>),
}

impl Body<Value> for TaskBody<'_> {
    fn resume(&mut self, cx: &mut Cx<'_, '_, Value>) -> Step<Value> {
        let interpreter = Interpreter {
            program: self.program,
        };
        let stepped = match &mut self.state {
            State::Frames(frames) => interpreter.resume_task(frames, cx),
            State::Builtin(builtin, args) => match interpreter.poll_builtin(cx, *builtin, args) {
                Ok(Poll::Ready(value)) => Ok(Step::Done(value)),
                Ok(Poll::Pending) => Ok(Step::Park),
                Err(trap) => Err(trap),
            },
        };
        match stepped {
            Ok(step) => step,
            Err(trap) => Step::Trap(trap),
        }
    }

    fn name(&self) -> &str {
        &self.name
    }
}

fn new_frame(program: &Program, function: FnId, args: Vec<Value>, dest: Option<Place>) -> Frame {
    let def = &program.fns[function];
    let mut locals = vec![Value::Unit; def.locals.len()];
    for (slot, value) in locals.iter_mut().zip(args) {
        *slot = value;
    }
    Frame {
        function,
        locals,
        block: 0,
        instr: 0,
        dest,
    }
}

struct Interpreter<'p> {
    program: &'p Program,
}

impl Interpreter<'_> {
    /// Run until the task finishes or suspends.
    ///
    /// A suspension point does not advance the frame: parking leaves `block` and `instr` where they
    /// were, so waking re-executes the same terminator and asks the runtime again. That is what makes
    /// "ask, and park if the answer is not ready" the only protocol either engine needs.
    fn resume_task(
        &self,
        frames: &mut Vec<Frame>,
        cx: &mut Cx<'_, '_, Value>,
    ) -> Result<Step<Value>, Trap> {
        loop {
            let frame = frames
                .last_mut()
                .expect("a running task has at least one frame");
            let function = &self.program.fns[frame.function];
            let block = &function.blocks[frame.block];

            // Run the straight-line part of the block, then act on its terminator.
            if frame.instr < block.instrs.len() {
                match &block.instrs[frame.instr] {
                    Instr::Assign(place, rvalue) => {
                        frame.instr += 1;
                        if let Rvalue::Call(callee, args) = rvalue {
                            let arguments: Vec<Value> =
                                args.iter().map(|arg| read_operand(frame, arg)).collect();
                            let dest = place.clone();
                            let callee = *callee;
                            frames.push(new_frame(self.program, callee, arguments, Some(dest)));
                            continue;
                        }
                        let value = self.eval(frame, cx, rvalue)?;
                        write_place(frame, place, value);
                    }
                    Instr::ScopeEnter => {
                        frame.instr += 1;
                        cx.scope_enter();
                    }
                    Instr::Spawn(operand) => {
                        frame.instr += 1;
                        let value = read_operand(frame, operand);
                        let Value::Task(task) = &value else {
                            return Err(self.trap(frame, "spawned a value that is not a task"));
                        };
                        let moved = moved_resources(&task.kind);
                        cx.spawn(value, &moved)?;
                    }
                }
                continue;
            }

            match &block.term {
                Term::Goto(target) => {
                    frame.block = *target;
                    frame.instr = 0;
                }
                Term::Branch { cond, then, els } => {
                    let taken = match read_operand(frame, cond) {
                        Value::Bool(true) => *then,
                        Value::Bool(false) => *els,
                        other => return Err(self.trap(frame, format!("branch on {other:?}"))),
                    };
                    frame.block = taken;
                    frame.instr = 0;
                }
                Term::SwitchTag {
                    scrutinee,
                    cases,
                    default,
                } => {
                    let value = read_place(frame, scrutinee);
                    let Value::Variant(_, tag, _) = value else {
                        return Err(self.trap(frame, "switch on a value that is not an enum"));
                    };
                    let target = cases
                        .iter()
                        .find(|(candidate, _)| *candidate == tag)
                        .map_or(*default, |(_, block)| *block);
                    frame.block = target;
                    frame.instr = 0;
                }
                Term::Await { task, dest, resume } => {
                    let awaited = read_operand(frame, task);
                    let Value::Task(awaited) = awaited else {
                        return Err(self.trap(frame, "awaited a value that is not a task"));
                    };
                    match &awaited.kind {
                        TaskKind::Fn(callee, args) => {
                            // Resume after the `await` when the callee returns. A task called
                            // inline is a call; only the possibility of parking is new.
                            frame.block = *resume;
                            frame.instr = 0;
                            let callee =
                                new_frame(self.program, *callee, args.to_vec(), Some(dest.clone()));
                            frames.push(callee);
                        }
                        TaskKind::Builtin(builtin, args) => {
                            match self.poll_builtin(cx, *builtin, args)? {
                                Poll::Ready(value) => {
                                    write_place(frame, dest, value);
                                    frame.block = *resume;
                                    frame.instr = 0;
                                }
                                Poll::Pending => return Ok(Step::Park),
                            }
                        }
                    }
                }
                Term::ScopeExit { resume } => match cx.scope_exit() {
                    Poll::Ready(()) => {
                        frame.block = *resume;
                        frame.instr = 0;
                    }
                    Poll::Pending => return Ok(Step::Park),
                },
                Term::Trap(message) => {
                    let message = message.to_string();
                    return Err(self.trap(frame, message));
                }
                Term::Return(operand) => {
                    let value = read_operand(frame, operand);
                    let finished = frames.pop().expect("the frame being returned from");
                    match (finished.dest, frames.last_mut()) {
                        (Some(dest), Some(caller)) => write_place(caller, &dest, value),
                        // The outermost frame returning is the task finishing.
                        _ => return Ok(Step::Done(value)),
                    }
                }
            }
        }
    }

    fn trap(&self, frame: &Frame, message: impl Into<String>) -> Trap {
        Trap::new(message, self.program.fns[frame.function].name.clone())
    }

    fn eval(
        &self,
        frame: &Frame,
        cx: &mut Cx<'_, '_, Value>,
        rvalue: &Rvalue,
    ) -> Result<Value, Trap> {
        Ok(match rvalue {
            Rvalue::Use(operand) => read_operand(frame, operand),
            Rvalue::Unary(op, operand) => match (op, read_operand(frame, operand)) {
                (UnOp::Neg, Value::Int(v)) => Value::Int(v.wrapping_neg()),
                (UnOp::Neg, Value::Float(v)) => Value::Float(-v),
                (UnOp::Not, Value::Bool(v)) => Value::Bool(!v),
                (op, value) => {
                    return Err(self.trap(frame, format!("cannot apply {op:?} to {value:?}")));
                }
            },
            Rvalue::Binary(op, lhs, rhs) => {
                let lhs = read_operand(frame, lhs);
                let rhs = read_operand(frame, rhs);
                self.binary(frame, *op, lhs, rhs)?
            }
            Rvalue::Builtin(builtin, args) => {
                let args: Vec<Value> = args.iter().map(|arg| read_operand(frame, arg)).collect();
                self.builtin(frame, cx, *builtin, &args)?
            }
            Rvalue::Task(id, args) => Value::Task(Rc::new(TaskValue {
                kind: TaskKind::Fn(
                    *id,
                    args.iter().map(|arg| read_operand(frame, arg)).collect(),
                ),
            })),
            Rvalue::BuiltinTask(builtin, args) => Value::Task(Rc::new(TaskValue {
                kind: TaskKind::Builtin(
                    *builtin,
                    args.iter().map(|arg| read_operand(frame, arg)).collect(),
                ),
            })),
            Rvalue::Record(id, args) => {
                let fields = args.iter().map(|arg| read_operand(frame, arg)).collect();
                Value::Record(*id, Rc::new(fields))
            }
            Rvalue::Variant(enum_id, variant, args) => {
                let fields = args.iter().map(|arg| read_operand(frame, arg)).collect();
                Value::Variant(*enum_id, *variant, Rc::new(fields))
            }
            Rvalue::Call(..) => unreachable!("calls are handled by the frame stack"),
        })
    }

    /// The builtins that produce a value immediately. The ones that produce a task are polled at the
    /// `await` that runs them.
    fn builtin(
        &self,
        frame: &Frame,
        cx: &mut Cx<'_, '_, Value>,
        builtin: Builtin,
        args: &[Value],
    ) -> Result<Value, Trap> {
        Ok(match builtin {
            Builtin::Print => {
                let text = self.render(&args[0]);
                cx.print(&text);
                Value::Unit
            }
            Builtin::ListenerPort => {
                let Value::Resource(_, id) = &args[0] else {
                    return Err(
                        self.trap(frame, "`listener_port` of something that is not a listener")
                    );
                };
                match cx.port(*id) {
                    Ok(port) => Value::Int(port),
                    Err(err) => {
                        return Err(self.trap(frame, format!("`listener_port`: {}", err.kind())));
                    }
                }
            }
            task => {
                return Err(self.trap(
                    frame,
                    format!(
                        "`{}` builds a task and cannot be evaluated here",
                        task.name()
                    ),
                ));
            }
        })
    }

    /// Ask the runtime for the effect of a task builtin. `Pending` means the task parks and asks
    /// again when it is woken, which is why nothing here has to remember an operation in flight.
    fn poll_builtin(
        &self,
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
            // Binding does not block, so this answers at once either way.
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
            plain => {
                return Err(Trap::new(
                    format!("`{}` does not build a task", plain.name()),
                    "runtime",
                ));
            }
        })
    }

    fn binary(&self, frame: &Frame, op: BinOp, lhs: Value, rhs: Value) -> Result<Value, Trap> {
        use Value::{Bool, Float, Int, Str};
        Ok(match (op, &lhs, &rhs) {
            (BinOp::AddInt, Int(a), Int(b)) => Int(a.wrapping_add(*b)),
            (BinOp::SubInt, Int(a), Int(b)) => Int(a.wrapping_sub(*b)),
            (BinOp::MulInt, Int(a), Int(b)) => Int(a.wrapping_mul(*b)),
            (BinOp::DivInt, Int(_), Int(0)) => {
                return Err(self.trap(frame, "divide by zero"));
            }
            (BinOp::DivInt, Int(a), Int(b)) => Int(a.wrapping_div(*b)),
            (BinOp::RemInt, Int(_), Int(0)) => {
                return Err(self.trap(frame, "remainder by zero"));
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
                    return Err(self.trap(frame, format!("cannot order {lhs:?} and {rhs:?}")));
                };
                Bool(match op {
                    BinOp::Lt => ordering.is_lt(),
                    BinOp::Le => ordering.is_le(),
                    BinOp::Gt => ordering.is_gt(),
                    _ => ordering.is_ge(),
                })
            }
            (op, a, b) => {
                return Err(self.trap(frame, format!("cannot apply {op:?} to {a:?} and {b:?}")));
            }
        })
    }

    /// Render a value in the surface syntax that would build it. At the top level a string is
    /// its own text — `print` should not add quotes — while nested inside an aggregate it is
    /// quoted, because there the reader needs to see where it starts and ends.
    pub fn render(&self, value: &Value) -> String {
        match value {
            Value::Str(v) => v.to_string(),
            other => self.render_nested(other),
        }
    }

    fn render_nested(&self, value: &Value) -> String {
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
                    TaskKind::Fn(id, _) => self.program.fns[*id].name.as_str(),
                    TaskKind::Builtin(builtin, _) => builtin.name(),
                };
                format!("<task {name}>")
            }
            Value::Resource(kind, id) => format!("<{} {id}>", kind.name()),
            Value::Record(id, fields) => {
                let layout = &self.program.records[*id];
                let mut out = format!("#{}(", layout.name);
                for (index, field) in fields.iter().enumerate() {
                    if index > 0 {
                        out.push_str(", ");
                    }
                    let _ = write!(
                        out,
                        "{}: {}",
                        layout.fields[index],
                        self.render_nested(field)
                    );
                }
                out.push(')');
                out
            }
            Value::Variant(enum_id, tag, fields) => {
                let layout = &self.program.enums[*enum_id];
                let variant = &layout.variants[*tag];
                // `Option` and `Result` are written unqualified in source, so they print that way.
                let builtin =
                    *enum_id == EnumId::OPTION.index() || *enum_id == EnumId::RESULT.index();
                let mut out = if builtin {
                    format!("#{}", variant.name)
                } else {
                    format!("#{}.{}", layout.name, variant.name)
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
                        let _ = write!(out, "{}: ", variant.fields[index]);
                    }
                    out.push_str(&self.render_nested(field));
                }
                out.push(')');
                out
            }
        }
    }
}

/// The resource handles a spawned task is being given. Ownership follows them: the child closes what
/// it was handed, which is the dynamic shadow of the move rule M4 makes static.
///
/// Only handles passed directly are seen. One buried inside a record stays with the parent, which is
/// another thing static ownership will fix rather than something to chase dynamically.
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

/// Wrap what a socket operation returned as a `Result<T, IoError>`.
fn fallible(outcome: io::Result<Value>) -> Value {
    let (variant, fields) = match outcome {
        Ok(value) => (EnumId::OK, vec![value]),
        Err(err) => (EnumId::ERR, vec![io_error_value(&err)]),
    };
    Value::Variant(EnumId::RESULT.index(), variant, Rc::new(fields))
}

/// Map a host I/O error onto the built-in `IoError`. The unknown case carries the host's own name
/// for the condition rather than its message, which varies by platform.
fn io_error_value(err: &io::Error) -> Value {
    use io::ErrorKind as K;
    let (variant, fields) = match err.kind() {
        K::NotFound => (io_error::NOT_FOUND, Vec::new()),
        K::PermissionDenied => (io_error::DENIED, Vec::new()),
        K::AddrInUse | K::AddrNotAvailable => (io_error::IN_USE, Vec::new()),
        K::ConnectionRefused => (io_error::REFUSED, Vec::new()),
        K::ConnectionReset
        | K::ConnectionAborted
        | K::NotConnected
        | K::BrokenPipe
        | K::WriteZero
        | K::UnexpectedEof => (io_error::CLOSED, Vec::new()),
        other => (
            io_error::OTHER,
            vec![Value::Str(format!("{other:?}").into())],
        ),
    };
    Value::Variant(EnumId::IO_ERROR.index(), variant, Rc::new(fields))
}

fn read_operand(frame: &Frame, operand: &Operand) -> Value {
    match operand {
        Operand::Const(value) => match value {
            Const::Unit => Value::Unit,
            Const::Int(v) => Value::Int(*v),
            Const::Float(v) => Value::Float(*v),
            Const::Bool(v) => Value::Bool(*v),
            Const::Str(v) => Value::Str(v.clone()),
        },
        Operand::Copy(place) => read_place(frame, place),
    }
}

fn read_place(frame: &Frame, place: &Place) -> Value {
    let mut value = &frame.locals[place.local];
    for index in &place.proj {
        value = match value {
            Value::Record(_, fields) | Value::Variant(_, _, fields) => &fields[*index],
            // Only reachable if lowering produced a projection the checker did not sanction.
            other => return other.clone(),
        };
    }
    value.clone()
}

fn write_place(frame: &mut Frame, place: &Place, value: Value) {
    let mut slot = &mut frame.locals[place.local];
    for index in &place.proj {
        slot = match slot {
            Value::Record(_, fields) | Value::Variant(_, _, fields) => {
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

/// Render a value without an interpreter in hand. Used by `norn run` to print a result.
pub fn render(program: &Program, value: &Value) -> String {
    Interpreter { program }.render(value)
}
