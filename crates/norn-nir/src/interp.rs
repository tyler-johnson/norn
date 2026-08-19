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

use std::cell::RefCell;

use norn_hir::hir;
use norn_hir::hir::{BinOp, Builtin, EnumId, UnOp, io_error};
use norn_rt::graph::{Handled, InputSpec, NodeSpec, ReactorSpec};
use norn_rt::{Body, Cx, Effect, Engine, Graph, ReactorId, Runtime, Step, Update};

pub use norn_rt::{Captured, Clock, Config, Output, Poll, ResourceId, ResourceKind, Stdout, Trap};

use crate::nir::*;

/// Mirrored in `norn-codegen/src/prelude.rs`, variant names included: trap messages interpolate
/// `{:?}` of these, so a rename here is a byte difference the differential oracle catches in
/// stderr.
#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    Unit,
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Rc<str>),
    Bytes(Rc<[u8]>),
    Struct(usize, Rc<Vec<Value>>),
    Variant(usize, usize, Rc<Vec<Value>>),
    /// A computation that has not run. `await` and `spawn` are what start it.
    Task(Rc<TaskValue>),
    /// A handle into the runtime's resource table.
    Resource(ResourceKind, ResourceId),
    /// A handle to a running reactor.
    Reactor(ReactorId),
    /// One of its inputs, as a value `send` can be handed.
    Input(ReactorId, usize),
    /// One of its exported signals, as a value `latest` can read.
    Signal(ReactorId, usize),
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
    let engine = Engine {
        make: Box::new(move |value| body(program, value)),
        graph: Box::new(Nodes { program }),
        reactors: specs(program),
    };
    let mut runtime = Runtime::new(config, out, engine);
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
        let interpreter = Interpreter::new(self.program);
        let stepped = match &mut self.state {
            State::Frames(frames) => interpreter.resume_task(frames, Some(cx)),
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
    /// Where a handler's slot writes and effect requests accumulate.
    ///
    /// `None` everywhere else, which is the second reason `SetSlot` and `Emit` cannot appear in
    /// ordinary code: `lower`'s verifier rejects them statically, and reaching one with nothing to
    /// put it in traps.
    turn: Option<RefCell<Handled<Value>>>,
}

impl<'p> Interpreter<'p> {
    fn new(program: &'p Program) -> Interpreter<'p> {
        Interpreter {
            program,
            turn: None,
        }
    }

    /// Run a plain function to completion with no runtime in reach.
    ///
    /// This is the whole of how a turn evaluates anything. Passing `None` for the `Cx` is not a
    /// convention the evaluator follows — it is the absence of the thing every impure arm needs, so
    /// there is no path from here to printing, spawning, or suspending.
    fn call(&self, function: FnId, args: Vec<Value>) -> Result<Value, Trap> {
        let mut frames = vec![new_frame(self.program, function, args, None)];
        match self.resume_task(&mut frames, None)? {
            Step::Done(value) => Ok(value),
            // Unreachable: every suspension point asks for a `Cx` first and traps without one.
            Step::Park => Err(Trap::new("a reactor node suspended", "turn")),
            Step::Trap(trap) => Err(trap),
        }
    }
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
        mut cx: Option<&mut Cx<'_, '_, Value>>,
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
                        let value = self.eval(frame, cx.as_deref_mut(), rvalue)?;
                        write_place(frame, place, value);
                    }
                    Instr::ScopeEnter => {
                        frame.instr += 1;
                        impure(cx.as_deref_mut(), "scope")?.scope_enter();
                    }
                    Instr::Spawn(operand) => {
                        frame.instr += 1;
                        let value = read_operand(frame, operand);
                        let Value::Task(task) = &value else {
                            return Err(self.trap(frame, "spawned a value that is not a task"));
                        };
                        let moved = moved_resources(&task.kind);
                        impure(cx.as_deref_mut(), "spawn")?.spawn(value, &moved)?;
                    }
                    Instr::SpawnReactor {
                        dest,
                        reactor,
                        args,
                    } => {
                        frame.instr += 1;
                        let args: Vec<Value> =
                            args.iter().map(|arg| read_operand(frame, arg)).collect();
                        let id = impure(cx.as_deref_mut(), "spawn reactor")?
                            .create_reactor(*reactor, args)?;
                        let dest = dest.clone();
                        write_place(frame, &dest, Value::Reactor(id));
                    }
                    Instr::SetSlot(slot, operand) => {
                        frame.instr += 1;
                        let value = read_operand(frame, operand);
                        let Some(turn) = &self.turn else {
                            return Err(self.trap(frame, "a state commit outside a turn"));
                        };
                        turn.borrow_mut().writes.push((*slot, value));
                    }
                    Instr::Emit { task, returns } => {
                        frame.instr += 1;
                        let value = read_operand(frame, task);
                        let Some(turn) = &self.turn else {
                            return Err(self.trap(frame, "an effect request outside a turn"));
                        };
                        // Built, not started. The runtime launches it after the snapshot is
                        // published, so describing it here cannot perform it.
                        turn.borrow_mut().effects.push(Effect {
                            task: value,
                            returns: *returns,
                        });
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
                            let cx = impure(cx.as_deref_mut(), builtin.name())?;
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
                Term::ScopeExit { resume } => {
                    match impure(cx.as_deref_mut(), "scope")?.scope_exit() {
                        Poll::Ready(()) => {
                            frame.block = *resume;
                            frame.instr = 0;
                        }
                        Poll::Pending => return Ok(Step::Park),
                    }
                }
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
        cx: Option<&mut Cx<'_, '_, Value>>,
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
            Rvalue::Struct(id, args) => {
                let fields = args.iter().map(|arg| read_operand(frame, arg)).collect();
                Value::Struct(*id, Rc::new(fields))
            }
            Rvalue::Variant(enum_id, variant, args) => {
                let fields = args.iter().map(|arg| read_operand(frame, arg)).collect();
                Value::Variant(*enum_id, *variant, Rc::new(fields))
            }
            Rvalue::ReactorInput(operand, index) => match read_operand(frame, operand) {
                Value::Reactor(id) => Value::Input(id, *index),
                other => {
                    return Err(self.trap(frame, format!("not a reactor handle: {other:?}")));
                }
            },
            Rvalue::ReactorExport(operand, index) => match read_operand(frame, operand) {
                Value::Reactor(id) => Value::Signal(id, *index),
                other => {
                    return Err(self.trap(frame, format!("not a reactor handle: {other:?}")));
                }
            },
            Rvalue::Call(..) => unreachable!("calls are handled by the frame stack"),
        })
    }

    /// The builtins that produce a value immediately. The ones that produce a task are polled at the
    /// `await` that runs them.
    fn builtin(
        &self,
        frame: &Frame,
        cx: Option<&mut Cx<'_, '_, Value>>,
        builtin: Builtin,
        args: &[Value],
    ) -> Result<Value, Trap> {
        Ok(match builtin {
            Builtin::Print => {
                let text = self.render(&args[0]);
                impure(cx, "print")?.print(&text);
                Value::Unit
            }
            Builtin::ListenerPort => {
                let Value::Resource(_, id) = &args[0] else {
                    return Err(
                        self.trap(frame, "`listener_port` of something that is not a listener")
                    );
                };
                match impure(cx, "listener_port")?.port(*id) {
                    Ok(port) => Value::Int(port),
                    Err(err) => {
                        return Err(self.trap(frame, format!("`listener_port`: {}", err.kind())));
                    }
                }
            }
            Builtin::Latest => {
                let Value::Signal(reactor, export) = &args[0] else {
                    return Err(self.trap(frame, "`latest` of something that is not a signal"));
                };
                let (reactor, export) = (*reactor, *export);
                match impure(cx, "latest")?.latest(reactor, export) {
                    Some(value) => value,
                    None => {
                        return Err(self.trap(frame, "`latest` of an export that does not exist"));
                    }
                }
            }
            Builtin::RequestMethod => {
                let id = resource("request_method", &args[0])?;
                match impure(cx, "request_method")?.request_method(id) {
                    Ok(method) => Value::Str(method.into()),
                    // Unreachable from a checked program — the borrow keeps the request alive —
                    // but the wording is ABI all the same, mirrored in the prelude.
                    Err(err) => {
                        return Err(self.trap(frame, format!("`request_method`: {}", err.kind())));
                    }
                }
            }
            Builtin::RequestPath => {
                let id = resource("request_path", &args[0])?;
                match impure(cx, "request_path")?.request_path(id) {
                    Ok(path) => Value::Str(path.into()),
                    Err(err) => {
                        return Err(self.trap(frame, format!("`request_path`: {}", err.kind())));
                    }
                }
            }
            Builtin::RequestHeader => {
                let id = resource("request_header", &args[0])?;
                let name = text("request_header", &args[1])?;
                match impure(cx, "request_header")?.request_header(id, &name) {
                    Ok(Some(value)) => Value::Variant(
                        EnumId::OPTION.index(),
                        EnumId::SOME,
                        Rc::new(vec![Value::Str(value.into())]),
                    ),
                    Ok(None) => {
                        Value::Variant(EnumId::OPTION.index(), EnumId::NONE, Rc::new(Vec::new()))
                    }
                    Err(err) => {
                        return Err(self.trap(frame, format!("`request_header`: {}", err.kind())));
                    }
                }
            }
            Builtin::RequestBody => {
                let id = resource("request_body", &args[0])?;
                match impure(cx, "request_body")?.request_body(id) {
                    Ok(flow) => Value::Resource(ResourceKind::Flow, flow),
                    Err(trap) => return Err(trap),
                }
            }
            Builtin::Bytes => Value::Bytes(text("bytes", &args[0])?.into_bytes().into()),
            Builtin::BytesLen => Value::Int(blob("bytes_len", &args[0])?.len() as i64),
            Builtin::BytesSlice => {
                let data = blob("bytes_slice", &args[0])?;
                let start = integer("bytes_slice", &args[1])?;
                let end = integer("bytes_slice", &args[2])?;
                let len = data.len() as i64;
                if start < 0 || end < start || end > len {
                    return Err(self.trap(
                        frame,
                        format!("`bytes_slice` out of range: {start}..{end} of {len}"),
                    ));
                }
                // A slice copies in v0: a clone-everything engine cannot make zero-copy
                // observable, so the cheap representation waits for typed layout (§8).
                Value::Bytes(data[start as usize..end as usize].into())
            }
            Builtin::Byte => {
                let value = integer("byte", &args[0])?;
                if value < 0 || value > 255 {
                    return Err(self.trap(frame, format!("`byte` out of range: {value}")));
                }
                Value::Bytes([value as u8].into())
            }
            Builtin::BytesConcat => {
                let a = blob("bytes_concat", &args[0])?;
                let b = blob("bytes_concat", &args[1])?;
                // Concatenation copies in v0, like `bytes_slice`: the cheap representation
                // waits for typed layout (§8).
                Value::Bytes([&a[..], &b[..]].concat().into())
            }
            Builtin::BytesAt => {
                let data = blob("bytes_at", &args[0])?;
                let index = integer("bytes_at", &args[1])?;
                let len = data.len() as i64;
                if index < 0 || index >= len {
                    return Err(
                        self.trap(frame, format!("byte index out of range: {index} of {len}"))
                    );
                }
                Value::Int(data[index as usize] as i64)
            }
            Builtin::TextUnchecked => {
                let data = blob("text_unchecked", &args[0])?;
                match std::str::from_utf8(&data) {
                    Ok(text) => Value::Str(text.into()),
                    Err(err) => {
                        return Err(self.trap(
                            frame,
                            format!(
                                "`text_unchecked` given invalid UTF-8 at byte {}",
                                err.valid_up_to()
                            ),
                        ));
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
                    Poll::Ready(fallible(outcome.map(|data| Value::Bytes(data.into()))))
                }
                Poll::Pending => Poll::Pending,
            },
            Builtin::TcpWrite => {
                let connection = resource(name, &args[0])?;
                let data = blob(name, &args[1])?;
                match cx.write(connection, &data) {
                    Poll::Ready(outcome) => Poll::Ready(fallible(outcome.map(|()| Value::Unit))),
                    Poll::Pending => Poll::Pending,
                }
            }
            Builtin::TcpClose => {
                cx.close(resource(name, &args[0])?);
                Poll::Ready(Value::Unit)
            }
            // Creating and opening do not block, so these answer at once either way.
            Builtin::FileCreate => Poll::Ready(fallible(
                cx.file_create(&text(name, &args[0])?)
                    .map(|id| Value::Resource(ResourceKind::File, id)),
            )),
            Builtin::FlowOfFile => Poll::Ready(fallible(
                cx.flow_of_file(&text(name, &args[0])?)
                    .map(|id| Value::Resource(ResourceKind::Flow, id)),
            )),
            Builtin::PipeTo => {
                let flow = resource(name, &args[0])?;
                let sink = resource(name, &args[1])?;
                match cx.pipe(flow, sink) {
                    Poll::Ready(outcome) => Poll::Ready(fallible(outcome.map(Value::Int))),
                    Poll::Pending => Poll::Pending,
                }
            }
            Builtin::HttpReadRequest => match cx.http_read_request(resource(name, &args[0])?) {
                Poll::Ready(outcome) => Poll::Ready(fallible(
                    outcome.map(|id| Value::Resource(ResourceKind::Request, id)),
                )),
                Poll::Pending => Poll::Pending,
            },
            Builtin::HttpRespond => {
                let request = resource(name, &args[0])?;
                let status = status(name, &args[1])?;
                let body = text(name, &args[2])?;
                match cx.http_respond(request, status, &body) {
                    Poll::Ready(outcome) => Poll::Ready(fallible(outcome.map(|()| Value::Unit))),
                    Poll::Pending => Poll::Pending,
                }
            }
            Builtin::HttpRespondEmpty => {
                let request = resource(name, &args[0])?;
                let status = status(name, &args[1])?;
                match cx.http_respond(request, status, "") {
                    Poll::Ready(outcome) => Poll::Ready(fallible(outcome.map(|()| Value::Unit))),
                    Poll::Pending => Poll::Pending,
                }
            }
            Builtin::HttpRespondFlow => {
                let request = resource(name, &args[0])?;
                let status = status(name, &args[1])?;
                let flow = resource(name, &args[2])?;
                match cx.http_respond_flow(request, status, flow) {
                    Poll::Ready(outcome) => Poll::Ready(fallible(outcome.map(|()| Value::Unit))),
                    Poll::Pending => Poll::Pending,
                }
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
                    (Value::Bytes(a), Value::Bytes(b)) => a.partial_cmp(b),
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
            Value::Bytes(v) => format!("<bytes {}>", v.len()),
            Value::Task(task) => {
                let name = match &task.kind {
                    TaskKind::Fn(id, _) => self.program.fns[*id].name.as_str(),
                    TaskKind::Builtin(builtin, _) => builtin.name(),
                };
                format!("<task {name}>")
            }
            Value::Resource(kind, id) => format!("<{} {id}>", kind.name()),
            Value::Reactor(id) => format!("<reactor {id}>"),
            Value::Input(id, index) => format!("<input {index} of {id}>"),
            Value::Signal(id, index) => format!("<signal {index} of {id}>"),
            Value::Struct(id, fields) => {
                let layout = &self.program.structs[*id];
                let mut out = format!("{}(", layout.name);
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
/// Only handles passed directly are seen. One buried inside a struct stays with the parent, which is
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

/// Reach the runtime, or trap because there is none.
///
/// A turn evaluates node bodies with no `Cx` at all, so every arm of the interpreter that could be
/// observed from outside — printing, spawning, opening a scope, polling a task builtin — is exactly
/// an arm that has to ask for one. That makes purity a property of what the evaluator was *handed*
/// rather than a rule it remembers to follow, and it is why one walker serves both.
///
/// Reaching here is a compiler bug, not a user error: `check_reactors` rejects an impure call
/// against the source with a span, and `lower` rejects it again against the node's blocks. This is
/// the third line, and it exists so that a hole in either of the first two surfaces as a trap rather
/// than as a turn that quietly printed something.
fn impure<'a, 'c, 'e, V>(
    cx: Option<&'a mut Cx<'c, 'e, V>>,
    what: &str,
) -> Result<&'a mut Cx<'c, 'e, V>, Trap> {
    cx.ok_or_else(|| {
        Trap::new(
            format!("`{what}` cannot run during a turn: a reactor node is pure"),
            "turn",
        )
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

/// A status code the wire can carry: HTTP's status line is exactly three digits. The trap is
/// unreachable through the differential oracle — reaching it needs a socket — so the wording is
/// pinned by being the same source string here and in the prelude.
fn status(builtin: &str, value: &Value) -> Result<i64, Trap> {
    let status = integer(builtin, value)?;
    if !(100..=999).contains(&status) {
        return Err(Trap::new(
            format!("`{builtin}` status must be 100..=999, found {status}"),
            "runtime",
        ));
    }
    Ok(status)
}

fn blob(builtin: &str, value: &Value) -> Result<Rc<[u8]>, Trap> {
    match value {
        Value::Bytes(data) => Ok(data.clone()),
        other => Err(Trap::new(
            format!("`{builtin}` wanted bytes, found {other:?}"),
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
            Value::Struct(_, fields) | Value::Variant(_, _, fields) => &fields[*index],
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

/// Render a value without an interpreter in hand. Used by `norn run` to print a result.
pub fn render(program: &Program, value: &Value) -> String {
    Interpreter::new(program).render(value)
}

/// The interpreter as the runtime's graph engine.
///
/// Every method here takes values and returns values, because that is all `trait Graph<V>` offers.
/// There is no `Cx` to reach for, so purity is not a rule this implementation follows — it is a
/// shape it could not break if it tried.
struct Nodes<'p> {
    program: &'p Program,
}

impl Graph<Value> for Nodes<'_> {
    fn create(&self, reactor: usize, args: Vec<Value>) -> Result<Vec<Value>, Trap> {
        let def = &self.program.reactors[reactor];
        let interpreter = Interpreter::new(self.program);
        // Parameters come before state in slot order, and an initialiser may read only parameters,
        // so one pass in slot order is enough: everything an initialiser can name is already there.
        let mut values: Vec<Option<Value>> = vec![None; def.nodes.len()];
        for &node in &def.slots {
            let value = match &def.nodes[node].kind {
                NodeKind::Param { index, .. } => args.get(*index).cloned().ok_or_else(|| {
                    Trap::new("a reactor was created with too few arguments", "runtime")
                })?,
                NodeKind::State { init, .. } => {
                    let mut deps = Vec::with_capacity(def.nodes[node].deps.len());
                    for &dep in &def.nodes[node].deps {
                        let Some(value) = &values[dep] else {
                            return Err(Trap::new(
                                "a state initialiser read a value that is not ready",
                                "runtime",
                            ));
                        };
                        deps.push(value.clone());
                    }
                    interpreter.call(*init, deps)?
                }
                NodeKind::Signal { .. } => unreachable!("a signal holds no slot"),
            };
            values[node] = Some(value);
        }
        Ok(def
            .slots
            .iter()
            .map(|node| values[*node].clone().expect("just filled"))
            .collect())
    }

    fn handle(
        &self,
        reactor: usize,
        input: usize,
        message: Value,
        slots: &[Value],
    ) -> Result<Handled<Value>, Trap> {
        let function = self.program.reactors[reactor].inputs[input].handler;
        // An input carrying `()` binds nothing, so the handler's arity says whether the message is
        // one of its arguments.
        let mut args = Vec::with_capacity(slots.len() + 1);
        if self.program.fns[function].params == slots.len() + 1 {
            args.push(message);
        }
        args.extend(slots.iter().cloned());

        let interpreter = Interpreter {
            program: self.program,
            turn: Some(RefCell::new(Handled {
                writes: Vec::new(),
                effects: Vec::new(),
            })),
        };
        interpreter.call(function, args)?;
        Ok(interpreter.turn.expect("just installed").into_inner())
    }

    fn recompute(
        &self,
        reactor: usize,
        node: usize,
        deps: &[Value],
    ) -> Result<Update<Value>, Trap> {
        let NodeKind::Signal { body } = self.program.reactors[reactor].nodes[node].kind else {
            return Err(Trap::new(
                "recomputed a node that is not a signal",
                "runtime",
            ));
        };
        let value = Interpreter::new(self.program).call(body, deps.to_vec())?;
        // Always `Set`: deciding a value is unchanged needs an equality on `Value`, and the only
        // pruning v0 does is the static one — each input's plan.
        Ok(Update::Set(value))
    }
}

/// The declared overflow policy, in the runtime's vocabulary.
///
/// Spelled twice on purpose. `norn-rt` may not depend on the front end — the same category of
/// decision as `ResourceKind` — so the translation is one match rather than a shared crate, and a
/// new policy has to be added on both sides deliberately.
fn overflow(policy: hir::Overflow) -> norn_rt::Overflow {
    match policy {
        hir::Overflow::Reject => norn_rt::Overflow::Reject,
        hir::Overflow::DropOldest => norn_rt::Overflow::DropOldest,
        hir::Overflow::DropNewest => norn_rt::Overflow::DropNewest,
        hir::Overflow::Wait => norn_rt::Overflow::Wait,
    }
}

/// The graph, as the runtime consumes it: names, indices, and enums, with nothing of NIR in it.
fn specs(program: &Program) -> Vec<ReactorSpec> {
    program
        .reactors
        .iter()
        .map(|reactor| ReactorSpec {
            name: reactor.name.clone(),
            nodes: reactor
                .nodes
                .iter()
                .map(|node| NodeSpec {
                    name: node.name.clone(),
                    deps: node.deps.clone(),
                    slot: node.kind.slot(),
                })
                .collect(),
            slots: reactor.slots.clone(),
            inputs: reactor
                .inputs
                .iter()
                .map(|input| InputSpec {
                    name: input.name.clone(),
                    capacity: input.capacity,
                    overflow: overflow(input.overflow),
                    plan: input.plan.clone(),
                })
                .collect(),
            order: reactor.order.clone(),
            exports: reactor.exports.clone(),
        })
        .collect()
}
