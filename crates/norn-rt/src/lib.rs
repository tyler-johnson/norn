//! The Norn runtime: one scheduler, generic over the value type.
//!
//! `norn-rt` owns the clock, the timers, the readiness poller, the ready queue, scopes, cancellation, and the
//! resource table. It does not know what a Norn value is: `Runtime<V>` and `trait Body<V>` keep it
//! ignorant of NIR, so the interpreter instantiates `Runtime<interp::Value>` and the generated code
//! of M5 will instantiate its own over whatever it represents values with. Two engines with two
//! schedulers is exactly the divergence `BOOTSTRAP.md` §1 warns about.
//!
//! The runtime is single-threaded and does not steal work. One thread is enough to be honest about
//! suspension, and a second scheduler is the wrong thing to be debugging at the same time as the
//! first.

use std::collections::VecDeque;
use std::io;

pub mod clock;
pub mod graph;
pub mod http;
pub mod poll;
pub mod scope;
pub mod task;
pub mod timer;
pub mod trace;

use crate::graph::{ReactorSpec, ReactorState};
use crate::poll::{PipeProgress, Readiness};
use crate::task::{TaskState, Wait};
use crate::timer::Timers;
use crate::trace::{Event, Trace, WaitReason};

pub use crate::clock::{Clock, Millis};
pub use crate::graph::{Effect, Graph, Handled, NodeSpec, Overflow, ReactorId, Update};
pub use crate::poll::{ResourceId, ResourceKind};
pub use crate::scope::Parent;
pub use crate::task::{Status, TaskId};

/// Where a program's output goes. Tests capture it; `norn run` writes it through. It belongs to the
/// runtime rather than to the interpreter because both execution engines print through the same
/// hole in the world.
pub trait Output {
    fn line(&mut self, text: &str);
}

pub struct Stdout;

impl Output for Stdout {
    fn line(&mut self, text: &str) {
        println!("{text}");
    }
}

#[derive(Default)]
pub struct Captured {
    pub lines: Vec<String>,
}

impl Output for Captured {
    fn line(&mut self, text: &str) {
        self.lines.push(text.to_string());
    }
}

/// A condition the compiler could not rule out. Not a host panic: the runtime reports it the way a
/// native binary will have to, and stops the world.
#[derive(Debug)]
pub struct Trap {
    pub message: String,
    /// Where it happened — the function under the interpreter, the runtime itself otherwise.
    pub function: String,
}

impl Trap {
    pub fn new(message: impl Into<String>, function: impl Into<String>) -> Trap {
        Trap {
            message: message.into(),
            function: function.into(),
        }
    }
}

impl std::fmt::Display for Trap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (in `{}`)", self.message, self.function)
    }
}

/// Something the scheduler can run a slice of.
///
/// One queue rather than two, so that "a reactor takes one input at a time, and a flood of messages
/// cannot starve a task" is a property of the ordering rather than a claim about it. A reactor
/// joins the queue when a message lands in an empty mailbox and rejoins it after its turn if more
/// remain, so everything else runnable goes ahead of its next message.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Runnable {
    Task(TaskId),
    Reactor(ReactorId),
}

/// What one resumption of a task body produced.
pub enum Step<V> {
    Done(V),
    /// Suspended, having registered with `Cx` whatever will wake it.
    Park,
    Trap(Trap),
}

/// The result of asking the runtime for something that may not be available yet. A body that gets
/// `Pending` returns `Step::Park` and is resumed at the same suspension point, where it asks again.
pub enum Poll<T> {
    Ready(T),
    Pending,
}

/// One suspendable computation, as the runtime sees it.
///
/// `resume` runs until the task suspends or finishes. The runtime never resumes a cancelled task:
/// cancellation runs no further user code, and cleanup is the resource table.
pub trait Body<V> {
    fn resume(&mut self, cx: &mut Cx<'_, '_, V>) -> Step<V>;

    /// The name this task is known by in the trace.
    fn name(&self) -> &str;
}

pub struct Config {
    pub clock: Clock,
    pub trace: bool,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            clock: Clock::real(),
            trace: false,
        }
    }
}

impl Config {
    /// Deterministic mode: a virtual clock and a recorded trace. When nothing is runnable and only
    /// timers are pending, the clock jumps to the next deadline instead of sleeping, so a timer test
    /// is instant and its trace is a golden file.
    pub fn deterministic() -> Config {
        Config {
            clock: Clock::simulated(),
            trace: true,
        }
    }
}

/// Everything the runtime cannot know for itself, in one place.
///
/// `make` turns a task value into a runnable body and `graph` evaluates a node; both are the
/// engine's business, because only the engine knows what a value is. `reactors` is the compile-time
/// plan the graph is walked by — plain data, so that holding it costs `norn-rt` no knowledge of NIR.
pub struct Engine<'e, V> {
    pub make: Box<dyn Fn(&V) -> Result<Box<dyn Body<V> + 'e>, Trap> + 'e>,
    pub graph: Box<dyn Graph<V> + 'e>,
    pub reactors: Vec<ReactorSpec>,
}

pub struct Runtime<'e, V> {
    core: Core<'e, V>,
}

impl<'e, V: Clone> Runtime<'e, V> {
    pub fn new(config: Config, out: &'e mut dyn Output, engine: Engine<'e, V>) -> Runtime<'e, V> {
        Runtime {
            core: Core {
                tasks: Vec::new(),
                reactors: Vec::new(),
                ready: VecDeque::new(),
                timers: Timers::default(),
                readiness: Readiness::default(),
                clock: config.clock,
                trace: Trace::new(config.trace),
                out,
                engine,
                root: None,
                result: None,
            },
        }
    }

    /// Run `root` as the root task until it finishes, then tear down anything left standing.
    pub fn block_on(&mut self, root: V) -> Result<V, Trap> {
        let outcome = self.core.drive(root);
        self.core.shutdown();
        outcome
    }

    pub fn trace(&self) -> &Trace {
        &self.core.trace
    }

    pub fn status(&self, task: TaskId) -> Option<Status> {
        self.core.tasks.get(task.index()).map(|state| state.status)
    }
}

/// Everything the runtime owns except the body currently running, which is taken out of the table
/// so that a `Cx` may borrow the rest.
pub(crate) struct Core<'e, V> {
    tasks: Vec<TaskState<'e, V>>,
    pub(crate) reactors: Vec<ReactorState<V>>,
    pub(crate) ready: VecDeque<Runnable>,
    timers: Timers,
    readiness: Readiness,
    clock: Clock,
    trace: Trace,
    out: &'e mut dyn Output,
    pub(crate) engine: Engine<'e, V>,
    root: Option<TaskId>,
    result: Option<V>,
}

impl<'e, V: Clone> Core<'e, V> {
    pub(crate) fn state(&self, task: TaskId) -> &TaskState<'e, V> {
        &self.tasks[task.index()]
    }

    pub(crate) fn state_mut(&mut self, task: TaskId) -> &mut TaskState<'e, V> {
        &mut self.tasks[task.index()]
    }

    pub(crate) fn emit(&mut self, event: Event) {
        if self.trace.enabled() {
            let at = self.clock.now();
            self.trace.push(at, event);
        }
    }

    // ---------------------------------------------------------------- the loop

    fn drive(&mut self, root: V) -> Result<V, Trap> {
        let root = self.spawn(root, None, &[])?;
        self.root = Some(root);

        loop {
            while let Some(next) = self.ready.pop_front() {
                match next {
                    Runnable::Task(task) => {
                        if self.state(task).status != Status::Ready {
                            continue;
                        }
                        self.step(task)?;
                    }
                    Runnable::Reactor(reactor) => self.turn(reactor)?,
                }
                if let Some(value) = self.result.take() {
                    return Ok(value);
                }
            }
            if self.state(root).status.finished() {
                // The root cannot be cancelled — nothing owns it — so it finished with a value.
                return self.result.take().ok_or_else(|| self.stuck(root));
            }
            self.wait()?;
        }
    }

    fn step(&mut self, task: TaskId) -> Result<(), Trap> {
        self.emit(Event::Resume { task });
        let Some(mut body) = self.state_mut(task).body.take() else {
            return Ok(());
        };
        let step = {
            let mut cx = Cx { core: self, task };
            body.resume(&mut cx)
        };
        self.state_mut(task).body = Some(body);

        match step {
            Step::Done(value) => {
                self.finish(task, value);
                Ok(())
            }
            Step::Park => {
                let wait = match &self.state(task).wait {
                    Some(Wait::Timer(deadline)) => WaitReason::Timer(*deadline),
                    Some(Wait::Io { resource, write }) if *write => WaitReason::Write(*resource),
                    Some(Wait::Io { resource, .. }) => WaitReason::Read(*resource),
                    Some(Wait::Mailbox(reactor)) => WaitReason::Mailbox(*reactor),
                    None => WaitReason::Nothing,
                };
                self.state_mut(task).status = Status::Parked;
                self.emit(Event::Park { task, wait });
                Ok(())
            }
            Step::Trap(trap) => Err(trap),
        }
    }

    /// Nothing is runnable: let time pass, or wait for a descriptor, and wake whatever that frees.
    fn wait(&mut self) -> Result<(), Trap> {
        let deadline = self.timers.earliest();
        if self.readiness.is_idle() {
            let Some(deadline) = deadline else {
                let root = self.root.expect("the root is spawned before the loop runs");
                return Err(self.stuck(root));
            };
            if self.clock.wait_until(deadline) {
                self.emit(Event::Clock);
            }
        } else {
            let timeout = deadline.map(|at| at.saturating_sub(self.clock.now()));
            let woken = self
                .readiness
                .wait(timeout)
                .map_err(|err| Trap::new(format!("waiting for readiness: {err}"), "runtime"))?;
            let timed_out = woken.is_empty();
            for task in woken {
                self.wake(task);
            }
            // A virtual clock still has to arrive at the deadline the wait was cut short by.
            if timed_out
                && let Some(deadline) = deadline
                && self.clock.wait_until(deadline)
            {
                self.emit(Event::Clock);
            }
        }

        let now = self.clock.now();
        while let Some(task) = self.timers.due(now) {
            self.wake(task);
        }
        Ok(())
    }

    /// Make a parked task runnable. The reason it parked stays on the task: the body re-executes
    /// the suspension point and asks again, which is what tells it the wait is over.
    fn wake(&mut self, task: TaskId) {
        if self.state(task).status != Status::Parked {
            return;
        }
        self.state_mut(task).status = Status::Ready;
        self.ready.push_back(Runnable::Task(task));
    }

    fn stuck(&self, task: TaskId) -> Trap {
        Trap::new(
            "every task is waiting and nothing can wake them",
            self.state(task).name.clone(),
        )
    }
}

/// What a task body may ask of the runtime while it is running.
pub struct Cx<'c, 'e, V> {
    core: &'c mut Core<'e, V>,
    task: TaskId,
}

impl<'e, V: Clone> Cx<'_, 'e, V> {
    pub fn task(&self) -> TaskId {
        self.task
    }

    pub fn print(&mut self, text: &str) {
        self.core.out.line(text);
    }

    // ---------------------------------------------------------------- time

    pub fn sleep(&mut self, millis: i64) -> Poll<()> {
        let deadline = match &self.core.state(self.task).wait {
            Some(Wait::Timer(deadline)) => *deadline,
            _ => {
                let deadline = self.core.clock.now() + millis.max(0) as Millis;
                self.core.state_mut(self.task).wait = Some(Wait::Timer(deadline));
                self.core.timers.arm(deadline, self.task);
                return Poll::Pending;
            }
        };
        if self.core.clock.now() >= deadline {
            self.core.state_mut(self.task).wait = None;
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }

    // ---------------------------------------------------------------- sockets

    pub fn listen(&mut self, port: i64) -> io::Result<ResourceId> {
        if !(0..=u16::MAX as i64).contains(&port) {
            return Err(io::Error::from(io::ErrorKind::InvalidInput));
        }
        let id = self.core.readiness.listen(port as u16)?;
        self.take_ownership(id);
        Ok(id)
    }

    pub fn port(&mut self, listener: ResourceId) -> io::Result<i64> {
        self.core.readiness.port(listener).map(|port| port as i64)
    }

    pub fn accept(&mut self, listener: ResourceId) -> Poll<io::Result<ResourceId>> {
        match self.core.readiness.accept(listener) {
            Ok(Some(id)) => {
                self.finish_wait();
                self.take_ownership(id);
                Poll::Ready(Ok(id))
            }
            Ok(None) => self.park_on(listener, false),
            Err(err) => {
                self.finish_wait();
                Poll::Ready(Err(err))
            }
        }
    }

    pub fn read(&mut self, connection: ResourceId) -> Poll<io::Result<Vec<u8>>> {
        match self.core.readiness.read_bytes(connection) {
            Ok(Some(bytes)) => {
                self.finish_wait();
                Poll::Ready(Ok(bytes))
            }
            Ok(None) => self.park_on(connection, false),
            Err(err) => {
                self.finish_wait();
                Poll::Ready(Err(err))
            }
        }
    }

    pub fn write(&mut self, connection: ResourceId, data: &[u8]) -> Poll<io::Result<()>> {
        match self.core.readiness.write(connection, data) {
            Ok(Some(())) => {
                self.finish_wait();
                Poll::Ready(Ok(()))
            }
            Ok(None) => self.park_on(connection, true),
            Err(err) => {
                self.finish_wait();
                Poll::Ready(Err(err))
            }
        }
    }

    // ---------------------------------------------------------------- files and flows

    pub fn file_create(&mut self, path: &str) -> io::Result<ResourceId> {
        let id = self.core.readiness.file_create(path)?;
        self.take_ownership(id);
        Ok(id)
    }

    pub fn flow_of_file(&mut self, path: &str) -> io::Result<ResourceId> {
        let id = self.core.readiness.flow_of_file(path)?;
        self.take_ownership(id);
        Ok(id)
    }

    /// Write a whole buffer to a file. A regular file is always ready under `poll(2)`, so this
    /// completes in one call rather than parking.
    pub fn file_write(&mut self, file: ResourceId, data: &[u8]) -> io::Result<()> {
        self.core.readiness.file_write(file, data)
    }

    /// One chunk of a flow, for a consumer written in Norn. An empty chunk means the flow is
    /// exhausted. A file-backed flow is always ready and never parks; a request-body flow parks
    /// reading on the stream its bytes arrive on.
    pub fn flow_next(&mut self, flow: ResourceId) -> Poll<io::Result<Vec<u8>>> {
        match self.core.readiness.flow_read(flow) {
            Ok(Some(chunk)) => {
                self.finish_wait();
                Poll::Ready(Ok(chunk))
            }
            Ok(None) => self.park_on(flow, false),
            Err(err) => {
                self.finish_wait();
                Poll::Ready(Err(err))
            }
        }
    }

    /// How many bytes the flow still promises to deliver.
    pub fn flow_len(&mut self, flow: ResourceId) -> io::Result<i64> {
        self.core.readiness.flow_len(flow).map(|len| len as i64)
    }

    /// Drive `flow` into `sink` until everything the flow promised has arrived. One trace line per
    /// delivered chunk; all transfer state lives in the flow's table entry, so a parked transfer
    /// resumes by asking again. Completion — and failure — consumes both ends: the language moved
    /// them into this call, so nothing can legally touch either again, and the close happens here
    /// rather than at whenever the owning scope ends.
    pub fn pipe(&mut self, flow: ResourceId, sink: ResourceId) -> Poll<io::Result<i64>> {
        loop {
            match self.core.readiness.pipe_step(flow, sink) {
                Ok(PipeProgress::Chunk(bytes)) => {
                    let task = self.task;
                    self.core.emit(Event::Pipe {
                        task,
                        source: flow,
                        sink,
                        bytes,
                    });
                }
                Ok(PipeProgress::Done(total)) => {
                    self.finish_wait();
                    self.close(flow);
                    self.close(sink);
                    return Poll::Ready(Ok(total as i64));
                }
                Ok(PipeProgress::ParkWrite(on)) => return self.park_on(on, true),
                Ok(PipeProgress::ParkRead(on)) => return self.park_on(on, false),
                Err(err) => {
                    self.finish_wait();
                    self.close(flow);
                    self.close(sink);
                    return Poll::Ready(Err(err));
                }
            }
        }
    }

    /// Register interest and park. `Pending` is returned as whatever the caller's result type is,
    /// because the value only ever arrives on a later attempt.
    fn park_on<T>(&mut self, resource: ResourceId, write: bool) -> Poll<io::Result<T>> {
        match self.core.readiness.watch(resource, write, self.task) {
            Ok(()) => {
                self.core.state_mut(self.task).wait = Some(Wait::Io { resource, write });
                Poll::Pending
            }
            Err(err) => {
                self.finish_wait();
                Poll::Ready(Err(err))
            }
        }
    }

    fn finish_wait(&mut self) {
        self.core.state_mut(self.task).wait = None;
        self.core.readiness.clear(self.task);
    }
}
