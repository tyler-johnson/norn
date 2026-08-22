//! The event trace.
//!
//! `BOOTSTRAP.md` §6 says to build the trace format before the thing it describes. Task lifecycle is
//! where it starts: cancellation and scheduling are close to untestable without it, the alternative
//! being assertions about timing and socket side effects. M3 layers reactor turns onto the same
//! file, and M5 diffs the native backend against it.
//!
//! One event per line, `<time>ms <task> <what>`, with `--` for events that belong to the runtime
//! rather than to any task. Under a virtual clock the whole file is deterministic, which is what
//! makes it a golden artifact rather than a log.

use crate::clock::Millis;
use crate::graph::{Overflow, ReactorId};
use crate::poll::{ResourceId, ResourceKind};
use crate::task::TaskId;

pub enum Event {
    Spawn {
        task: TaskId,
        parent: Option<TaskId>,
        name: String,
    },
    Resume {
        task: TaskId,
    },
    Park {
        task: TaskId,
        wait: WaitReason,
    },
    Done {
        task: TaskId,
    },
    Cancel {
        task: TaskId,
    },
    ScopeEnter {
        task: TaskId,
        depth: usize,
    },
    ScopeExit {
        task: TaskId,
        depth: usize,
    },
    Open {
        task: TaskId,
        resource: ResourceId,
        kind: ResourceKind,
    },
    Close {
        task: TaskId,
        resource: ResourceId,
    },
    /// A resource handle passed to a spawned task, which becomes its owner. The dynamic shadow of
    /// the move rule M4 makes static.
    Move {
        task: TaskId,
        resource: ResourceId,
        from: TaskId,
    },
    /// A virtual clock arriving at the next deadline because nothing else could run.
    Clock,

    // ------------------------------------------------------------------ reactors
    //
    // No event carries a `V`. `Trace` must not become generic — it is shared by both engines, and
    // an engine's value type is the one thing it may not know — and the determinism claim is about
    // *order* anyway. What a node computed is the program's output; that it computed when it did,
    // once, before publication, is what these lines are for.
    ReactorCreated {
        reactor: ReactorId,
        name: String,
        owner: TaskId,
    },
    /// The `init` body running, between creation and the publication of version 0. No sequence
    /// number: creation is the turn before the numbered ones, and message turns still start at 0.
    /// Emitted only by a reactor that declares an `init`.
    Init {
        reactor: ReactorId,
    },
    /// One message taken from the mailbox. The sequence number is reactor-local and the reason
    /// "serial turns" is a thing a reader can check rather than a thing the runtime asserts.
    Turn {
        reactor: ReactorId,
        seq: u64,
        input: String,
    },
    /// One node updated, in propagation order: a state cell committed by the handler, or a signal
    /// recomputed from its dependencies.
    Node {
        reactor: ReactorId,
        node: String,
        commit: bool,
    },
    /// The snapshot swap. Everything before it in this turn is invisible from outside; everything
    /// after it is a consequence.
    Publish {
        reactor: ReactorId,
        version: u64,
    },
    /// An effect request becoming a task — always after the publish of the turn that asked for it.
    Effect {
        reactor: ReactorId,
        task: TaskId,
        name: String,
        returns: Option<String>,
    },
    /// A message meeting a full mailbox, and what the declared policy did about it.
    Overflow {
        reactor: ReactorId,
        input: String,
        policy: Overflow,
    },
    ReactorClosed {
        reactor: ReactorId,
    },
}

pub enum WaitReason {
    Timer(Millis),
    Read(ResourceId),
    Write(ResourceId),
    Mailbox(ReactorId),
    /// A task that parked without registering anything to wake it. The scheduler reports this as a
    /// stuck program rather than waiting forever, but the trace records it where it happened.
    Nothing,
}

impl WaitReason {
    fn text(&self) -> String {
        match self {
            WaitReason::Timer(deadline) => format!("timer {deadline}ms"),
            WaitReason::Read(resource) => format!("read {resource}"),
            WaitReason::Write(resource) => format!("write {resource}"),
            WaitReason::Mailbox(reactor) => format!("mailbox {reactor}"),
            WaitReason::Nothing => "nothing".into(),
        }
    }
}

/// Who a line is about. A trace is read down the subject column, so an event that belongs to no one
/// in particular has to say so rather than borrow the last task's name.
pub enum Subject {
    Task(TaskId),
    Reactor(ReactorId),
    /// The runtime itself: the clock, and anything else with no owner.
    Runtime,
}

impl Subject {
    fn text(&self) -> String {
        match self {
            Subject::Task(task) => task.to_string(),
            Subject::Reactor(reactor) => reactor.to_string(),
            Subject::Runtime => "--".into(),
        }
    }
}

impl Event {
    fn subject(&self) -> Subject {
        match self {
            Event::Spawn { task, .. }
            | Event::Resume { task }
            | Event::Park { task, .. }
            | Event::Done { task }
            | Event::Cancel { task }
            | Event::ScopeEnter { task, .. }
            | Event::ScopeExit { task, .. }
            | Event::Open { task, .. }
            | Event::Close { task, .. }
            | Event::Move { task, .. } => Subject::Task(*task),
            Event::ReactorCreated { reactor, .. }
            | Event::Init { reactor }
            | Event::Turn { reactor, .. }
            | Event::Node { reactor, .. }
            | Event::Publish { reactor, .. }
            | Event::Effect { reactor, .. }
            | Event::Overflow { reactor, .. }
            | Event::ReactorClosed { reactor } => Subject::Reactor(*reactor),
            Event::Clock => Subject::Runtime,
        }
    }

    fn text(&self) -> String {
        match self {
            Event::Spawn { name, parent, .. } => match parent {
                Some(parent) => format!("spawn {name} in {parent}"),
                None => format!("spawn {name} root"),
            },
            Event::Resume { .. } => "resume".into(),
            Event::Park { wait, .. } => format!("park {}", wait.text()),
            Event::Done { .. } => "done".into(),
            Event::Cancel { .. } => "cancel".into(),
            Event::ScopeEnter { depth, .. } => format!("scope enter {depth}"),
            Event::ScopeExit { depth, .. } => format!("scope exit {depth}"),
            Event::Open { resource, kind, .. } => format!("open {resource} {}", kind.name()),
            Event::Close { resource, .. } => format!("close {resource}"),
            Event::Move { resource, from, .. } => format!("move {resource} from {from}"),
            Event::ReactorCreated { name, owner, .. } => format!("create {name} in {owner}"),
            Event::Init { .. } => "init".into(),
            Event::Turn { seq, input, .. } => format!("turn {seq} {input}"),
            Event::Node { node, commit, .. } => {
                let what = if *commit { "commit" } else { "recompute" };
                format!("{what} {node}")
            }
            Event::Publish { version, .. } => format!("publish {version}"),
            Event::Effect {
                task,
                name,
                returns,
                ..
            } => match returns {
                Some(input) => format!("effect {name} {task} -> {input}"),
                None => format!("effect {name} {task}"),
            },
            Event::Overflow { input, policy, .. } => {
                format!("overflow {input} {}", policy.name())
            }
            Event::ReactorClosed { .. } => "stop".into(),
            Event::Clock => "clock".into(),
        }
    }
}

/// A recorded event and the time it happened.
pub struct Record {
    pub at: Millis,
    pub event: Event,
}

impl Record {
    pub fn line(&self) -> String {
        format!(
            "{}ms {} {}",
            self.at,
            self.event.subject().text(),
            self.event.text()
        )
    }
}

/// Where events go. Recording is off unless asked for, so an ordinary `norn run` pays nothing.
#[derive(Default)]
pub struct Trace {
    enabled: bool,
    records: Vec<Record>,
}

impl Trace {
    pub fn new(enabled: bool) -> Trace {
        Trace {
            enabled,
            records: Vec::new(),
        }
    }

    pub fn enabled(&self) -> bool {
        self.enabled
    }

    pub fn push(&mut self, at: Millis, event: Event) {
        if self.enabled {
            self.records.push(Record { at, event });
        }
    }

    pub fn records(&self) -> &[Record] {
        &self.records
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        for record in &self.records {
            out.push_str(&record.line());
            out.push('\n');
        }
        out
    }
}
