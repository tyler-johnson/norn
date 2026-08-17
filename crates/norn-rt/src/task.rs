//! Tasks: identity, status, what they are waiting for, and what they own.
//!
//! A task waits on exactly one thing at a time, because it suspends at exactly one `await`. That is
//! why `wait` is an `Option` rather than a set, and why waking is unambiguous.

use crate::Body;
use crate::clock::Millis;
use crate::graph::{Completion, ReactorId};
use crate::poll::ResourceId;
use crate::scope::Scope;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TaskId(pub u32);

impl TaskId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for TaskId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Status {
    /// In the ready queue, or currently running.
    Ready,
    Parked,
    Done,
    Cancelled,
}

impl Status {
    pub fn finished(self) -> bool {
        matches!(self, Status::Done | Status::Cancelled)
    }
}

pub(crate) enum Wait {
    Timer(Millis),
    Io {
        resource: ResourceId,
        write: bool,
    },
    /// Parked on a full mailbox whose input declared `overflow: wait`. Woken by the turn that
    /// makes room.
    Mailbox(ReactorId),
}

pub(crate) struct TaskState<'e, V> {
    pub name: String,
    /// Taken out while the task is running, so the scheduler can hand the body a `Cx` over
    /// everything else the runtime owns.
    pub body: Option<Box<dyn Body<V> + 'e>>,
    pub parent: Option<TaskId>,
    /// Scopes the task has open, innermost last. A spawned child joins the innermost one.
    pub scopes: Vec<Scope>,
    pub wait: Option<Wait>,
    /// Resources this task owns and will close when it ends, however it ends.
    pub resources: Vec<ResourceId>,
    /// Where this task's value goes when it finishes, when it is an effect a reactor asked for.
    /// Without it `finish` would drop every non-root value, and an effect could not report back.
    pub completion: Option<Completion>,
    pub status: Status,
}
