//! The deadline heap.
//!
//! One entry per parked task, and at most one entry per task at a time — a task waits on exactly
//! one thing, because it suspends at exactly one `await`. Cancellation disarms rather than leaving
//! a tombstone: a stale deadline would make a virtual clock jump to a time nothing is waiting for,
//! and that jump would show up in a golden trace.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::clock::Millis;
use crate::task::TaskId;

#[derive(Default)]
pub struct Timers {
    heap: BinaryHeap<Reverse<(Millis, u32)>>,
}

impl Timers {
    pub fn arm(&mut self, deadline: Millis, task: TaskId) {
        self.heap.push(Reverse((deadline, task.0)));
    }

    pub fn disarm(&mut self, task: TaskId) {
        if self.heap.iter().any(|Reverse((_, id))| *id == task.0) {
            self.heap = self
                .heap
                .drain()
                .filter(|Reverse((_, id))| *id != task.0)
                .collect();
        }
    }

    pub fn earliest(&self) -> Option<Millis> {
        self.heap.peek().map(|Reverse((deadline, _))| *deadline)
    }

    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Take the next task whose deadline has passed.
    pub fn due(&mut self, now: Millis) -> Option<TaskId> {
        match self.heap.peek() {
            Some(Reverse((deadline, _))) if *deadline <= now => {
                let Reverse((_, task)) = self.heap.pop().expect("just peeked");
                Some(TaskId(task))
            }
            _ => None,
        }
    }
}
