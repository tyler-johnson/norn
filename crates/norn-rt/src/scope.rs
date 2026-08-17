//! Scopes: spawning, cancel-then-join, and resource release.
//!
//! A task spawned inside a scope cannot outlive it. Leaving the scope cancels every child and joins
//! them before the parent goes on, and joining is immediate: a cancelled task runs no further user
//! code, so there is nothing left to wait for. Cleanup is the resource table, not a user-visible
//! handler.
//!
//! Resources are owned by the task that created them and closed when it ends, however it ends.
//! `spawn` transfers any handle passed to the child, which is the dynamic shadow of the move rule
//! M4 will make static.

use crate::task::{Status, TaskId, TaskState};
use crate::trace::Event;
use crate::{Core, Cx, Poll, ResourceId, Trap};

/// One open scope and the children spawned into it.
#[derive(Default)]
pub struct Scope {
    pub children: Vec<TaskId>,
}

impl<'e, V> Core<'e, V> {
    pub(crate) fn spawn(
        &mut self,
        value: V,
        parent: Option<TaskId>,
        moved: &[ResourceId],
    ) -> Result<TaskId, Trap> {
        let body = (self.make)(&value)?;
        let name = body.name().to_string();
        let task = TaskId(self.tasks.len() as u32);
        self.tasks.push(TaskState {
            name: name.clone(),
            body: Some(body),
            parent,
            // Every task starts with one implicit scope, so that whatever it spawns dies with it
            // even if lowering never emitted an explicit one.
            scopes: vec![Scope::default()],
            wait: None,
            resources: Vec::new(),
            status: Status::Ready,
        });
        self.emit(Event::Spawn { task, parent, name });

        if let Some(parent) = parent {
            self.state_mut(parent)
                .scopes
                .last_mut()
                .expect("every task has an implicit outermost scope")
                .children
                .push(task);
            for resource in moved {
                self.transfer(*resource, parent, task);
            }
        }
        self.ready.push_back(task);
        Ok(task)
    }

    /// Hand a resource to a task that was passed it. Only the current owner can give it away, so a
    /// handle that was copied rather than moved stays where it was.
    fn transfer(&mut self, resource: ResourceId, from: TaskId, to: TaskId) {
        let owner = self.state_mut(from);
        let before = owner.resources.len();
        owner.resources.retain(|held| *held != resource);
        if owner.resources.len() == before {
            return;
        }
        self.state_mut(to).resources.push(resource);
        self.emit(Event::Move {
            task: to,
            resource,
            from,
        });
    }

    pub(crate) fn finish(&mut self, task: TaskId, value: V) {
        self.state_mut(task).status = Status::Done;
        self.cancel_children(task);
        self.release(task);
        self.emit(Event::Done { task });
        self.state_mut(task).body = None;
        self.detach(task);
        if self.root == Some(task) {
            self.result = Some(value);
        }
    }

    /// Cancel a task and everything below it. Synchronous, because a cancelled task runs no user
    /// code: there is no suspension point left in it to wait for.
    pub(crate) fn cancel(&mut self, task: TaskId) {
        if self.state(task).status.finished() {
            return;
        }
        self.state_mut(task).status = Status::Cancelled;
        self.emit(Event::Cancel { task });
        self.timers.disarm(task);
        self.reactor.clear(task);
        self.cancel_children(task);
        self.release(task);
        self.state_mut(task).body = None;
        self.detach(task);
    }

    fn cancel_children(&mut self, task: TaskId) {
        let children: Vec<TaskId> = self
            .state_mut(task)
            .scopes
            .iter_mut()
            .flat_map(|scope| std::mem::take(&mut scope.children))
            .collect();
        for child in children {
            self.cancel(child);
        }
    }

    /// Close everything the task still owns. This is what makes cancellation leak-free without a
    /// cleanup handler.
    fn release(&mut self, task: TaskId) {
        let resources = std::mem::take(&mut self.state_mut(task).resources);
        for resource in resources {
            if self.reactor.close(resource) {
                self.emit(Event::Close { task, resource });
            }
        }
    }

    fn detach(&mut self, task: TaskId) {
        let Some(parent) = self.state(task).parent else {
            return;
        };
        for scope in &mut self.state_mut(parent).scopes {
            scope.children.retain(|child| *child != task);
        }
    }

    /// Tear down whatever is left standing once the root has finished. Lowering exits every scope
    /// on every path out of a function, so this should find nothing; it runs anyway, because "the
    /// trace says every descriptor was closed" is the claim M2 is asked to make.
    pub(crate) fn shutdown(&mut self) {
        for index in 0..self.tasks.len() {
            let task = TaskId(index as u32);
            if !self.state(task).status.finished() {
                self.cancel(task);
            }
        }
    }
}

impl<'e, V> Cx<'_, 'e, V> {
    /// Start a task in the innermost open scope of the current task.
    pub fn spawn(&mut self, task: V, moved: &[ResourceId]) -> Result<TaskId, Trap> {
        let parent = self.task;
        self.core.spawn(task, Some(parent), moved)
    }

    pub fn scope_enter(&mut self) {
        let task = self.task;
        self.core.state_mut(task).scopes.push(Scope::default());
        let depth = self.core.state(task).scopes.len() - 1;
        self.core.emit(Event::ScopeEnter { task, depth });
    }

    /// Leave the innermost scope: cancel and join its children.
    ///
    /// The result is a `Poll` because `Term::ScopeExit` is a suspension point — block ids are state
    /// numbers, and M5 emits one state per terminator. Joining cannot actually block in M2, since a
    /// cancelled task runs no further user code, so this is always `Ready`.
    pub fn scope_exit(&mut self) -> Poll<()> {
        let task = self.task;
        let scopes = &mut self.core.state_mut(task).scopes;
        let depth = scopes.len() - 1;
        // The outermost scope belongs to the task itself and is closed when the task ends.
        let children = if scopes.len() > 1 {
            scopes.pop().expect("just checked").children
        } else {
            std::mem::take(&mut scopes[0].children)
        };
        for child in children {
            self.core.cancel(child);
        }
        self.core.emit(Event::ScopeExit { task, depth });
        Poll::Ready(())
    }

    /// Close a resource explicitly, before the owning task ends.
    pub fn close(&mut self, resource: ResourceId) {
        let task = self.task;
        self.core
            .state_mut(task)
            .resources
            .retain(|held| *held != resource);
        if self.core.reactor.close(resource) {
            self.core.emit(Event::Close { task, resource });
        }
    }

    /// Record a freshly created resource as owned by the running task.
    pub(crate) fn take_ownership(&mut self, resource: ResourceId) {
        let task = self.task;
        self.core.state_mut(task).resources.push(resource);
        if let Some(kind) = self.core.reactor.kind(resource) {
            self.core.emit(Event::Open {
                task,
                resource,
                kind,
            });
        }
    }
}
