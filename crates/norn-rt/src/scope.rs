//! Scopes: spawning, cancel-then-join, and resource release.
//!
//! A task spawned inside a scope cannot outlive it. Leaving the scope cancels every child and joins
//! them before the parent goes on, and joining is immediate: a cancelled task runs no further user
//! code, so there is nothing left to wait for. Cleanup is the resource table, not a user-visible
//! handler.
//!
//! Resources are owned by the scope that created them and closed when it is left, however it is
//! left — normally, through an error, or through cancellation, because lowering unwinds every open
//! scope on every path out of a function. `spawn` transfers any handle passed to the child, which
//! is the dynamic half of the move rule the checker enforces statically.

use crate::graph::ReactorId;
use crate::task::{Status, TaskId, TaskState};
use crate::trace::Event;
use crate::{Core, Cx, Poll, ResourceId, Runnable, Trap};

/// One open scope, and what was started or opened inside it.
#[derive(Default)]
pub struct Scope {
    pub children: Vec<TaskId>,
    /// Reactors created here. A reactor is passive — it runs only when sent to — but it is owned
    /// all the same, and leaving the scope has to stop it, or a later `send` would queue a message
    /// for a turn that can never happen.
    pub reactors: Vec<ReactorId>,
    /// Descriptors opened here and not since moved away. Closed on the way out, which is what makes
    /// "resources close on scope exit" a fact about `scope_exit` rather than about the end of the
    /// task that happens to contain it.
    pub resources: Vec<ResourceId>,
}

/// Who a new task is spawned under, and into which of that task's open scopes.
///
/// The scope is named rather than assumed. For a task spawning from its own body — the only caller
/// M2 had — the innermost scope is always right, and `Parent::innermost` says exactly that. It stops
/// being right the moment something is spawned *later* on behalf of a task whose scope stack has
/// moved on since: an effect launched after a turn belongs to the scope its reactor was created in,
/// not to whichever scope its owner happens to be standing in when the effect fires.
#[derive(Clone, Copy, Debug)]
pub struct Parent {
    pub task: TaskId,
    /// Index into the parent's `scopes`, outermost `0`.
    pub scope: usize,
}

impl<'e, V: Clone> Core<'e, V> {
    pub(crate) fn spawn(
        &mut self,
        value: V,
        parent: Option<Parent>,
        moved: &[ResourceId],
    ) -> Result<TaskId, Trap> {
        let body = (self.engine.make)(&value)?;
        let name = body.name().to_string();
        let task = TaskId(self.tasks.len() as u32);
        self.tasks.push(TaskState {
            name: name.clone(),
            body: Some(body),
            parent: parent.map(|parent| parent.task),
            // Every task starts with one implicit scope: the default owner of anything spawned
            // outside an explicit `scope { … }`, cancelled when the task finishes.
            scopes: vec![Scope::default()],
            wait: None,
            completion: None,
            status: Status::Ready,
        });
        self.emit(Event::Spawn {
            task,
            parent: parent.map(|parent| parent.task),
            name,
        });

        if let Some(parent) = parent {
            let scopes = &mut self.state_mut(parent.task).scopes;
            // A named scope may already have been left — an effect can outlive the `scope { … }`
            // its reactor was declared in. Falling back to the outermost scope keeps the child
            // owned by *something* that will cancel it, which is the invariant that matters; the
            // scope exit itself is what stops obsolete effects from being launched at all.
            let index = parent.scope.min(scopes.len() - 1);
            scopes[index].children.push(task);
            for resource in moved {
                self.transfer(*resource, parent.task, task);
            }
        }
        self.ready.push_back(Runnable::Task(task));
        Ok(task)
    }

    /// Hand a resource to a task that was passed it. Only the current owner can give it away, so a
    /// handle that was copied rather than moved stays where it was.
    fn transfer(&mut self, resource: ResourceId, from: TaskId, to: TaskId) {
        if !self.disown(from, resource) {
            return;
        }
        // The child is freshly spawned, so its outermost scope is its only one, and it is what will
        // close the handle when the child ends.
        self.state_mut(to).scopes[0].resources.push(resource);
        self.emit(Event::Move {
            task: to,
            resource,
            from,
        });
    }

    /// Remove a resource from whichever of a task's scopes holds it. `false` means this task did not
    /// own it — a handle that was copied rather than moved, or one already given away.
    pub(crate) fn disown(&mut self, task: TaskId, resource: ResourceId) -> bool {
        for scope in &mut self.state_mut(task).scopes {
            let before = scope.resources.len();
            scope.resources.retain(|held| *held != resource);
            if scope.resources.len() != before {
                return true;
            }
        }
        false
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
            return;
        }
        // An effect's result re-enters as a later input: `DESIGN.md` §2's `EffectResult →
        // ReactorMailbox → a later turn`, as one field. Only *finishing* delivers — `cancel` does
        // not — which is what makes a cancelled effect observable as a cancel with no matching turn.
        if let Some(completion) = self.state(task).completion {
            self.deliver(completion, value, task);
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
        self.readiness.clear(task);
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
        let reactors: Vec<ReactorId> = self
            .state_mut(task)
            .scopes
            .iter_mut()
            .flat_map(|scope| std::mem::take(&mut scope.reactors))
            .collect();
        for reactor in reactors {
            self.kill_reactor(reactor);
        }
    }

    /// Record a reactor as owned by the scope it was created in.
    pub(crate) fn attach_reactor(&mut self, owner: Parent, reactor: ReactorId) {
        let scopes = &mut self.state_mut(owner.task).scopes;
        let index = owner.scope.min(scopes.len() - 1);
        scopes[index].reactors.push(reactor);
    }

    /// Close everything the task still owns, in every scope it had open. This is what makes
    /// cancellation leak-free without a cleanup handler.
    fn release(&mut self, task: TaskId) {
        let resources: Vec<ResourceId> = self
            .state_mut(task)
            .scopes
            .iter_mut()
            .flat_map(|scope| std::mem::take(&mut scope.resources))
            .collect();
        self.close_all(task, resources);
    }

    /// Close a scope's worth of descriptors, tracing each one that was still open.
    fn close_all(&mut self, task: TaskId, resources: Vec<ResourceId>) {
        for resource in resources {
            if self.readiness.close(resource) {
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

impl<'e, V: Clone> Cx<'_, 'e, V> {
    /// Start a task in the innermost open scope of the current task.
    pub fn spawn(&mut self, task: V, moved: &[ResourceId]) -> Result<TaskId, Trap> {
        let parent = self.innermost();
        self.core.spawn(task, Some(parent), moved)
    }

    /// The running task and the scope it is standing in. A reactor records this when it is created,
    /// so that effects launched turns later land where the reactor lives.
    pub fn innermost(&self) -> Parent {
        Parent {
            task: self.task,
            scope: self.core.state(self.task).scopes.len() - 1,
        }
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
        // The outermost scope belongs to the task itself: what it started is stopped here, but what
        // it opened stays open, because the task is still running and still owns it.
        let (children, reactors, resources) = if scopes.len() > 1 {
            let scope = scopes.pop().expect("just checked");
            (scope.children, scope.reactors, scope.resources)
        } else {
            (
                std::mem::take(&mut scopes[0].children),
                std::mem::take(&mut scopes[0].reactors),
                Vec::new(),
            )
        };
        for child in children {
            self.core.cancel(child);
        }
        for reactor in reactors {
            self.core.kill_reactor(reactor);
        }
        // After the children, because a handle they were given is theirs to close, and before the
        // exit itself, because these descriptors belong to the scope that is ending.
        self.core.close_all(task, resources);
        self.core.emit(Event::ScopeExit { task, depth });
        Poll::Ready(())
    }

    /// Close a resource explicitly, before the scope that owns it ends.
    pub fn close(&mut self, resource: ResourceId) {
        let task = self.task;
        self.core.disown(task, resource);
        if self.core.readiness.close(resource) {
            self.core.emit(Event::Close { task, resource });
        }
    }

    /// Record a freshly created resource as owned by the scope the task is standing in.
    pub(crate) fn take_ownership(&mut self, resource: ResourceId) {
        let task = self.task;
        let scopes = &mut self.core.state_mut(task).scopes;
        scopes
            .last_mut()
            .expect("every task has at least its own scope")
            .resources
            .push(resource);
        if let Some(kind) = self.core.readiness.kind(resource) {
            self.core.emit(Event::Open {
                task,
                resource,
                kind,
            });
        }
    }
}
