//! Reactors: the plan as data, the turn, and publication.
//!
//! The runtime asks an engine to recompute a node through `trait Graph<V>`, whose methods take
//! dependency values and return values — no `Cx`, no `Poll`, no `Step`. An engine cannot suspend,
//! spawn, print, or touch a descriptor mid-turn because it is never handed anything that could.
//! `Graph<V>` is to a turn what `Body<V>` is to a task: the one thing `norn-rt` cannot know, and
//! the reason both engines share one propagation loop — which is what will make M5's turn traces
//! byte-identical by construction rather than by comparison.
//!
//! The plan itself arrives as plain data. `ReactorSpec` is names, indices, and enums — the same
//! category of thing as `ResourceKind` — so the runtime stays ignorant of NIR while executing a
//! graph NIR computed.

use std::collections::VecDeque;
use std::rc::Rc;

use crate::scope::Parent;
use crate::task::{TaskId, Wait};
use crate::trace::Event;
use crate::{Core, Cx, Poll, Runnable, Trap};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ReactorId(pub u32);

impl ReactorId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for ReactorId {
    /// `R0`, capitalised, because `r0` is already a `ResourceId` and a trace is read down its
    /// subject column.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "R{}", self.0)
    }
}

/// What to do with a message that arrives at a full mailbox.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Overflow {
    /// Refuse the arriving message.
    Reject,
    /// Evict the oldest queued message to make room.
    DropOldest,
    /// Evict the most recently queued message to make room.
    DropNewest,
    /// Suspend the sender until there is room.
    Wait,
}

impl Overflow {
    pub fn name(self) -> &'static str {
        match self {
            Overflow::Reject => "reject",
            Overflow::DropOldest => "drop_oldest",
            Overflow::DropNewest => "drop_newest",
            Overflow::Wait => "wait",
        }
    }
}

/// One reactor's compile-time plan.
pub struct ReactorSpec {
    pub name: String,
    pub nodes: Vec<NodeSpec>,
    /// The node holding each slot, in slot order. Slot order is source order, so that a slot index
    /// stays stable as derived signals are added around it.
    pub slots: Vec<usize>,
    pub inputs: Vec<InputSpec>,
    /// A topological order over the whole graph. Every node appears after its dependencies, which
    /// is what makes one pass a fixed point.
    pub order: Vec<usize>,
    pub exports: Vec<usize>,
}

pub struct NodeSpec {
    pub name: String,
    pub deps: Vec<usize>,
    /// Set when the node's value survives between turns. Such a node is committed by a handler
    /// rather than recomputed.
    pub slot: Option<usize>,
}

pub struct InputSpec {
    pub name: String,
    pub capacity: usize,
    pub overflow: Overflow,
    /// The subsequence of `order` a message on this input can affect. Everything else is provably
    /// untouched, so a turn does not walk it.
    pub plan: Vec<usize>,
}

/// What one node update produced.
pub enum Update<V> {
    Set(V),
    /// The value did not change, so nothing downstream needs to know.
    ///
    /// v0's engine never says this: deciding it needs an equality on `V`, and `V` has none. It is
    /// the vocabulary for dynamic change propagation, and the loop below already honours it — the
    /// only pruning v0 does is the static one, each input's plan.
    Silent,
}

/// What one handler produced: the slots it committed, in the order it wrote them, and the effects
/// it asked for.
pub struct Handled<V> {
    pub writes: Vec<(usize, V)>,
    pub effects: Vec<Effect<V>>,
}

/// An effect request. `task` is a computation that has been *built* and not started.
pub struct Effect<V> {
    pub task: V,
    /// The input its result comes back on, making a completion a later input.
    pub returns: Option<usize>,
}

/// The one thing `norn-rt` cannot know about a graph: how to evaluate it.
///
/// Every method takes values and returns values. There is no way to express suspending, printing,
/// or reading a descriptor in these signatures, which is what makes turn purity a property of the
/// type rather than a rule an implementation has to remember.
pub trait Graph<V> {
    /// The initial value of every slot, given the constructor arguments.
    fn create(&self, reactor: usize, args: Vec<V>) -> Result<Vec<V>, Trap>;

    /// Run one handler: the message, plus every slot in slot order.
    fn handle(
        &self,
        reactor: usize,
        input: usize,
        message: V,
        slots: &[V],
    ) -> Result<Handled<V>, Trap>;

    /// Recompute one derived node from the current values of its dependencies.
    fn recompute(&self, reactor: usize, node: usize, deps: &[V]) -> Result<Update<V>, Trap>;
}

pub(crate) struct Message<V> {
    pub input: usize,
    pub value: V,
}

/// A sender parked on a full `wait` mailbox.
struct Waiting<V> {
    task: TaskId,
    input: usize,
    value: V,
}

pub(crate) struct ReactorState<V> {
    pub spec: usize,
    /// The current value of every node, indexed the way `NodeSpec` is.
    pub values: Vec<V>,
    pub mailbox: VecDeque<Message<V>>,
    pub next_seq: u64,
    pub version: u64,
    /// The last stable snapshot: the exported values, as one immutable thing a reader takes whole.
    pub published: Rc<Vec<V>>,
    /// The task and scope that own it. Recorded at creation, because an effect launched turns later
    /// belongs where the reactor lives and not wherever its owner has since got to.
    pub owner: Parent,
    /// Whether it is already in the ready queue.
    pub queued: bool,
    waiting: Vec<Waiting<V>>,
    pub alive: bool,
}

/// Where an effect's value goes when it finishes.
#[derive(Clone, Copy, Debug)]
pub struct Completion {
    pub reactor: ReactorId,
    pub input: usize,
}

impl<'e, V: Clone> Core<'e, V> {
    /// Create a reactor, run it to its first stable state, and publish version 0.
    ///
    /// Publishing at creation is what makes `latest` total: there is never a moment when a handle
    /// exists and has no snapshot behind it.
    pub(crate) fn create_reactor(
        &mut self,
        spec: usize,
        args: Vec<V>,
        owner: Parent,
    ) -> Result<ReactorId, Trap> {
        let slots = self.engine.graph.create(spec, args)?;
        let count = self.engine.reactors[spec].nodes.len();
        let name = self.engine.reactors[spec].name.clone();

        // Every node needs a value before anything can read one, and a signal's is whatever its
        // dependencies say. Slots are filled from `create`, then one pass over the whole order
        // settles the rest — the same pass a turn runs, over `order` instead of a plan.
        let mut values: Vec<V> = Vec::with_capacity(count);
        for index in 0..count {
            let slot = self.engine.reactors[spec].nodes[index].slot;
            values.push(match slot {
                Some(slot) => slots[slot].clone(),
                // Replaced by the pass below before anything can observe it; `order` visits every
                // node, and a signal always precedes its dependents.
                None => slots.first().cloned().unwrap_or_else(|| {
                    unreachable!("a reactor with a signal has at least one slot")
                }),
            });
        }

        let id = ReactorId(self.reactors.len() as u32);
        self.reactors.push(ReactorState {
            spec,
            values,
            mailbox: VecDeque::new(),
            next_seq: 0,
            version: 0,
            published: Rc::new(Vec::new()),
            owner,
            queued: false,
            waiting: Vec::new(),
            alive: true,
        });
        self.emit(Event::ReactorCreated {
            reactor: id,
            name,
            owner: owner.task,
        });

        let order = self.engine.reactors[spec].order.clone();
        self.propagate(id, &order, None)?;
        self.publish(id);
        self.attach_reactor(owner, id);
        Ok(id)
    }

    /// Put a message in a reactor's mailbox, honouring the declared overflow policy.
    pub(crate) fn send(
        &mut self,
        id: ReactorId,
        input: usize,
        value: V,
        sender: TaskId,
    ) -> Poll<()> {
        if !self.reactors[id.index()].alive {
            // The scope that owned it has closed. Nothing will ever read this, and the sender
            // should not wait for a turn that cannot happen.
            return Poll::Ready(());
        }
        // A sender parked on a full `wait` mailbox re-asks when it wakes, and finds its message
        // already queued.
        if let Some(at) = self.reactors[id.index()]
            .waiting
            .iter()
            .position(|w| w.task == sender)
        {
            if self.full(id, input) {
                return Poll::Pending;
            }
            let waiting = self.reactors[id.index()].waiting.remove(at);
            self.state_mut(sender).wait = None;
            self.enqueue(id, waiting.input, waiting.value);
            return Poll::Ready(());
        }

        let spec = self.reactors[id.index()].spec;
        let overflow = self.engine.reactors[spec].inputs[input].overflow;
        if !self.full(id, input) {
            self.enqueue(id, input, value);
            return Poll::Ready(());
        }

        let name = self.engine.reactors[spec].inputs[input].name.clone();
        match overflow {
            Overflow::Reject => {
                self.emit(Event::Overflow {
                    reactor: id,
                    input: name,
                    policy: overflow,
                });
                Poll::Ready(())
            }
            Overflow::DropOldest | Overflow::DropNewest => {
                let queued = self.reactors[id.index()]
                    .mailbox
                    .iter()
                    .enumerate()
                    .filter(|(_, message)| message.input == input)
                    .map(|(at, _)| at);
                let evict = match overflow {
                    Overflow::DropOldest => queued.min(),
                    _ => queued.max(),
                };
                if let Some(at) = evict {
                    self.reactors[id.index()].mailbox.remove(at);
                }
                self.emit(Event::Overflow {
                    reactor: id,
                    input: name,
                    policy: overflow,
                });
                self.enqueue(id, input, value);
                Poll::Ready(())
            }
            Overflow::Wait => {
                self.emit(Event::Overflow {
                    reactor: id,
                    input: name,
                    policy: overflow,
                });
                self.reactors[id.index()].waiting.push(Waiting {
                    task: sender,
                    input,
                    value,
                });
                self.state_mut(sender).wait = Some(Wait::Mailbox(id));
                Poll::Pending
            }
        }
    }

    /// Whether this input's share of the mailbox is full.
    ///
    /// One mailbox, because a reactor processes one message at a time and the order it sees them in
    /// has to be one order. Capacity is per input all the same: it is declared per input, and a
    /// noisy input must not be able to consume the room a quiet one was promised.
    fn full(&self, id: ReactorId, input: usize) -> bool {
        let spec = self.reactors[id.index()].spec;
        let capacity = self.engine.reactors[spec].inputs[input].capacity;
        let queued = self.reactors[id.index()]
            .mailbox
            .iter()
            .filter(|message| message.input == input)
            .count();
        queued >= capacity
    }

    fn enqueue(&mut self, id: ReactorId, input: usize, value: V) {
        let state = &mut self.reactors[id.index()];
        state.mailbox.push_back(Message { input, value });
        // A reactor joins the ready queue when a message lands in an empty mailbox, and rejoins it
        // after a turn if more remain. That is what makes "one input at a time" observable rather
        // than asserted, and why a flood of messages cannot starve a task: every other runnable
        // thing in the queue goes first.
        if !state.queued {
            state.queued = true;
            self.ready.push_back(Runnable::Reactor(id));
        }
    }

    /// Take one message and run its turn to completion.
    pub(crate) fn turn(&mut self, id: ReactorId) -> Result<(), Trap> {
        self.reactors[id.index()].queued = false;
        if !self.reactors[id.index()].alive {
            return Ok(());
        }
        let Some(message) = self.reactors[id.index()].mailbox.pop_front() else {
            return Ok(());
        };

        let spec = self.reactors[id.index()].spec;
        let seq = self.reactors[id.index()].next_seq;
        self.reactors[id.index()].next_seq += 1;
        let input_name = self.engine.reactors[spec].inputs[message.input]
            .name
            .clone();
        self.emit(Event::Turn {
            reactor: id,
            seq,
            input: input_name,
        });

        // The handler runs first and in full: it reads state, writes state, and describes effects,
        // all before any signal is recomputed. That ordering is the reason a handler may not read a
        // signal — at this point every one of them still holds last turn's value.
        let slots: Vec<V> = self.engine.reactors[spec]
            .slots
            .iter()
            .map(|node| self.reactors[id.index()].values[*node].clone())
            .collect();
        let handled = self
            .engine
            .graph
            .handle(spec, message.input, message.value, &slots)?;

        // Last write wins: a handler may assign the same cell more than once, and what the turn
        // commits is where it ended up.
        let mut committed: Vec<Option<V>> = vec![None; slots.len()];
        for (slot, value) in handled.writes {
            committed[slot] = Some(value);
        }

        let plan = self.engine.reactors[spec].inputs[message.input]
            .plan
            .clone();
        self.propagate(id, &plan, Some(&committed))?;
        self.reactors[id.index()].version += 1;
        self.publish(id);

        // Strictly after publication, and structurally so: the requests sat in a local `Vec` that
        // nothing above could reach, so no code path exists by which an effect observes an
        // intermediate graph.
        for effect in handled.effects {
            self.launch_effect(id, effect)?;
        }

        // Re-enqueued rather than looped, so a reactor with a full mailbox yields to everything
        // else between turns.
        if !self.reactors[id.index()].mailbox.is_empty() && !self.reactors[id.index()].queued {
            self.reactors[id.index()].queued = true;
            self.ready.push_back(Runnable::Reactor(id));
        }
        // A `wait` sender can only be woken once there is room, which is now.
        self.wake_senders(id);
        Ok(())
    }

    /// Walk a plan in order, updating each node.
    ///
    /// One pass, because the graph is acyclic: by the time a node is reached every dependency is
    /// already at this turn's value, so there is nothing to iterate towards. That is the concrete
    /// return on rejecting instantaneous cycles at compile time.
    ///
    /// `writes` is what the handler committed, indexed by slot — `None` during creation, where
    /// there is no handler and the whole graph is being settled for the first time.
    fn propagate(
        &mut self,
        id: ReactorId,
        plan: &[usize],
        writes: Option<&[Option<V>]>,
    ) -> Result<(), Trap> {
        let spec = self.reactors[id.index()].spec;
        for &node in plan {
            // A state cell is committed by the handler rather than recomputed; it appears in the
            // plan because it is where propagation starts. One the handler did not touch is
            // `Silent` — nothing to record, and nothing downstream that needs to know.
            let update = match self.engine.reactors[spec].nodes[node].slot {
                Some(slot) => match writes.and_then(|writes| writes[slot].clone()) {
                    Some(value) => Update::Set(value),
                    None => Update::Silent,
                },
                None => {
                    let deps: Vec<V> = self.engine.reactors[spec].nodes[node]
                        .deps
                        .iter()
                        .map(|dep| self.reactors[id.index()].values[*dep].clone())
                        .collect();
                    self.engine.graph.recompute(spec, node, &deps)?
                }
            };
            let Update::Set(value) = update else {
                continue;
            };
            self.reactors[id.index()].values[node] = value;
            if writes.is_some() {
                let commit = self.engine.reactors[spec].nodes[node].slot.is_some();
                let name = self.engine.reactors[spec].nodes[node].name.clone();
                self.emit(Event::Node {
                    reactor: id,
                    node: name,
                    commit,
                });
            }
        }
        Ok(())
    }

    /// Swap in a new snapshot atomically: one `Rc`, replaced in one move.
    ///
    /// Version 0 is the state the reactor was created in; version *n* is the state after its *n*th
    /// turn, so a version number and a turn's sequence number line up in the trace.
    ///
    /// A reader takes the whole thing or the whole previous one, which is what makes glitch freedom
    /// observable rather than merely intended — there is no moment at which half of a snapshot is
    /// visible, because a half of an `Rc` is not a thing anyone can hold.
    fn publish(&mut self, id: ReactorId) {
        let spec = self.reactors[id.index()].spec;
        let snapshot: Vec<V> = self.engine.reactors[spec]
            .exports
            .iter()
            .map(|node| self.reactors[id.index()].values[*node].clone())
            .collect();
        let state = &mut self.reactors[id.index()];
        state.published = Rc::new(snapshot);
        let version = state.version;
        self.emit(Event::Publish {
            reactor: id,
            version,
        });
    }

    /// Start an effect on behalf of a reactor, in the scope the reactor was created in.
    fn launch_effect(&mut self, id: ReactorId, effect: Effect<V>) -> Result<(), Trap> {
        let owner = self.reactors[id.index()].owner;
        let task = self.spawn(effect.task, Some(owner), &[])?;
        let name = self.state(task).name.clone();
        if let Some(input) = effect.returns {
            self.state_mut(task).completion = Some(Completion { reactor: id, input });
        }
        let spec = self.reactors[id.index()].spec;
        let returns = effect
            .returns
            .map(|input| self.engine.reactors[spec].inputs[input].name.clone());
        self.emit(Event::Effect {
            reactor: id,
            task,
            name,
            returns,
        });
        Ok(())
    }

    /// Hand a finished effect's value back as a message.
    ///
    /// Only a task that *finished* delivers. A cancelled one does not, which is what makes a
    /// cancelled effect observable as a cancel with no matching turn.
    pub(crate) fn deliver(&mut self, completion: Completion, value: V, sender: TaskId) {
        self.send(completion.reactor, completion.input, value, sender);
    }

    fn wake_senders(&mut self, id: ReactorId) {
        let waiting: Vec<TaskId> = self.reactors[id.index()]
            .waiting
            .iter()
            .map(|w| w.task)
            .collect();
        for task in waiting {
            self.wake(task);
        }
    }

    /// The last published snapshot, without entering the reactor.
    pub(crate) fn latest(&self, id: ReactorId, export: usize) -> Option<V> {
        self.reactors[id.index()].published.get(export).cloned()
    }

    /// Whether a reactor is still accepting messages. A dead one is not an error to send to; it is
    /// simply a reactor whose scope has closed.
    pub(crate) fn reactor_alive(&self, id: ReactorId) -> bool {
        self.reactors[id.index()].alive
    }

    /// Stop a reactor: no further turns, and nothing left queued to run one.
    pub(crate) fn kill_reactor(&mut self, id: ReactorId) {
        let state = &mut self.reactors[id.index()];
        if !state.alive {
            return;
        }
        state.alive = false;
        state.mailbox.clear();
        let waiting: Vec<TaskId> = state.waiting.drain(..).map(|w| w.task).collect();
        self.emit(Event::ReactorClosed { reactor: id });
        // A sender parked on a mailbox that will never drain has to be let go, or the program is
        // stuck waiting for a turn that cannot happen.
        for task in waiting {
            self.wake(task);
        }
    }
}

impl<'e, V: Clone> Cx<'_, 'e, V> {
    /// `spawn reactor Gate(…)`, owned by the scope the running task is standing in.
    pub fn create_reactor(&mut self, spec: usize, args: Vec<V>) -> Result<ReactorId, Trap> {
        let owner = self.innermost();
        self.core.create_reactor(spec, args, owner)
    }

    /// `send(gate.opened, message)`.
    ///
    /// `Pending` means a `wait` mailbox is full and the sender has been recorded; it re-asks when
    /// the reactor's next turn makes room, and finds its own message queued rather than sending it
    /// twice.
    pub fn send(&mut self, reactor: ReactorId, input: usize, value: V) -> Poll<()> {
        let sender = self.task();
        self.core.send(reactor, input, value, sender)
    }

    /// `latest(gate.snapshot)` — the last published value, without entering the reactor.
    pub fn latest(&self, reactor: ReactorId, export: usize) -> Option<V> {
        self.core.latest(reactor, export)
    }

    pub fn reactor_alive(&self, reactor: ReactorId) -> bool {
        self.core.reactor_alive(reactor)
    }
}
