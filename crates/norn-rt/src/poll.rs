//! Readiness and the resource table.
//!
//! Sockets come from `std::net` in non-blocking mode; only readiness needs a syscall, and that
//! syscall is `poll(2)`, declared by hand. `pollfd` is three scalars with a layout that does not
//! vary by architecture, unlike `epoll_event`, which is packed on x86-64 and not on aarch64 — so
//! this keeps the workspace at zero external dependencies with no layout risk. Swapping to `epoll`
//! when the fd count makes it matter is internal to this file.
//!
//! The resource table lives here too, because a resource *is* a file descriptor plus whatever
//! `std::net` object owns it. Who owns which resource is a task property, and lives in `task.rs`.

use std::io::{self, Read, Write};
use std::net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream};
use std::os::fd::{AsRawFd, RawFd};

use crate::clock::Millis;
use crate::task::TaskId;

#[repr(C)]
#[derive(Clone, Copy)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

// `nfds_t` is `unsigned long` on Linux, which `usize` matches on both LP64 and ILP32.
unsafe extern "C" {
    fn poll(fds: *mut PollFd, nfds: usize, timeout: i32) -> i32;
}

const POLLIN: i16 = 0x001;
const POLLOUT: i16 = 0x004;

/// Handle to an operating-system resource. Affine in the language from M4; owned dynamically by
/// one task until then.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ResourceId(pub u32);

impl ResourceId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for ResourceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "r{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ResourceKind {
    Listener,
    Connection,
    File,
    Request,
    Flow,
}

impl ResourceKind {
    pub fn name(self) -> &'static str {
        match self {
            ResourceKind::Listener => "listener",
            ResourceKind::Connection => "connection",
            ResourceKind::File => "file",
            ResourceKind::Request => "request",
            ResourceKind::Flow => "flow",
        }
    }
}

/// What a resource actually is under its handle. M2's table held only sockets; M6 adds files,
/// HTTP requests, and flows, all behind the same affine `ResourceId` and the same close-on-scope
/// discipline, because "a resource has exactly one closer" does not care what the closer closes.
enum Backing {
    Listener(TcpListener),
    Connection {
        stream: TcpStream,
        /// How much of the text currently being written has already gone out. A non-blocking write
        /// may take only part of it, and the task re-polls the same `await` with the same text, so
        /// progress has to be remembered somewhere that outlives the attempt.
        written: usize,
    },
    /// A write-only sink on the filesystem. A regular file is always ready under `poll(2)`, so a
    /// write here blocks the loop for as long as one chunk takes — at most 4 KiB, which is the
    /// accepted v0 behaviour rather than a thread pool nothing else needs yet.
    File(std::fs::File),
    Flow(FlowEntry),
}

/// A flow in flight. Every v0 flow knows its length up front — a file's size, a request body's
/// `Content-Length` — which is why `remaining` can be a number and a close-delimited transfer has
/// no representation here.
///
/// All transfer progress lives in this entry rather than in the task that drives it, because the
/// interpreter's re-ask protocol resumes a suspension point by asking again from the top: a parked
/// `pipe_to` must find the half-flushed chunk where it left it.
struct FlowEntry {
    source: FlowSource,
    /// Bytes the source still owes, beyond what is buffered.
    remaining: u64,
    /// The chunk currently in transit — at most one, which is the demand claim: nothing is read
    /// from the source until the sink has taken what was already read.
    buffered: Vec<u8>,
    /// How much of `buffered` the sink has already accepted.
    buffered_written: usize,
    /// Bytes fully delivered, which is what `pipe_to` resolves to.
    transferred: u64,
}

enum FlowSource {
    File(std::fs::File),
}

struct Entry {
    kind: ResourceKind,
    backing: Backing,
}

impl Backing {
    /// The descriptor readiness would poll for this backing, when it owns one directly.
    fn fd(&self) -> Option<RawFd> {
        match self {
            Backing::Listener(listener) => Some(listener.as_raw_fd()),
            Backing::Connection { stream, .. } => Some(stream.as_raw_fd()),
            Backing::File(file) => Some(file.as_raw_fd()),
            Backing::Flow(flow) => match &flow.source {
                FlowSource::File(file) => Some(file.as_raw_fd()),
            },
        }
    }
}

struct Interest {
    task: TaskId,
    fd: RawFd,
    write: bool,
}

/// One observable step of a flow-to-sink transfer, as `pipe_step` reports it.
pub enum PipeProgress {
    /// One chunk was fully delivered: this many bytes.
    Chunk(usize),
    /// Everything the flow promised has been delivered: the total.
    Done(u64),
    /// The sink cannot take more right now; park writing on this resource.
    ParkWrite(ResourceId),
    /// The source has nothing to give right now; park reading on this resource.
    ParkRead(ResourceId),
}

/// The resource table and the readiness registry. Slots are never reused, so a stale handle names
/// a closed resource rather than someone else's socket.
///
/// Named for what it answers rather than for the pattern it implements. "Reactor" is the usual word
/// for this — `DESIGN.md` §9 uses it — but in this language a reactor is a graph of state and
/// signals, and the two would collide in exactly the file where turns meet I/O.
#[derive(Default)]
pub struct Readiness {
    entries: Vec<Option<Entry>>,
    interests: Vec<Interest>,
}

impl Readiness {
    /// Whether nothing is waiting on a descriptor, in which case time is the only thing that can
    /// make a task runnable again.
    pub fn is_idle(&self) -> bool {
        self.interests.is_empty()
    }

    pub fn kind(&self, id: ResourceId) -> Option<ResourceKind> {
        self.entries
            .get(id.index())
            .and_then(Option::as_ref)
            .map(|entry| entry.kind)
    }

    fn entry(&mut self, id: ResourceId) -> io::Result<&mut Entry> {
        self.entries
            .get_mut(id.index())
            .and_then(Option::as_mut)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotConnected))
    }

    fn push(&mut self, kind: ResourceKind, backing: Backing) -> ResourceId {
        let id = ResourceId(self.entries.len() as u32);
        self.entries.push(Some(Entry { kind, backing }));
        id
    }

    /// Bind a listener on the loopback interface. Port 0 asks the operating system to choose, which
    /// is what lets a test run a server without agreeing on a port first.
    pub fn listen(&mut self, port: u16) -> io::Result<ResourceId> {
        let address = SocketAddr::from((Ipv4Addr::LOCALHOST, port));
        let listener = TcpListener::bind(address)?;
        listener.set_nonblocking(true)?;
        Ok(self.push(ResourceKind::Listener, Backing::Listener(listener)))
    }

    pub fn port(&mut self, id: ResourceId) -> io::Result<u16> {
        match &self.entry(id)?.backing {
            Backing::Listener(listener) => Ok(listener.local_addr()?.port()),
            Backing::Connection { stream, .. } => Ok(stream.local_addr()?.port()),
            _ => Err(io::Error::from(io::ErrorKind::InvalidInput)),
        }
    }

    /// `Ok(None)` means the operation would block; the caller registers interest and parks.
    pub fn accept(&mut self, id: ResourceId) -> io::Result<Option<ResourceId>> {
        let accepted = match &self.entry(id)?.backing {
            Backing::Listener(listener) => listener.accept(),
            _ => return Err(io::Error::from(io::ErrorKind::InvalidInput)),
        };
        match accepted {
            Ok((stream, _)) => {
                stream.set_nonblocking(true)?;
                Ok(Some(self.push(
                    ResourceKind::Connection,
                    Backing::Connection { stream, written: 0 },
                )))
            }
            Err(err) if err.kind() == io::ErrorKind::WouldBlock => Ok(None),
            Err(err) => Err(err),
        }
    }

    /// Read whatever has arrived, as the raw octets the wire carried. End of stream is an error
    /// rather than an empty chunk: a reader that cannot tell the two apart loops forever on a
    /// closed connection.
    pub fn read_bytes(&mut self, id: ResourceId) -> io::Result<Option<Vec<u8>>> {
        let Backing::Connection { stream, .. } = &mut self.entry(id)?.backing else {
            return Err(io::Error::from(io::ErrorKind::InvalidInput));
        };
        let mut buffer = [0u8; 4096];
        loop {
            match stream.read(&mut buffer) {
                Ok(0) => return Err(io::Error::from(io::ErrorKind::UnexpectedEof)),
                Ok(read) => return Ok(Some(buffer[..read].to_vec())),
                Err(err) if err.kind() == io::ErrorKind::WouldBlock => return Ok(None),
                Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
                Err(err) => return Err(err),
            }
        }
    }

    pub fn write(&mut self, id: ResourceId, text: &str) -> io::Result<Option<()>> {
        let Backing::Connection { stream, written } = &mut self.entry(id)?.backing else {
            return Err(io::Error::from(io::ErrorKind::InvalidInput));
        };
        let bytes = text.as_bytes();
        loop {
            if *written >= bytes.len() {
                *written = 0;
                return Ok(Some(()));
            }
            match stream.write(&bytes[*written..]) {
                Ok(0) => {
                    *written = 0;
                    return Err(io::Error::from(io::ErrorKind::WriteZero));
                }
                Ok(wrote) => *written += wrote,
                Err(err) if err.kind() == io::ErrorKind::WouldBlock => return Ok(None),
                Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
                Err(err) => {
                    *written = 0;
                    return Err(err);
                }
            }
        }
    }

    // ---------------------------------------------------------------- files and flows

    /// Create (or truncate) a file as a write-only sink.
    pub fn file_create(&mut self, path: &str) -> io::Result<ResourceId> {
        let file = std::fs::File::create(path)?;
        Ok(self.push(ResourceKind::File, Backing::File(file)))
    }

    /// Open a file and wrap it as a flow. The length is read once, here: a file that shrinks
    /// under the transfer surfaces as `UnexpectedEof` rather than a short flow that looks whole.
    pub fn flow_of_file(&mut self, path: &str) -> io::Result<ResourceId> {
        let file = std::fs::File::open(path)?;
        let remaining = file.metadata()?.len();
        Ok(self.push(
            ResourceKind::Flow,
            Backing::Flow(FlowEntry {
                source: FlowSource::File(file),
                remaining,
                buffered: Vec::new(),
                buffered_written: 0,
                transferred: 0,
            }),
        ))
    }

    /// Drive one flow-to-sink transfer forward by one observable step. The caller loops on
    /// `Chunk` — emitting a trace line per delivered chunk is its business — and parks on the
    /// `Park` variants, re-asking from the top when woken; every intermediate state lives in the
    /// `FlowEntry`, so re-asking is safe.
    pub fn pipe_step(&mut self, flow: ResourceId, sink: ResourceId) -> io::Result<PipeProgress> {
        // The flow entry comes out of its slot so that the sink can be reached mutably beside it.
        // Nothing in between can close either — this is one synchronous step of one task.
        let slot = self
            .entries
            .get_mut(flow.index())
            .and_then(Option::take)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotConnected))?;
        let Backing::Flow(mut state) = slot.backing else {
            self.entries[flow.index()] = Some(slot);
            return Err(io::Error::from(io::ErrorKind::InvalidInput));
        };
        let outcome = self.flow_progress(&mut state, sink);
        self.entries[flow.index()] = Some(Entry {
            kind: slot.kind,
            backing: Backing::Flow(state),
        });
        outcome
    }

    fn flow_progress(
        &mut self,
        state: &mut FlowEntry,
        sink: ResourceId,
    ) -> io::Result<PipeProgress> {
        loop {
            // Flush the chunk in transit before touching the source: at most one chunk is ever
            // buffered, which is what makes the transfer demand-driven.
            while state.buffered_written < state.buffered.len() {
                match self.sink_write(sink, &state.buffered[state.buffered_written..])? {
                    Some(0) => return Err(io::Error::from(io::ErrorKind::WriteZero)),
                    Some(wrote) => state.buffered_written += wrote,
                    None => return Ok(PipeProgress::ParkWrite(sink)),
                }
            }
            if !state.buffered.is_empty() {
                let bytes = state.buffered.len();
                state.transferred += bytes as u64;
                state.buffered.clear();
                state.buffered_written = 0;
                return Ok(PipeProgress::Chunk(bytes));
            }
            if state.remaining == 0 {
                return Ok(PipeProgress::Done(state.transferred));
            }
            let want = state.remaining.min(4096) as usize;
            match &mut state.source {
                FlowSource::File(file) => {
                    let mut chunk = vec![0u8; want];
                    let read = loop {
                        match file.read(&mut chunk) {
                            Ok(read) => break read,
                            Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
                            Err(err) => return Err(err),
                        }
                    };
                    if read == 0 {
                        // The file shrank under the transfer: the promised length cannot arrive.
                        return Err(io::Error::from(io::ErrorKind::UnexpectedEof));
                    }
                    chunk.truncate(read);
                    state.remaining -= read as u64;
                    state.buffered = chunk;
                    state.buffered_written = 0;
                }
            }
        }
    }

    /// Push bytes at whatever kind of sink this is. `Ok(None)` means it would block.
    fn sink_write(&mut self, sink: ResourceId, data: &[u8]) -> io::Result<Option<usize>> {
        match &mut self.entry(sink)?.backing {
            Backing::File(file) => loop {
                match file.write(data) {
                    Ok(wrote) => return Ok(Some(wrote)),
                    Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
                    Err(err) => return Err(err),
                }
            },
            _ => Err(io::Error::from(io::ErrorKind::InvalidInput)),
        }
    }

    /// Close a resource. `false` means it was already closed, which the checker now rules out for
    /// anything a program says twice: `tcp_close` consumes its connection, so reaching that name
    /// again is a use after a move. `false` is still returned rather than trapped, because
    /// `scope_exit` and `release` sweep whatever a scope has left and neither knows what the other
    /// already took.
    pub fn close(&mut self, id: ResourceId) -> bool {
        let Some(slot) = self.entries.get_mut(id.index()) else {
            return false;
        };
        let Some(entry) = slot.take() else {
            return false;
        };
        let fd = entry.backing.fd();
        // Dropping the backing closes any descriptor it owns, so no interest may outlive it.
        drop(entry);
        if let Some(fd) = fd {
            self.interests.retain(|interest| interest.fd != fd);
        }
        true
    }

    pub fn watch(&mut self, id: ResourceId, write: bool, task: TaskId) -> io::Result<()> {
        let Some(fd) = self.entry(id)?.backing.fd() else {
            return Err(io::Error::from(io::ErrorKind::InvalidInput));
        };
        self.interests.retain(|interest| interest.task != task);
        self.interests.push(Interest { task, fd, write });
        Ok(())
    }

    pub fn clear(&mut self, task: TaskId) {
        self.interests.retain(|interest| interest.task != task);
    }

    /// Wait for readiness, up to `timeout` milliseconds, and return the tasks that may now proceed.
    ///
    /// An error or hang-up wakes the task too: the point of waking is to let the syscall report
    /// what happened, and the poller never interprets a condition it can hand to the language.
    pub fn wait(&mut self, timeout: Option<Millis>) -> io::Result<Vec<TaskId>> {
        if self.interests.is_empty() {
            return Ok(Vec::new());
        }
        let mut fds: Vec<PollFd> = self
            .interests
            .iter()
            .map(|interest| PollFd {
                fd: interest.fd,
                events: if interest.write { POLLOUT } else { POLLIN },
                revents: 0,
            })
            .collect();
        let timeout = match timeout {
            Some(millis) => millis.min(i32::MAX as Millis) as i32,
            None => -1,
        };

        let ready = loop {
            let count = unsafe { poll(fds.as_mut_ptr(), fds.len(), timeout) };
            if count >= 0 {
                break count;
            }
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(err);
        };
        if ready == 0 {
            return Ok(Vec::new());
        }

        let mut woken = Vec::new();
        for (index, entry) in fds.iter().enumerate() {
            if entry.revents != 0 {
                woken.push(self.interests[index].task);
            }
        }
        self.interests
            .retain(|interest| !woken.contains(&interest.task));
        Ok(woken)
    }
}
