// The runtime prelude of every generated program.
//
// This file is not a module of norn-codegen: `lib.rs` carries it as a string and `emit.rs` writes
// it into the generated source ahead of the per-program part. Since the typed backend (BOOTSTRAP
// §8 item 6a) the value semantics live in the generated code itself — bodies are fully typed, and
// what remains here is the scaffolding that is the same for every program: the driver loop, the
// body impls, the entry point, and the scalar helpers whose trap texts must match the
// interpreter's byte for byte (`norn-nir/src/interp.rs` words every one of them; the differential
// oracle catches a drifted byte in stderr).
//
// The restricted-Rust charter (BOOTSTRAP.md §3), as it is interpreted here: structs, enums,
// `match`, loops, `Rc`, and calls into `norn-rt`; no `async`, no trait definitions, no generic
// definitions, and no named lifetimes — `'static` data-section references and the elided `'_` in
// signatures the runtime ABI dictates are the whole of what appears. Implementing `Body<Value>`
// and `Graph<Value>` at the one concrete `Value` is the sanctioned ABI, not a generic definition.
// Everything in this file maps mechanically onto a Cranelift backend.
//
// The emitted header provides the imports: `Rc`, `io`, `ExitCode`, and the `norn_rt` names. The
// per-program part provides, and this file may name freely:
//
//   enum Value                              the boundary enum: scalars, handles, one variant per aggregate
//   enum TaskVal                            a built task: one variant per task fn and used task builtin
//   enum Frame                              one variant per task fn, holding its typed locals
//   static FN_NAMES: &[&str]                every function's name, by id
//   const MAIN_FN: usize                    the entry point
//   fn task_name(&TaskVal) -> &'static str
//   fn step_frame(&mut Frame, &mut Cx, Option<Value>) -> Result<Cont, Trap>
//   fn push_frame(&TaskVal, &mut Vec<Frame>) -> Result<(), Trap>
//   fn poll_task(&mut Cx, &TaskVal) -> Result<Poll<Value>, Trap>   task builtins; the home of io mapping
//   fn call_plain(usize, Option<&mut Cx>) -> Result<Value, Trap>   a single MAIN arm
//   fn make_body(&Value) -> Result<Box<dyn Body<Value>>, Trap>
//   fn root_task() -> Value                 the task main() blocks on
//   fn finish(Value) -> ExitCode            main's result convention, typed by main's return
//   struct Nodes + impl Graph<Value>        the reactor engine
//   fn reactor_specs() -> Vec<ReactorSpec>  the plan, as plain data

// ---------------------------------------------------------------- frames

// A suspended task is a stack of frames, innermost last. Each task fn's frame is a generated
// struct of its typed locals plus `state`, which numbers the emitted match arms: `2*b` runs block
// `b` whole, `2*b + 1` re-executes only its terminator — waking re-asks a suspension point
// without re-running the instructions before it. When an awaited callee returns, the driver hands
// its value to the caller's next step as `resumed`; the caller's odd arm writes it typed and
// jumps, and a `None` at the same arm means re-ask the runtime (a parked builtin).
pub enum Cont {
    Return(Value),
    Park,
    AwaitTask(Rc<TaskVal>),
}

// Run until the task finishes or suspends. Parking leaves every frame's state where it was, so
// waking re-executes the same suspension point and asks the runtime again.
fn resume_frames(frames: &mut Vec<Frame>, cx: &mut Cx<'_, '_, Value>) -> Result<Step<Value>, Trap> {
    let mut resumed: Option<Value> = None;
    loop {
        let frame = frames
            .last_mut()
            .expect("a running task has at least one frame");
        match step_frame(frame, cx, resumed.take())? {
            Cont::Park => return Ok(Step::Park),
            Cont::AwaitTask(task) => push_frame(&task, frames)?,
            Cont::Return(value) => {
                frames.pop().expect("the frame being returned from");
                if frames.is_empty() {
                    // The outermost frame returning is the task finishing.
                    return Ok(Step::Done(value));
                }
                resumed = Some(value);
            }
        }
    }
}

// ---------------------------------------------------------------- bodies

pub struct FnBody {
    name: &'static str,
    frames: Vec<Frame>,
}

impl Body<Value> for FnBody {
    fn resume(&mut self, cx: &mut Cx<'_, '_, Value>) -> Step<Value> {
        match resume_frames(&mut self.frames, cx) {
            Ok(step) => step,
            Err(trap) => Step::Trap(trap),
        }
    }

    fn name(&self) -> &str {
        self.name
    }
}

pub struct BuiltinBody {
    task: Rc<TaskVal>,
}

impl Body<Value> for BuiltinBody {
    fn resume(&mut self, cx: &mut Cx<'_, '_, Value>) -> Step<Value> {
        match poll_task(cx, &self.task) {
            Ok(Poll::Ready(value)) => Step::Done(value),
            Ok(Poll::Pending) => Step::Park,
            Err(trap) => Step::Trap(trap),
        }
    }

    fn name(&self) -> &str {
        task_name(&self.task)
    }
}

// A plain function run as a task: it never parks, so one resumption is the whole run. Only `main`
// can arrive here — every other task value is built from a `task fn` or a builtin.
pub struct PlainBody {
    func: usize,
}

impl Body<Value> for PlainBody {
    fn resume(&mut self, cx: &mut Cx<'_, '_, Value>) -> Step<Value> {
        match call_plain(self.func, Some(cx)) {
            Ok(value) => Step::Done(value),
            Err(trap) => Step::Trap(trap),
        }
    }

    fn name(&self) -> &str {
        FN_NAMES[self.func]
    }
}

// ---------------------------------------------------------------- operators

// Purity's trap of last resort: emitted code in a turn-called function has no `Cx` to hand over,
// so every observable operation is an arm that has to ask for one and cannot get it.
fn impure_trap(what: &str) -> Trap {
    Trap::new(
        format!("`{what}` cannot run during a turn: a reactor node is pure"),
        "turn",
    )
}

fn div_i64(a: i64, b: i64, func: &str) -> Result<i64, Trap> {
    if b == 0 {
        return Err(Trap::new("divide by zero", func));
    }
    // Wrapping: `i64::MIN / -1` does not trap, exactly like the interpreter.
    Ok(a.wrapping_div(b))
}

fn rem_i64(a: i64, b: i64, func: &str) -> Result<i64, Trap> {
    if b == 0 {
        return Err(Trap::new("remainder by zero", func));
    }
    Ok(a.wrapping_rem(b))
}

// Float ordering traps on NaN — the one value-interpolating trap reachable from well-typed code.
// The text spells the interpreter's `{:?}` of its Float values over the raw f64s.
fn cmp_f64(a: f64, b: f64, func: &str) -> Result<std::cmp::Ordering, Trap> {
    match a.partial_cmp(&b) {
        Some(ordering) => Ok(ordering),
        None => Err(Trap::new(
            format!("cannot order Float({a:?}) and Float({b:?})"),
            func,
        )),
    }
}

fn str_concat(a: Rc<str>, b: Rc<str>) -> Rc<str> {
    format!("{a}{b}").into()
}

// ---------------------------------------------------------------- bytes

fn bytes_slice(data: Rc<[u8]>, start: i64, end: i64, func: &str) -> Result<Rc<[u8]>, Trap> {
    let len = data.len() as i64;
    if start < 0 || end < start || end > len {
        return Err(Trap::new(
            format!("`bytes_slice` out of range: {start}..{end} of {len}"),
            func,
        ));
    }
    // A slice copies in v0, deliberately matching the interpreter; the cheap representation is
    // 6b's Bytes views.
    Ok(data[start as usize..end as usize].into())
}

fn byte(value: i64, func: &str) -> Result<Rc<[u8]>, Trap> {
    if value < 0 || value > 255 {
        return Err(Trap::new(format!("`byte` out of range: {value}"), func));
    }
    Ok([value as u8].into())
}

fn bytes_concat(a: Rc<[u8]>, b: Rc<[u8]>) -> Rc<[u8]> {
    // Concatenation copies in v0, deliberately matching the interpreter; `+` on Bytes is 6b's.
    [&a[..], &b[..]].concat().into()
}

fn bytes_at(data: Rc<[u8]>, index: i64, func: &str) -> Result<i64, Trap> {
    let len = data.len() as i64;
    if index < 0 || index >= len {
        return Err(Trap::new(
            format!("byte index out of range: {index} of {len}"),
            func,
        ));
    }
    Ok(data[index as usize] as i64)
}

fn text_unchecked(data: Rc<[u8]>, func: &str) -> Result<Rc<str>, Trap> {
    match std::str::from_utf8(&data) {
        Ok(text) => Ok(text.into()),
        Err(err) => Err(Trap::new(
            format!(
                "`text_unchecked` given invalid UTF-8 at byte {}",
                err.valid_up_to()
            ),
            func,
        )),
    }
}

// ---------------------------------------------------------------- rendering

// The float spelling, shared by every generated renderer: `{}` plus a `.0` suffix when nothing
// marks the text as non-integral. `NaN` gains the suffix too — the check is for the lowercase
// letters of `inf` and exponents — and that quirk is part of the contract.
fn render_float(v: f64) -> String {
    let text = format!("{v}");
    if text.contains(['.', 'e', 'E', 'n', 'i']) {
        text
    } else {
        format!("{text}.0")
    }
}

// ---------------------------------------------------------------- entry

// The generated binary's whole interface, mirroring `norn run` byte for byte from the point where
// the front end has finished: the same flags, the same output conventions, the same exit codes.
fn main() -> ExitCode {
    let mut trace = false;
    let mut virtual_clock = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--trace" => trace = true,
            "--virtual-clock" => virtual_clock = true,
            flag if flag.starts_with('-') => {
                eprintln!("norn: unknown option `{flag}`");
                return ExitCode::FAILURE;
            }
            arg => {
                eprintln!("norn: unexpected argument `{arg}`");
                return ExitCode::FAILURE;
            }
        }
    }

    let config = Config {
        clock: if virtual_clock {
            Clock::simulated()
        } else {
            Clock::real()
        },
        trace,
    };
    let mut out = Stdout;
    let engine = Engine {
        make: Box::new(|value: &Value| make_body(value)),
        graph: Box::new(Nodes),
        reactors: reactor_specs(),
    };
    let mut runtime = Runtime::new(config, &mut out, engine);
    let value = runtime.block_on(root_task());
    if trace {
        eprint!("{}", runtime.trace().render());
    }
    match value {
        // A `main` returning a `Result` reports rather than prints; `finish` is generated against
        // main's static return type, exactly as `norn run` decides by the value's shape.
        Ok(value) => finish(value),
        Err(trap) => {
            eprintln!("norn: trapped: {trap}");
            ExitCode::FAILURE
        }
    }
}
