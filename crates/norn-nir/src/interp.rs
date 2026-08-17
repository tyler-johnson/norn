//! The NIR interpreter.
//!
//! Calls are managed with an explicit frame stack rather than the host call stack. Nothing in M1
//! needs that — pure functions could recurse on Rust's stack quite happily — but suspension in M2
//! does, and retrofitting it would mean rewriting every path that can call. Resuming a frame is
//! already just picking a `(block, instruction)` back up.

use std::fmt::Write as _;
use std::rc::Rc;

use norn_hir::hir::{BinOp, Builtin, UnOp};

use crate::nir::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    Unit,
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Rc<str>),
    Record(usize, Rc<Vec<Value>>),
    Variant(usize, usize, Rc<Vec<Value>>),
}

/// A condition the compiler could not rule out. Not a Rust panic: the interpreter reports it the
/// way the native runtime will have to.
#[derive(Debug)]
pub struct Trap {
    pub message: String,
    pub function: String,
}

impl std::fmt::Display for Trap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (in `{}`)", self.message, self.function)
    }
}

/// Where a program's output goes. Tests capture it; `norn run` writes it through.
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

struct Frame {
    function: FnId,
    locals: Vec<Value>,
    block: BlockId,
    instr: usize,
    /// Where this frame's result goes in its caller, and which frame that is.
    dest: Option<Place>,
}

pub fn run(program: &Program, entry: FnId, out: &mut dyn Output) -> Result<Value, Trap> {
    Interpreter { program, out }.run(entry)
}

struct Interpreter<'a> {
    program: &'a Program,
    out: &'a mut dyn Output,
}

impl Interpreter<'_> {
    fn run(&mut self, entry: FnId) -> Result<Value, Trap> {
        let mut stack = vec![self.frame(entry, Vec::new(), None)];

        loop {
            let frame = stack
                .last_mut()
                .expect("the stack is never empty while running");
            let function = &self.program.fns[frame.function];
            let block = &function.blocks[frame.block];

            // Run the straight-line part of the block, then act on its terminator.
            if frame.instr < block.instrs.len() {
                let Instr::Assign(place, rvalue) = &block.instrs[frame.instr];
                frame.instr += 1;

                if let Rvalue::Call(callee, args) = rvalue {
                    let arguments: Vec<Value> =
                        args.iter().map(|arg| read_operand(frame, arg)).collect();
                    let dest = place.clone();
                    let callee = *callee;
                    stack.push(self.frame(callee, arguments, Some(dest)));
                    continue;
                }

                let value = self.eval(frame, rvalue)?;
                write_place(frame, place, value);
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
                Term::Trap(message) => {
                    let message = message.to_string();
                    return Err(self.trap(frame, message));
                }
                Term::Return(operand) => {
                    let value = read_operand(frame, operand);
                    let finished = stack.pop().expect("the frame being returned from");
                    match (finished.dest, stack.last_mut()) {
                        (Some(dest), Some(caller)) => write_place(caller, &dest, value),
                        _ => return Ok(value),
                    }
                }
            }
        }
    }

    fn frame(&self, function: FnId, args: Vec<Value>, dest: Option<Place>) -> Frame {
        let def = &self.program.fns[function];
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

    fn trap(&self, frame: &Frame, message: impl Into<String>) -> Trap {
        Trap {
            message: message.into(),
            function: self.program.fns[frame.function].name.clone(),
        }
    }

    fn eval(&mut self, frame: &Frame, rvalue: &Rvalue) -> Result<Value, Trap> {
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
                match builtin {
                    Builtin::Print => {
                        let text = self.render(&args[0]);
                        self.out.line(&text);
                        Value::Unit
                    }
                }
            }
            Rvalue::Record(id, args) => {
                let fields = args.iter().map(|arg| read_operand(frame, arg)).collect();
                Value::Record(*id, Rc::new(fields))
            }
            Rvalue::Variant(enum_id, variant, args) => {
                let fields = args.iter().map(|arg| read_operand(frame, arg)).collect();
                Value::Variant(*enum_id, *variant, Rc::new(fields))
            }
            Rvalue::Call(..) => unreachable!("calls are handled by the frame stack"),
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
            Value::Record(id, fields) => {
                let layout = &self.program.records[*id];
                let mut out = format!("#{}(", layout.name);
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
                let builtin = *enum_id == norn_hir::hir::EnumId::OPTION.index()
                    || *enum_id == norn_hir::hir::EnumId::RESULT.index();
                let mut out = if builtin {
                    format!("#{}", variant.name)
                } else {
                    format!("#{}.{}", layout.name, variant.name)
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
            Value::Record(_, fields) | Value::Variant(_, _, fields) => &fields[*index],
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
            Value::Record(_, fields) | Value::Variant(_, _, fields) => {
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
    let mut sink = Captured::default();
    Interpreter {
        program,
        out: &mut sink,
    }
    .render(value)
}
