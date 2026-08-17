//! The lowered IR.
//!
//! NIR is flat: each function is a list of basic blocks, each block a straight run of assignments
//! ending in one terminator. Nothing nests, nothing is implicit — `match` has become switches and
//! branches, `&&` has become control flow, `?` has become an early return.
//!
//! Flatness is the point. When tasks arrive in M2, a suspension point splits a block and the
//! function becomes a state machine over the same representation; when native code arrives in M5,
//! the backend walks these blocks and prints. Neither step should have to understand `match`.

use std::rc::Rc;

use norn_hir::hir::{BinOp, Builtin, UnOp};

pub type BlockId = usize;
pub type LocalId = usize;
pub type FnId = usize;

pub struct Program {
    pub records: Vec<RecordLayout>,
    pub enums: Vec<EnumLayout>,
    pub fns: Vec<Function>,
    pub main: Option<FnId>,
}

/// Names are kept so that a value can be rendered in the surface syntax that built it.
pub struct RecordLayout {
    pub name: String,
    pub fields: Vec<String>,
}

pub struct EnumLayout {
    pub name: String,
    pub variants: Vec<VariantLayout>,
}

pub struct VariantLayout {
    pub name: String,
    pub fields: Vec<String>,
    /// Whether the payload was declared positionally, which decides how it is printed.
    pub positional: bool,
}

pub struct Function {
    pub name: String,
    pub params: usize,
    pub locals: Vec<String>,
    pub blocks: Vec<Block>,
}

#[derive(Default)]
pub struct Block {
    pub instrs: Vec<Instr>,
    pub term: Term,
}

pub enum Instr {
    Assign(Place, Rvalue),
}

/// A local, optionally projected into: `x`, `x.2`, `x.0.1`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Place {
    pub local: LocalId,
    pub proj: Vec<usize>,
}

impl Place {
    pub fn local(local: LocalId) -> Place {
        Place {
            local,
            proj: Vec::new(),
        }
    }

    pub fn field(&self, index: usize) -> Place {
        let mut proj = self.proj.clone();
        proj.push(index);
        Place {
            local: self.local,
            proj,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Operand {
    Const(Const),
    Copy(Place),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Const {
    Unit,
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Rc<str>),
}

pub enum Rvalue {
    Use(Operand),
    Unary(UnOp, Operand),
    Binary(BinOp, Operand, Operand),
    Call(FnId, Vec<Operand>),
    Builtin(Builtin, Vec<Operand>),
    Record(usize, Vec<Operand>),
    Variant(usize, usize, Vec<Operand>),
}

pub enum Term {
    Goto(BlockId),
    Branch {
        cond: Operand,
        then: BlockId,
        els: BlockId,
    },
    /// Dispatch on the variant tag of an enum value.
    SwitchTag {
        scrutinee: Place,
        cases: Vec<(usize, BlockId)>,
        default: BlockId,
    },
    Return(Operand),
    /// A state the checker could not rule out and the program must not reach.
    Trap(&'static str),
}

impl Default for Term {
    fn default() -> Term {
        Term::Trap("block was never terminated")
    }
}

/// Render a program in the textual form `norn nir` prints. This is a debugging surface and the
/// artifact M5 will diff the native backend against, so it is deliberately explicit.
pub fn print(program: &Program) -> String {
    let mut out = String::new();
    for (id, record) in program.records.iter().enumerate() {
        out.push_str(&format!(
            "record {} #{id} ({})\n",
            record.name,
            record.fields.join(", ")
        ));
    }
    for (id, def) in program.enums.iter().enumerate() {
        let variants: Vec<String> = def
            .variants
            .iter()
            .map(|v| format!("{}/{}", v.name, v.fields.len()))
            .collect();
        out.push_str(&format!(
            "enum {} #{id} ({})\n",
            def.name,
            variants.join(", ")
        ));
    }
    if !program.records.is_empty() || !program.enums.is_empty() {
        out.push('\n');
    }

    for (id, function) in program.fns.iter().enumerate() {
        let params: Vec<String> = (0..function.params)
            .map(|i| local_name(function, i))
            .collect();
        out.push_str(&format!(
            "fn {} #{id}({})\n",
            function.name,
            params.join(", ")
        ));
        for index in function.params..function.locals.len() {
            out.push_str(&format!("    local {}\n", local_name(function, index)));
        }
        for (index, block) in function.blocks.iter().enumerate() {
            out.push_str(&format!("  b{index}:\n"));
            for instr in &block.instrs {
                let Instr::Assign(place, rvalue) = instr;
                out.push_str(&format!(
                    "    {} = {}\n",
                    print_place(function, place),
                    print_rvalue(program, function, rvalue)
                ));
            }
            out.push_str(&format!("    {}\n", print_term(function, &block.term)));
        }
        out.push('\n');
    }
    out
}

fn local_name(function: &Function, index: usize) -> String {
    match function.locals.get(index) {
        Some(name) if !name.is_empty() => format!("_{index}/{name}"),
        _ => format!("_{index}"),
    }
}

fn print_place(function: &Function, place: &Place) -> String {
    let mut out = local_name(function, place.local);
    for index in &place.proj {
        out.push_str(&format!(".{index}"));
    }
    out
}

fn print_operand(function: &Function, operand: &Operand) -> String {
    match operand {
        Operand::Const(c) => print_const(c),
        Operand::Copy(place) => print_place(function, place),
    }
}

fn print_const(value: &Const) -> String {
    match value {
        Const::Unit => "()".into(),
        Const::Int(v) => v.to_string(),
        Const::Float(v) => format!("{v:?}"),
        Const::Bool(v) => v.to_string(),
        Const::Str(v) => format!("{:?}", &**v),
    }
}

fn print_rvalue(program: &Program, function: &Function, rvalue: &Rvalue) -> String {
    let args = |operands: &[Operand]| {
        operands
            .iter()
            .map(|o| print_operand(function, o))
            .collect::<Vec<_>>()
            .join(", ")
    };
    match rvalue {
        Rvalue::Use(operand) => print_operand(function, operand),
        Rvalue::Unary(op, operand) => {
            format!("{} {}", unary_name(*op), print_operand(function, operand))
        }
        Rvalue::Binary(op, lhs, rhs) => format!(
            "{} {} {}",
            print_operand(function, lhs),
            binary_name(*op),
            print_operand(function, rhs)
        ),
        Rvalue::Call(id, operands) => {
            format!("call {}#{id}({})", program.fns[*id].name, args(operands))
        }
        Rvalue::Builtin(builtin, operands) => {
            format!("builtin {}({})", builtin.name(), args(operands))
        }
        Rvalue::Record(id, operands) => {
            format!("#{}({})", program.records[*id].name, args(operands))
        }
        Rvalue::Variant(enum_id, variant, operands) => {
            let def = &program.enums[*enum_id];
            format!(
                "#{}.{}({})",
                def.name,
                def.variants[*variant].name,
                args(operands)
            )
        }
    }
}

fn print_term(function: &Function, term: &Term) -> String {
    match term {
        Term::Goto(target) => format!("goto b{target}"),
        Term::Branch { cond, then, els } => {
            format!(
                "branch {} ? b{then} : b{els}",
                print_operand(function, cond)
            )
        }
        Term::SwitchTag {
            scrutinee,
            cases,
            default,
        } => {
            let cases: Vec<String> = cases
                .iter()
                .map(|(tag, block)| format!("{tag} => b{block}"))
                .collect();
            format!(
                "switch tag {} [{}] else b{default}",
                print_place(function, scrutinee),
                cases.join(", ")
            )
        }
        Term::Return(operand) => format!("return {}", print_operand(function, operand)),
        Term::Trap(message) => format!("trap {message:?}"),
    }
}

fn unary_name(op: UnOp) -> &'static str {
    match op {
        UnOp::Neg => "neg",
        UnOp::Not => "not",
    }
}

fn binary_name(op: BinOp) -> &'static str {
    match op {
        BinOp::AddInt => "add.i",
        BinOp::SubInt => "sub.i",
        BinOp::MulInt => "mul.i",
        BinOp::DivInt => "div.i",
        BinOp::RemInt => "rem.i",
        BinOp::AddFloat => "add.f",
        BinOp::SubFloat => "sub.f",
        BinOp::MulFloat => "mul.f",
        BinOp::DivFloat => "div.f",
        BinOp::RemFloat => "rem.f",
        BinOp::Concat => "concat",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
    }
}
