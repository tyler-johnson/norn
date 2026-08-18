//! The prelude must compile on its own.
//!
//! `src/prelude.rs` is carried as a string and only ever compiled inside generated programs, so
//! without this test the first thing to notice a broken prelude would be a `norn build`. Here it
//! is included under stub versions of everything the generated part normally provides, with
//! `norn-rt` as a dev-dependency standing in for the embedded rlib.

#[allow(warnings)]
mod generated {
    use std::io;
    use std::process::ExitCode;
    use std::rc::Rc;

    use norn_rt::graph::{InputSpec, ReactorSpec};
    use norn_rt::{
        Body, Clock, Config, Cx, Effect, Engine, Graph, Handled, NodeSpec, Overflow, Poll,
        ReactorId, ResourceId, ResourceKind, Runtime, Stdout, Step, Trap, Update,
    };

    // The generated contract, stubbed: one plain `main` with no locals and no reactors.
    static RECORDS: &[RecordLayout] = &[];
    static ENUMS: &[EnumLayout] = &[];
    static FN_NAMES: &[&str] = &["main"];
    static FN_LOCALS: &[usize] = &[0];
    static FN_IS_TASK: &[bool] = &[false];
    const MAIN_FN: usize = 0;

    fn step_frame(frame: &mut Frame, cx: &mut Cx<'_, '_, Value>) -> Result<Cont, Trap> {
        Err(Trap::new(
            "resumed a function that is not a task",
            "runtime",
        ))
    }

    fn call_plain(
        func: usize,
        cx: Option<&mut Cx<'_, '_, Value>>,
        args: Vec<Value>,
    ) -> Result<Value, Trap> {
        Ok(Value::Unit)
    }

    struct Nodes;

    impl Graph<Value> for Nodes {
        fn create(&self, reactor: usize, args: Vec<Value>) -> Result<Vec<Value>, Trap> {
            Err(Trap::new(
                "created a reactor that does not exist",
                "runtime",
            ))
        }

        fn handle(
            &self,
            reactor: usize,
            input: usize,
            message: Value,
            slots: &[Value],
        ) -> Result<Handled<Value>, Trap> {
            Err(Trap::new(
                "a message for an input that does not exist",
                "runtime",
            ))
        }

        fn recompute(
            &self,
            reactor: usize,
            node: usize,
            deps: &[Value],
        ) -> Result<Update<Value>, Trap> {
            Err(Trap::new(
                "recomputed a node that is not a signal",
                "runtime",
            ))
        }
    }

    fn reactor_specs() -> Vec<ReactorSpec> {
        Vec::new()
    }

    include!("../src/prelude.rs");

    pub fn touch() {
        let _ = main;
    }
}

/// The include above is the test: everything in the prelude has to type-check against the real
/// `norn-rt` before any generated program exists.
#[test]
fn the_prelude_compiles() {
    generated::touch();
}
