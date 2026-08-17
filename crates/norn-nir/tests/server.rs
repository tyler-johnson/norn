//! Turns and tasks composing: a reactor driven by a real socket.
//!
//! `examples/reactors/server.norn` is `examples/tcp/echo.norn` with a reactor counting what the
//! server is holding open. Nothing about the reactor knows there is a socket and nothing about the
//! socket code knows there is a graph; they meet at an ordinary `send` from ordinary task code.
//!
//! Driven by a real client on a real clock, so it lives here rather than in the golden corpus: the
//! port the operating system chooses is not a thing a snapshot can hold.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::sync::mpsc::{Sender, channel};
use std::time::Duration;

use norn_nir::{Clock, Config, Output, execute, lower};
use norn_syntax::{SourceFile, parse, render_all};

struct Channel(Sender<String>);

impl Output for Channel {
    fn line(&mut self, text: &str) {
        let _ = self.0.send(text.to_string());
    }
}

#[test]
fn a_reactor_counts_what_the_server_is_holding_open() {
    let (sender, printed) = channel();
    let server = std::thread::spawn(move || {
        let path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/reactors/server.norn");
        let source = std::fs::read_to_string(&path).unwrap();
        let file = SourceFile::new(path.display().to_string(), source.clone());

        let parsed = parse(&source);
        assert!(
            parsed.ok(),
            "the server does not parse:\n{}",
            render_all(&file, &parsed.errors)
        );
        let checked = norn_hir::check(&parsed.module);
        assert!(
            checked.ok(),
            "the server does not check:\n{}",
            render_all(&file, &checked.errors)
        );

        let nir = lower(&checked.program);
        let main = checked.program.main.expect("the server has a `main`");
        let mut out = Channel(sender);
        let outcome = execute(
            &nir,
            main.index(),
            &mut out,
            Config {
                clock: Clock::real(),
                trace: true,
            },
        );
        if let Err(trap) = outcome.value {
            panic!("the server trapped: {trap}");
        }
        outcome.trace
    });

    let announced = printed
        .recv_timeout(Duration::from_secs(10))
        .expect("the server prints the port it bound");
    let port: u16 = announced
        .trim()
        .parse()
        .unwrap_or_else(|_| panic!("expected a port number, got {announced:?}"));

    for message in [b"one".as_slice(), b"two".as_slice()] {
        let mut client = TcpStream::connect(("127.0.0.1", port)).expect("the server is listening");
        client
            .set_read_timeout(Some(Duration::from_secs(10)))
            .unwrap();
        client.write_all(message).unwrap();
        let mut echoed = [0u8; 64];
        let read = client.read(&mut echoed).expect("the server replies");
        assert_eq!(&echoed[..read], message);
    }

    let snapshot = printed
        .recv_timeout(Duration::from_secs(10))
        .expect("the server prints its final snapshot");
    assert_eq!(
        snapshot, "#Snapshot(accepted: 2, open: 0, healthy: true)",
        "the reactor did not see both connections open and close"
    );

    let trace = server.join().expect("the server thread finishes");
    // Two connections, four messages, four turns — and never two of them at once.
    let turns: Vec<&str> = trace
        .lines()
        .filter(|line| line.contains(" turn "))
        .collect();
    assert_eq!(turns.len(), 4, "expected four turns:\n{trace}");
    for (expected, line) in turns.iter().enumerate() {
        assert!(
            line.contains(&format!(" turn {expected} ")),
            "turns are not consecutive:\n{trace}"
        );
    }
    // Every turn publishes, and every publish follows the turn that produced it.
    assert_eq!(
        trace
            .lines()
            .filter(|line| line.contains(" publish "))
            .count(),
        5,
        "expected one publish per turn plus the one at creation:\n{trace}"
    );
    assert!(
        trace.contains("R0 create Gate"),
        "the reactor was never created:\n{trace}"
    );
}
