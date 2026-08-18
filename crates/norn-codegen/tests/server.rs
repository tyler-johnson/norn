//! The reactor-gated server as a native binary.
//!
//! The native counterpart of `crates/norn-nir/tests/server.rs`: a reactor counting what the M2
//! echo server holds open, driven by real clients on a real clock. The snapshot line and the
//! turn/publish structure of the trace are the assertions; the port is the operating system's.

mod common;

use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;

#[test]
fn the_native_server_counts_what_it_is_holding_open() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/reactors/server.norn");
    let (nir, main) = common::build(&path);
    let binary = common::native(&nir, main, "reactors-server");

    let mut child = Command::new(&binary)
        .arg("--trace")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the built binary starts");
    let mut lines = BufReader::new(child.stdout.take().expect("stdout is piped"));
    let mut announced = String::new();
    lines
        .read_line(&mut announced)
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

    let mut snapshot = String::new();
    lines
        .read_line(&mut snapshot)
        .expect("the server prints its final snapshot");
    assert_eq!(
        snapshot.trim_end(),
        "#Snapshot(accepted: 2, open: 0, healthy: true)",
        "the reactor did not see both connections open and close"
    );

    let output = child.wait_with_output().expect("the server finishes");
    let trace = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(output.status.success(), "the server failed:\n{trace}");

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
