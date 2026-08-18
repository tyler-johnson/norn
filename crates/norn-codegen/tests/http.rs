//! The HTTP hello server as a native binary.
//!
//! The native counterpart of `crates/norn-nir/tests/http.rs`: the same program on a real clock
//! and a real socket, so the trace cannot be compared byte for byte — the port and the wakeup
//! order belong to the operating system. What is asserted instead is the same structural claim:
//! a real client gets the response, and everything the server opened, it closed.

mod common;

use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;

#[test]
fn the_native_hello_server_answers_and_closes_every_socket() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/http/hello.norn");
    let (nir, main) = common::build(&path);
    let binary = common::native(&nir, main, "http-hello");

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

    let mut client = TcpStream::connect(("127.0.0.1", port)).expect("the server is listening");
    client
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    client
        .write_all(b"GET /anything HTTP/1.1\r\nHost: localhost\r\n\r\n")
        .unwrap();
    let mut response = String::new();
    client
        .read_to_string(&mut response)
        .expect("the server responds and closes");
    let (head, body) = response
        .split_once("\r\n\r\n")
        .expect("the response has a head");
    assert!(
        head.starts_with("HTTP/1.1 200 OK\r\n"),
        "unexpected status: {head}"
    );
    assert!(head.contains("\r\nContent-Length: 16"), "{head}");
    assert!(head.contains("\r\nConnection: close"), "{head}");
    assert_eq!(body, "hello from norn\n");

    // The server ends itself on the timer in `main`.
    let output = child.wait_with_output().expect("the server finishes");
    let trace = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(output.status.success(), "the server failed:\n{trace}");

    let opened = resources(&trace, "open");
    let closed = resources(&trace, "close");
    assert!(
        opened.len() >= 2,
        "expected a listener and a connection:\n{trace}"
    );
    assert_eq!(opened, closed, "a resource was left open:\n{trace}");
}

/// The resource handles named by one kind of trace event, in the order they appear.
fn resources(trace: &str, verb: &str) -> Vec<String> {
    let mut found: Vec<String> = trace
        .lines()
        .filter_map(|line| {
            let mut fields = line.split_whitespace().skip(2);
            (fields.next() == Some(verb)).then(|| fields.next().unwrap_or_default().to_string())
        })
        .collect();
    found.sort();
    found
}
