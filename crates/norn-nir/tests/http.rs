//! The HTTP hello server under the interpreter: a real client gets a real response, and the
//! trace closes what it opens.
//!
//! The shape mirrors `tests/echo.rs`: the server runs on a worker thread with a channel-backed
//! `Output`, the test learns the port from the first printed line, and shutdown is the timer in
//! `main`. The socket is a plain connection its whole life — std/http's `read_request` borrows
//! it and `respond` consumes and closes it — so open==close pairs on the connection itself.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::sync::mpsc::{Sender, channel};
use std::time::Duration;

use norn_nir::{Clock, Config, Output, execute};

mod common;

/// Forwards each printed line to the test as it appears, rather than collecting them for the end.
struct Channel(Sender<String>);

impl Output for Channel {
    fn line(&mut self, text: &str) {
        let _ = self.0.send(text.to_string());
    }
}

#[test]
fn the_hello_server_answers_and_closes_every_socket() {
    let (sender, printed) = channel();
    let server = std::thread::spawn(move || {
        let (nir, main) = common::build(&hello_path());
        let mut out = Channel(sender);
        let outcome = execute(
            &nir,
            main,
            &mut out,
            Config {
                clock: Clock::real(),
                trace: true,
            },
        );
        if let Err(trap) = outcome.value {
            panic!("the hello server trapped: {trap}");
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

    let response = get(port, "/anything");
    let (status, headers, body) = split_response(&response);
    assert_eq!(status, "HTTP/1.1 200 OK");
    assert!(
        headers.contains(&"Content-Length: 16".to_string()),
        "no Content-Length in {headers:?}"
    );
    assert!(
        headers.contains(&"Connection: close".to_string()),
        "no Connection: close in {headers:?}"
    );
    assert_eq!(body, "hello from norn\n");

    let trace = server.join().expect("the server thread finishes");
    let opened = resources(&trace, "open");
    let closed = resources(&trace, "close");
    assert!(
        opened.len() >= 2,
        "expected a listener and a connection:\n{trace}"
    );
    assert_eq!(opened, closed, "a resource was left open:\n{trace}");
}

/// One whole HTTP exchange: the server closes after responding, so reading to EOF is the protocol.
fn get(port: u16, path: &str) -> String {
    let mut client = TcpStream::connect(("127.0.0.1", port)).expect("the server is listening");
    client
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    client
        .write_all(format!("GET {path} HTTP/1.1\r\nHost: localhost\r\n\r\n").as_bytes())
        .unwrap();
    let mut response = String::new();
    client
        .read_to_string(&mut response)
        .expect("the server responds and closes");
    response
}

fn split_response(response: &str) -> (&str, Vec<String>, &str) {
    let (head, body) = response
        .split_once("\r\n\r\n")
        .expect("the response has a head");
    let mut lines = head.split("\r\n");
    let status = lines.next().expect("the response has a status line");
    (status, lines.map(str::to_string).collect(), body)
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

fn hello_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/http/hello.norn")
}
