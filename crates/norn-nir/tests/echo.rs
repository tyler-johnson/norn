//! M2's done-when: a TCP echo server written in Norn runs under the interpreter, and cancelling its
//! scope closes every socket.
//!
//! The server runs on a worker thread with a channel-backed `Output`, so the test learns the port
//! the operating system chose from the first line the program prints. Shutdown is the timer in
//! `main`: when that scope closes, the accept loop and every connection it is serving are cancelled,
//! and the trace is the evidence that each descriptor went with them.

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
fn the_echo_server_echoes_and_closes_every_socket() {
    let (sender, printed) = channel();
    let server = std::thread::spawn(move || {
        let (nir, main) = common::build(&echo_path());
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
        // A real socket needs a real clock, so this is the one place M2 is timing-dependent. The
        // trace is still exact about what was opened and closed, which is what is being claimed.
        if let Err(trap) = outcome.value {
            panic!("the echo server trapped: {trap}");
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

    let mut client = TcpStream::connect(("127.0.0.1", port)).expect("the server is listening");
    client
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    client.write_all(b"hello norn").unwrap();
    let mut echoed = [0u8; 64];
    let read = client.read(&mut echoed).expect("the server replies");
    assert_eq!(&echoed[..read], b"hello norn");
    drop(client);

    let trace = server.join().expect("the server thread finishes");
    let opened = resources(&trace, "open");
    let closed = resources(&trace, "close");
    assert!(
        opened.len() >= 2,
        "expected a listener and a connection:\n{trace}"
    );
    assert_eq!(opened, closed, "a descriptor was left open:\n{trace}");
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

fn echo_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/tcp/echo.norn")
}
