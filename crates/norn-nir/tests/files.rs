//! The file server under the interpreter: M6's done-when, driven end to end.
//!
//! This test is alone in its file on purpose: the example resolves paths against the working
//! directory, and `set_current_dir` is process-global, so nothing else may share the test binary.
//! (The native twin passes `Command::current_dir` instead and needs no such care.)
//!
//! The script covers both streaming directions and the cancellation claim the pipe tests could
//! not make: a PUT big enough to take multiple chunks lands on disk byte for byte; a GET streams
//! it back with the right `Content-Length`; a GET for a missing file is a 404; and a PUT that
//! promises 100,000 bytes and delivers 10 is still parked in `save_body`'s read loop when the
//! server's scope closes — cancellation must close the connection and the half-written file,
//! which is what open==close over a trace containing `file` and `flow` opens asserts (the `flow`
//! is the GET download's). The partial file left on disk by the abandoned upload is accepted v0
//! behaviour.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::sync::mpsc::{Sender, channel};
use std::time::Duration;

use norn_nir::{Clock, Config, Output, execute};

mod common;

struct Channel(Sender<String>);

impl Output for Channel {
    fn line(&mut self, text: &str) {
        let _ = self.0.send(text.to_string());
    }
}

#[test]
fn the_file_server_streams_both_ways_and_cancellation_closes_everything() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("files-interp");
    std::fs::create_dir_all(&dir).unwrap();
    std::env::set_current_dir(&dir).unwrap();

    let (sender, printed) = channel();
    let server = std::thread::spawn(move || {
        // The entry path is absolute, so the `set_current_dir` above cannot bend where the
        // loader's reads resolve — `normalize` preserves the leading `/`.
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/http/files.norn");
        let (nir, main) = common::build(&path);
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
            panic!("the file server trapped: {trap}");
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

    // A body long enough to need three pipe chunks, so the upload streams rather than fits.
    let payload: Vec<u8> = (0..10_240u32).map(|i| (i % 239) as u8).collect();

    let put = exchange(
        port,
        &[
            format!(
                "PUT /upload.bin HTTP/1.1\r\nContent-Length: {}\r\n\r\n",
                payload.len()
            )
            .into_bytes(),
            payload.clone(),
        ]
        .concat(),
    );
    let (head, _) = split_response(&put);
    assert!(
        head.starts_with("HTTP/1.1 204 No Content\r\n"),
        "unexpected PUT response: {head}"
    );
    assert_eq!(
        std::fs::read(dir.join("upload.bin")).unwrap(),
        payload,
        "the upload did not land on disk intact"
    );

    let get = exchange(port, b"GET /upload.bin HTTP/1.1\r\n\r\n");
    let (head, body) = split_response(&get);
    assert!(head.starts_with("HTTP/1.1 200 OK\r\n"), "{head}");
    assert!(head.contains("\r\nContent-Length: 10240"), "{head}");
    assert_eq!(body, payload, "the download differs");

    let missing = exchange(port, b"GET /missing.bin HTTP/1.1\r\n\r\n");
    let (head, _) = split_response(&missing);
    assert!(
        head.starts_with("HTTP/1.1 404 Not Found\r\n"),
        "unexpected response for a missing file: {head}"
    );

    // `..` traversal is refused before the method is dispatched.
    let traversal = exchange(port, b"GET /../upload.bin HTTP/1.1\r\n\r\n");
    let (head, body) = split_response(&traversal);
    assert!(
        head.starts_with("HTTP/1.1 400 Bad Request\r\n"),
        "a `..` path was not refused: {head}"
    );
    assert_eq!(body, b"bad path\n", "unexpected 400 body");

    // The cancellation claim: promise a long body, deliver a sliver, and hold the socket open
    // through the server's shutdown. The handler is parked on the body flow when the scope
    // closes, and the close lines for its request, flow, and file must appear all the same.
    let mut abandoned = TcpStream::connect(("127.0.0.1", port)).unwrap();
    abandoned
        .write_all(b"PUT /abandoned.bin HTTP/1.1\r\nContent-Length: 100000\r\n\r\n0123456789")
        .unwrap();

    let trace = server.join().expect("the server thread finishes");
    drop(abandoned);

    let opened = resources(&trace, "open");
    let closed = resources(&trace, "close");
    assert_eq!(opened, closed, "a resource was left open:\n{trace}");
    let kinds: Vec<&str> = trace
        .lines()
        .filter(|line| line.split_whitespace().nth(2) == Some("open"))
        .filter_map(|line| line.split_whitespace().nth(4))
        .collect();
    assert!(kinds.contains(&"file"), "no file was opened:\n{trace}");
    assert!(kinds.contains(&"flow"), "no flow was opened:\n{trace}");
}

/// One whole HTTP exchange, bytes in and bytes out. The server closes after responding, so
/// reading to EOF is the protocol.
fn exchange(port: u16, request: &[u8]) -> Vec<u8> {
    let mut client = TcpStream::connect(("127.0.0.1", port)).expect("the server is listening");
    client
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    client.write_all(request).unwrap();
    let mut response = Vec::new();
    client
        .read_to_end(&mut response)
        .expect("the server responds and closes");
    response
}

/// The head as text — it is ASCII by construction — and the body as the bytes it is.
fn split_response(response: &[u8]) -> (String, &[u8]) {
    let at = response
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .expect("the response has a head");
    (
        String::from_utf8_lossy(&response[..at + 4]).into_owned(),
        &response[at + 4..],
    )
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
