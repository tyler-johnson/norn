//! The file server as a native binary — the repo's stated goal, held to the same script as the
//! interpreter run in `crates/norn-nir/tests/files.rs`.
//!
//! The working directory is per-process here, so `Command::current_dir` does what the interpreter
//! test needed `set_current_dir` for, and this file has no isolation constraint. The clock and
//! the sockets are real, so the trace is compared structurally rather than byte for byte: every
//! resource the server opened — request, flow, and file, the abandoned upload's among them — has
//! a matching close.

mod common;

use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

#[test]
fn the_native_file_server_streams_both_ways_and_cancellation_closes_everything() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("files-native");
    std::fs::create_dir_all(&dir).unwrap();
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/http/files.norn");
    let (nir, main) = common::build(&path);
    let binary = common::native(&nir, main, "http-files");

    let mut child = Command::new(&binary)
        .arg("--trace")
        .current_dir(&dir)
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

    // The cancellation claim, exactly as in the interpreter test: a long-promised body, a sliver
    // delivered, and the socket held open through the server's shutdown.
    let mut abandoned = TcpStream::connect(("127.0.0.1", port)).unwrap();
    abandoned
        .write_all(b"PUT /abandoned.bin HTTP/1.1\r\nContent-Length: 100000\r\n\r\n0123456789")
        .unwrap();

    // The server ends itself on the timer in `main`.
    let output = child.wait_with_output().expect("the server finishes");
    drop(abandoned);
    let trace = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(output.status.success(), "the server failed:\n{trace}");

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
    assert!(
        trace
            .lines()
            .any(|line| line.split_whitespace().nth(2) == Some("pipe")),
        "no pipe chunk was traced:\n{trace}"
    );
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
