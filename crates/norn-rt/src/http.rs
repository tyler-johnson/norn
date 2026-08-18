//! An HTTP/1.1 request head, parsed and printed — the pure half of M6's HTTP surface.
//!
//! The parsing and printing here touch no socket and no resource table: bytes in, structure out,
//! so every wire decision is unit-testable without a connection. The stateful side — gathering a
//! head across reads, streaming a body, stepping a response — lives in `poll.rs`; the `Cx`
//! methods at the bottom of this file orchestrate it and carry the protocol policy.
//!
//! The v0 wire is deliberately small: request line plus headers, strict CRLF, bodies delimited by
//! `Content-Length` only, and `Connection: close` on every response. `Transfer-Encoding` is
//! rejected outright rather than half-supported — chunked bodies and keep-alive are recorded as
//! deferred in `BOOTSTRAP.md` §8. Every flow in v0 therefore knows its length up front, and a
//! close-delimited body has no representation at all.

/// The most bytes a head may occupy, terminator included. A client that has sent this much
/// without a blank line is not speaking a protocol this server wants to hear more of.
pub const HEAD_CAP: usize = 8192;

/// A parsed request head. Header names are lowercased at parse time, so lookup is
/// case-insensitive by construction rather than by everyone remembering.
pub struct Head {
    pub method: String,
    pub path: String,
    pub headers: Vec<(String, String)>,
    /// The declared body length; absent means zero, exactly as HTTP says for requests.
    pub content_length: u64,
}

impl Head {
    pub fn header(&self, name: &str) -> Option<&str> {
        let wanted = name.to_ascii_lowercase();
        self.headers
            .iter()
            .find(|(name, _)| *name == wanted)
            .map(|(_, value)| value.as_str())
    }
}

/// What one attempt to parse a head out of the gathered bytes produced.
///
/// The caller re-parses the whole buffer on every attempt rather than resuming a half-parsed
/// state: the buffer is capped at [`HEAD_CAP`], so the wasted work is bounded and the state that
/// has to survive a park is just the bytes.
pub enum HeadParse {
    /// The blank line has not arrived yet: gather more and ask again.
    Incomplete,
    /// A complete head, and how many bytes of the buffer it consumed. Anything after the offset
    /// is the first piece of the body.
    Complete(Head, usize),
    /// These bytes are not a request this server accepts. The wording surfaces in no trap and no
    /// `IoError` payload — malformed input becomes `Err(IoError.Other("InvalidData"))` at the
    /// language level — but it names the rule for whoever is reading the runtime.
    Invalid(&'static str),
}

pub fn parse_head(gathered: &[u8]) -> HeadParse {
    let Some(end) = find_terminator(gathered) else {
        if gathered.len() >= HEAD_CAP {
            return HeadParse::Invalid("the request head exceeds 8192 bytes");
        }
        return HeadParse::Incomplete;
    };
    if end > HEAD_CAP {
        return HeadParse::Invalid("the request head exceeds 8192 bytes");
    }
    // Everything before the terminator must be text; HTTP header fields are ASCII on this wire.
    let Ok(text) = std::str::from_utf8(&gathered[..end - 4]) else {
        return HeadParse::Invalid("the request head is not ASCII text");
    };

    let mut lines = text.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split(' ');
    let (Some(method), Some(path), Some(version), None) =
        (parts.next(), parts.next(), parts.next(), parts.next())
    else {
        return HeadParse::Invalid("the request line is not `METHOD PATH HTTP/1.1`");
    };
    if method.is_empty() || !method.bytes().all(|b| b.is_ascii_uppercase()) {
        return HeadParse::Invalid("the method is not an upper-case token");
    }
    if path.is_empty() {
        return HeadParse::Invalid("the request path is empty");
    }
    if version != "HTTP/1.1" {
        return HeadParse::Invalid("only HTTP/1.1 is spoken here");
    }

    let mut headers = Vec::new();
    for line in lines {
        // A bare LF inside the head would have produced a line with a stray `\n`; the split on
        // `\r\n` already enforced strict CRLF by construction.
        let Some((name, value)) = line.split_once(':') else {
            return HeadParse::Invalid("a header line has no `:`");
        };
        if name.is_empty() || name.contains(' ') || name.contains('\t') {
            return HeadParse::Invalid("a header name is not a token");
        }
        headers.push((name.to_ascii_lowercase(), value.trim().to_string()));
    }

    if headers.iter().any(|(name, _)| name == "transfer-encoding") {
        return HeadParse::Invalid("Transfer-Encoding is not supported; bodies are Content-Length");
    }
    let mut lengths = headers.iter().filter(|(name, _)| name == "content-length");
    let content_length = match (lengths.next(), lengths.next()) {
        (None, _) => 0,
        (Some((_, value)), None) => match value.parse::<u64>() {
            Ok(length) => length,
            Err(_) => return HeadParse::Invalid("Content-Length is not a number"),
        },
        (Some(_), Some(_)) => return HeadParse::Invalid("Content-Length appears twice"),
    };

    let head = Head {
        method: method.to_string(),
        path: path.to_string(),
        headers,
        content_length,
    };
    HeadParse::Complete(head, end)
}

fn find_terminator(gathered: &[u8]) -> Option<usize> {
    gathered
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .map(|at| at + 4)
}

/// The response head, byte for byte. Every response declares its length and closes the
/// connection: keep-alive is deferred, and saying so on the wire is what keeps clients from
/// waiting on a socket this server is about to drop.
pub fn render_head(status: i64, content_length: u64) -> String {
    format!(
        "HTTP/1.1 {status} {}\r\nContent-Length: {content_length}\r\nConnection: close\r\n\r\n",
        reason(status)
    )
}

/// The reason phrases a v0 server can want. Anything else gets an empty phrase, which HTTP
/// permits; the *status* is range-checked at the builtin, where an impossible number traps.
pub fn reason(status: i64) -> &'static str {
    match status {
        200 => "OK",
        201 => "Created",
        204 => "No Content",
        400 => "Bad Request",
        404 => "Not Found",
        405 => "Method Not Allowed",
        500 => "Internal Server Error",
        _ => "",
    }
}

// ---------------------------------------------------------------- the Cx surface
//
// The HTTP methods a task body can ask for, beside the protocol they speak — the same by-concern
// split that puts scope methods in `scope.rs`. The stateful stepping they orchestrate lives in
// `poll.rs`; what lives here is the protocol policy: what gets built, what gets closed, and when.

use std::io;

use crate::poll::{GatherProgress, ResourceId};
use crate::{Cx, Poll, Trap};

impl<'e, V: Clone> Cx<'_, 'e, V> {
    /// Read a request head off a connection. Consumes the connection in the language and converts
    /// its table entry in place, so the id — and the trace's `open` line — carries over. Failure
    /// closes the socket: the caller gave it up by asking, and an `Err` is all it gets back.
    pub fn http_read_request(&mut self, connection: ResourceId) -> Poll<io::Result<ResourceId>> {
        match self.core.readiness.request_read_step(connection) {
            Ok(GatherProgress::Ready) => {
                self.finish_wait();
                Poll::Ready(Ok(connection))
            }
            Ok(GatherProgress::Wait) => self.park_on(connection, false),
            Err(err) => {
                self.finish_wait();
                self.close(connection);
                Poll::Ready(Err(err))
            }
        }
    }

    pub fn request_method(&mut self, request: ResourceId) -> io::Result<String> {
        Ok(self.core.readiness.request_head(request)?.method.clone())
    }

    pub fn request_path(&mut self, request: ResourceId) -> io::Result<String> {
        Ok(self.core.readiness.request_head(request)?.path.clone())
    }

    pub fn request_header(
        &mut self,
        request: ResourceId,
        name: &str,
    ) -> io::Result<Option<String>> {
        Ok(self
            .core
            .readiness
            .request_head(request)?
            .header(name)
            .map(str::to_string))
    }

    /// Open the request's body as a scope-owned flow, seeded with whatever body bytes arrived
    /// alongside the head. A second take is a trap — two flows over one stream would each see
    /// half the bytes — and the trap is built here so both engines word it identically.
    pub fn request_body(&mut self, request: ResourceId) -> Result<ResourceId, Trap> {
        match self.core.readiness.request_body_flow(request) {
            Ok(Some(flow)) => {
                self.take_ownership(flow);
                Ok(flow)
            }
            Ok(None) => Err(Trap::new("the request body was already taken", "runtime")),
            Err(err) => Err(Trap::new(
                format!("`request_body`: {}", err.kind()),
                "runtime",
            )),
        }
    }

    /// Send a whole response — head and body in one buffer — and close the request. `Connection:
    /// close` is on the wire, so closing is not a policy choice; it is keeping the promise.
    pub fn http_respond(
        &mut self,
        request: ResourceId,
        status: i64,
        body: &str,
    ) -> Poll<io::Result<()>> {
        let mut data = render_head(status, body.len() as u64).into_bytes();
        data.extend_from_slice(body.as_bytes());
        if let Err(err) = self.core.readiness.respond_queue(request, data) {
            return self.respond_failed(request, err);
        }
        match self.core.readiness.respond_step(request) {
            Ok(Some(())) => {
                self.finish_wait();
                self.close(request);
                Poll::Ready(Ok(()))
            }
            Ok(None) => self.park_on(request, true),
            Err(err) => self.respond_failed(request, err),
        }
    }

    /// Send a response whose body is a flow: the head goes out first, then the body rides the
    /// pipe machinery — one chunk in flight, one trace line per chunk — and completion closes
    /// request and flow alike.
    pub fn http_respond_flow(
        &mut self,
        request: ResourceId,
        status: i64,
        flow: ResourceId,
    ) -> Poll<io::Result<()>> {
        let length = match self.core.readiness.flow_len(flow) {
            Ok(length) => length,
            Err(err) => {
                self.close(flow);
                return self.respond_failed(request, err);
            }
        };
        if let Err(err) = self
            .core
            .readiness
            .respond_queue(request, render_head(status, length).into_bytes())
        {
            self.close(flow);
            return self.respond_failed(request, err);
        }
        match self.core.readiness.respond_step(request) {
            Ok(Some(())) => {}
            Ok(None) => return self.park_on(request, true),
            Err(err) => {
                self.close(flow);
                return self.respond_failed(request, err);
            }
        }
        match self.pipe(flow, request) {
            Poll::Ready(Ok(_)) => Poll::Ready(Ok(())),
            Poll::Ready(Err(err)) => Poll::Ready(Err(err)),
            Poll::Pending => Poll::Pending,
        }
    }

    /// A response that cannot continue: the caller consumed the request, so the socket has no
    /// owner left with a way to reach it, and closing it here is what keeps the table clean.
    fn respond_failed(&mut self, request: ResourceId, err: io::Error) -> Poll<io::Result<()>> {
        self.finish_wait();
        self.close(request);
        Poll::Ready(Err(err))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn complete(bytes: &[u8]) -> (Head, usize) {
        match parse_head(bytes) {
            HeadParse::Complete(head, consumed) => (head, consumed),
            HeadParse::Incomplete => panic!("incomplete"),
            HeadParse::Invalid(why) => panic!("invalid: {why}"),
        }
    }

    fn invalid(bytes: &[u8]) -> &'static str {
        match parse_head(bytes) {
            HeadParse::Invalid(why) => why,
            _ => panic!("expected invalid"),
        }
    }

    #[test]
    fn a_get_parses() {
        let (head, consumed) = complete(b"GET /x HTTP/1.1\r\nHost: localhost\r\n\r\n");
        assert_eq!(head.method, "GET");
        assert_eq!(head.path, "/x");
        assert_eq!(head.content_length, 0);
        assert_eq!(head.header("HOST"), Some("localhost"));
        assert_eq!(consumed, 36);
    }

    #[test]
    fn the_body_starts_where_the_head_ends() {
        let bytes = b"PUT /f HTTP/1.1\r\nContent-Length: 5\r\n\r\nhello";
        let (head, consumed) = complete(bytes);
        assert_eq!(head.content_length, 5);
        assert_eq!(&bytes[consumed..], b"hello");
    }

    #[test]
    fn a_split_read_is_incomplete_until_the_blank_line() {
        let whole = b"GET / HTTP/1.1\r\nHost: a\r\n\r\n";
        for cut in 0..whole.len() {
            let attempt = parse_head(&whole[..cut]);
            assert!(
                matches!(attempt, HeadParse::Incomplete),
                "a prefix of {cut} bytes should be incomplete"
            );
        }
        assert!(matches!(parse_head(whole), HeadParse::Complete(..)));
    }

    #[test]
    fn malformed_request_lines_are_invalid() {
        assert_eq!(
            invalid(b"GET /\r\n\r\n"),
            "the request line is not `METHOD PATH HTTP/1.1`"
        );
        assert_eq!(
            invalid(b"get / HTTP/1.1\r\n\r\n"),
            "the method is not an upper-case token"
        );
        assert_eq!(
            invalid(b"GET / HTTP/1.0\r\n\r\n"),
            "only HTTP/1.1 is spoken here"
        );
        assert_eq!(
            invalid(b"GET / HTTP/1.1\r\nno-colon\r\n\r\n"),
            "a header line has no `:`"
        );
        assert_eq!(
            invalid(b"GET / HTTP/1.1\r\nbad name: x\r\n\r\n"),
            "a header name is not a token"
        );
    }

    #[test]
    fn content_length_must_be_one_number() {
        assert_eq!(
            invalid(b"PUT / HTTP/1.1\r\nContent-Length: ten\r\n\r\n"),
            "Content-Length is not a number"
        );
        assert_eq!(
            invalid(b"PUT / HTTP/1.1\r\nContent-Length: 1\r\nContent-Length: 2\r\n\r\n"),
            "Content-Length appears twice"
        );
    }

    #[test]
    fn transfer_encoding_is_rejected() {
        assert_eq!(
            invalid(b"POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n"),
            "Transfer-Encoding is not supported; bodies are Content-Length"
        );
    }

    #[test]
    fn an_endless_head_hits_the_cap() {
        let mut endless = b"GET / HTTP/1.1\r\n".to_vec();
        while endless.len() < HEAD_CAP {
            endless.extend_from_slice(b"X-Padding: yes\r\n");
        }
        assert_eq!(invalid(&endless), "the request head exceeds 8192 bytes");
        // A head whose terminator lands past the cap is no better than one with no terminator.
        endless.extend_from_slice(b"\r\n");
        assert_eq!(invalid(&endless), "the request head exceeds 8192 bytes");
    }

    #[test]
    fn response_heads_always_declare_length_and_close() {
        assert_eq!(
            render_head(204, 0),
            "HTTP/1.1 204 No Content\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
        );
        assert_eq!(
            render_head(418, 3),
            "HTTP/1.1 418 \r\nContent-Length: 3\r\nConnection: close\r\n\r\n"
        );
    }
}
