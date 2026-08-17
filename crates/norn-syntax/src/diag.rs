//! Diagnostics and their rendering.
//!
//! Compiler diagnostics are part of the language's surface. They are rendered here rather than at
//! the call site so that every stage produces the same shape.

use crate::span::{SourceFile, Span};

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
    /// Short label printed under the caret, describing the span itself.
    pub label: Option<String>,
    /// Further spans this error is also about, each with its own label.
    ///
    /// A causality cycle is the construct that needs this: `a` depends on `b` and `b` on `a` is a
    /// fact about two declarations, and naming only one of them leaves the reader to find the
    /// other. Squeezing the second span into a note would lose the one thing that makes it
    /// actionable — the line and column an editor can jump to.
    pub secondary: Vec<(Span, String)>,
    /// Longer trailing remarks: why this is an error, or what to write instead.
    pub notes: Vec<String>,
}

impl Diagnostic {
    pub fn new(span: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            span,
            message: message.into(),
            label: None,
            secondary: Vec::new(),
            notes: Vec::new(),
        }
    }

    pub fn label(mut self, label: impl Into<String>) -> Diagnostic {
        self.label = Some(label.into());
        self
    }

    pub fn secondary(mut self, span: Span, label: impl Into<String>) -> Diagnostic {
        self.secondary.push((span, label.into()));
        self
    }

    pub fn note(mut self, note: impl Into<String>) -> Diagnostic {
        self.notes.push(note.into());
        self
    }
}

/// Render one diagnostic as `file:line:col`, the offending line, and a caret run, followed by one
/// further such block per secondary span and then the notes.
pub fn render(file: &SourceFile, d: &Diagnostic) -> String {
    // Every block in one diagnostic shares a gutter width, so the `|` rules line up down the whole
    // message even when a secondary span sits on a line with more digits than the primary.
    let gutter = std::iter::once(d.span)
        .chain(d.secondary.iter().map(|(span, _)| *span))
        .map(|span| file.line_col(span.start).0.to_string().len())
        .max()
        .unwrap_or(1);
    let pad = " ".repeat(gutter);

    let mut out = format!("error: {}\n", d.message);
    out.push_str(&snippet(file, gutter, d.span, d.label.as_deref()));
    for (span, label) in &d.secondary {
        out.push_str(&snippet(file, gutter, *span, Some(label)));
    }
    for note in &d.notes {
        out.push_str(&format!("{pad} = note: {note}\n"));
    }
    out
}

/// One `-->` block: the location, the source line, and the carets under the span.
fn snippet(file: &SourceFile, gutter: usize, span: Span, label: Option<&str>) -> String {
    let (line, col) = file.line_col(span.start);
    let text = file.line_text(line);
    let number = format!("{line:>gutter$}");
    let pad = " ".repeat(gutter);

    // The caret run stops at the end of the line so a multi-line span stays legible.
    let line_start = span.start - (col as u32 - 1);
    let visual_col = text[..(span.start - line_start) as usize].chars().count();
    let available = text.chars().count().saturating_sub(visual_col);
    let width = (span.len() as usize).clamp(1, available.max(1));

    let mut out = format!("{pad}--> {}:{line}:{col}\n", file.name);
    out.push_str(&format!("{pad} |\n"));
    out.push_str(&format!("{number} | {text}\n"));
    out.push_str(&format!(
        "{pad} | {}{}",
        " ".repeat(visual_col),
        "^".repeat(width)
    ));
    match label {
        Some(label) => out.push_str(&format!(" {label}\n")),
        None => out.push('\n'),
    }
    out
}

pub fn render_all(file: &SourceFile, diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(|d| render(file, d))
        .collect::<Vec<_>>()
        .join("\n")
}
