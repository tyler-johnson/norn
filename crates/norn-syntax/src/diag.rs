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
    /// Longer trailing remarks: why this is an error, or what to write instead.
    pub notes: Vec<String>,
}

impl Diagnostic {
    pub fn new(span: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            span,
            message: message.into(),
            label: None,
            notes: Vec::new(),
        }
    }

    pub fn label(mut self, label: impl Into<String>) -> Diagnostic {
        self.label = Some(label.into());
        self
    }

    pub fn note(mut self, note: impl Into<String>) -> Diagnostic {
        self.notes.push(note.into());
        self
    }
}

/// Render one diagnostic as `file:line:col`, the offending line, and a caret run.
pub fn render(file: &SourceFile, d: &Diagnostic) -> String {
    let (line, col) = file.line_col(d.span.start);
    let text = file.line_text(line);
    let gutter = line.to_string();
    let pad = " ".repeat(gutter.len());

    // The caret run stops at the end of the line so a multi-line span stays legible.
    let line_start = d.span.start - (col as u32 - 1);
    let visual_col = text[..(d.span.start - line_start) as usize].chars().count();
    let available = text.chars().count().saturating_sub(visual_col);
    let width = (d.span.len() as usize).clamp(1, available.max(1));

    let mut out = String::new();
    out.push_str(&format!("error: {}\n", d.message));
    out.push_str(&format!("{pad}--> {}:{line}:{col}\n", file.name));
    out.push_str(&format!("{pad} |\n"));
    out.push_str(&format!("{gutter} | {text}\n"));
    out.push_str(&format!(
        "{pad} | {}{}",
        " ".repeat(visual_col),
        "^".repeat(width)
    ));
    match &d.label {
        Some(label) => out.push_str(&format!(" {label}\n")),
        None => out.push('\n'),
    }
    for note in &d.notes {
        out.push_str(&format!("{pad} = note: {note}\n"));
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
