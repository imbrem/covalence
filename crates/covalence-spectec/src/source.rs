//! Source locations and diagnostics.
//!
//! Spans carry a [`FileId`] so they survive being moved across file
//! boundaries; a [`SourceMap`] resolves them back to (file, line, column)
//! for display.

use std::fmt;
use std::num::NonZeroU32;
use std::path::PathBuf;

/// Opaque file identifier. Allocated by [`SourceMap::add`].
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct FileId(NonZeroU32);

impl FileId {
    pub(crate) fn new(idx: usize) -> Self {
        let raw = u32::try_from(idx + 1).expect("FileId overflow");
        Self(NonZeroU32::new(raw).expect("idx+1 is always nonzero"))
    }

    fn index(self) -> usize {
        usize::try_from(self.0.get() - 1).expect("u32 fits in usize")
    }
}

/// A half-open byte range `[start, end)` in a known file.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(file: FileId, start: u32, end: u32) -> Self {
        debug_assert!(start <= end, "Span start must be <= end");
        Self { file, start, end }
    }

    /// Smallest span containing both `self` and `other`. Both must share `file`.
    pub fn join(self, other: Span) -> Span {
        debug_assert_eq!(self.file, other.file, "cannot join cross-file spans");
        Span {
            file: self.file,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    pub fn len(self) -> u32 {
        self.end - self.start
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }
}

/// Registry of source files. Owns the source text so spans remain valid.
#[derive(Default, Debug)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

#[derive(Debug)]
struct SourceFile {
    name: PathBuf,
    text: String,
    /// Byte offsets of each line start. `line_starts[0] == 0`.
    line_starts: Vec<u32>,
}

impl SourceMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a source file. Returns a [`FileId`] usable for [`Span`]s into the text.
    pub fn add(&mut self, name: impl Into<PathBuf>, text: impl Into<String>) -> FileId {
        let text = text.into();
        let line_starts = compute_line_starts(&text);
        let id = FileId::new(self.files.len());
        self.files.push(SourceFile {
            name: name.into(),
            text,
            line_starts,
        });
        id
    }

    pub fn name(&self, id: FileId) -> &std::path::Path {
        &self.files[id.index()].name
    }

    pub fn text(&self, id: FileId) -> &str {
        &self.files[id.index()].text
    }

    /// Resolve a byte offset to a 1-based `(line, column)` pair. Column is
    /// counted in bytes, not characters; callers wanting display columns
    /// should iterate `char_indices` over the line slice themselves.
    pub fn line_col(&self, id: FileId, byte_offset: u32) -> (u32, u32) {
        let file = &self.files[id.index()];
        let line = match file.line_starts.binary_search(&byte_offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let col = byte_offset - file.line_starts[line];
        (u32::try_from(line + 1).expect("line in u32"), col + 1)
    }

    /// Slice of the original source corresponding to the span.
    pub fn snippet(&self, span: Span) -> &str {
        let text = self.text(span.file);
        &text[span.start as usize..span.end as usize]
    }
}

fn compute_line_starts(text: &str) -> Vec<u32> {
    let mut out = Vec::with_capacity(text.len() / 32 + 1);
    out.push(0);
    for (i, b) in text.bytes().enumerate() {
        if b == b'\n' {
            out.push(u32::try_from(i + 1).expect("source files fit in u32"));
        }
    }
    out
}

/// Severity of a diagnostic.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Severity {
    Error,
    Warning,
}

/// A diagnostic with a primary location and optional secondary notes.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: String,
    pub primary: Span,
    pub notes: Vec<(Span, String)>,
}

impl Diagnostic {
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            message: message.into(),
            primary: span,
            notes: Vec::new(),
        }
    }

    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warning,
            message: message.into(),
            primary: span,
            notes: Vec::new(),
        }
    }

    pub fn with_note(mut self, span: Span, message: impl Into<String>) -> Self {
        self.notes.push((span, message.into()));
        self
    }
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Severity::Error => f.write_str("error"),
            Severity::Warning => f.write_str("warning"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_basic() {
        let mut map = SourceMap::new();
        let id = map.add("test", "abc\ndef\n\nxyz");
        assert_eq!(map.line_col(id, 0), (1, 1));
        assert_eq!(map.line_col(id, 2), (1, 3));
        assert_eq!(map.line_col(id, 3), (1, 4)); // newline column
        assert_eq!(map.line_col(id, 4), (2, 1));
        assert_eq!(map.line_col(id, 8), (3, 1)); // blank line
        assert_eq!(map.line_col(id, 9), (4, 1));
    }

    #[test]
    fn span_join() {
        let mut map = SourceMap::new();
        let id = map.add("test", "0123456789");
        let a = Span::new(id, 1, 4);
        let b = Span::new(id, 6, 9);
        let j = a.join(b);
        assert_eq!(j.start, 1);
        assert_eq!(j.end, 9);
    }

    #[test]
    fn snippet_roundtrip() {
        let mut map = SourceMap::new();
        let id = map.add("test", "hello world");
        let span = Span::new(id, 6, 11);
        assert_eq!(map.snippet(span), "world");
    }

    #[test]
    fn multiple_files_have_distinct_ids() {
        let mut map = SourceMap::new();
        let a = map.add("a", "x");
        let b = map.add("b", "y");
        assert_ne!(a, b);
        assert_eq!(map.name(a).to_str(), Some("a"));
        assert_eq!(map.name(b).to_str(), Some("b"));
    }
}
