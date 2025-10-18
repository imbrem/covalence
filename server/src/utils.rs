use lsp_types::Position;

/// A line map
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LineMap {
    /// The byte offsets of each line, in sorted order
    line_starts: Vec<usize>,
}

impl LineMap {
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, byte) in text.bytes().enumerate() {
            if byte == b'\n' {
                line_starts.push(i + 1);
            }
        }
        Self { line_starts }
    }

    pub fn line_number(&self, byte_offset: usize) -> usize {
        // Binary search to find the line
        match self.line_starts.binary_search(&byte_offset) {
            Ok(line) => line,
            Err(line) => line.saturating_sub(1),
        }
    }

    pub fn byte_offset_to_position(&self, text: &str, byte_offset: usize) -> Position {
        let line = self.line_number(byte_offset);

        let line_start = self.line_starts[line];
        let line_text = &text[line_start..byte_offset.min(text.len())];

        // Count UTF-16 code units for the column
        // This can probably be optimized too...
        let column = line_text.encode_utf16().count() as u32;

        Position::new(line as u32, column)
    }
}
