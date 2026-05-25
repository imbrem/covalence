use crate::StringKind;

/// SAX-style event handler for S-expression parsing.
///
/// The visitor provides both configuration (trivia parsing, delimiters)
/// and receives parsing events (atoms, strings, lists).
pub trait SExpVisitor {
    /// Parse and skip whitespace/comments from the input stream.
    fn parse_trivia(&mut self, input: &mut &str);

    /// Delimiter for quoted symbols: `Some(b'|')` for SMT-LIB/Covalence, `None` for WAT.
    fn quoted_symbol_delim(&self) -> Option<u8>;

    /// What a bare `"..."` produces: String or ByteString.
    fn bare_string_kind(&self) -> StringKind;

    /// Whether `b"..."` explicit bytestring prefix is supported.
    fn supports_byte_prefix(&self) -> bool;

    // --- Events ---

    /// A `(` was encountered.
    fn open_list(&mut self);

    /// A `)` was encountered.
    fn close_list(&mut self);

    /// An atom token was parsed.
    fn atom(&mut self, text: &str);

    /// A string literal was parsed (UTF-8 content).
    fn string(&mut self, content: &str);

    /// A byte string was parsed.
    fn bytestring(&mut self, content: &[u8]);

    /// A quoted symbol `|...|` was parsed (content without delimiters).
    fn quoted_symbol(&mut self, content: &str);
}
