pub use bytes::Bytes;
use smol_str::SmolStr;

/// A parsed S-expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExp {
    /// An atom: symbol, numeral, keyword, etc. Stored as-is from the source.
    Atom(SmolStr),
    /// A quoted string (contents are unescaped).
    String(SmolStr),
    /// A byte string (arbitrary bytes).
    ByteString(Bytes),
    /// A quoted symbol `|...|` (contents stored without delimiters).
    QuotedSymbol(SmolStr),
    /// A parenthesized list of S-expressions.
    List(Vec<SExp>),
}

/// What a bare `"..."` produces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringKind {
    /// UTF-8 string (SMT-LIB, Covalence).
    String,
    /// Byte sequence (WAT).
    ByteString,
}

/// A parse error with byte offset.
#[derive(Debug, Clone, thiserror::Error)]
#[error("offset {offset}: {message}")]
pub struct ParseError {
    pub offset: usize,
    pub message: String,
}
