//! Errors from lexing or parsing a Dedukti `.dk` source.

/// An error produced while reading a `.dk` source. Byte offsets (`pos`) are
/// into the original source string; line/column rendering is a deferred
/// nicety (see the crate `SKELETONS.md`).
#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum DkError {
    /// The lexer hit a character it could not tokenise (e.g. a stray `=`, an
    /// unterminated `(; … ;)` comment, or an unterminated `{| … |}` identifier
    /// or `"…"` string).
    #[error("lex error at byte {pos}: {message}")]
    Lex {
        /// Byte offset into the source where lexing failed.
        pos: usize,
        /// Human-readable description.
        message: String,
    },

    /// The parser found a token it did not expect.
    #[error("parse error at byte {pos}: expected {expected}, found {found}")]
    Unexpected {
        /// Byte offset of the offending token.
        pos: usize,
        /// What the parser was looking for.
        expected: String,
        /// What it found instead.
        found: String,
    },

    /// A structural parse error not attributable to a single unexpected token.
    #[error("parse error at byte {pos}: {message}")]
    Parse {
        /// Byte offset into the source.
        pos: usize,
        /// Human-readable description.
        message: String,
    },

    /// The source ended while the parser still expected more input.
    #[error("unexpected end of input: expected {expected}")]
    UnexpectedEof {
        /// What the parser was looking for.
        expected: String,
    },
}
