/// Errors that can occur when parsing DIMACS CNF or DRAT files.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseError {
    #[error("missing problem header line (expected `p cnf <vars> <clauses>`)")]
    MissingHeader,

    #[error("line {line}: invalid header: {message}")]
    InvalidHeader { line: usize, message: String },

    #[error("line {line}: invalid literal: {message}")]
    InvalidLiteral { line: usize, message: String },

    #[error("line {line}: unterminated clause (missing trailing 0)")]
    UnterminatedClause { line: usize },

    #[error("clause count mismatch: header declared {declared}, found {actual}")]
    ClauseCountMismatch { declared: usize, actual: usize },

    #[error("line {line}: expected integer, got `{token}`")]
    ExpectedInteger { line: usize, token: String },

    #[error("unexpected end of input")]
    UnexpectedEof,

    #[error("invalid binary encoding at offset {offset}")]
    InvalidBinaryEncoding { offset: usize },
}
