use covalence_sexp::ParseError;

/// Errors that can occur when parsing or processing Alethe proofs.
#[derive(Debug, Clone, thiserror::Error)]
pub enum AletheError {
    #[error("S-expression parse error: {0}")]
    Parse(#[from] ParseError),

    #[error("unrecognized command: {0}")]
    UnrecognizedCommand(String),

    #[error("missing field: {0}")]
    MissingField(&'static str),

    #[error("expected symbol, got list")]
    ExpectedSymbol,

    #[error("expected list, got atom")]
    ExpectedList,
}
