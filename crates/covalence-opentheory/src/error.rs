//! Errors from the OpenTheory interpreter.

use covalence_hol::types::HolError;

/// Errors from the OpenTheory interpreter.
#[derive(Debug, thiserror::Error)]
pub enum OtError {
    #[error("stack underflow")]
    StackUnderflow,
    #[error("type error on stack: expected {expected}, got {got}")]
    TypeError { expected: String, got: String },
    #[error("unknown command: {0}")]
    UnknownCommand(String),
    #[error("parse error: {0}")]
    ParseError(String),
    #[error("dictionary key not found: {0}")]
    DictKeyNotFound(u32),
    #[error("kernel error: {0}")]
    KernelError(#[from] HolError),
    #[error("empty list")]
    EmptyList,
    #[error("unknown constant: {0}")]
    UnknownConstant(String),
    #[error("unknown type operator: {0}")]
    UnknownTypeOperator(String),
    #[error("axiom introduced: {0} hypotheses")]
    AxiomIntroduced(usize),
}
