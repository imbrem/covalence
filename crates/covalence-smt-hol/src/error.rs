//! Error type for the Alethe → HOL bridge.

use covalence_hol::types::HolError;
use covalence_smt::AletheError;

/// Errors raised by an [`AletheBridge`](crate::bridge::AletheBridge) or its driver.
///
/// `NotImplemented` is the intended escape hatch: a kernel-redesign-in-flight
/// can leave individual Alethe rules stubbed without breaking the bridge API.
#[derive(Debug, thiserror::Error)]
pub enum BridgeError {
    /// A required Alethe rule is not yet wired through to the kernel.
    #[error("Alethe rule not implemented: {0}")]
    NotImplemented(String),

    /// The Alethe proof references an unknown rule name.
    #[error("unknown Alethe rule: {0}")]
    UnknownRule(String),

    /// A `:premises` (or `:discharge`) id refers to a step that hasn't been seen.
    #[error("undefined step id: {0}")]
    UndefinedStep(String),

    /// An SMT-LIB sort symbol was used before being declared.
    #[error("unknown sort: {0}")]
    UnknownSort(String),

    /// An SMT-LIB function/constant symbol was used before being declared.
    #[error("unknown function: {0}")]
    UnknownFun(String),

    /// A sort/term S-expression was structurally malformed.
    #[error("malformed S-expression: {0}")]
    Malformed(String),

    /// Sort declaration with parametric arity > 0 is not yet supported.
    #[error("parametric sort `{name}` (arity {arity}) not yet supported")]
    ParametricSort { name: String, arity: u32 },

    /// An Alethe-level error (parse, structural).
    #[error(transparent)]
    Alethe(#[from] AletheError),

    /// An underlying HOL kernel error.
    #[error(transparent)]
    Hol(#[from] HolError),
}
