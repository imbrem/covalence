//! Error type for the egglog bridge.

/// Errors raised by an [`EgglogBridge`](crate::bridge::EgglogBridge) or its
/// driver.
///
/// `NotImplemented` is the intended escape hatch: a kernel-redesign-in-flight
/// (or, more commonly here, an in-progress Stage) can leave individual
/// justification variants stubbed without breaking the bridge API.
#[derive(Debug, thiserror::Error)]
pub enum BridgeError {
    /// A required justification variant or rule is not yet wired through to
    /// the kernel. The string carries a short label so callers can route
    /// around (or surface) specific gaps.
    #[error("egglog justification not implemented: {0}")]
    NotImplemented(String),

    /// A [`Justification`](crate::proof::Justification) references a
    /// [`ProofId`](crate::proof::ProofId) the driver hasn't seen yet — the
    /// proof DAG was not in dependency order, or contains a dangling
    /// reference.
    #[error("undefined proof id: {0}")]
    UndefinedProof(u32),

    /// A [`Term`](crate::proof::Term) references a
    /// [`TermId`](crate::proof::TermId) outside the
    /// [`TermDag`](crate::proof::TermDag).
    #[error("undefined term id: {0}")]
    UndefinedTerm(u32),

    /// An egglog sort symbol was used before being declared.
    #[error("unknown sort: {0}")]
    UnknownSort(String),

    /// An egglog constructor/relation symbol was used before being declared.
    #[error("unknown constructor: {0}")]
    UnknownConstructor(String),

    /// A term arity disagreed with the constructor's declared arity.
    #[error("constructor `{name}` declared with {expected} params, got {actual}")]
    ArityMismatch {
        name: String,
        expected: usize,
        actual: usize,
    },

    /// Catch-all for shapes the bridge couldn't make sense of.
    #[error("malformed: {0}")]
    Malformed(String),
}
