//! Error types for the inductive-types API.

use smol_str::SmolStr;
use thiserror::Error;

/// Structural validation errors for portable datatype specifications.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum SpecError {
    /// A datatype/functor name must be non-empty.
    #[error("datatype name is empty")]
    EmptyTypeName,
    /// A spec must have at least one constructor.
    #[error("inductive spec `{0}` has no constructors")]
    EmptySpec(SmolStr),
    /// Constructor names must be distinct within a spec.
    #[error("duplicate constructor name `{0}`")]
    DuplicateCtor(SmolStr),
    /// Argument binder names must be distinct within a constructor.
    #[error("duplicate argument name `{arg}` in constructor `{ctor}`")]
    DuplicateArg { ctor: SmolStr, arg: SmolStr },
    /// Constructor / argument names must be non-empty.
    #[error("empty name in constructor #{ctor}")]
    EmptyName { ctor: usize },
    /// Aggregate field names must be non-empty.
    #[error("empty field name at position {field} in `{aggregate}`")]
    EmptyFieldName { aggregate: SmolStr, field: usize },
    /// Field names must be distinct within one product.
    #[error("duplicate field name `{field}` in `{aggregate}`")]
    DuplicateField { aggregate: SmolStr, field: SmolStr },
    /// Records and ordinary variants cannot contain the functor variable.
    #[error("aggregate `{0}` contains a recursive position")]
    UnexpectedVariable(SmolStr),
}

/// An API-level error, generic over the logic's own error type `E`
/// ([`crate::Logic::Error`]).
///
/// The blanket `From<E>` lets backend code use `?` on the logic's native
/// operations directly.
#[derive(Debug, Error)]
pub enum InductiveError<E> {
    /// An error from the underlying logic (term construction, rule
    /// application, …).
    #[error("logic error: {0}")]
    Logic(#[source] E),
    /// The spec is structurally ill-formed.
    #[error("spec error: {0}")]
    Spec(SpecError),
    /// Constructor index out of range.
    #[error("constructor index {index} out of range ({arity} constructors)")]
    CtorIndex { index: usize, arity: usize },
    /// Argument index out of range for a constructor.
    #[error("argument index {index} out of range for constructor `{ctor}` ({arity} arguments)")]
    ArgIndex {
        ctor: SmolStr,
        index: usize,
        arity: usize,
    },
    /// A slice argument had the wrong length.
    #[error("{what}: expected {expected} items, got {got}")]
    Arity {
        what: &'static str,
        expected: usize,
        got: usize,
    },
    /// The backend cannot realize this spec, or cannot supply this fact.
    /// Honest capability reporting — see [`crate::BackendCaps`].
    #[error("unsupported by this backend — {what}: {why}")]
    Unsupported { what: &'static str, why: String },
    /// The spec does not match what this backend realizes (e.g. an adapter
    /// for one carved type asked to realize a different spec).
    #[error("spec mismatch: {0}")]
    SpecMismatch(String),
    /// An internal invariant of a backend derivation failed (a bug in the
    /// backend, never in the consumer).
    #[error("backend internal error: {0}")]
    Internal(String),
}

impl<E> From<E> for InductiveError<E> {
    fn from(e: E) -> Self {
        InductiveError::Logic(e)
    }
}

impl<E> InductiveError<E> {
    /// Wrap a [`SpecError`] (no blanket `From` to avoid overlap with the
    /// `From<E>` blanket).
    pub fn spec(e: SpecError) -> Self {
        InductiveError::Spec(e)
    }
}

/// Result alias for bundle/backend operations in logic `L`.
pub type IndResult<T, L> = Result<T, InductiveError<<L as crate::Logic>::Error>>;
