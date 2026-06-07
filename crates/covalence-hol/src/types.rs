//! Shared HOL-Light name interning and error types.
//!
//! Concrete type/term/theorem representations live with each kernel
//! implementation (e.g. `HolPrim` in `covalence-shell`). This module
//! only carries the bits every backend agrees on: the `NameId`
//! namespace used by the OpenTheory `NameTable`, the well-known
//! constants reserved at the start of that table, and the unified
//! `HolError` returned by kernel methods.

/// Interned name — a 64-bit index into a name table.
pub type NameId = u64;

// ---------------------------------------------------------------------------
// Well-known constants
// ---------------------------------------------------------------------------

/// Well-known name ID for `->` (function type constructor).
/// Must be the first name interned in the NameTable (index 0).
pub const FUN_TYCON_ID: NameId = 0;

/// Well-known name ID for `bool` (boolean type constructor).
/// Must be the second name interned in the NameTable (index 1).
pub const BOOL_TYCON_ID: NameId = 1;

/// Well-known name ID for `=` (equality constant).
/// Must be the third name interned in the NameTable (index 2).
pub const EQ_CONST_ID: NameId = 2;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from HOL Light kernel operations.
#[derive(Debug, thiserror::Error)]
pub enum HolError {
    #[error("type mismatch: {0}")]
    TypeMismatch(String),
    #[error("not an equation")]
    NotAnEquation,
    #[error("not a beta-redex")]
    NotBetaRedex,
    #[error("term is not boolean")]
    NotBoolean,
    #[error("hypothesis variable is free in conclusion")]
    FreeVariable,
    #[error("variable capture in substitution")]
    VariableCapture,
    #[error("not a variable")]
    NotAVariable,
    #[error("not a combination (application)")]
    NotACombination,
    #[error("not an abstraction")]
    NotAnAbstraction,
    #[error("type constructor already defined: {0}")]
    TypeAlreadyDefined(String),
    #[error("constant already defined: {0}")]
    ConstantAlreadyDefined(String),
    #[error("unknown type constructor: {0}")]
    UnknownTypeConstructor(u64),
    #[error("wrong arity for type constructor: expected {expected}, got {got}")]
    WrongTypeArity { expected: usize, got: usize },
    #[error("unknown constant: {0}")]
    UnknownConstant(u64),
    #[error("type not an instance of the constant's generic type")]
    NotAnInstance,
    #[error("definition must have form `c = t` with c a variable: {0}")]
    BadDefinition(String),
    #[error("free type variables in definiens not in definiendum")]
    FreeTypeVarsInDefinition,
    #[error("type definition requires existential theorem `|- ?x. P x`")]
    BadTypeDefinition(String),
    #[error("unsupported operation: {0}")]
    Unsupported(String),
    #[error("invalid theorem handle: {0}")]
    InvalidThmId(u32),
}
