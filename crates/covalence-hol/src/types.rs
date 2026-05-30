//! Core HOL Light types: types, terms, and theorems.
//!
//! Uses arena-allocated index handles (`TypeId`, `TermId`, `ThmId`) instead of
//! `Arc`-wrapped recursive enums. The kernel owns `Vec` arenas; indices are just
//! lightweight `u32` handles that the kernel validates on dereference.

/// Interned name — a 64-bit index into a name table.
pub type NameId = u64;

// ---------------------------------------------------------------------------
// Index handles
// ---------------------------------------------------------------------------

/// Handle to a type in a `HolArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

/// Handle to a term in a `HolArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermId(pub u32);

/// Handle to a theorem in a `HolArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ThmId(pub u32);

// ---------------------------------------------------------------------------
// Arena definitions (the actual data stored per slot)
// ---------------------------------------------------------------------------

/// A type stored in the arena.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HolTypeDef {
    /// Type variable: `'a`, `'b`, ...
    Tyvar(NameId),
    /// Type constructor applied to arguments: `bool`, `fun(A,B)`, `list(A)`, ...
    Tyapp(NameId, Vec<TypeId>),
}

/// A term stored in the arena.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermDef {
    /// Variable: `Var(name, type)`.
    Var(NameId, TypeId),
    /// Constant with instantiated type: `Const(name, type)`.
    Const(NameId, TypeId),
    /// Application: `Comb(f, x)` represents `f x`.
    Comb(TermId, TermId),
    /// Lambda abstraction: `Abs(var, body)`.
    /// The binder must be a `Var` node (same as HOL Light).
    Abs(TermId, TermId),
}

/// A theorem stored in the arena.
#[derive(Debug, Clone)]
pub struct ThmDef {
    /// Hypotheses.
    pub(crate) hyps: Vec<TermId>,
    /// Conclusion.
    pub(crate) concl: TermId,
}

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
    #[error("invalid type index: {0}")]
    InvalidTypeId(u32),
    #[error("invalid term index: {0}")]
    InvalidTermId(u32),
    #[error("invalid theorem index: {0}")]
    InvalidThmId(u32),
}
