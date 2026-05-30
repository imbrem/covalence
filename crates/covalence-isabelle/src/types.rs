//! Core Isabelle/Pure types: sorts, types, terms, and errors.
//!
//! Uses arena-allocated index handles (`TypId`, `TermId`, `ThmId`) instead of
//! `Arc`-wrapped recursive enums. The kernel owns `Vec` arenas; indices are just
//! lightweight `u32` handles that the kernel validates on dereference.
//!
//! De Bruijn indices for bound variables — structural equality gives
//! alpha-equivalence for free. Three kinds of variables: `Bound` (de Bruijn),
//! `Free` (named), `Var` (schematic). Two kinds of type variables: `TFree`
//! (fixed), `TVar` (schematic with index).

/// Interned name — a 64-bit index into a name table.
pub type NameId = u64;

/// Indexed name for schematic variables: `?name.index`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IndexName {
    pub name: NameId,
    pub index: u32,
}

/// A sort — a sorted, deduplicated set of class names.
/// Empty sort = universal (belongs to all classes).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort(pub Vec<NameId>);

impl Sort {
    /// The universal sort (empty class set).
    pub fn universal() -> Self {
        Sort(vec![])
    }

    /// Create a sort from a single class.
    pub fn single(class: NameId) -> Self {
        Sort(vec![class])
    }

    /// Merge two sorts (intersection of constraints = union of classes).
    pub fn merge(&self, other: &Sort) -> Sort {
        let mut classes = self.0.clone();
        for &c in &other.0 {
            if !classes.contains(&c) {
                classes.push(c);
            }
        }
        classes.sort_unstable();
        classes.dedup();
        Sort(classes)
    }
}

// ---------------------------------------------------------------------------
// Index handles
// ---------------------------------------------------------------------------

/// Handle to a type in a `PureArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypId(pub u32);

/// Handle to a term in a `PureArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermId(pub u32);

/// Handle to a theorem in a `PureArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ThmId(pub u32);

// ---------------------------------------------------------------------------
// Arena definitions (the actual data stored per slot)
// ---------------------------------------------------------------------------

/// A type stored in the arena.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypDef {
    /// Free type variable: `'a::sort`.
    TFree(NameId, Sort),
    /// Schematic type variable: `?'a.i::sort`.
    TVar(IndexName, Sort),
    /// Type constructor applied to arguments: `('a,'b) tycon`.
    Type(NameId, Vec<TypId>),
}

/// A term stored in the arena.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermDef {
    /// de Bruijn index (bound variable reference).
    Bound(u32),
    /// Free variable: `Free(name, type)`.
    Free(NameId, TypId),
    /// Schematic variable: `Var(indexname, type)`.
    Var(IndexName, TypId),
    /// Constant with instantiated type: `Const(name, type)`.
    Const(NameId, TypId),
    /// Application: `App(f, x)` represents `f x`.
    App(TermId, TermId),
    /// Lambda abstraction: `Abs(hint_name, var_type, body)`.
    /// The name is just a display hint (not semantically significant due to de Bruijn).
    Abs(NameId, TypId, TermId),
}

/// A theorem stored in the arena.
#[derive(Debug, Clone)]
pub struct ThmDef {
    /// Hypotheses (deduplicated by structural `==`).
    pub(crate) hyps: Vec<TermId>,
    /// Conclusion (must have type `prop`).
    pub(crate) concl: TermId,
}

// ---------------------------------------------------------------------------
// Well-known constants
// ---------------------------------------------------------------------------

/// Well-known name ID for `fun` (function type constructor).
pub const FUN_TYCON_ID: NameId = 0;
/// Well-known name ID for `prop` (proposition type constructor).
pub const PROP_TYCON_ID: NameId = 1;
/// Well-known name ID for `Pure.imp` (`==>`).
pub const IMP_CONST_ID: NameId = 2;
/// Well-known name ID for `Pure.all` (`!!`).
pub const ALL_CONST_ID: NameId = 3;
/// Well-known name ID for `Pure.eq` (`==`).
pub const EQ_CONST_ID: NameId = 4;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from Isabelle/Pure kernel operations.
#[derive(Debug, thiserror::Error)]
pub enum PureError {
    #[error("type mismatch: {0}")]
    TypeMismatch(String),
    #[error("not an equation (==)")]
    NotAnEquation,
    #[error("not an implication (==>)")]
    NotAnImplication,
    #[error("not a forall (!!)")]
    NotAForall,
    #[error("not a proposition (type prop)")]
    NotAProp,
    #[error("not a beta-redex")]
    NotBetaRedex,
    #[error("free variable in hypotheses")]
    FreeVariable,
    #[error("sort error: {0}")]
    SortError(String),
    #[error("unknown axiom: {0}")]
    UnknownAxiom(String),
    #[error("class already defined: {0}")]
    ClassAlreadyDefined(u64),
    #[error("unknown class: {0}")]
    UnknownClass(u64),
    #[error("type constructor already defined: {0}")]
    TypeAlreadyDefined(u64),
    #[error("constant already defined: {0}")]
    ConstantAlreadyDefined(u64),
    #[error("unknown type constructor: {0}")]
    UnknownTypeConstructor(u64),
    #[error("wrong arity for type constructor: expected {expected}, got {got}")]
    WrongTypeArity { expected: usize, got: usize },
    #[error("unknown constant: {0}")]
    UnknownConstant(u64),
    #[error("unsupported operation: {0}")]
    Unsupported(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sort_merge() {
        let s1 = Sort(vec![1, 3]);
        let s2 = Sort(vec![2, 3]);
        let merged = s1.merge(&s2);
        assert_eq!(merged.0, vec![1, 2, 3]);
    }

    #[test]
    fn test_sort_universal() {
        let s = Sort::universal();
        assert!(s.0.is_empty());
    }

    #[test]
    fn test_handle_copy() {
        let t = TypId(0);
        let t2 = t; // Copy
        assert_eq!(t, t2);

        let tm = TermId(1);
        let tm2 = tm; // Copy
        assert_eq!(tm, tm2);

        let th = ThmId(2);
        let th2 = th; // Copy
        assert_eq!(th, th2);
    }
}
