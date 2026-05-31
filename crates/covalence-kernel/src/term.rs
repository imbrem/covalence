//! Term-level data: `TermDef` (one enum with structural + builtin variants)
//! and `TermRef` (local or foreign-arena reference). Plus `BitsValue` for
//! bit-string literals.

use std::sync::Arc;

use crate::arena::Arena;
use crate::id::{BitsId, TermId};
use crate::name::{ConstName, VarName};
use crate::ty::TypeRef;

/// Reference to a term, possibly in a foreign (imported) arena.
///
/// Identity semantics mirror [`TypeRef`]: `Foreign(a, id) == Foreign(b, id)`
/// iff `Arc::ptr_eq(a, b)`.
#[derive(Debug, Clone)]
pub enum TermRef {
    Local(TermId),
    Foreign(Arc<Arena>, TermId),
}

impl PartialEq for TermRef {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TermRef::Local(a), TermRef::Local(b)) => a == b,
            (TermRef::Foreign(a_arc, a_id), TermRef::Foreign(b_arc, b_id)) => {
                Arc::ptr_eq(a_arc, b_arc) && a_id == b_id
            }
            _ => false,
        }
    }
}

impl Eq for TermRef {}

/// A bit-string value as it appears inside `TermDef::Bits`.
///
/// `Inline` carries the bytes directly inside the TermDef (cheap, used
/// for short literals). `Indirect` points at the arena's bitvectors
/// side table (used for longer strings to keep TermDef small).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitsValue {
    Inline(Vec<u8>),
    Indirect(BitsId),
}

/// Threshold (in bytes) at which the arena promotes a `Bits` literal
/// from `Inline` to `Indirect`. Implementation detail; both forms are
/// logically equivalent.
pub const BITS_INLINE_MAX_BYTES: usize = 32;

/// The kernel's term language.
///
/// All term kinds — structural shapes *and* builtins — live in this one
/// enum. Inference rules pattern-match on it directly; there are no
/// "well-known" name-IDs to look up alongside.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermDef {
    // --- structural ---
    /// de Bruijn-indexed bound variable.
    Bound(u32),
    /// Free variable, named, with a type.
    Free(VarName, TypeRef),
    /// User-declared HOL constant at a particular type instance.
    Const(ConstName, TypeRef),
    /// Application `f x`.
    Comb(TermRef, TermRef),
    /// Lambda abstraction. `VarName` is a display hint; binding is by
    /// de Bruijn index, so the name doesn't affect identity.
    Abs(VarName, TypeRef, TermRef),

    // --- builtins ---
    /// Boolean true.
    True,
    /// Boolean false.
    False,
    /// Polymorphic primitive equality. Equal-as-bool; built-in to avoid
    /// the bootstrap circularity of defining `=` via Hilbert choice.
    Eq(TermRef, TermRef),
    /// A bit-string value (the primitive infinite type).
    Bits(BitsValue),
}
