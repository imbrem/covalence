//! Index handles into the Arena's internal tables.
//!
//! These are local to one Arena. To name a term across arenas, use the
//! `TermRef::Foreign(arc, id)` form from `term.rs`.

/// Index into `Arena.types`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeId(pub u32);

/// Index into `Arena.terms`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub u32);

/// Index into `Arena.bitvectors`. Carried inside `BitsValue::Indirect`
/// to point at a bit string too large to inline in the TermDef.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BitsId(pub u32);
