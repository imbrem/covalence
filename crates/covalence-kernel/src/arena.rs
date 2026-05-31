//! The Arena: pool of types, terms, and bitvectors, plus union-find
//! state. Identity is by pointer (see architecture §2.2): a freshly
//! built Arena is mutable; freezing produces an `Arc<Arena>` that other
//! arenas may import via foreign-arena references.

use std::sync::Arc;

use crate::id::{BitsId, TermId, TypeId};
use crate::term::{BITS_INLINE_MAX_BYTES, BitsValue, TermDef, TermRef};
use crate::ty::{TypeDef, TypeRef};
use crate::uf::{TermUfEntry, TypeUfEntry};

/// A pool of types, terms, and bitvectors with union-find state.
///
/// Build one mutably (`Arena::new`, `alloc_type`, `alloc_term`, …),
/// then `freeze()` it into an `Arc<Arena>` for sharing as a foreign
/// import. Frozen arenas are immutable.
#[derive(Debug, Clone)]
pub struct Arena {
    types: Vec<TypeDef>,
    terms: Vec<TermDef>,
    bitvectors: Vec<Vec<u8>>,
    uf_terms: Vec<TermUfEntry>,
    uf_types: Vec<TypeUfEntry>,
    /// Frozen arenas this one references. Carrying them here keeps
    /// them alive even if no `TermRef::Foreign` currently mentions
    /// them; it also lets serialization enumerate dependencies.
    imports: Vec<Arc<Arena>>,
}

impl Arena {
    /// Build an empty mutable arena.
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            terms: Vec::new(),
            bitvectors: Vec::new(),
            uf_terms: Vec::new(),
            uf_types: Vec::new(),
            imports: Vec::new(),
        }
    }

    /// Freeze this arena, producing an `Arc<Arena>` suitable for use as
    /// a foreign import by other arenas. After freezing the arena is
    /// immutable; further allocations require [unfreezing](Self::unfreeze).
    pub fn freeze(self) -> Arc<Arena> {
        Arc::new(self)
    }

    /// Clone a frozen arena into a fresh mutable copy with the same
    /// indices. The original `Arc` remains valid and identity-distinct
    /// from the new arena.
    pub fn unfreeze(frozen: &Arc<Arena>) -> Self {
        (**frozen).clone()
    }

    /// Register `import` as a foreign-arena import. Repeated calls
    /// with the same arena are silently deduped by `Arc::ptr_eq`.
    pub fn add_import(&mut self, import: Arc<Arena>) {
        if !self.imports.iter().any(|a| Arc::ptr_eq(a, &import)) {
            self.imports.push(import);
        }
    }

    // -- accessors -------------------------------------------------------

    /// Read a type definition by local id.
    pub fn type_def(&self, id: TypeId) -> &TypeDef {
        &self.types[id.0 as usize]
    }

    /// Read a term definition by local id.
    pub fn term_def(&self, id: TermId) -> &TermDef {
        &self.terms[id.0 as usize]
    }

    /// Read a bitvector by local id.
    pub fn bits(&self, id: BitsId) -> &[u8] {
        &self.bitvectors[id.0 as usize]
    }

    /// The local UF entry for a term.
    pub fn term_uf(&self, id: TermId) -> &TermUfEntry {
        &self.uf_terms[id.0 as usize]
    }

    /// The local UF entry for a type.
    pub fn type_uf(&self, id: TypeId) -> &TypeUfEntry {
        &self.uf_types[id.0 as usize]
    }

    /// The frozen arenas this arena imports from.
    pub fn imports(&self) -> &[Arc<Arena>] {
        &self.imports
    }

    pub fn num_types(&self) -> u32 {
        self.types.len() as u32
    }

    pub fn num_terms(&self) -> u32 {
        self.terms.len() as u32
    }

    pub fn num_bitvectors(&self) -> u32 {
        self.bitvectors.len() as u32
    }

    // -- allocators ------------------------------------------------------

    /// Allocate a type. Returns the local id. The new entry is its own
    /// canonical (no equalities asserted).
    pub fn alloc_type(&mut self, def: TypeDef) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        self.types.push(def);
        self.uf_types.push(TypeUfEntry {
            canonical: TypeRef::Local(id),
        });
        id
    }

    /// Allocate a term. Returns the local id. The new entry is its own
    /// canonical (no equalities asserted). The closed-flag components
    /// (`bound_depth`, `has_free`) are computed in O(1) from the
    /// already-stored entries of the children.
    pub fn alloc_term(&mut self, def: TermDef) -> TermId {
        let (bound_depth, has_free) = self.term_props(&def);
        let id = TermId(self.terms.len() as u32);
        self.terms.push(def);
        self.uf_terms.push(TermUfEntry {
            canonical: TermRef::Local(id),
            bound_depth,
            has_free,
        });
        id
    }

    /// Allocate a bit-string value. Chooses `Inline` for short strings
    /// and `Indirect` for longer ones based on
    /// [`BITS_INLINE_MAX_BYTES`].
    pub fn alloc_bits(&mut self, bytes: Vec<u8>) -> BitsValue {
        if bytes.len() <= BITS_INLINE_MAX_BYTES {
            BitsValue::Inline(bytes)
        } else {
            let id = BitsId(self.bitvectors.len() as u32);
            self.bitvectors.push(bytes);
            BitsValue::Indirect(id)
        }
    }

    // -- closed-flag computation ----------------------------------------

    /// Read a TermRef's stored properties — O(1).
    ///
    /// Returns `(bound_depth, has_free)`: the smallest `n` such that
    /// the term would be closed if wrapped in `n` more lambdas, and
    /// whether any `Free(_, _)` is reachable.
    fn ref_props(&self, r: &TermRef) -> (u32, bool) {
        let entry = match r {
            TermRef::Local(id) => self.term_uf(*id),
            TermRef::Foreign(arena, id) => arena.term_uf(*id),
        };
        (entry.bound_depth, entry.has_free)
    }

    /// Compute `(bound_depth, has_free)` for a TermDef whose children
    /// have already been allocated (their UF entries are populated).
    /// Used by [`alloc_term`](Self::alloc_term).
    fn term_props(&self, def: &TermDef) -> (u32, bool) {
        match def {
            TermDef::Bound(i) => (i + 1, false),
            TermDef::Free(_, _) => (0, true),
            TermDef::Const(_, _) => (0, false),
            TermDef::True | TermDef::False | TermDef::Bits(_) => (0, false),
            TermDef::Comb(f, x) | TermDef::Eq(f, x) => {
                let (f_bd, f_hf) = self.ref_props(f);
                let (x_bd, x_hf) = self.ref_props(x);
                (f_bd.max(x_bd), f_hf || x_hf)
            }
            TermDef::Abs(_, _, body) => {
                let (b_bd, b_hf) = self.ref_props(body);
                (b_bd.saturating_sub(1), b_hf)
            }
        }
    }

    // -- canonical walks -------------------------------------------------

    /// Resolve a term reference to its current UF canonical, chasing
    /// canonical chains across arenas. Returns a `TermRef` whose UF
    /// entry points at itself (the chain's fixed point).
    pub fn canonical_term(&self, r: &TermRef) -> TermRef {
        let mut cur = r.clone();
        loop {
            // Read the raw canonical stored at `cur`'s UF entry.
            let raw_next = match &cur {
                TermRef::Local(id) => self.term_uf(*id).canonical.clone(),
                TermRef::Foreign(arena, id) => arena.term_uf(*id).canonical.clone(),
            };
            // If `cur` is a Foreign ref into some arena, then a Local
            // canonical there is "Local in that arena," not in self.
            // Rewrap to keep us anchored at the right arena.
            let next = match (&cur, raw_next) {
                (TermRef::Foreign(arena, _), TermRef::Local(other)) => {
                    TermRef::Foreign(arena.clone(), other)
                }
                (_, next) => next,
            };
            // Compare the *rewrapped* next to cur. A self-canonical entry
            // (Local(id) at index id, or Foreign(arc, id) whose source
            // arena has term_uf(id).canonical = Local(id)) terminates here.
            if refs_point_same(&cur, &next) {
                return cur;
            }
            cur = next;
        }
    }

    /// Resolve a type reference to its current UF canonical.
    pub fn canonical_type(&self, r: &TypeRef) -> TypeRef {
        let mut cur = r.clone();
        loop {
            let raw_next = match &cur {
                TypeRef::Local(id) => self.type_uf(*id).canonical.clone(),
                TypeRef::Foreign(arena, id) => arena.type_uf(*id).canonical.clone(),
            };
            let next = match (&cur, raw_next) {
                (TypeRef::Foreign(arena, _), TypeRef::Local(other)) => {
                    TypeRef::Foreign(arena.clone(), other)
                }
                (_, next) => next,
            };
            if type_refs_point_same(&cur, &next) {
                return cur;
            }
            cur = next;
        }
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

/// Compare two `TermRef`s for pointer-equality of their arena and
/// equality of their inner id. `Local` is treated as referring to
/// "this arena" — but since this helper is private to `canonical_term`
/// (which works within a single arena context), `Local` vs `Local`
/// just compares ids.
fn refs_point_same(a: &TermRef, b: &TermRef) -> bool {
    match (a, b) {
        (TermRef::Local(x), TermRef::Local(y)) => x == y,
        (TermRef::Foreign(arc_a, x), TermRef::Foreign(arc_b, y)) => {
            Arc::ptr_eq(arc_a, arc_b) && x == y
        }
        _ => false,
    }
}

fn type_refs_point_same(a: &TypeRef, b: &TypeRef) -> bool {
    match (a, b) {
        (TypeRef::Local(x), TypeRef::Local(y)) => x == y,
        (TypeRef::Foreign(arc_a, x), TypeRef::Foreign(arc_b, y)) => {
            Arc::ptr_eq(arc_a, arc_b) && x == y
        }
        _ => false,
    }
}
