//! The Arena: pool of types, terms, and value tables, plus union-find
//! state. Identity is by pointer (see architecture §2.2): a freshly built
//! Arena is mutable; freezing produces an `Arc<Arena>` that other arenas
//! may import via foreign-arena references.

use std::sync::Arc;

use smol_str::SmolStr;

use crate::id::{
    BitsId, BytesId, ForeignTermId, ForeignTypeId, ImportId, StrId, TermId, TyArgsId, TypeId,
};
#[cfg(feature = "int")]
use crate::id::{IntId, NatId};
use crate::term::{BITS_INLINE_MAX_BYTES, BitsValue, TermDef, TermRef};
use crate::ty::{TypeDef, TypeRef};
use crate::uf::{TermUfEntry, TypeUfEntry};

/// A pool of types, terms, value literals, and union-find state.
///
/// Build one mutably (`Arena::new`, `alloc_type`, `alloc_term`, …),
/// then `freeze()` it into an `Arc<Arena>` for sharing as a foreign
/// import. Frozen arenas are immutable.
#[derive(Debug, Clone)]
pub struct Arena {
    types: Vec<TypeDef>,
    terms: Vec<TermDef>,
    uf_terms: Vec<TermUfEntry>,
    uf_types: Vec<TypeUfEntry>,
    /// Frozen arenas this one references. Carrying them here keeps
    /// them alive even if no `TermRef::Foreign` currently mentions
    /// them; it also lets serialization enumerate dependencies. Indexed
    /// by [`ImportId`].
    imports: Vec<Arc<Arena>>,

    // -- interning tables: variable-sized payloads pulled out of
    //    TermDef / TypeDef so those enums can stay (or become) Copy.
    strings: Vec<SmolStr>,
    bytes: Vec<Vec<u8>>,
    bits: Vec<Vec<u8>>,
    // Behind the default `int` feature of covalence-types.
    #[cfg(feature = "int")]
    ints: Vec<covalence_types::Int>,
    #[cfg(feature = "int")]
    nats: Vec<covalence_types::Nat>,
    tyargs: Vec<Vec<TypeRef>>,

    /// Side table for foreign-arena term references. The packed
    /// [`TermRef`](crate::term::TermRef) carries a foreign-flag bit
    /// plus an index into this vec; entries hold the source
    /// `(ImportId, TermId)` pair.
    foreign_terms: Vec<(ImportId, TermId)>,
    /// Side table for foreign-arena type references; same scheme.
    foreign_types: Vec<(ImportId, TypeId)>,
}

impl Arena {
    /// Build an empty mutable arena.
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            terms: Vec::new(),
            uf_terms: Vec::new(),
            uf_types: Vec::new(),
            imports: Vec::new(),
            strings: Vec::new(),
            bytes: Vec::new(),
            bits: Vec::new(),
            #[cfg(feature = "int")]
            ints: Vec::new(),
            #[cfg(feature = "int")]
            nats: Vec::new(),
            tyargs: Vec::new(),
            foreign_terms: Vec::new(),
            foreign_types: Vec::new(),
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

    /// Register `import` as a foreign-arena import, returning the
    /// `ImportId` to use in `TermRef::Foreign` / `TypeRef::Foreign`.
    /// Repeated calls with the same arena are deduped by `Arc::ptr_eq`.
    pub fn add_import(&mut self, import: Arc<Arena>) -> ImportId {
        if let Some(pos) = self.imports.iter().position(|a| Arc::ptr_eq(a, &import)) {
            return ImportId(pos as u32);
        }
        let id = ImportId(self.imports.len() as u32);
        self.imports.push(import);
        id
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

    /// Look up an imported arena.
    pub fn import(&self, id: ImportId) -> &Arc<Arena> {
        &self.imports[id.0 as usize]
    }

    /// Read a bit string by local id.
    pub fn bits(&self, id: BitsId) -> &[u8] {
        &self.bits[id.0 as usize]
    }

    /// Read a byte string by local id.
    pub fn bytes_value(&self, id: BytesId) -> &[u8] {
        &self.bytes[id.0 as usize]
    }

    /// Read an interned string by local id.
    pub fn string(&self, id: StrId) -> &SmolStr {
        &self.strings[id.0 as usize]
    }

    #[cfg(feature = "int")]
    /// Read an interned big-int by local id.
    pub fn int(&self, id: IntId) -> &covalence_types::Int {
        &self.ints[id.0 as usize]
    }

    #[cfg(feature = "int")]
    /// Read an interned big-nat by local id.
    pub fn nat(&self, id: NatId) -> &covalence_types::Nat {
        &self.nats[id.0 as usize]
    }

    /// Read an interned type-arg list by local id.
    pub fn tyargs(&self, id: TyArgsId) -> &[TypeRef] {
        &self.tyargs[id.0 as usize]
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

    pub fn num_bits(&self) -> u32 {
        self.bits.len() as u32
    }

    // -- allocators ------------------------------------------------------

    /// Allocate a type. Returns the local id. The new entry is its own
    /// canonical (no equalities asserted).
    pub fn alloc_type(&mut self, def: TypeDef) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        self.types.push(def);
        self.uf_types.push(TypeUfEntry {
            canonical: TypeRef::local(id),
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
            canonical: TermRef::local(id),
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
            let id = BitsId(self.bits.len() as u32);
            self.bits.push(bytes);
            BitsValue::Indirect(id)
        }
    }

    /// Intern a `SmolStr`. Returns the existing id if already present.
    pub fn intern_string(&mut self, s: SmolStr) -> StrId {
        if let Some(pos) = self.strings.iter().position(|x| x == &s) {
            return StrId(pos as u32);
        }
        let id = StrId(self.strings.len() as u32);
        self.strings.push(s);
        id
    }

    /// Intern a byte-string literal. Always appends; no dedup (callers
    /// who care about sharing should dedup at their own layer).
    pub fn intern_bytes(&mut self, b: Vec<u8>) -> BytesId {
        let id = BytesId(self.bytes.len() as u32);
        self.bytes.push(b);
        id
    }

    #[cfg(feature = "int")]
    /// Intern a big-int literal.
    pub fn intern_int(&mut self, i: covalence_types::Int) -> IntId {
        let id = IntId(self.ints.len() as u32);
        self.ints.push(i);
        id
    }

    #[cfg(feature = "int")]
    /// Intern a big-nat literal.
    pub fn intern_nat(&mut self, n: covalence_types::Nat) -> NatId {
        let id = NatId(self.nats.len() as u32);
        self.nats.push(n);
        id
    }

    /// Intern a type-argument list.
    pub fn intern_tyargs(&mut self, args: Vec<TypeRef>) -> TyArgsId {
        let id = TyArgsId(self.tyargs.len() as u32);
        self.tyargs.push(args);
        id
    }

    /// Build a foreign [`TermRef`] pointing at `id` inside the arena
    /// registered under `import`. Dedupes against existing entries in
    /// `foreign_terms`.
    pub fn foreign_term_ref(&mut self, import: ImportId, id: TermId) -> TermRef {
        let entry = (import, id);
        let idx = match self.foreign_terms.iter().position(|e| *e == entry) {
            Some(i) => i,
            None => {
                let i = self.foreign_terms.len();
                self.foreign_terms.push(entry);
                i
            }
        };
        TermRef::foreign(ForeignTermId(idx as u32))
    }

    /// Build a foreign [`TypeRef`]; analogous to
    /// [`foreign_term_ref`](Self::foreign_term_ref).
    pub fn foreign_type_ref(&mut self, import: ImportId, id: TypeId) -> TypeRef {
        let entry = (import, id);
        let idx = match self.foreign_types.iter().position(|e| *e == entry) {
            Some(i) => i,
            None => {
                let i = self.foreign_types.len();
                self.foreign_types.push(entry);
                i
            }
        };
        TypeRef::foreign(ForeignTypeId(idx as u32))
    }

    /// Look up a foreign-term entry by its side-table id.
    pub fn foreign_term(&self, id: ForeignTermId) -> (ImportId, TermId) {
        self.foreign_terms[id.0 as usize]
    }

    /// Look up a foreign-type entry.
    pub fn foreign_type(&self, id: ForeignTypeId) -> (ImportId, TypeId) {
        self.foreign_types[id.0 as usize]
    }

    // -- closed-flag computation ----------------------------------------

    /// Read a TermRef's stored properties — O(1).
    ///
    /// Returns `(bound_depth, has_free)`: the smallest `n` such that
    /// the term would be closed if wrapped in `n` more lambdas, and
    /// whether any `Free(_, _)` is reachable.
    fn ref_props(&self, r: TermRef) -> (u32, bool) {
        let entry = if let Some(local) = r.as_local() {
            self.term_uf(local)
        } else {
            let foreign = r.as_foreign().expect("ref must be local or foreign");
            let (import, source_id) = self.foreign_term(foreign);
            self.import(import).term_uf(source_id)
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
                let (f_bd, f_hf) = self.ref_props(*f);
                let (x_bd, x_hf) = self.ref_props(*x);
                (f_bd.max(x_bd), f_hf || x_hf)
            }
            TermDef::Abs(_, _, body) => {
                let (b_bd, b_hf) = self.ref_props(*body);
                (b_bd.saturating_sub(1), b_hf)
            }
        }
    }

    // -- canonical walks -------------------------------------------------

    /// Resolve a term reference to its current UF canonical, chasing
    /// canonical chains across arenas.
    ///
    /// Returns a `(Arc<Arena>, TermId)` pair: the arena whose UF entry
    /// at that id is self-canonical (`canonical = Local(id)`), and the
    /// id itself. Two canonicals are equal iff their arenas are
    /// `Arc::ptr_eq` and their ids are equal.
    pub fn canonical_term(self_arc: &Arc<Arena>, r: TermRef) -> (Arc<Arena>, TermId) {
        let (mut cur_arena, mut cur_id) = resolve_term_ref(self_arc, r);
        loop {
            let next = cur_arena.term_uf(cur_id).canonical;
            if let Some(other) = next.as_local() {
                if other == cur_id {
                    return (cur_arena, cur_id);
                }
                cur_id = other;
            } else {
                let foreign = next.as_foreign().expect("ref must be local or foreign");
                let (import, source_id) = cur_arena.foreign_term(foreign);
                cur_arena = cur_arena.import(import).clone();
                cur_id = source_id;
            }
        }
    }

    /// Resolve a type reference to its current UF canonical.
    pub fn canonical_type(self_arc: &Arc<Arena>, r: TypeRef) -> (Arc<Arena>, TypeId) {
        let (mut cur_arena, mut cur_id) = resolve_type_ref(self_arc, r);
        loop {
            let next = cur_arena.type_uf(cur_id).canonical;
            if let Some(other) = next.as_local() {
                if other == cur_id {
                    return (cur_arena, cur_id);
                }
                cur_id = other;
            } else {
                let foreign = next.as_foreign().expect("ref must be local or foreign");
                let (import, source_id) = cur_arena.foreign_type(foreign);
                cur_arena = cur_arena.import(import).clone();
                cur_id = source_id;
            }
        }
    }
}

/// Decode a [`TermRef`] in `self_arc`'s namespace to a global
/// `(Arc<Arena>, TermId)` pair without walking the canonical chain.
fn resolve_term_ref(self_arc: &Arc<Arena>, r: TermRef) -> (Arc<Arena>, TermId) {
    if let Some(local) = r.as_local() {
        (self_arc.clone(), local)
    } else {
        let foreign = r.as_foreign().expect("ref must be local or foreign");
        let (import, source_id) = self_arc.foreign_term(foreign);
        (self_arc.import(import).clone(), source_id)
    }
}

/// Type-side analogue of [`resolve_term_ref`].
fn resolve_type_ref(self_arc: &Arc<Arena>, r: TypeRef) -> (Arc<Arena>, TypeId) {
    if let Some(local) = r.as_local() {
        (self_arc.clone(), local)
    } else {
        let foreign = r.as_foreign().expect("ref must be local or foreign");
        let (import, source_id) = self_arc.foreign_type(foreign);
        (self_arc.import(import).clone(), source_id)
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}
