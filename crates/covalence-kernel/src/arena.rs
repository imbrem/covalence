//! The Arena: pool of types, terms, and value tables, plus union-find
//! state. Identity is by pointer (see architecture §2.2): a freshly built
//! Arena is mutable; freezing produces an `Arc<Arena>` that other arenas
//! may import via foreign-arena references.

use std::sync::Arc;

use smol_str::SmolStr;

use crate::id::{
    BitsId, BytesId, ForeignTermId, ForeignTypeId, ImportId, IntId, NatId, StrId, TermId,
    TyArgsId, TypeId,
};
use crate::term::{TermDef, TermKind, TermRef};
use crate::ty::{TypeDef, TypeInfo, TypeRef};
use crate::uf::{TermUfEntry, TypeUfEntry};

/// Layout of pre-allocated primitive types: the [`TypeDef`] at index
/// `i` of `PRIMITIVE_TYPES` is allocated at `TypeId(i)` during
/// [`Arena::new`]. Order is significant — accessors and the
/// `is_primitive_def` deduper depend on it.
const PRIMITIVE_TYPES: &[TypeDef] = &[
    TypeDef::Bool,  // 0
    TypeDef::Bits,  // 1
    TypeDef::Bytes, // 2
    TypeDef::Int,   // 3
    TypeDef::Nat,   // 4
    TypeDef::U8,    // 5
    TypeDef::U16,   // 6
    TypeDef::U32,   // 7
    TypeDef::U64,   // 8
    TypeDef::I8,    // 9
    TypeDef::I16,   // 10
    TypeDef::I32,   // 11
    TypeDef::I64,   // 12
];

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
    bytes: Vec<bytes::Bytes>,
    bits: Vec<covalence_types::Bits>,
    ints: Vec<covalence_types::Int>,
    nats: Vec<covalence_types::Nat>,
    tyargs: Vec<Vec<TypeRef>>,

    /// Side table for foreign-arena term references. The packed
    /// [`TermRef`](crate::term::TermRef) carries a foreign-flag bit
    /// plus an index into this vec; entries hold the source
    /// `(ImportId, TermId)` pair.
    foreign_terms: Vec<(ImportId, TermId)>,
    /// Side table for foreign-arena type references; same scheme.
    foreign_types: Vec<(ImportId, TypeId)>,

    /// Display-hint side table for `Abs` terms. Indexed by TermId,
    /// parallel to `terms`. `None` for non-`Abs` terms and for `Abs`
    /// terms whose binder was never given a hint. Hints never affect
    /// correctness — only printing.
    abs_hints: Vec<Option<StrId>>,
}

impl Arena {
    /// Build an empty mutable arena with the primitive types
    /// (`bool`, `bits`, `bytes`, `int`, `nat`, `uN`, `iN`)
    /// pre-allocated at well-known [`TypeId`]s — see [`PRIMITIVE_TYPES`].
    /// Type inference at [`alloc_term`](Self::alloc_term) refers to
    /// these by their stable IDs, so callers shouldn't allocate
    /// duplicate primitives; [`alloc_type`](Self::alloc_type)
    /// dedupes on nullary primitives.
    pub fn new() -> Self {
        let mut arena = Self {
            types: Vec::with_capacity(PRIMITIVE_TYPES.len()),
            terms: Vec::new(),
            uf_terms: Vec::new(),
            uf_types: Vec::with_capacity(PRIMITIVE_TYPES.len()),
            imports: Vec::new(),
            strings: Vec::new(),
            bytes: Vec::new(),
            bits: Vec::new(),
            ints: Vec::new(),
            nats: Vec::new(),
            tyargs: Vec::new(),
            foreign_terms: Vec::new(),
            foreign_types: Vec::new(),
            abs_hints: Vec::new(),
        };
        for def in PRIMITIVE_TYPES {
            let id = TypeId(arena.types.len() as u32);
            arena.types.push(*def);
            arena.uf_types.push(TypeUfEntry {
                canonical: TypeRef::local(id),
            });
        }
        arena
    }

    // -- primitive-type accessors ---------------------------------------

    /// `bool` as a [`TypeRef`].
    pub fn bool_ty(&self) -> TypeRef { TypeRef::local(TypeId(0)) }
    /// `bits` as a [`TypeRef`].
    pub fn bits_ty(&self) -> TypeRef { TypeRef::local(TypeId(1)) }
    /// `bytes` as a [`TypeRef`].
    pub fn bytes_ty(&self) -> TypeRef { TypeRef::local(TypeId(2)) }
    /// `int` as a [`TypeRef`].
    pub fn int_ty(&self) -> TypeRef { TypeRef::local(TypeId(3)) }
    /// `nat` as a [`TypeRef`].
    pub fn nat_ty(&self) -> TypeRef { TypeRef::local(TypeId(4)) }
    /// `u8`/`u16`/`u32`/`u64` as a [`TypeRef`].
    pub fn u8_ty(&self) -> TypeRef { TypeRef::local(TypeId(5)) }
    pub fn u16_ty(&self) -> TypeRef { TypeRef::local(TypeId(6)) }
    pub fn u32_ty(&self) -> TypeRef { TypeRef::local(TypeId(7)) }
    pub fn u64_ty(&self) -> TypeRef { TypeRef::local(TypeId(8)) }
    /// `i8`/`i16`/`i32`/`i64` as a [`TypeRef`].
    pub fn i8_ty(&self) -> TypeRef { TypeRef::local(TypeId(9)) }
    pub fn i16_ty(&self) -> TypeRef { TypeRef::local(TypeId(10)) }
    pub fn i32_ty(&self) -> TypeRef { TypeRef::local(TypeId(11)) }
    pub fn i64_ty(&self) -> TypeRef { TypeRef::local(TypeId(12)) }

    /// If `def` is a nullary primitive type, return its pre-allocated
    /// [`TypeId`]; otherwise `None`.
    fn primitive_type_id(def: &TypeDef) -> Option<TypeId> {
        let idx = PRIMITIVE_TYPES.iter().position(|p| p == def)?;
        Some(TypeId(idx as u32))
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

    /// Project a term to its public-API [`TermKind`] view. Use this
    /// for pattern matching in user code — the underlying `TermDef`
    /// has one variant per primop and is intended as internal
    /// storage. Arbitrary-precision literals are materialised: a
    /// `TermDef::NatStored(id)` becomes `TermKind::Nat(self.nat(id).clone())`,
    /// hiding the inline-vs-stored split entirely.
    pub fn kind(&self, id: TermId) -> TermKind {
        let def = self.term_def(id);
        if let Some((op, x)) = def.as_op1() {
            return TermKind::Op1(op, x);
        }
        if let Some((op, a, b)) = def.as_op2() {
            return TermKind::Op2(op, a, b);
        }
        match *def {
            TermDef::Bound(i) => TermKind::Bound(i),
            TermDef::Free(n, t) => TermKind::Free(n, t),
            TermDef::Const(n, t) => TermKind::Const(n, t),
            TermDef::Comb(f, x) => TermKind::Comb(f, x),
            TermDef::Abs(t, b) => TermKind::Abs(t, b),
            TermDef::True => TermKind::True,
            TermDef::False => TermKind::False,
            TermDef::Eq(a, b) => TermKind::Eq(a, b),
            TermDef::Ne(a, b) => TermKind::Ne(a, b),
            TermDef::Forall(p) => TermKind::Forall(p),
            TermDef::Exists(p) => TermKind::Exists(p),
            TermDef::Eps(t, p) => TermKind::Eps(t, p),
            TermDef::Id(t) => TermKind::Id(t),
            TermDef::Comp(f, g) => TermKind::Comp(f, g),
            TermDef::Iter(n, f) => TermKind::Iter(n, f),
            TermDef::Ite(c, t) => TermKind::Ite(c, t),
            TermDef::LiftOp1(op) => TermKind::LiftOp1(op),
            TermDef::LiftOp2(op) => TermKind::LiftOp2(op),
            TermDef::U8(v) => TermKind::U8(v),
            TermDef::U16(v) => TermKind::U16(v),
            TermDef::U32(v) => TermKind::U32(v),
            TermDef::U64(packed) => TermKind::U64(packed.to_u64()),
            TermDef::I8(v) => TermKind::I8(v),
            TermDef::I16(v) => TermKind::I16(v),
            TermDef::I32(v) => TermKind::I32(v),
            TermDef::I64(packed) => TermKind::I64(packed.to_i64()),
            // Materialise arbitrary-precision literals — hide the
            // inline-vs-stored split.
            TermDef::IntInline(packed) => {
                TermKind::Int(covalence_types::Int::from(packed.to_i64()))
            }
            TermDef::IntStored(id) => TermKind::Int(self.int(id).clone()),
            TermDef::NatInline(packed) => {
                TermKind::Nat(covalence_types::Nat::from(packed.to_u64()))
            }
            TermDef::NatStored(id) => TermKind::Nat(self.nat(id).clone()),
            TermDef::BitsStored(id) => TermKind::Bits(self.bits(id).clone()),
            TermDef::BytesStored(id) => TermKind::Bytes(self.bytes_value(id).clone()),
            _ => unreachable!("per-op variant handled by as_op1/as_op2 above"),
        }
    }

    /// Look up an imported arena.
    pub fn import(&self, id: ImportId) -> &Arc<Arena> {
        &self.imports[id.0 as usize]
    }

    /// Read a bit string by local id.
    pub fn bits(&self, id: BitsId) -> &covalence_types::Bits {
        &self.bits[id.0 as usize]
    }

    /// Read a byte string by local id.
    pub fn bytes_value(&self, id: BytesId) -> &bytes::Bytes {
        &self.bytes[id.0 as usize]
    }

    /// Read an interned string by local id.
    pub fn string(&self, id: StrId) -> &SmolStr {
        &self.strings[id.0 as usize]
    }

    /// Read an interned big-int by local id.
    pub fn int(&self, id: IntId) -> &covalence_types::Int {
        &self.ints[id.0 as usize]
    }

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
    ///
    /// Nullary primitive types are deduped — calling
    /// `alloc_type(TypeDef::Bool)` always returns `TypeId(0)`, the
    /// pre-allocated `bool`. This makes equality checks at the kernel
    /// level work even when callers separately allocate primitives.
    pub fn alloc_type(&mut self, def: TypeDef) -> TypeId {
        if let Some(id) = Self::primitive_type_id(&def) {
            return id;
        }
        let id = TypeId(self.types.len() as u32);
        self.types.push(def);
        self.uf_types.push(TypeUfEntry {
            canonical: TypeRef::local(id),
        });
        id
    }

    /// Allocate a term. Returns the local id. The new entry is its own
    /// canonical (no equalities asserted). The type info and free-var
    /// flag are computed in O(1) from the children's already-stored
    /// entries.
    ///
    /// **Ill-typed terms are allowed.** If type inference can't derive
    /// a type for `def`, the term gets `TypeInfo::IllTyped`. The
    /// kernel only checks type soundness when constructing a `Thm`.
    pub fn alloc_term(&mut self, def: TermDef) -> TermId {
        // Compute type info BEFORE pushing — `compute_term_props` may
        // intern Fun types (mutating `self.types`), but never reads
        // the term-table indices we're about to write.
        let (type_info, has_free) = self.compute_term_props(&def);
        let id = TermId(self.terms.len() as u32);
        self.terms.push(def);
        self.uf_terms.push(TermUfEntry {
            canonical: TermRef::local(id),
            type_info,
            has_free,
        });
        id
    }

    /// Intern a bit string. Always appends; callers who want dedup
    /// should dedup at their own layer.
    pub fn intern_bits(&mut self, bits: covalence_types::Bits) -> BitsId {
        let id = BitsId(self.bits.len() as u32);
        self.bits.push(bits);
        id
    }

    /// Look up the display hint for an `Abs` term, if any.
    pub fn abs_hint(&self, id: TermId) -> Option<StrId> {
        self.abs_hints.get(id.0 as usize).copied().flatten()
    }

    /// Set the display hint for an `Abs` term. No-op for non-`Abs`
    /// terms; the kernel doesn't validate the term's shape since
    /// hints never affect correctness.
    pub fn set_abs_hint(&mut self, id: TermId, hint: StrId) {
        let idx = id.0 as usize;
        if idx >= self.abs_hints.len() {
            self.abs_hints.resize(idx + 1, None);
        }
        self.abs_hints[idx] = Some(hint);
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
    pub fn intern_bytes(&mut self, b: bytes::Bytes) -> BytesId {
        let id = BytesId(self.bytes.len() as u32);
        self.bytes.push(b);
        id
    }

    /// Intern a big-int literal.
    pub fn intern_int(&mut self, i: covalence_types::Int) -> IntId {
        let id = IntId(self.ints.len() as u32);
        self.ints.push(i);
        id
    }

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

    // -- type / closedness computation ----------------------------------

    /// Read a TermRef's stored type info and free-var flag — O(1).
    fn ref_props(&self, r: TermRef) -> (TypeInfo, bool) {
        let entry = if let Some(local) = r.as_local() {
            self.term_uf(local)
        } else {
            let foreign = r.as_foreign().expect("ref must be local or foreign");
            let (import, source_id) = self.foreign_term(foreign);
            self.import(import).term_uf(source_id)
        };
        (entry.type_info, entry.has_free)
    }

    /// Resolve a `TypeRef` to its underlying `TypeDef` if it's local.
    /// Foreign types return `None` for now — typing rules treat them
    /// opaquely.
    fn type_def_of(&self, r: TypeRef) -> Option<TypeDef> {
        r.as_local().map(|id| *self.type_def(id))
    }

    /// Compute `(type_info, has_free)` for a `TermDef` whose children
    /// have already been allocated. Used by [`alloc_term`](Self::alloc_term).
    ///
    /// Only `Abs` binds a variable (decrements `unbound_depth` by 1).
    /// Every other variant propagates from its children. Type
    /// inference is intentionally conservative: when a typing rule
    /// doesn't apply or can't determine the result, the term gets
    /// `TypeInfo::IllTyped` rather than blocking allocation.
    fn compute_term_props(&mut self, def: &TermDef) -> (TypeInfo, bool) {
        match def {
            // ---- locally-open atoms ----------------------------------------
            TermDef::Bound(i) => (TypeInfo::Unbound(i + 1), false),
            TermDef::Free(_, ty) => (TypeInfo::Typed(*ty), true),

            // ---- closed atoms with a known type ----------------------------
            TermDef::Const(_, ty) => (TypeInfo::Typed(*ty), false),
            TermDef::True | TermDef::False => (TypeInfo::Typed(self.bool_ty()), false),
            TermDef::U8(_) => (TypeInfo::Typed(self.u8_ty()), false),
            TermDef::U16(_) => (TypeInfo::Typed(self.u16_ty()), false),
            TermDef::U32(_) => (TypeInfo::Typed(self.u32_ty()), false),
            TermDef::U64(_) => (TypeInfo::Typed(self.u64_ty()), false),
            TermDef::I8(_) => (TypeInfo::Typed(self.i8_ty()), false),
            TermDef::I16(_) => (TypeInfo::Typed(self.i16_ty()), false),
            TermDef::I32(_) => (TypeInfo::Typed(self.i32_ty()), false),
            TermDef::I64(_) => (TypeInfo::Typed(self.i64_ty()), false),
            TermDef::IntInline(_) | TermDef::IntStored(_) => {
                (TypeInfo::Typed(self.int_ty()), false)
            }
            TermDef::NatInline(_) | TermDef::NatStored(_) => {
                (TypeInfo::Typed(self.nat_ty()), false)
            }
            TermDef::BitsStored(_) => (TypeInfo::Typed(self.bits_ty()), false),
            TermDef::BytesStored(_) => (TypeInfo::Typed(self.bytes_ty()), false),

            // ---- structural with typing rules ------------------------------
            TermDef::Comb(f, x) => self.compute_comb(*f, *x),
            TermDef::Abs(param_ty, body) => self.compute_abs(*param_ty, *body),
            TermDef::Eq(a, b) | TermDef::Ne(a, b) => self.compute_eq_like(*a, *b),
            TermDef::Forall(p) | TermDef::Exists(p) => self.compute_quant(*p),
            TermDef::Eps(elem_ty, p) => self.compute_eps(*elem_ty, *p),
            TermDef::Id(ty) => (TypeInfo::Typed(self.intern_fun(*ty, *ty)), false),

            // ---- ops / combinators / lifts — propagation only for now -----
            //
            // These need primop-signature tables (Op1/Op2) and Fun-decomp
            // (Comp, Iter, Ite, LiftOpN) to type-check properly. We
            // propagate the dangling-bound count and the has_free flag,
            // and mark the term IllTyped when locally closed — until
            // the signature table lands the kernel can't derive the
            // result type. Subsequent Thm-construction will reject
            // these, but they're allowed to sit in the arena.
            TermDef::Comp(a, b)
            | TermDef::Iter(a, b)
            | TermDef::Ite(a, b)
            | TermDef::Op2(_, a, b) => {
                let (a_info, a_hf) = self.ref_props(*a);
                let (b_info, b_hf) = self.ref_props(*b);
                (propagate2_until_typed(a_info, b_info), a_hf || b_hf)
            }
            TermDef::Op1(_, x) => {
                let (info, hf) = self.ref_props(*x);
                (propagate1_until_typed(info), hf)
            }
            TermDef::LiftOp1(_) | TermDef::LiftOp2(_) => (TypeInfo::IllTyped, false),
        }
    }

    /// Typing rule for `Comb(f, x)`: requires `f : a → b` and `x : a`;
    /// result is `b`. Open-ness propagates.
    fn compute_comb(&mut self, f: TermRef, x: TermRef) -> (TypeInfo, bool) {
        let (f_info, f_hf) = self.ref_props(f);
        let (x_info, x_hf) = self.ref_props(x);
        let has_free = f_hf || x_hf;
        // Open / ill-typed propagation.
        let f_ty = match f_info {
            TypeInfo::Typed(t) => t,
            TypeInfo::Unbound(_) => return (propagate2_until_typed(f_info, x_info), has_free),
            TypeInfo::IllTyped => return (TypeInfo::IllTyped, has_free),
        };
        let x_ty = match x_info {
            TypeInfo::Typed(t) => t,
            TypeInfo::Unbound(_) => return (propagate2_until_typed(f_info, x_info), has_free),
            TypeInfo::IllTyped => return (TypeInfo::IllTyped, has_free),
        };
        match self.type_def_of(f_ty) {
            Some(TypeDef::Fun(dom, cod)) if dom == x_ty => (TypeInfo::Typed(cod), has_free),
            // Either f isn't a function, the domain mismatches, or f's
            // type is foreign-and-opaque. All ill-typed for now.
            _ => (TypeInfo::IllTyped, has_free),
        }
    }

    /// Typing rule for `Abs(α, body)`. If `body` is typed `τ`, the
    /// result is `α → τ`. If `body` is `Unbound(n)`, drop the depth by
    /// one (the new binder binds the outermost `Bound`). If `n` was 1
    /// the body becomes locally closed but its type is unknown until a
    /// later typing pass — mark `IllTyped` to flag that.
    fn compute_abs(&mut self, param_ty: TypeRef, body: TermRef) -> (TypeInfo, bool) {
        let (body_info, has_free) = self.ref_props(body);
        let info = match body_info {
            TypeInfo::Typed(body_ty) => {
                TypeInfo::Typed(self.intern_fun(param_ty, body_ty))
            }
            TypeInfo::Unbound(0) | TypeInfo::IllTyped => TypeInfo::IllTyped,
            TypeInfo::Unbound(n) => {
                let next = n - 1;
                if next == 0 {
                    // Body became locally closed; full type requires a
                    // proper typing pass under the binder. Defer.
                    TypeInfo::IllTyped
                } else {
                    TypeInfo::Unbound(next)
                }
            }
        };
        (info, has_free)
    }

    /// Typing rule for `Eq(a, b)` / `Ne(a, b)`: requires the same
    /// type on both sides; result is `bool`.
    fn compute_eq_like(&mut self, a: TermRef, b: TermRef) -> (TypeInfo, bool) {
        let (a_info, a_hf) = self.ref_props(a);
        let (b_info, b_hf) = self.ref_props(b);
        let has_free = a_hf || b_hf;
        match (a_info, b_info) {
            (TypeInfo::Typed(ta), TypeInfo::Typed(tb)) if ta == tb => {
                (TypeInfo::Typed(self.bool_ty()), has_free)
            }
            (TypeInfo::Typed(_), TypeInfo::Typed(_)) => (TypeInfo::IllTyped, has_free),
            _ => (propagate2_until_typed(a_info, b_info), has_free),
        }
    }

    /// Typing rule for `Forall(p)` / `Exists(p)`: requires `p : α → bool`
    /// for some `α`; result is `bool`.
    fn compute_quant(&self, p: TermRef) -> (TypeInfo, bool) {
        let (p_info, has_free) = self.ref_props(p);
        let p_ty = match p_info {
            TypeInfo::Typed(t) => t,
            TypeInfo::Unbound(_) => return (p_info, has_free),
            TypeInfo::IllTyped => return (TypeInfo::IllTyped, has_free),
        };
        let bool_ref = self.bool_ty();
        match self.type_def_of(p_ty) {
            Some(TypeDef::Fun(_dom, cod)) if cod == bool_ref => {
                (TypeInfo::Typed(bool_ref), has_free)
            }
            _ => (TypeInfo::IllTyped, has_free),
        }
    }

    /// Typing rule for `Eps(α, p)`: requires `p : α → bool`; result is `α`.
    fn compute_eps(&self, elem_ty: TypeRef, p: TermRef) -> (TypeInfo, bool) {
        let (p_info, has_free) = self.ref_props(p);
        let p_ty = match p_info {
            TypeInfo::Typed(t) => t,
            TypeInfo::Unbound(_) => return (p_info, has_free),
            TypeInfo::IllTyped => return (TypeInfo::IllTyped, has_free),
        };
        let bool_ref = self.bool_ty();
        match self.type_def_of(p_ty) {
            Some(TypeDef::Fun(dom, cod)) if dom == elem_ty && cod == bool_ref => {
                (TypeInfo::Typed(elem_ty), has_free)
            }
            _ => (TypeInfo::IllTyped, has_free),
        }
    }

    /// Allocate (or look up) a `Fun(α, β)` type. Linear scan of the
    /// existing types table — fine while the kernel is small;
    /// hash-dedup is a future micro-optimisation.
    fn intern_fun(&mut self, dom: TypeRef, cod: TypeRef) -> TypeRef {
        let target = TypeDef::Fun(dom, cod);
        if let Some(pos) = self.types.iter().position(|d| d == &target) {
            return TypeRef::local(TypeId(pos as u32));
        }
        let id = TypeId(self.types.len() as u32);
        self.types.push(target);
        self.uf_types.push(TypeUfEntry {
            canonical: TypeRef::local(id),
        });
        TypeRef::local(id)
    }
}

/// Combine two child `TypeInfo`s when their parent's typing rule
/// doesn't apply — IllTyped dominates, then Unbound(max), then
/// IllTyped as the closed-but-no-rule fallback.
fn propagate2_until_typed(a: TypeInfo, b: TypeInfo) -> TypeInfo {
    if matches!(a, TypeInfo::IllTyped) || matches!(b, TypeInfo::IllTyped) {
        return TypeInfo::IllTyped;
    }
    let depth = a.unbound_depth().max(b.unbound_depth());
    if depth > 0 {
        TypeInfo::Unbound(depth)
    } else {
        TypeInfo::IllTyped
    }
}

fn propagate1_until_typed(a: TypeInfo) -> TypeInfo {
    match a {
        TypeInfo::Typed(_) => TypeInfo::IllTyped,
        TypeInfo::Unbound(n) if n > 0 => TypeInfo::Unbound(n),
        _ => TypeInfo::IllTyped,
    }
}

impl Arena {

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
