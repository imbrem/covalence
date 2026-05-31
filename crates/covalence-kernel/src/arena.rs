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
use crate::ty::{BuiltinTy, TypeDef, TypeInfo, TypeInfoKind, TypeRef, TypeRefKind};
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
    /// Build an empty mutable arena. Primitive types are not arena-
    /// allocated — they live as builtin-tagged [`TypeRef`]s. Callers
    /// reach them via [`bool_ty`](Self::bool_ty),
    /// [`nat_ty`](Self::nat_ty), and friends.
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
            ints: Vec::new(),
            nats: Vec::new(),
            tyargs: Vec::new(),
            foreign_terms: Vec::new(),
            foreign_types: Vec::new(),
            abs_hints: Vec::new(),
        }
    }

    // -- primitive-type accessors ---------------------------------------

    pub fn bool_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Bool) }
    pub fn bits_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Bits) }
    pub fn bytes_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Bytes) }
    pub fn int_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Int) }
    pub fn nat_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Nat) }
    pub fn u8_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::U8) }
    pub fn u16_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::U16) }
    pub fn u32_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::U32) }
    pub fn u64_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::U64) }
    pub fn i8_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::I8) }
    pub fn i16_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::I16) }
    pub fn i32_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::I32) }
    pub fn i64_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::I64) }

    /// `TypeRef` for the primitive corresponding to a [`BuiltinTy`].
    pub fn builtin_ty(&self, ty: BuiltinTy) -> TypeRef {
        TypeRef::builtin(ty)
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

    /// Allocate a type. Returns a [`TypeRef`].
    ///
    /// For nullary primitive `TypeDef`s (Bool, Bits, …, I64), the
    /// kernel returns the matching builtin TypeRef without writing
    /// to `arena.types`. For everything else (Fun, TVar, Tyapp), a
    /// new entry is appended and a fresh local TypeRef returned.
    pub fn alloc_type(&mut self, def: TypeDef) -> TypeRef {
        if let Some(b) = def.as_builtin() {
            return TypeRef::builtin(b);
        }
        let id = TypeId(self.types.len() as u32);
        self.types.push(def);
        self.uf_types.push(TypeUfEntry {
            canonical: TypeRef::local(id),
        });
        TypeRef::local(id)
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

    /// Resolve a `TypeRef` to its underlying `TypeDef`.
    /// Builtins map back to their nullary `TypeDef` variants;
    /// local types look up via `self.types`; foreign types return
    /// `None` (typing rules treat them opaquely for now).
    pub fn type_def_of(&self, r: TypeRef) -> Option<TypeDef> {
        match r.decode() {
            TypeRefKind::Local(id) => Some(*self.type_def(id)),
            TypeRefKind::Foreign(_) => None,
            TypeRefKind::Builtin(b) => Some(match b {
                BuiltinTy::Bool => TypeDef::Bool,
                BuiltinTy::Bits => TypeDef::Bits,
                BuiltinTy::Bytes => TypeDef::Bytes,
                BuiltinTy::Int => TypeDef::Int,
                BuiltinTy::Nat => TypeDef::Nat,
                BuiltinTy::U8 => TypeDef::U8,
                BuiltinTy::U16 => TypeDef::U16,
                BuiltinTy::U32 => TypeDef::U32,
                BuiltinTy::U64 => TypeDef::U64,
                BuiltinTy::I8 => TypeDef::I8,
                BuiltinTy::I16 => TypeDef::I16,
                BuiltinTy::I32 => TypeDef::I32,
                BuiltinTy::I64 => TypeDef::I64,
            }),
        }
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
            TermDef::Bound(i) => (TypeInfo::unbound(i + 1), false),
            TermDef::Free(_, ty) => (TypeInfo::typed(*ty), true),

            // ---- closed atoms with a known type ----------------------------
            TermDef::Const(_, ty) => (TypeInfo::typed(*ty), false),
            TermDef::True | TermDef::False => (TypeInfo::typed(self.bool_ty()), false),
            TermDef::U8(_) => (TypeInfo::typed(self.u8_ty()), false),
            TermDef::U16(_) => (TypeInfo::typed(self.u16_ty()), false),
            TermDef::U32(_) => (TypeInfo::typed(self.u32_ty()), false),
            TermDef::U64(_) => (TypeInfo::typed(self.u64_ty()), false),
            TermDef::I8(_) => (TypeInfo::typed(self.i8_ty()), false),
            TermDef::I16(_) => (TypeInfo::typed(self.i16_ty()), false),
            TermDef::I32(_) => (TypeInfo::typed(self.i32_ty()), false),
            TermDef::I64(_) => (TypeInfo::typed(self.i64_ty()), false),
            TermDef::IntInline(_) | TermDef::IntStored(_) => {
                (TypeInfo::typed(self.int_ty()), false)
            }
            TermDef::NatInline(_) | TermDef::NatStored(_) => {
                (TypeInfo::typed(self.nat_ty()), false)
            }
            TermDef::BitsStored(_) => (TypeInfo::typed(self.bits_ty()), false),
            TermDef::BytesStored(_) => (TypeInfo::typed(self.bytes_ty()), false),

            // ---- structural with typing rules ------------------------------
            TermDef::Comb(f, x) => self.compute_comb(*f, *x),
            TermDef::Abs(param_ty, body) => self.compute_abs(*param_ty, *body),
            TermDef::Eq(a, b) | TermDef::Ne(a, b) => self.compute_eq_like(*a, *b),
            TermDef::Forall(p) | TermDef::Exists(p) => self.compute_quant(*p),
            TermDef::Eps(elem_ty, p) => self.compute_eps(*elem_ty, *p),
            TermDef::Id(ty) => (TypeInfo::typed(self.intern_fun(*ty, *ty)), false),

            // ---- applied primops via signature tables ----------------------
            TermDef::Op1(op, x) => self.compute_op1(*op, *x),
            TermDef::Op2(op, a, b) => self.compute_op2(*op, *a, *b),

            // ---- lifted primops: η-expanded function values ---------------
            TermDef::LiftOp1(op) => {
                let (dom, cod) = op.sig();
                (TypeInfo::typed(self.intern_fun(dom, cod)), false)
            }
            TermDef::LiftOp2(op) => {
                let (in1, in2, out) = op.sig();
                let curried = self.intern_fun(in2, out); // in2 -> out
                (TypeInfo::typed(self.intern_fun(in1, curried)), false)
            }

            // ---- structural combinators / control flow ---------------------
            TermDef::Comp(f, g) => self.compute_comp(*f, *g),
            TermDef::Iter(n, f) => self.compute_iter(*n, *f),
            TermDef::Ite(cond, then_branch) => self.compute_ite(*cond, *then_branch),
        }
    }

    /// Typing rule for `Comb(f, x)`: requires `f : a → b` and `x : a`;
    /// result is `b`. Open-ness propagates.
    fn compute_comb(&mut self, f: TermRef, x: TermRef) -> (TypeInfo, bool) {
        let (f_info, f_hf) = self.ref_props(f);
        let (x_info, x_hf) = self.ref_props(x);
        let has_free = f_hf || x_hf;
        let f_ty = match f_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return (propagate2_until_typed(f_info, x_info), has_free),
            TypeInfoKind::IllTyped => return (TypeInfo::ILL_TYPED, has_free),
        };
        let x_ty = match x_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return (propagate2_until_typed(f_info, x_info), has_free),
            TypeInfoKind::IllTyped => return (TypeInfo::ILL_TYPED, has_free),
        };
        match self.type_def_of(f_ty) {
            Some(TypeDef::Fun(dom, cod)) if dom == x_ty => (TypeInfo::typed(cod), has_free),
            _ => (TypeInfo::ILL_TYPED, has_free),
        }
    }

    /// Typing rule for `Abs(α, body)`. See [`TermDef::Abs`].
    fn compute_abs(&mut self, param_ty: TypeRef, body: TermRef) -> (TypeInfo, bool) {
        let (body_info, has_free) = self.ref_props(body);
        let info = match body_info.decode() {
            TypeInfoKind::Typed(body_ty) => TypeInfo::typed(self.intern_fun(param_ty, body_ty)),
            TypeInfoKind::Unbound(0) | TypeInfoKind::IllTyped => TypeInfo::ILL_TYPED,
            TypeInfoKind::Unbound(n) => {
                let next = n - 1;
                if next == 0 {
                    TypeInfo::ILL_TYPED
                } else {
                    TypeInfo::unbound(next)
                }
            }
        };
        (info, has_free)
    }

    /// Typing rule for `Eq(a, b)` / `Ne(a, b)`.
    fn compute_eq_like(&mut self, a: TermRef, b: TermRef) -> (TypeInfo, bool) {
        let (a_info, a_hf) = self.ref_props(a);
        let (b_info, b_hf) = self.ref_props(b);
        let has_free = a_hf || b_hf;
        match (a_info.decode(), b_info.decode()) {
            (TypeInfoKind::Typed(ta), TypeInfoKind::Typed(tb)) if ta == tb => {
                (TypeInfo::typed(self.bool_ty()), has_free)
            }
            (TypeInfoKind::Typed(_), TypeInfoKind::Typed(_)) => (TypeInfo::ILL_TYPED, has_free),
            _ => (propagate2_until_typed(a_info, b_info), has_free),
        }
    }

    /// Typing rule for `Forall(p)` / `Exists(p)`.
    fn compute_quant(&mut self, p: TermRef) -> (TypeInfo, bool) {
        let (p_info, has_free) = self.ref_props(p);
        let p_ty = match p_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return (p_info, has_free),
            TypeInfoKind::IllTyped => return (TypeInfo::ILL_TYPED, has_free),
        };
        let bool_ref = self.bool_ty();
        match self.type_def_of(p_ty) {
            Some(TypeDef::Fun(_dom, cod)) if cod == bool_ref => {
                (TypeInfo::typed(bool_ref), has_free)
            }
            _ => (TypeInfo::ILL_TYPED, has_free),
        }
    }

    /// Typing rule for `Eps(α, p)`.
    fn compute_eps(&mut self, elem_ty: TypeRef, p: TermRef) -> (TypeInfo, bool) {
        let (p_info, has_free) = self.ref_props(p);
        let p_ty = match p_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return (p_info, has_free),
            TypeInfoKind::IllTyped => return (TypeInfo::ILL_TYPED, has_free),
        };
        let bool_ref = self.bool_ty();
        match self.type_def_of(p_ty) {
            Some(TypeDef::Fun(dom, cod)) if dom == elem_ty && cod == bool_ref => {
                (TypeInfo::typed(elem_ty), has_free)
            }
            _ => (TypeInfo::ILL_TYPED, has_free),
        }
    }

    /// Typing rule for `Op1(op, x)`: lookup `op`'s `(input, output)`
    /// signature; requires `x : input`; result is `output`.
    fn compute_op1(&mut self, op: crate::primop::PrimOp1, x: TermRef) -> (TypeInfo, bool) {
        let (x_info, has_free) = self.ref_props(x);
        let (input, output) = op.sig();
        match x_info.decode() {
            TypeInfoKind::Typed(t) if t == input => (TypeInfo::typed(output), has_free),
            TypeInfoKind::Typed(_) => (TypeInfo::ILL_TYPED, has_free),
            TypeInfoKind::Unbound(_) => (x_info, has_free),
            TypeInfoKind::IllTyped => (TypeInfo::ILL_TYPED, has_free),
        }
    }

    /// Typing rule for `Op2(op, a, b)`: signature `(in1, in2, output)`.
    fn compute_op2(
        &mut self,
        op: crate::primop::PrimOp2,
        a: TermRef,
        bx: TermRef,
    ) -> (TypeInfo, bool) {
        let (a_info, a_hf) = self.ref_props(a);
        let (b_info, b_hf) = self.ref_props(bx);
        let has_free = a_hf || b_hf;
        let (in1, in2, output) = op.sig();
        match (a_info.decode(), b_info.decode()) {
            (TypeInfoKind::Typed(ta), TypeInfoKind::Typed(tb)) if ta == in1 && tb == in2 => {
                (TypeInfo::typed(output), has_free)
            }
            (TypeInfoKind::Typed(_), TypeInfoKind::Typed(_)) => (TypeInfo::ILL_TYPED, has_free),
            (TypeInfoKind::IllTyped, _) | (_, TypeInfoKind::IllTyped) => {
                (TypeInfo::ILL_TYPED, has_free)
            }
            _ => (propagate2_until_typed(a_info, b_info), has_free),
        }
    }

    /// Typing rule for `Comp(f, g)`: `f : β → γ`, `g : α → β` → `α → γ`.
    fn compute_comp(&mut self, f: TermRef, g: TermRef) -> (TypeInfo, bool) {
        let (f_info, f_hf) = self.ref_props(f);
        let (g_info, g_hf) = self.ref_props(g);
        let has_free = f_hf || g_hf;
        let f_ty = match f_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return (propagate2_until_typed(f_info, g_info), has_free),
            TypeInfoKind::IllTyped => return (TypeInfo::ILL_TYPED, has_free),
        };
        let g_ty = match g_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return (propagate2_until_typed(f_info, g_info), has_free),
            TypeInfoKind::IllTyped => return (TypeInfo::ILL_TYPED, has_free),
        };
        let (f_dom, f_cod) = match self.type_def_of(f_ty) {
            Some(TypeDef::Fun(a, b)) => (a, b),
            _ => return (TypeInfo::ILL_TYPED, has_free),
        };
        let (g_dom, g_cod) = match self.type_def_of(g_ty) {
            Some(TypeDef::Fun(a, b)) => (a, b),
            _ => return (TypeInfo::ILL_TYPED, has_free),
        };
        if g_cod != f_dom {
            return (TypeInfo::ILL_TYPED, has_free);
        }
        (TypeInfo::typed(self.intern_fun(g_dom, f_cod)), has_free)
    }

    /// Typing rule for `Iter(n, f)`: `n : nat`, `f : α → α` → `α → α`.
    fn compute_iter(&mut self, n: TermRef, f: TermRef) -> (TypeInfo, bool) {
        let (n_info, n_hf) = self.ref_props(n);
        let (f_info, f_hf) = self.ref_props(f);
        let has_free = n_hf || f_hf;
        let nat_ref = self.nat_ty();
        let f_ty = match (n_info.decode(), f_info.decode()) {
            (TypeInfoKind::IllTyped, _) | (_, TypeInfoKind::IllTyped) => {
                return (TypeInfo::ILL_TYPED, has_free)
            }
            (TypeInfoKind::Unbound(_), _) | (_, TypeInfoKind::Unbound(_)) => {
                return (propagate2_until_typed(n_info, f_info), has_free)
            }
            (TypeInfoKind::Typed(nt), TypeInfoKind::Typed(ft)) if nt == nat_ref => ft,
            _ => return (TypeInfo::ILL_TYPED, has_free),
        };
        match self.type_def_of(f_ty) {
            Some(TypeDef::Fun(dom, cod)) if dom == cod => (TypeInfo::typed(f_ty), has_free),
            _ => (TypeInfo::ILL_TYPED, has_free),
        }
    }

    /// Typing rule for `Ite(cond, then)`: `cond : bool`, `then : α` → `α → α`.
    fn compute_ite(&mut self, cond: TermRef, then_branch: TermRef) -> (TypeInfo, bool) {
        let (c_info, c_hf) = self.ref_props(cond);
        let (t_info, t_hf) = self.ref_props(then_branch);
        let has_free = c_hf || t_hf;
        let bool_ref = self.bool_ty();
        match (c_info.decode(), t_info.decode()) {
            (TypeInfoKind::IllTyped, _) | (_, TypeInfoKind::IllTyped) => {
                (TypeInfo::ILL_TYPED, has_free)
            }
            (TypeInfoKind::Unbound(_), _) | (_, TypeInfoKind::Unbound(_)) => {
                (propagate2_until_typed(c_info, t_info), has_free)
            }
            (TypeInfoKind::Typed(ct), TypeInfoKind::Typed(tt)) if ct == bool_ref => {
                (TypeInfo::typed(self.intern_fun(tt, tt)), has_free)
            }
            _ => (TypeInfo::ILL_TYPED, has_free),
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
    if a.is_ill_typed() || b.is_ill_typed() {
        return TypeInfo::ILL_TYPED;
    }
    let depth = a.unbound_depth().max(b.unbound_depth());
    if depth > 0 {
        TypeInfo::unbound(depth)
    } else {
        TypeInfo::ILL_TYPED
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
