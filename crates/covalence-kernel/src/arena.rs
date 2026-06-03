//! The [`Arena`]: a pool of types, terms, and interned literals
//! plus union-find equality state.
//!
//! Identity is by pointer (see architecture §2.2). A freshly built
//! arena is mutable; freezing it produces an `Arc<Arena>` that other
//! arenas may import via foreign-arena references.

use std::sync::Arc;

use smol_str::SmolStr;

use crate::id::{
    BytesId, ImportId, IntId, NatId, StrId, TermId, TermSubstId,
    TyArgsId, TypeId, TypeSubstId,
};
use crate::subst::{TermSubst, TypeSubst};
use crate::term::{Deps, TermDef, TermKind, TermRef};

/// Errors returned by [`Arena::union`] and friends.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnionError {
    /// Both refs terminate at foreign canonicals — there's no local
    /// UF slot to mutate. Callers can wrap one in a local term and
    /// retry.
    BothForeign,
}
use crate::ty::{BuiltinTy, TypeDef, TypeInfo, TypeInfoKind, TypeKind, TypeRef, TypeRefKind};
use crate::uf::TermProps;

/// A pool of types, terms, and interned literals.
///
/// Build one mutably (`Arena::new`, `alloc_type`, `alloc_term`, …),
/// then [`freeze`](Self::freeze) it into an `Arc<Arena>` for sharing
/// as a foreign import. Frozen arenas are immutable.
///
/// Arenas hold **structural** state only. Equality state (union-find)
/// lives in a separate [`TermUf`](crate::TermUf) — many UFs can
/// coexist over the same arena.
#[derive(Debug, Clone)]
pub struct Arena {
    types: Vec<TypeDef>,
    terms: Vec<TermDef>,
    /// Cached structural properties (type info + free-var flag) per
    /// allocated term, computed at alloc time. Parallel to `terms`.
    term_props: Vec<TermProps>,
    imports: Vec<Import>,

    // Interning tables for variable-sized payloads.
    strings: Vec<SmolStr>,
    bytes: Vec<bytes::Bytes>,
    ints: Vec<covalence_types::Int>,
    nats: Vec<covalence_types::Nat>,
    tyargs: Vec<Vec<TypeRef>>,
    term_substs: Vec<TermSubst>,
    type_substs: Vec<TypeSubst>,
}

/// An import edge in an arena: a frozen source arena plus a pair of
/// substitutions that translate source-arena names into local refs.
/// Unmapped names default to the epsilon-of-true sentinel when the
/// kernel walks through this edge (see [`Arena::deref_term`]).
#[derive(Debug, Clone)]
pub struct Import {
    pub arena: Arc<Arena>,
    pub term_subst: TermSubstId,
    pub type_subst: TypeSubstId,
}

impl Arena {
    /// Build an empty mutable arena. Builtin types ([`bool_ty`](Self::bool_ty),
    /// [`nat_ty`](Self::nat_ty), …) are kernel-known and never get an
    /// arena entry.
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            terms: Vec::new(),
            term_props: Vec::new(),
            imports: Vec::new(),
            strings: Vec::new(),
            bytes: Vec::new(),
            ints: Vec::new(),
            nats: Vec::new(),
            tyargs: Vec::new(),
            // Slot 0 of each substitution table is reserved for the
            // identity (empty) substitution.
            term_substs: vec![TermSubst::empty()],
            type_substs: vec![TypeSubst::empty()],
        }
    }

    /// The `TermSubstId` of the always-empty substitution.
    /// Unmapped names default to epsilon-of-true.
    pub fn empty_term_subst(&self) -> TermSubstId {
        TermSubstId(0)
    }

    /// The `TypeSubstId` of the always-empty substitution.
    /// Unmapped names default to epsilon-of-true.
    pub fn empty_type_subst(&self) -> TypeSubstId {
        TypeSubstId(0)
    }

    /// Read an interned term substitution.
    pub fn term_subst(&self, id: TermSubstId) -> &TermSubst {
        &self.term_substs[id.0 as usize]
    }

    /// Read an interned type substitution.
    pub fn type_subst(&self, id: TypeSubstId) -> &TypeSubst {
        &self.type_substs[id.0 as usize]
    }

    /// Intern a [`TermSubst`]. Returns the id of an equal existing entry
    /// when present (so the empty substitution always rounds-trips to
    /// `TermSubstId(0)`).
    pub fn intern_term_subst(&mut self, subst: TermSubst) -> TermSubstId {
        if let Some(pos) = self.term_substs.iter().position(|s| *s == subst) {
            return TermSubstId(pos as u32);
        }
        let id = TermSubstId(self.term_substs.len() as u32);
        self.term_substs.push(subst);
        id
    }

    /// Intern a [`TypeSubst`]. Returns the id of an equal existing entry
    /// when present (so the empty substitution always rounds-trips to
    /// `TypeSubstId(0)`).
    pub fn intern_type_subst(&mut self, subst: TypeSubst) -> TypeSubstId {
        if let Some(pos) = self.type_substs.iter().position(|s| *s == subst) {
            return TypeSubstId(pos as u32);
        }
        let id = TypeSubstId(self.type_substs.len() as u32);
        self.type_substs.push(subst);
        id
    }

    // -- primitive-type accessors ---------------------------------------

    pub fn bool_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Bool) }
    pub fn bytes_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Bytes) }
    pub fn int_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Int) }
    pub fn nat_ty(&self) -> TypeRef { TypeRef::builtin(BuiltinTy::Nat) }

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

    /// Register `arena` as a foreign-arena import, returning the
    /// `ImportId` to use in [`TermDef::Foreign`] / [`TypeDef::Foreign`].
    ///
    /// The substitution arguments translate `arena`'s free-variable
    /// names (and type-variable names) into refs local to `self`.
    /// Unmapped names default to epsilon-of-true at deref time.
    ///
    /// Imports are deduped on `(Arc::ptr_eq(arena), term_subst,
    /// type_subst)`: two imports of the same source arena under
    /// different substitutions are distinct.
    pub fn add_import(
        &mut self,
        arena: Arc<Arena>,
        term_subst: TermSubstId,
        type_subst: TypeSubstId,
    ) -> ImportId {
        if let Some(pos) = self.imports.iter().position(|imp| {
            Arc::ptr_eq(&imp.arena, &arena)
                && imp.term_subst == term_subst
                && imp.type_subst == type_subst
        }) {
            return ImportId(pos as u32);
        }
        let id = ImportId(self.imports.len() as u32);
        self.imports.push(Import {
            arena,
            term_subst,
            type_subst,
        });
        id
    }

    // -- accessors -------------------------------------------------------

    /// Read a type definition by local id. **Internal-only** — the
    /// `TypeDef` shape is `pub(crate)`. External callers use
    /// [`type_kind`](Self::type_kind) instead.
    pub(crate) fn type_def(&self, id: TypeId) -> &TypeDef {
        &self.types[id.0 as usize]
    }

    /// Read a term definition by local id.
    pub fn term_def(&self, id: TermId) -> &TermDef {
        &self.terms[id.0 as usize]
    }

    /// Try one **primitive-op reduction step** on `t`.
    ///
    /// Fires when `t` resolves to a primop (`Op1` / `Op2`) applied to
    /// fully-literal arguments (booleans, inline / interned nat / int
    /// literals). Returns the freshly-allocated reduced term, or
    /// `None` if no rule applies, or if any required dereference fails
    /// (today only on unusual encodings; in future, on hash-only
    /// imports the kernel can't see into).
    ///
    /// Foreign-arena children are **transparently dereferenced** —
    /// `Op1(NatSucc, foreign-import-of-NatInline(4))` reduces to local
    /// `NatInline(5)`. The reduction is purely a computational fact
    /// (every input is a literal); algebraic identities and
    /// definitional unfoldings are theorems, not reductions.
    pub fn reduce_primop(&mut self, t: crate::term::TermRef) -> Option<crate::term::TermRef> {
        let result = {
            let (active, def) = self.deref_term(t)?;
            crate::reduce::compute(active, def)?
        };
        let id = self.alloc_prim_result(result);
        Some(crate::term::TermRef::local(id))
    }

    fn alloc_prim_result(&mut self, r: crate::reduce::PrimResult) -> TermId {
        use crate::reduce::PrimResult;
        match r {
            PrimResult::Def(d) => self.alloc_term(d),
            PrimResult::NatBig(n) => {
                let id = self.intern_nat(n);
                self.alloc_term(TermDef::NatStored(id))
            }
            PrimResult::IntBig(i) => {
                let id = self.intern_int(i);
                self.alloc_term(TermDef::IntStored(id))
            }
        }
    }

    /// Follow foreign-arena references starting from `r` and return the
    /// resulting `TermDef` together with the arena that hosts it.
    ///
    /// `r` is interpreted in this arena's namespace; on each foreign hop,
    /// the walker descends into the imported arena and re-resolves the
    /// source id there. The returned `TermDef`'s `TermRef` children are
    /// valid in the **returned** arena, not necessarily in `self`.
    ///
    /// **Substitution semantics (partial — see refactor plan Phase E3).**
    /// When a foreign hop lands on a `Free(name, _)` leaf in the source
    /// arena, the import edge's term substitution is consulted: a mapped
    /// name yields the image (a `TermRef` in the *importing* arena), and
    /// the walker resumes there. An *unmapped* name produces `None` —
    /// callers must treat that as "the kernel can't see this term".
    /// Substitution is not yet applied recursively to compound terms
    /// (e.g. `Comb`, `Abs`); that lands in a follow-up.
    ///
    /// Returns `None` when the chain cannot be fully resolved. Causes
    /// today: unmapped substitution name; unusual encodings; eventually
    /// **hash-only imports** (arenas referenced by content hash whose
    /// bodies we can't inspect locally).
    pub fn deref_term<'a>(&'a self, r: TermRef) -> Option<(&'a Arena, TermDef)> {
        let mut cur: &Arena = self;
        let mut id = r.as_local()?;
        loop {
            let def = *cur.term_def(id);
            if let TermDef::Foreign(import_id, source_id) = def {
                let import = &cur.imports[import_id.0 as usize];
                // Peek at source's top-level def: a Free leaf gets the
                // edge's substitution applied; compound source terms
                // fall through to a transparent walk.
                if let TermDef::Free(name, _) = *import.arena.term_def(source_id) {
                    let subst = cur.term_subst(import.term_subst);
                    match subst.lookup(name) {
                        Some(image) => {
                            // Image lives in `cur` (the importing arena).
                            id = image.as_local()?;
                            continue;
                        }
                        None => return None,
                    }
                }
                cur = &import.arena;
                id = source_id;
            } else {
                return Some((cur, def));
            }
        }
    }

    /// Re-infer the type of a term, walking under binders if needed.
    ///
    /// `alloc_term` caches a type at insertion but can only handle the
    /// "easy" cases — for example, `Abs(α, Bound(0))` gets `IllTyped`
    /// at insertion because re-walking the body under the new binder
    /// isn't done eagerly. `infer` does that walk: it pushes binder
    /// types into a context as it descends, so `Bound(i)` resolves to
    /// the i-th enclosing binder's type. The result is then cached in
    /// the UF entry so subsequent calls are O(1).
    ///
    /// If the cached type is already `Typed(_)`, `infer` returns
    /// immediately. Cached `Unbound`/`IllTyped` entries are re-walked
    /// (a subsequent `Thm` construction may still reject them).
    pub fn infer(&mut self, id: TermId) -> TypeInfo {
        let cached = self.term_props(id).type_info;
        if cached.is_typed() {
            return cached;
        }
        let mut ctx: Vec<TypeRef> = Vec::new();
        let info = self.infer_term(id, &mut ctx);
        self.term_props[id.0 as usize].type_info = info;
        info
    }

    /// **Unchecked** setter for a term's `type_info`. The kernel does
    /// not validate the supplied type against the term's structure —
    /// ill-typedness in the arena is allowed (see [`TypeInfo`]).
    /// Soundness is enforced by `Thm`, not by `alloc_term` or this
    /// setter.
    pub fn set_type_info(&mut self, id: TermId, info: TypeInfo) {
        self.term_props[id.0 as usize].type_info = info;
    }

    /// Is `t` well-typed (has a known `Typed(_)` info)?
    ///
    /// `Thm` rules typically require their inputs to be well-typed.
    pub fn is_well_typed(&self, t: TermId) -> bool {
        self.term_props(t).type_info.is_typed()
    }

    // ---- rewrite (architecture §4.4) ---------------------------------------

    /// Replace term `t`'s stored `TermDef` with `new_def` **in place**,
    /// re-computing its type info and free-var flag from the new
    /// shape.
    ///
    /// **Unchecked.** The kernel does not verify that `new_def` is
    /// equal to t's old def — soundness lives at the `Thm` layer,
    /// not here (same policy as `union` and `set_type_info`). After
    /// rewrite, any term holding a child `TermRef::Local(t)` sees
    /// the new structural form, so an unsound rewrite leaks
    /// throughout the arena. Callers must have a proof (or be doing
    /// a trusted internal step like the §10 reduction rules,
    /// implemented in [`reduce`](Self::reduce)).
    ///
    /// Note on scope: this primitive does *one* in-place rewrite of
    /// *one* term. Recursive / strategic rewriting (walk subterms,
    /// fixpoint, etc.) is **out of kernel scope** by design —
    /// untrusted external code composes the kernel's top-level
    /// rewrite calls into whatever strategy it wants. The kernel
    /// stays small.
    ///
    /// Rule logic (literal-arg evaluation, numeral normalisation,
    /// …) lives in the [`crate::reduce`] module and is exposed via
    /// [`crate::Thm::reduce`]. Arena is rule-blind.
    pub fn rewrite(&mut self, t: TermId, new_def: TermDef) {
        let (new_info, new_hf) = self.compute_term_props(&new_def);
        self.terms[t.0 as usize] = new_def;
        let entry = &mut self.term_props[t.0 as usize];
        entry.type_info = new_info;
        entry.has_free = new_hf;
    }

    // ---- substitution & shifting (locally-nameless) ------------------------

    /// Shift every dangling `Bound(i)` with `i ≥ cutoff` by `amount`,
    /// leaving variables bound *within* `t` unchanged. This is the
    /// classical de-Bruijn shift used to lift a term across a fresh
    /// binder.
    ///
    /// Allocates new TermDef entries for shifted subterms; subterms
    /// whose `Bound` indices are all below `cutoff` are returned
    /// unchanged. Foreign refs are not walked — they're treated
    /// opaquely (typically they're closed anyway).
    pub fn shift(&mut self, t: TermRef, cutoff: u32, amount: u32) -> TermRef {
        if amount == 0 {
            return t;
        }
        self.shift_inner(t, cutoff, amount)
    }

    /// β-style substitution: replace every `Bound(depth)` in `t` with
    /// `replacement`, shifting `replacement`'s dangling indices to
    /// account for the binders between its original site and the
    /// substitution point.
    ///
    /// The arena exposes only the raw substitution; the
    /// β-reduction equality (i.e. that `(λ. body) arg = subst(body,
    /// 0, arg)` is a *theorem*) is enforced at the `Thm` layer via
    /// [`Thm::beta`](crate::prop::Thm::beta).
    pub fn subst(&mut self, t: TermRef, depth: u32, replacement: TermRef) -> TermRef {
        self.subst_inner(t, depth, replacement)
    }

    /// Close `t` over the free variable `Free(name, ty)`: replace
    /// every such occurrence with `Bound(depth + d)` where `d` is the
    /// number of `Abs` binders crossed. Dual of [`subst`](Self::subst).
    ///
    /// `depth` is the de-Bruijn index assigned at the *outermost*
    /// occurrence — callers typically pass `0` and then wrap the
    /// result in `Abs(ty, _)` to bind it. The `Thm::abs` rule does
    /// exactly this.
    ///
    /// Fast path: terms with no free vars (`has_free = false`) are
    /// returned unchanged without a walk.
    pub fn abstract_over(
        &mut self,
        t: TermRef,
        name: StrId,
        ty: TypeRef,
        depth: u32,
    ) -> TermRef {
        self.abstract_inner(t, name, ty, depth)
    }

    /// Replace every `Free(name, ty)` in `t` with `replacement`,
    /// shifting `replacement`'s dangling `Bound` indices when
    /// crossing internal `Abs` binders.
    ///
    /// Like [`subst`](Self::subst), but keyed on a named free
    /// variable rather than a de-Bruijn index. The
    /// `Thm::inst` rule wraps this with the kernel-level checks.
    pub fn subst_free(
        &mut self,
        t: TermRef,
        name: StrId,
        ty: TypeRef,
        replacement: TermRef,
    ) -> TermRef {
        self.subst_free_inner(t, name, ty, replacement, 0)
    }

    /// Does `t` contain a `Free(name, ty)` occurrence anywhere in its
    /// local subtree? Foreign refs are treated opaquely (return
    /// `false`).
    pub fn contains_free(&self, t: TermRef, name: StrId, ty: TypeRef) -> bool {
        self.contains_free_inner(t, name, ty)
    }

    fn contains_free_inner(&self, t: TermRef, name: StrId, ty: TypeRef) -> bool {
        let Some(id) = t.as_local() else { return false };
        if !self.term_props(id).has_free {
            return false;
        }
        let def = *self.term_def(id);
        if let TermDef::Free(n, ty2) = def {
            return n == name && ty2 == ty;
        }
        match def.deps() {
            Deps::None => false,
            Deps::One(c) => self.contains_free_inner(c, name, ty),
            Deps::Two(a, b) => {
                self.contains_free_inner(a, name, ty) || self.contains_free_inner(b, name, ty)
            }
        }
    }

    fn subst_free_inner(
        &mut self,
        t: TermRef,
        name: StrId,
        ty: TypeRef,
        replacement: TermRef,
        binder_depth: u32,
    ) -> TermRef {
        let Some(id) = t.as_local() else { return t };
        if !self.term_props(id).has_free {
            return t;
        }
        let def = *self.term_def(id);
        if let TermDef::Free(n, ty2) = def {
            if n == name && ty2 == ty {
                // Replacement crosses `binder_depth` Abs layers on the way in;
                // lift its dangling Bound indices accordingly.
                return self.shift(replacement, 0, binder_depth);
            }
            return t;
        }
        let new_def = self.subst_free_children(def, name, ty, replacement, binder_depth);
        if new_def == def {
            return t;
        }
        TermRef::local(self.alloc_term(new_def))
    }

    fn subst_free_children(
        &mut self,
        def: TermDef,
        name: StrId,
        ty: TypeRef,
        replacement: TermRef,
        bd: u32,
    ) -> TermDef {
        use TermDef::*;
        match def {
            Abs(ty_a, body) => Abs(ty_a, self.subst_free_inner(body, name, ty, replacement, bd + 1)),
            Forall(p) => Forall(self.subst_free_inner(p, name, ty, replacement, bd)),
            Exists(p) => Exists(self.subst_free_inner(p, name, ty, replacement, bd)),
            Op1(o, p) => Op1(o, self.subst_free_inner(p, name, ty, replacement, bd)),
            Eps(ty_e, p) => Eps(ty_e, self.subst_free_inner(p, name, ty, replacement, bd)),
            Comb(a, b) => Comb(
                self.subst_free_inner(a, name, ty, replacement, bd),
                self.subst_free_inner(b, name, ty, replacement, bd),
            ),
            Eq(a, b) => Eq(
                self.subst_free_inner(a, name, ty, replacement, bd),
                self.subst_free_inner(b, name, ty, replacement, bd),
            ),
            Op2(o, a, b) => Op2(
                o,
                self.subst_free_inner(a, name, ty, replacement, bd),
                self.subst_free_inner(b, name, ty, replacement, bd),
            ),
            other => other,
        }
    }

    fn abstract_inner(
        &mut self,
        t: TermRef,
        name: StrId,
        ty: TypeRef,
        depth: u32,
    ) -> TermRef {
        let Some(id) = t.as_local() else { return t };
        if !self.term_props(id).has_free {
            return t;
        }
        let def = *self.term_def(id);
        if let TermDef::Free(n, ty2) = def {
            if n == name && ty2 == ty {
                return TermRef::local(self.alloc_term(TermDef::Bound(depth)));
            }
            return t;
        }
        let new_def = self.abstract_children(def, name, ty, depth);
        if new_def == def {
            return t;
        }
        TermRef::local(self.alloc_term(new_def))
    }

    fn abstract_children(
        &mut self,
        def: TermDef,
        name: StrId,
        ty: TypeRef,
        depth: u32,
    ) -> TermDef {
        use TermDef::*;
        match def {
            Abs(ty_a, body) => Abs(ty_a, self.abstract_inner(body, name, ty, depth + 1)),
            Forall(p) => Forall(self.abstract_inner(p, name, ty, depth)),
            Exists(p) => Exists(self.abstract_inner(p, name, ty, depth)),
            Op1(o, p) => Op1(o, self.abstract_inner(p, name, ty, depth)),
            Eps(ty_e, p) => Eps(ty_e, self.abstract_inner(p, name, ty, depth)),
            Comb(a, b) => Comb(
                self.abstract_inner(a, name, ty, depth),
                self.abstract_inner(b, name, ty, depth),
            ),
            Eq(a, b) => Eq(
                self.abstract_inner(a, name, ty, depth),
                self.abstract_inner(b, name, ty, depth),
            ),
            Op2(o, a, b) => Op2(
                o,
                self.abstract_inner(a, name, ty, depth),
                self.abstract_inner(b, name, ty, depth),
            ),
            // Free is handled in abstract_inner; everything else is a leaf.
            other => other,
        }
    }

    fn shift_inner(&mut self, t: TermRef, cutoff: u32, amount: u32) -> TermRef {
        let local_id = match t.as_local() {
            Some(id) => id,
            None => return t,
        };
        // Fast path: subterm has no dangling Bound at or above cutoff.
        let depth_here = self.term_props(local_id).type_info.unbound_depth();
        if depth_here <= cutoff {
            return t;
        }
        let def = *self.term_def(local_id);
        let new_def = self.shift_def(def, cutoff, amount);
        if new_def == def {
            return t;
        }
        TermRef::local(self.alloc_term(new_def))
    }

    fn shift_def(&mut self, def: TermDef, cutoff: u32, amount: u32) -> TermDef {
        match def {
            TermDef::Bound(i) => {
                if i >= cutoff {
                    TermDef::Bound(i + amount)
                } else {
                    def
                }
            }
            TermDef::Abs(ty, body) => {
                let new_body = self.shift_inner(body, cutoff + 1, amount);
                TermDef::Abs(ty, new_body)
            }
            // Two-child shapes.
            TermDef::Comb(a, b) => TermDef::Comb(
                self.shift_inner(a, cutoff, amount),
                self.shift_inner(b, cutoff, amount),
            ),
            TermDef::Eq(a, b) => TermDef::Eq(
                self.shift_inner(a, cutoff, amount),
                self.shift_inner(b, cutoff, amount),
            ),
            TermDef::Op2(op, a, b) => TermDef::Op2(
                op,
                self.shift_inner(a, cutoff, amount),
                self.shift_inner(b, cutoff, amount),
            ),
            // One-child shapes.
            TermDef::Forall(p) => TermDef::Forall(self.shift_inner(p, cutoff, amount)),
            TermDef::Exists(p) => TermDef::Exists(self.shift_inner(p, cutoff, amount)),
            TermDef::Eps(ty, p) => TermDef::Eps(ty, self.shift_inner(p, cutoff, amount)),
            TermDef::Op1(op, x) => TermDef::Op1(op, self.shift_inner(x, cutoff, amount)),
            // Leaves (no local TermRef children). Foreign children
            // are in another arena's namespace and opaque to local
            // traversal.
            TermDef::Free(_, _)
            | TermDef::Const(_, _)
            | TermDef::Bool(_)
            | TermDef::IntInline(_) | TermDef::IntStored(_)
            | TermDef::NatInline(_) | TermDef::NatStored(_)
            | TermDef::BytesStored(_)
            | TermDef::Foreign(_, _) => def,
        }
    }

    fn subst_inner(&mut self, t: TermRef, depth: u32, replacement: TermRef) -> TermRef {
        let local_id = match t.as_local() {
            Some(id) => id,
            None => return t,
        };
        let depth_here = self.term_props(local_id).type_info.unbound_depth();
        if depth_here == 0 || depth_here <= depth {
            return t;
        }
        let def = *self.term_def(local_id);

        // Bound at the target depth: substitute directly, returning the
        // (possibly shifted) replacement ref — NOT a copy of its def.
        if let TermDef::Bound(i) = def {
            if i == depth {
                return self.shift_inner(replacement, 0, depth);
            } else if i > depth {
                // Outer-bound index decrements by one (we removed a binder
                // layer by substituting the inner Bound away).
                return TermRef::local(self.alloc_term(TermDef::Bound(i - 1)));
            } else {
                return t;
            }
        }

        let new_def = self.subst_children(def, depth, replacement);
        if new_def == def {
            return t;
        }
        TermRef::local(self.alloc_term(new_def))
    }

    fn subst_children(&mut self, def: TermDef, depth: u32, replacement: TermRef) -> TermDef {
        match def {
            // Bound handled in subst_inner above.
            TermDef::Bound(_) => def,
            TermDef::Abs(ty, body) => {
                let new_body = self.subst_inner(body, depth + 1, replacement);
                TermDef::Abs(ty, new_body)
            }
            TermDef::Comb(a, b) => TermDef::Comb(
                self.subst_inner(a, depth, replacement),
                self.subst_inner(b, depth, replacement),
            ),
            TermDef::Eq(a, b) => TermDef::Eq(
                self.subst_inner(a, depth, replacement),
                self.subst_inner(b, depth, replacement),
            ),
            TermDef::Op2(op, a, b) => TermDef::Op2(
                op,
                self.subst_inner(a, depth, replacement),
                self.subst_inner(b, depth, replacement),
            ),
            TermDef::Forall(p) => TermDef::Forall(self.subst_inner(p, depth, replacement)),
            TermDef::Exists(p) => TermDef::Exists(self.subst_inner(p, depth, replacement)),
            TermDef::Eps(ty, p) => TermDef::Eps(ty, self.subst_inner(p, depth, replacement)),
            TermDef::Op1(op, x) => TermDef::Op1(op, self.subst_inner(x, depth, replacement)),
            TermDef::Free(_, _)
            | TermDef::Const(_, _)
            | TermDef::Bool(_)
            | TermDef::IntInline(_) | TermDef::IntStored(_)
            | TermDef::NatInline(_) | TermDef::NatStored(_)
            | TermDef::BytesStored(_)
            | TermDef::Foreign(_, _) => def,
        }
    }

    fn infer_term(&mut self, id: TermId, ctx: &mut Vec<TypeRef>) -> TypeInfo {
        // Cached Typed values are context-independent (a term's
        // structural type doesn't depend on the surrounding ctx), so
        // we can reuse them. Unbound/IllTyped need re-walking — we
        // may now have enough binder context to resolve them.
        let cached = self.term_props(id).type_info;
        if cached.is_typed() {
            return cached;
        }
        let def = *self.term_def(id);
        self.infer_def(&def, ctx)
    }

    fn infer_ref(&mut self, r: TermRef, ctx: &mut Vec<TypeRef>) -> TypeInfo {
        if let Some(local) = r.as_local() {
            self.infer_term(local, ctx)
        } else {
            // Foreign — use the cached value as-is.
            self.ref_props(r).0
        }
    }

    fn infer_def(&mut self, def: &TermDef, ctx: &mut Vec<TypeRef>) -> TypeInfo {
        match def {
            // ---- de Bruijn: resolve via ctx --------------------------------
            TermDef::Bound(i) => {
                let depth = *i as usize;
                if depth < ctx.len() {
                    TypeInfo::typed(ctx[ctx.len() - 1 - depth])
                } else {
                    TypeInfo::unbound((depth - ctx.len() + 1) as u32)
                }
            }
            // ---- atoms with declared types --------------------------------
            TermDef::Free(_, ty) | TermDef::Const(_, ty) => TypeInfo::typed(*ty),
            TermDef::Bool(true) | TermDef::Bool(false) => TypeInfo::typed(self.bool_ty()),
            TermDef::IntInline(_) | TermDef::IntStored(_) => TypeInfo::typed(self.int_ty()),
            TermDef::NatInline(_) | TermDef::NatStored(_) => TypeInfo::typed(self.nat_ty()),
            TermDef::BytesStored(_) => TypeInfo::typed(self.bytes_ty()),

            // ---- the binder --------------------------------------------------
            TermDef::Abs(param_ty, body) => {
                ctx.push(*param_ty);
                let body_info = self.infer_ref(*body, ctx);
                ctx.pop();
                match body_info.decode() {
                    TypeInfoKind::Typed(body_ty) => {
                        TypeInfo::typed(self.intern_fun(*param_ty, body_ty))
                    }
                    TypeInfoKind::Unbound(n) if n > 0 => {
                        // Body still has dangling Bound — propagate.
                        TypeInfo::unbound(n)
                    }
                    _ => TypeInfo::ILL_TYPED,
                }
            }

            // ---- combinators / control flow / primops ---------------------
            TermDef::Comb(f, x) => self.infer_comb(*f, *x, ctx),
            TermDef::Eq(a, b) => self.infer_eq_like(*a, *b, ctx),
            TermDef::Forall(p) | TermDef::Exists(p) => self.infer_quant(*p, ctx),
            TermDef::Eps(elem_ty, p) => self.infer_eps(*elem_ty, *p, ctx),
            TermDef::Op1(op, x) => self.infer_op1(*op, *x, ctx),
            TermDef::Op2(op, a, b) => self.infer_op2(*op, *a, *b, ctx),
            // Foreign refs: forward the source term's cached info.
            // Its TypeRef interprets in the foreign arena's namespace;
            // translation will land in Phase E. Out-of-range
            // source_id yields IllTyped.
            TermDef::Foreign(import_id, source_id) => {
                let source = &self.import(*import_id).arena;
                if (source_id.0 as usize) < source.num_terms() as usize {
                    source.term_props(*source_id).type_info
                } else {
                    TypeInfo::ILL_TYPED
                }
            }
        }
    }

    fn infer_comb(&mut self, f: TermRef, x: TermRef, ctx: &mut Vec<TypeRef>) -> TypeInfo {
        let f_info = self.infer_ref(f, ctx);
        let x_info = self.infer_ref(x, ctx);
        let f_ty = match f_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return propagate2_until_typed(f_info, x_info),
            TypeInfoKind::IllTyped => return TypeInfo::ILL_TYPED,
        };
        let x_ty = match x_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return propagate2_until_typed(f_info, x_info),
            TypeInfoKind::IllTyped => return TypeInfo::ILL_TYPED,
        };
        match self.type_def_of(f_ty) {
            Some(TypeDef::Fun(dom, cod)) if dom == x_ty => TypeInfo::typed(cod),
            _ => TypeInfo::ILL_TYPED,
        }
    }

    fn infer_eq_like(&mut self, a: TermRef, b: TermRef, ctx: &mut Vec<TypeRef>) -> TypeInfo {
        let a_info = self.infer_ref(a, ctx);
        let b_info = self.infer_ref(b, ctx);
        match (a_info.decode(), b_info.decode()) {
            (TypeInfoKind::Typed(ta), TypeInfoKind::Typed(tb)) if ta == tb => {
                TypeInfo::typed(self.bool_ty())
            }
            (TypeInfoKind::Typed(_), TypeInfoKind::Typed(_)) => TypeInfo::ILL_TYPED,
            _ => propagate2_until_typed(a_info, b_info),
        }
    }

    fn infer_quant(&mut self, p: TermRef, ctx: &mut Vec<TypeRef>) -> TypeInfo {
        let p_info = self.infer_ref(p, ctx);
        let p_ty = match p_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return p_info,
            TypeInfoKind::IllTyped => return TypeInfo::ILL_TYPED,
        };
        let bool_ref = self.bool_ty();
        match self.type_def_of(p_ty) {
            Some(TypeDef::Fun(_dom, cod)) if cod == bool_ref => TypeInfo::typed(bool_ref),
            _ => TypeInfo::ILL_TYPED,
        }
    }

    fn infer_eps(
        &mut self,
        elem_ty: TypeRef,
        p: TermRef,
        ctx: &mut Vec<TypeRef>,
    ) -> TypeInfo {
        let p_info = self.infer_ref(p, ctx);
        let p_ty = match p_info.decode() {
            TypeInfoKind::Typed(t) => t,
            TypeInfoKind::Unbound(_) => return p_info,
            TypeInfoKind::IllTyped => return TypeInfo::ILL_TYPED,
        };
        let bool_ref = self.bool_ty();
        match self.type_def_of(p_ty) {
            Some(TypeDef::Fun(dom, cod)) if dom == elem_ty && cod == bool_ref => {
                TypeInfo::typed(elem_ty)
            }
            _ => TypeInfo::ILL_TYPED,
        }
    }

    fn infer_op1(
        &mut self,
        op: crate::primop::PrimOp1,
        x: TermRef,
        ctx: &mut Vec<TypeRef>,
    ) -> TypeInfo {
        let x_info = self.infer_ref(x, ctx);
        let (input, output) = op.sig();
        match x_info.decode() {
            TypeInfoKind::Typed(t) if t == input => TypeInfo::typed(output),
            TypeInfoKind::Typed(_) => TypeInfo::ILL_TYPED,
            TypeInfoKind::Unbound(_) => x_info,
            TypeInfoKind::IllTyped => TypeInfo::ILL_TYPED,
        }
    }

    fn infer_op2(
        &mut self,
        op: crate::primop::PrimOp2,
        a: TermRef,
        bx: TermRef,
        ctx: &mut Vec<TypeRef>,
    ) -> TypeInfo {
        let a_info = self.infer_ref(a, ctx);
        let b_info = self.infer_ref(bx, ctx);
        let (in1, in2, output) = op.sig();
        match (a_info.decode(), b_info.decode()) {
            (TypeInfoKind::Typed(ta), TypeInfoKind::Typed(tb)) if ta == in1 && tb == in2 => {
                TypeInfo::typed(output)
            }
            (TypeInfoKind::Typed(_), TypeInfoKind::Typed(_)) => TypeInfo::ILL_TYPED,
            (TypeInfoKind::IllTyped, _) | (_, TypeInfoKind::IllTyped) => TypeInfo::ILL_TYPED,
            _ => propagate2_until_typed(a_info, b_info),
        }
    }

    /// Project a term to its public [`TermKind`] view. Arbitrary-
    /// precision literals are materialised as full
    /// [`Nat`](covalence_types::Nat) / [`Int`](covalence_types::Int)
    /// values regardless of how they're stored internally.
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
            TermDef::Bool(true) => TermKind::Bool(true),
            TermDef::Bool(false) => TermKind::Bool(false),
            TermDef::Eq(a, b) => TermKind::Eq(a, b),
            TermDef::Forall(p) => TermKind::Forall(p),
            TermDef::Exists(p) => TermKind::Exists(p),
            TermDef::Eps(t, p) => TermKind::Eps(t, p),
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
            TermDef::BytesStored(id) => TermKind::Bytes(self.bytes_value(id).clone()),
            TermDef::Foreign(import_id, source_id) => TermKind::Foreign(import_id, source_id),
            _ => unreachable!("per-op variant handled by as_op1/as_op2 above"),
        }
    }

    /// Look up an import edge (source arena + substitutions).
    pub fn import(&self, id: ImportId) -> &Import {
        &self.imports[id.0 as usize]
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

    /// The cached structural properties (type info + free-var flag)
    /// for an allocated term.
    pub fn term_props(&self, id: TermId) -> &TermProps {
        &self.term_props[id.0 as usize]
    }

    /// The frozen arenas this arena imports from (with their
    /// substitutions).
    pub fn imports(&self) -> &[Import] {
        &self.imports
    }

    pub fn num_types(&self) -> u32 {
        self.types.len() as u32
    }

    pub fn num_terms(&self) -> u32 {
        self.terms.len() as u32
    }

    // -- allocators ------------------------------------------------------

    /// Internal type-allocator. External callers use the per-shape
    /// methods ([`alloc_fun_ty`](Self::alloc_fun_ty),
    /// [`alloc_tvar`](Self::alloc_tvar), [`alloc_tyapp`](Self::alloc_tyapp))
    /// or the builtin accessors ([`bool_ty`](Self::bool_ty), …).
    pub(crate) fn alloc_type(&mut self, def: TypeDef) -> TypeRef {
        if let Some(b) = def.as_builtin() {
            return TypeRef::builtin(b);
        }
        let id = TypeId(self.types.len() as u32);
        self.types.push(def);
        TypeRef::local(id)
    }

    /// Allocate the function type `α → β`.
    pub fn alloc_fun_ty(&mut self, dom: TypeRef, cod: TypeRef) -> TypeRef {
        self.alloc_type(TypeDef::Fun(dom, cod))
    }

    /// Allocate a polymorphic type variable.
    pub fn alloc_tvar(&mut self, name: StrId) -> TypeRef {
        self.alloc_type(TypeDef::TVar(name))
    }

    /// Allocate a user-declared type-constructor application.
    pub fn alloc_tyapp(&mut self, name: StrId, args: TyArgsId) -> TypeRef {
        self.alloc_type(TypeDef::Tyapp(name, args))
    }

    /// Public view of an allocated type. Use this to pattern-match
    /// on a type's shape (mirrors [`kind`](Self::kind) for terms).
    pub fn type_kind(&self, id: TypeId) -> TypeKind {
        match *self.type_def(id) {
            TypeDef::Bool => TypeKind::Builtin(BuiltinTy::Bool),
            TypeDef::Bytes => TypeKind::Builtin(BuiltinTy::Bytes),
            TypeDef::Int => TypeKind::Builtin(BuiltinTy::Int),
            TypeDef::Nat => TypeKind::Builtin(BuiltinTy::Nat),
            TypeDef::Fun(a, b) => TypeKind::Fun(a, b),
            TypeDef::TVar(s) => TypeKind::TVar(s),
            TypeDef::Tyapp(s, args) => TypeKind::Tyapp(s, args),
            TypeDef::Foreign(import_id, source_id) => TypeKind::Foreign(import_id, source_id),
        }
    }

    /// Project a [`TypeRef`] to its public [`TypeKind`] view. Returns
    /// `None` for foreign references (use [`type_kind`](Self::type_kind)
    /// on the resolved id for those).
    pub fn type_ref_kind(&self, r: TypeRef) -> Option<TypeKind> {
        match r.decode() {
            TypeRefKind::Local(id) => Some(self.type_kind(id)),
            TypeRefKind::Builtin(b) => Some(TypeKind::Builtin(b)),
        }
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
        self.term_props.push(TermProps { type_info, has_free });
        id
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
    /// registered under `import`. Allocates a [`TermDef::Foreign`]
    /// term in this arena (deduped — repeat calls with the same
    /// `(import, id)` return the same [`TermRef`]).
    pub fn foreign_term_ref(&mut self, import: ImportId, id: TermId) -> TermRef {
        let target = TermDef::Foreign(import, id);
        if let Some(pos) = self.terms.iter().position(|d| *d == target) {
            return TermRef::local(TermId(pos as u32));
        }
        let local = self.alloc_term(target);
        TermRef::local(local)
    }

    /// Build a foreign [`TypeRef`]; analogous to
    /// [`foreign_term_ref`](Self::foreign_term_ref). Deduped.
    pub fn foreign_type_ref(&mut self, import: ImportId, id: TypeId) -> TypeRef {
        let target = TypeDef::Foreign(import, id);
        if let Some(pos) = self.types.iter().position(|d| *d == target) {
            return TypeRef::local(TypeId(pos as u32));
        }
        let local = self.alloc_type(target);
        TypeRef::local(local.as_local().expect("Foreign TypeDef must be local"))
    }

    // -- type / closedness computation ----------------------------------

    /// Read a TermRef's stored type info and free-var flag — O(1).
    fn ref_props(&self, r: TermRef) -> (TypeInfo, bool) {
        let local = r.as_local().expect("TermRef must be local");
        let entry = self.term_props(local);
        (entry.type_info, entry.has_free)
    }

    /// Resolve a [`TypeRef`] to its underlying [`TypeDef`].
    ///
    /// Returns the [`TypeDef::Foreign`] variant directly for foreign
    /// references — callers walking the chain should match on it and
    /// recurse into the imported arena.
    pub(crate) fn type_def_of(&self, r: TypeRef) -> Option<TypeDef> {
        match r.decode() {
            TypeRefKind::Local(id) => Some(*self.type_def(id)),
            TypeRefKind::Builtin(b) => Some(match b {
                BuiltinTy::Bool => TypeDef::Bool,
                BuiltinTy::Bytes => TypeDef::Bytes,
                BuiltinTy::Int => TypeDef::Int,
                BuiltinTy::Nat => TypeDef::Nat,
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
            TermDef::Bool(true) | TermDef::Bool(false) => (TypeInfo::typed(self.bool_ty()), false),
            TermDef::IntInline(_) | TermDef::IntStored(_) => {
                (TypeInfo::typed(self.int_ty()), false)
            }
            TermDef::NatInline(_) | TermDef::NatStored(_) => {
                (TypeInfo::typed(self.nat_ty()), false)
            }
            TermDef::BytesStored(_) => (TypeInfo::typed(self.bytes_ty()), false),

            // ---- structural with typing rules ------------------------------
            TermDef::Comb(f, x) => self.compute_comb(*f, *x),
            TermDef::Abs(param_ty, body) => self.compute_abs(*param_ty, *body),
            TermDef::Eq(a, b) => self.compute_eq_like(*a, *b),
            TermDef::Forall(p) | TermDef::Exists(p) => self.compute_quant(*p),
            TermDef::Eps(elem_ty, p) => self.compute_eps(*elem_ty, *p),
            // ---- applied primops via signature tables ----------------------
            TermDef::Op1(op, x) => self.compute_op1(*op, *x),
            TermDef::Op2(op, a, b) => self.compute_op2(*op, *a, *b),
            // Foreign refs: forward the source's cached props.
            // Type-info translation lands in Phase E; for now we
            // verbatim-copy and accept the same-namespace caveat.
            // Out-of-range source_id (e.g. forward reference into
            // an empty foreign arena) yields IllTyped.
            TermDef::Foreign(import_id, source_id) => {
                let source = &self.import(*import_id).arena;
                if (source_id.0 as usize) < source.num_terms() as usize {
                    let entry = source.term_props(*source_id);
                    (entry.type_info, entry.has_free)
                } else {
                    (TypeInfo::ILL_TYPED, false)
                }
            }
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

    /// Resolve a term reference structurally — walk through any
    /// [`TermDef::Foreign`] chain to its landing arena + local id.
    ///
    /// Returns a `(Arc<Arena>, TermId)` pair: the arena whose
    /// `terms[id]` is *not* a `Foreign` variant. Two canonicals are
    /// equal iff their arenas are `Arc::ptr_eq` and their ids are
    /// equal.
    ///
    /// This is a purely structural walk — equality state (UF) lives
    /// outside the arena (see [`TermUf`](crate::TermUf)).
    pub fn canonical_term(self_arc: &Arc<Arena>, r: TermRef) -> (Arc<Arena>, TermId) {
        let mut cur = self_arc.clone();
        let mut id = r.as_local().expect("TermRef must be local");
        while let TermDef::Foreign(import_id, source_id) = *cur.term_def(id) {
            cur = cur.import(import_id).arena.clone();
            id = source_id;
        }
        (cur, id)
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}
