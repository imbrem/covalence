//! The [`Arena`]: a pool of types, terms, and interned literals
//! plus union-find equality state.
//!
//! Identity is by pointer (see architecture §2.2). A freshly built
//! arena is mutable; freezing it produces an `Arc<Arena>` that other
//! arenas may import via foreign-arena references.
//!
//! ⚠️ Staging code — see [crate-level docs](crate) for the list of
//! known holes (linear-scan dedup, auto-`infer` papering over stale
//! caches, opaque `Subset` handling in `subst_tyvar_in_type`, etc.).

use std::collections::HashMap;
use std::sync::Arc;

use smol_str::SmolStr;

use crate::id::{
    BytesId, ImportId, IntId, NatId, StrId, TermId, TermSubstId, TyArgsId, TyVarId, TypeId,
    TypeSubstId, VarId,
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

/// Errors returned by [`Arena::alloc_subset_ty`] and
/// [`Arena::declare_type_operator`] when the predicate fails a
/// well-formedness side condition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubsetError {
    /// `term_props(p).bound_depth() != 0` — predicate has surviving
    /// De-Bruijn indices.
    PredicateNotLocallyClosed,
    /// Predicate has at least one free variable.
    PredicateHasFreeVars,
    /// Predicate's type is not `α → bool`.
    PredicateNotPredicateType,
    /// Predicate id is out of bounds.
    PredicateOutOfRange,
    /// `declare_type_operator`: a tyvar appearing in the parent type
    /// or predicate is missing from the declared order list.
    DeclaredOrderMissingTyvar(StrId),
    /// `declare_type_operator`: the declared order lists a tyvar name
    /// that does not appear in the parent type or predicate.
    DeclaredOrderExtraTyvar(StrId),
    /// `declare_type_operator`: the declared order lists the same
    /// tyvar name twice.
    DeclaredOrderDuplicateTyvar(StrId),
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

    /// Hash-cons map for terms — `TermDef → TermId`. Keeps
    /// [`alloc_term`] dedup O(1) instead of an O(n) linear scan.
    term_dedup: HashMap<TermDef, TermId>,
    /// Hash-cons map for types.
    type_dedup: HashMap<TypeDef, TypeId>,
    /// Hash-cons map for type-argument lists.
    tyargs_dedup: HashMap<Vec<TypeRef>, TyArgsId>,
    /// Hash-cons map for strings.
    string_dedup: HashMap<SmolStr, StrId>,

    // Interning tables for variable-sized payloads.
    strings: Vec<SmolStr>,
    bytes: Vec<bytes::Bytes>,
    ints: Vec<covalence_types::Int>,
    nats: Vec<covalence_types::Nat>,
    tyargs: Vec<Vec<TypeRef>>,
    term_substs: Vec<TermSubst>,
    type_substs: Vec<TypeSubst>,

    // Phase F1: per-arena monotonic counters for the forthcoming
    // VarId / TyVarId. Allocators only — the IDs are not yet wired
    // into TermDef::Free / TypeDef::TVar (that's Phase F2).
    next_var: u32,
    next_tyvar: u32,
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
            term_dedup: HashMap::new(),
            type_dedup: HashMap::new(),
            tyargs_dedup: HashMap::new(),
            string_dedup: HashMap::new(),
            strings: Vec::new(),
            bytes: Vec::new(),
            ints: Vec::new(),
            nats: Vec::new(),
            tyargs: Vec::new(),
            // Slot 0 of each substitution table is reserved for the
            // identity (empty) substitution.
            term_substs: vec![TermSubst::empty()],
            type_substs: vec![TypeSubst::empty()],
            next_var: 0,
            next_tyvar: 0,
        }
    }

    /// Allocate a fresh [`VarId`] (Phase F1). Monotonic per arena.
    pub fn alloc_var(&mut self) -> VarId {
        let id = VarId(self.next_var);
        self.next_var = self.next_var.checked_add(1).expect("VarId overflow");
        id
    }

    /// Allocate a fresh [`TyVarId`] (Phase F1). Monotonic per arena.
    pub fn alloc_tyvar_id(&mut self) -> TyVarId {
        let id = TyVarId(self.next_tyvar);
        self.next_tyvar = self.next_tyvar.checked_add(1).expect("TyVarId overflow");
        id
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

    pub fn bool_ty(&self) -> TypeRef {
        TypeRef::builtin(BuiltinTy::Bool)
    }
    pub fn bytes_ty(&self) -> TypeRef {
        TypeRef::builtin(BuiltinTy::Bytes)
    }
    pub fn int_ty(&self) -> TypeRef {
        TypeRef::builtin(BuiltinTy::Int)
    }
    pub fn nat_ty(&self) -> TypeRef {
        TypeRef::builtin(BuiltinTy::Nat)
    }

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
    /// Substitution semantics: import edges with non-empty
    /// substitutions are materialised eagerly at
    /// [`foreign_term_ref`](Self::foreign_term_ref) time, so foreign
    /// chains that survive into [`deref_term`] are always pure
    /// pointer hops (no live substitution is consulted here).
    ///
    /// Returns `None` when the chain cannot be fully resolved — today
    /// only on unusual encodings; eventually on **hash-only imports**
    /// (arenas referenced by content hash whose bodies we can't
    /// inspect locally).
    pub fn deref_term<'a>(&'a self, r: TermRef) -> Option<(&'a Arena, TermDef)> {
        let mut cur: &Arena = self;
        let mut id = r.as_local()?;
        loop {
            let def = *cur.term_def(id);
            if let TermDef::Foreign(import_id, source_id) = def {
                cur = &cur.imports[import_id.0 as usize].arena;
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
        // Keep the hash-cons in sync: remove the stale old-def
        // entry, register the new-def entry. If `new_def` was
        // already cached at another TermId, the cached entry stays
        // and we lose dedup uniqueness — but `rewrite` callers are
        // expected to maintain that invariant themselves.
        let old_def = self.terms[t.0 as usize];
        if self.term_dedup.get(&old_def) == Some(&t) {
            self.term_dedup.remove(&old_def);
        }
        let (new_info, new_hf) = self.compute_term_props(&new_def);
        self.terms[t.0 as usize] = new_def;
        self.term_dedup.entry(new_def).or_insert(t);
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
    pub fn abstract_over(&mut self, t: TermRef, name: StrId, ty: TypeRef, depth: u32) -> TermRef {
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

    /// Replace every occurrence of the type variable `name` in `ty`
    /// with `replacement`. Walks `Fun` / `Tyapp` shapes; treats
    /// `Subset` and `Foreign` as opaque (closed by construction).
    pub fn subst_tyvar_in_type(
        &mut self,
        ty: TypeRef,
        name: StrId,
        replacement: TypeRef,
    ) -> TypeRef {
        let kind = match self.type_ref_kind(ty) {
            Some(k) => k,
            None => return ty,
        };
        match kind {
            crate::ty::TypeKind::Builtin(_) => ty,
            crate::ty::TypeKind::TVar(n) if n == name => replacement,
            crate::ty::TypeKind::TVar(_) => ty,
            crate::ty::TypeKind::Fun(d, c) => {
                let d2 = self.subst_tyvar_in_type(d, name, replacement);
                let c2 = self.subst_tyvar_in_type(c, name, replacement);
                if d2 == d && c2 == c {
                    ty
                } else {
                    self.alloc_fun_ty(d2, c2)
                }
            }
            crate::ty::TypeKind::Tyapp(tn, args_id) => {
                let args = self.tyargs(args_id).to_vec();
                let new_args: Vec<TypeRef> = args
                    .iter()
                    .map(|&a| self.subst_tyvar_in_type(a, name, replacement))
                    .collect();
                if new_args == args {
                    ty
                } else {
                    let new_args_id = self.intern_tyargs(new_args);
                    self.alloc_tyapp(tn, new_args_id)
                }
            }
            crate::ty::TypeKind::Subset(_, _) | crate::ty::TypeKind::Foreign(_, _) => ty,
        }
    }

    /// Replace every `Free` / `Const` / `Lam` / `Eps` type annotation
    /// in `tm` by [`Self::subst_tyvar_in_type`] of that type. Returns
    /// a fresh `TermRef` if anything changed.
    pub fn subst_tyvar_in_term(
        &mut self,
        tm: TermRef,
        name: StrId,
        replacement: TypeRef,
    ) -> TermRef {
        let id = match tm.as_local() {
            Some(i) => i,
            None => return tm,
        };
        let def = *self.term_def(id);
        let new_def = match def {
            TermDef::Bound(_)
            | TermDef::Bool(_)
            | TermDef::IntInline(_)
            | TermDef::IntStored(_)
            | TermDef::NatInline(_)
            | TermDef::NatStored(_)
            | TermDef::BytesStored(_)
            | TermDef::Foreign(_, _)
            | TermDef::Abs(_)
            | TermDef::Rep(_) => return tm,
            TermDef::Free(s, ty) => {
                let ty2 = self.subst_tyvar_in_type(ty, name, replacement);
                if ty2 == ty {
                    return tm;
                }
                TermDef::Free(s, ty2)
            }
            TermDef::Const(s, ty) => {
                let ty2 = self.subst_tyvar_in_type(ty, name, replacement);
                if ty2 == ty {
                    return tm;
                }
                TermDef::Const(s, ty2)
            }
            TermDef::Comb(f, x) => {
                let f2 = self.subst_tyvar_in_term(f, name, replacement);
                let x2 = self.subst_tyvar_in_term(x, name, replacement);
                if f2 == f && x2 == x {
                    return tm;
                }
                TermDef::Comb(f2, x2)
            }
            TermDef::Lam(ty, body) => {
                let ty2 = self.subst_tyvar_in_type(ty, name, replacement);
                let body2 = self.subst_tyvar_in_term(body, name, replacement);
                if ty2 == ty && body2 == body {
                    return tm;
                }
                TermDef::Lam(ty2, body2)
            }
            TermDef::Eq(a, b) => {
                let a2 = self.subst_tyvar_in_term(a, name, replacement);
                let b2 = self.subst_tyvar_in_term(b, name, replacement);
                if a2 == a && b2 == b {
                    return tm;
                }
                TermDef::Eq(a2, b2)
            }
            TermDef::Forall(p) => {
                let p2 = self.subst_tyvar_in_term(p, name, replacement);
                if p2 == p {
                    return tm;
                }
                TermDef::Forall(p2)
            }
            TermDef::Exists(p) => {
                let p2 = self.subst_tyvar_in_term(p, name, replacement);
                if p2 == p {
                    return tm;
                }
                TermDef::Exists(p2)
            }
            TermDef::Eps(ty, p) => {
                let ty2 = self.subst_tyvar_in_type(ty, name, replacement);
                let p2 = self.subst_tyvar_in_term(p, name, replacement);
                if ty2 == ty && p2 == p {
                    return tm;
                }
                TermDef::Eps(ty2, p2)
            }
            TermDef::Op1(o, x) => {
                let x2 = self.subst_tyvar_in_term(x, name, replacement);
                if x2 == x {
                    return tm;
                }
                TermDef::Op1(o, x2)
            }
            TermDef::Op2(o, a, b) => {
                let a2 = self.subst_tyvar_in_term(a, name, replacement);
                let b2 = self.subst_tyvar_in_term(b, name, replacement);
                if a2 == a && b2 == b {
                    return tm;
                }
                TermDef::Op2(o, a2, b2)
            }
        };
        let new_id = self.alloc_term(new_def);
        let _ = self.infer(new_id);
        TermRef::local(new_id)
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
            Lam(ty_a, body) => Lam(
                ty_a,
                self.subst_free_inner(body, name, ty, replacement, bd + 1),
            ),
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

    fn abstract_inner(&mut self, t: TermRef, name: StrId, ty: TypeRef, depth: u32) -> TermRef {
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

    fn abstract_children(&mut self, def: TermDef, name: StrId, ty: TypeRef, depth: u32) -> TermDef {
        use TermDef::*;
        match def {
            Lam(ty_a, body) => Lam(ty_a, self.abstract_inner(body, name, ty, depth + 1)),
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
            TermDef::Lam(ty, body) => {
                let new_body = self.shift_inner(body, cutoff + 1, amount);
                TermDef::Lam(ty, new_body)
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
            | TermDef::IntInline(_)
            | TermDef::IntStored(_)
            | TermDef::NatInline(_)
            | TermDef::NatStored(_)
            | TermDef::BytesStored(_)
            | TermDef::Abs(_)
            | TermDef::Rep(_)
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
            TermDef::Lam(ty, body) => {
                let new_body = self.subst_inner(body, depth + 1, replacement);
                TermDef::Lam(ty, new_body)
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
            | TermDef::IntInline(_)
            | TermDef::IntStored(_)
            | TermDef::NatInline(_)
            | TermDef::NatStored(_)
            | TermDef::BytesStored(_)
            | TermDef::Abs(_)
            | TermDef::Rep(_)
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
            TermDef::Lam(param_ty, body) => {
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

            // ---- subset operations ---------------------------------------
            TermDef::Abs(subset_ty) => self.infer_subset_abs(*subset_ty),
            TermDef::Rep(subset_ty) => self.infer_subset_rep(*subset_ty),
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

    fn infer_eps(&mut self, elem_ty: TypeRef, p: TermRef, ctx: &mut Vec<TypeRef>) -> TypeInfo {
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

    /// Type of the subset-abstraction function: `α → subset_ty`.
    fn infer_subset_abs(&mut self, subset_ty: TypeRef) -> TypeInfo {
        let alpha = match self.type_def_of(subset_ty) {
            Some(TypeDef::Subset(alpha, _)) => alpha,
            _ => return TypeInfo::ILL_TYPED,
        };
        TypeInfo::typed(self.intern_fun(alpha, subset_ty))
    }

    /// Type of the subset-projection function: `subset_ty → α`.
    fn infer_subset_rep(&mut self, subset_ty: TypeRef) -> TypeInfo {
        let alpha = match self.type_def_of(subset_ty) {
            Some(TypeDef::Subset(alpha, _)) => alpha,
            _ => return TypeInfo::ILL_TYPED,
        };
        TypeInfo::typed(self.intern_fun(subset_ty, alpha))
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
            TermDef::Lam(t, b) => TermKind::Lam(t, b),
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

    // ---- crate-internal table accessors for content hashing (Phase H) ----
    pub(crate) fn all_types(&self) -> &[TypeDef] {
        &self.types
    }
    pub(crate) fn all_terms(&self) -> &[TermDef] {
        &self.terms
    }
    pub(crate) fn all_term_props(&self) -> &[TermProps] {
        &self.term_props
    }
    pub(crate) fn all_strings(&self) -> &[SmolStr] {
        &self.strings
    }
    pub(crate) fn all_bytes(&self) -> &[bytes::Bytes] {
        &self.bytes
    }
    pub(crate) fn all_ints(&self) -> &[covalence_types::Int] {
        &self.ints
    }
    pub(crate) fn all_nats(&self) -> &[covalence_types::Nat] {
        &self.nats
    }
    pub(crate) fn all_tyargs(&self) -> &[Vec<TypeRef>] {
        &self.tyargs
    }
    pub(crate) fn all_term_substs(&self) -> &[TermSubst] {
        &self.term_substs
    }
    pub(crate) fn all_type_substs(&self) -> &[TypeSubst] {
        &self.type_substs
    }

    /// Compute the BLAKE3 content hash of this arena. See
    /// [`crate::hash::arena`] for details.
    pub fn hash(&self) -> covalence_hash::O256 {
        crate::hash::arena(self)
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
        // Dedup via hash-cons: identical TypeDefs share a TypeRef.
        // Crucial for HOL Light-style polymorphic-instance equality
        // — two `alloc_tvar("A")` or two `alloc_tyapp("unit", [])`
        // calls must agree.
        if let Some(&id) = self.type_dedup.get(&def) {
            return TypeRef::local(id);
        }
        let id = TypeId(self.types.len() as u32);
        self.types.push(def);
        self.type_dedup.insert(def, id);
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

    /// Allocate a subset type `{ x : α | P x }` (Phase G).
    ///
    /// Side conditions enforced (returned as [`SubsetError`] otherwise):
    /// - `p` references a term in this arena.
    /// - That term is locally closed (`bound_depth() == 0`).
    /// - It has no free variables (`has_free == false`).
    /// - Its cached type is `α → bool`.
    ///
    /// On success returns a fresh local [`TypeRef`] whose underlying
    /// [`TypeDef`] is `Subset(α, p)`. The two HOL axioms — `abs(rep a)
    /// = a` and `rep(abs x) = x ⇔ P x ∨ ¬∃y. P y` — are derivable from
    /// [`Thm::subset_axioms`](crate::Thm::subset_axioms) once
    /// implemented.
    pub fn alloc_subset_ty(&mut self, alpha: TypeRef, p: TermId) -> Result<TypeRef, SubsetError> {
        if (p.0 as usize) >= self.terms.len() {
            return Err(SubsetError::PredicateOutOfRange);
        }
        let props = self.term_props(p);
        if props.bound_depth() != 0 {
            return Err(SubsetError::PredicateNotLocallyClosed);
        }
        if props.has_free {
            return Err(SubsetError::PredicateHasFreeVars);
        }
        let p_ty = props
            .type_info
            .as_type()
            .ok_or(SubsetError::PredicateNotPredicateType)?;
        let (dom, cod) = match self.type_def_of(p_ty) {
            Some(TypeDef::Fun(d, c)) => (d, c),
            _ => return Err(SubsetError::PredicateNotPredicateType),
        };
        if cod != self.bool_ty() {
            return Err(SubsetError::PredicateNotPredicateType);
        }
        if dom != alpha {
            return Err(SubsetError::PredicateNotPredicateType);
        }
        Ok(self.alloc_type(TypeDef::Subset(alpha, p)))
    }

    /// Declare a polymorphic subset type, supplying an explicit
    /// **type-variable ordering** (Phase G3).
    ///
    /// Like [`alloc_subset_ty`](Self::alloc_subset_ty), but also
    /// validates that `declared_order` is exactly the set of free
    /// type-variable names appearing in `parent` ∪ `p`, listed once
    /// each in whatever order the caller wants.
    ///
    /// The order matters for content-addressed type identity (Phase
    /// H): two subset declarations whose underlying predicates are
    /// structurally identical hash the same iff their declared orders
    /// also match.
    ///
    /// Returns the same [`TypeRef`] `alloc_subset_ty` would produce
    /// — the order itself is not (yet) stored in the [`TypeDef`].
    pub fn declare_type_operator(
        &mut self,
        parent: TypeRef,
        p: TermId,
        declared_order: Vec<StrId>,
    ) -> Result<TypeRef, SubsetError> {
        // Collect the actual tyvar set in (parent, p).
        let mut found = std::collections::HashSet::new();
        self.collect_tyvars_in_type(parent, &mut found);
        if (p.0 as usize) < self.terms.len() {
            self.collect_tyvars_in_term(p, &mut std::collections::HashSet::new(), &mut found);
        }

        // No duplicates in declared_order.
        let mut declared = std::collections::HashSet::new();
        for name in &declared_order {
            if !declared.insert(*name) {
                return Err(SubsetError::DeclaredOrderDuplicateTyvar(*name));
            }
        }

        // declared ⊇ found (every actual tyvar is declared).
        for name in &found {
            if !declared.contains(name) {
                return Err(SubsetError::DeclaredOrderMissingTyvar(*name));
            }
        }
        // declared ⊆ found (no extras).
        for name in &declared {
            if !found.contains(name) {
                return Err(SubsetError::DeclaredOrderExtraTyvar(*name));
            }
        }

        // All checks pass — same as alloc_subset_ty.
        self.alloc_subset_ty(parent, p)
    }

    /// Walk a [`TypeRef`] and accumulate every free [`TVar`] name into
    /// `out`. Builtins, foreign refs, and bound positions contribute
    /// nothing.
    fn collect_tyvars_in_type(&self, r: TypeRef, out: &mut std::collections::HashSet<StrId>) {
        let id = match r.decode() {
            TypeRefKind::Builtin(_) => return,
            TypeRefKind::Local(id) => id,
        };
        match *self.type_def(id) {
            TypeDef::Bool | TypeDef::Bytes | TypeDef::Int | TypeDef::Nat => {}
            TypeDef::Fun(a, b) => {
                self.collect_tyvars_in_type(a, out);
                self.collect_tyvars_in_type(b, out);
            }
            TypeDef::TVar(name) => {
                out.insert(name);
            }
            TypeDef::Tyapp(_, args) => {
                let args_vec: Vec<TypeRef> = self.tyargs(args).to_vec();
                for arg in args_vec {
                    self.collect_tyvars_in_type(arg, out);
                }
            }
            TypeDef::Subset(parent, _p) => {
                // P's tyvars are walked by collect_tyvars_in_term if
                // the caller has reached this Subset via a term. Here
                // we only need the parent — nested Subset types are
                // rare and would be a separate G3 design point.
                self.collect_tyvars_in_type(parent, out);
            }
            TypeDef::Foreign(_, _) => {}
        }
    }

    /// Walk a term and accumulate every free [`TVar`] name visible in
    /// any of its type annotations. Uses `visited` to avoid retracing
    /// shared sub-terms.
    fn collect_tyvars_in_term(
        &self,
        id: TermId,
        visited: &mut std::collections::HashSet<TermId>,
        out: &mut std::collections::HashSet<StrId>,
    ) {
        if !visited.insert(id) {
            return;
        }
        let def = *self.term_def(id);
        match def {
            TermDef::Bound(_)
            | TermDef::Bool(_)
            | TermDef::IntInline(_)
            | TermDef::IntStored(_)
            | TermDef::NatInline(_)
            | TermDef::NatStored(_)
            | TermDef::BytesStored(_)
            | TermDef::Foreign(_, _) => {}
            TermDef::Free(_, ty) | TermDef::Const(_, ty) => {
                self.collect_tyvars_in_type(ty, out);
            }
            TermDef::Comb(f, x) => {
                if let Some(fid) = f.as_local() {
                    self.collect_tyvars_in_term(fid, visited, out);
                }
                if let Some(xid) = x.as_local() {
                    self.collect_tyvars_in_term(xid, visited, out);
                }
            }
            TermDef::Lam(ty, body) => {
                self.collect_tyvars_in_type(ty, out);
                if let Some(bid) = body.as_local() {
                    self.collect_tyvars_in_term(bid, visited, out);
                }
            }
            TermDef::Eq(a, b) => {
                if let Some(aid) = a.as_local() {
                    self.collect_tyvars_in_term(aid, visited, out);
                }
                if let Some(bid) = b.as_local() {
                    self.collect_tyvars_in_term(bid, visited, out);
                }
            }
            TermDef::Forall(p) | TermDef::Exists(p) => {
                if let Some(pid) = p.as_local() {
                    self.collect_tyvars_in_term(pid, visited, out);
                }
            }
            TermDef::Eps(ty, p) => {
                self.collect_tyvars_in_type(ty, out);
                if let Some(pid) = p.as_local() {
                    self.collect_tyvars_in_term(pid, visited, out);
                }
            }
            TermDef::Op1(_, x) => {
                if let Some(xid) = x.as_local() {
                    self.collect_tyvars_in_term(xid, visited, out);
                }
            }
            TermDef::Op2(_, a, b) => {
                if let Some(aid) = a.as_local() {
                    self.collect_tyvars_in_term(aid, visited, out);
                }
                if let Some(bid) = b.as_local() {
                    self.collect_tyvars_in_term(bid, visited, out);
                }
            }
            TermDef::Abs(subset_ty) | TermDef::Rep(subset_ty) => {
                self.collect_tyvars_in_type(subset_ty, out);
            }
        }
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
            TypeDef::Subset(alpha, p) => TypeKind::Subset(alpha, p),
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
        // Dedup via hash-cons: identical `TermDef`s share a
        // `TermId`. The UF and structural-equality bridges rely on
        // `==` for α-equivalent terms even after independent
        // allocations (e.g. fresh terms produced by `inst` /
        // `inst_type`).
        if let Some(&id) = self.term_dedup.get(&def) {
            // Force a re-inference on the existing entry — its
            // cached type info may have been computed in a stale
            // child context.
            let _ = self.infer(id);
            return id;
        }
        let (type_info, has_free) = self.compute_term_props(&def);
        let id = TermId(self.terms.len() as u32);
        self.terms.push(def);
        self.term_props.push(TermProps {
            type_info,
            has_free,
        });
        self.term_dedup.insert(def, id);
        // Force a top-level re-walk so the cache reflects the
        // structurally-correct type, ignoring stale child caches.
        let _ = self.infer(id);
        id
    }

    /// Intern a `SmolStr`. Returns the existing id if already present.
    pub fn intern_string(&mut self, s: SmolStr) -> StrId {
        if let Some(&id) = self.string_dedup.get(&s) {
            return id;
        }
        let id = StrId(self.strings.len() as u32);
        self.strings.push(s.clone());
        self.string_dedup.insert(s, id);
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
    ///
    /// Dedups by structural equality of the argument vector so that
    /// two `Tyapp` allocations with the same args resolve to the
    /// same `TyArgsId` — and therefore to the same `TypeRef` after
    /// `alloc_type`'s structural dedup. Without this, every
    /// independent `intern_tyargs(vec![])` produced a fresh
    /// `TyArgsId` and inflated every nullary `Tyapp` to a distinct
    /// `TypeRef`, breaking polymorphic-instance equality across
    /// rules.
    pub fn intern_tyargs(&mut self, args: Vec<TypeRef>) -> TyArgsId {
        if let Some(&id) = self.tyargs_dedup.get(&args) {
            return id;
        }
        let id = TyArgsId(self.tyargs.len() as u32);
        self.tyargs.push(args.clone());
        self.tyargs_dedup.insert(args, id);
        id
    }

    /// Build a foreign [`TermRef`] pointing at `id` inside the arena
    /// registered under `import`.
    ///
    /// **With empty substitutions** (`TermSubstId::EMPTY` and
    /// `TypeSubstId::EMPTY` on the import edge): allocates an opaque
    /// [`TermDef::Foreign`] leaf in this arena — deduped, preserves
    /// pointer-identity across diamond imports.
    ///
    /// **With non-empty substitutions**: eagerly materialises the
    /// σ-translated form of `source`'s term tree as fresh local
    /// allocations. The result is a local term whose free-variable
    /// names and type-variable names have been mapped through the
    /// import edge's substitutions; unmapped names default to the
    /// identity substitution (the source name is interned locally with
    /// the corresponding type translated). Substitution is HOL-style:
    /// applied uniformly to all type / term subterms.
    ///
    /// **Locally-closed requirement (Phase E4).** The source term must
    /// be locally closed pre-substitution (bound-depth 0) — surviving
    /// free De-Bruijn indices are currently forbidden and cause a
    /// panic. The architecture reserves an epsilon-of-true default for
    /// them as a forward-compat hook.
    pub fn foreign_term_ref(&mut self, import: ImportId, id: TermId) -> TermRef {
        let imp = &self.imports[import.0 as usize];
        let source = &imp.arena;
        if (id.0 as usize) < source.terms.len() {
            let depth = source.term_props(id).bound_depth();
            assert!(
                depth == 0,
                "foreign_term_ref: source term has surviving De-Bruijn \
                 index (bound_depth={depth}); imported terms must be \
                 locally closed pre-substitution"
            );
        }
        let imp = &self.imports[import.0 as usize];
        if imp.term_subst == TermSubstId::EMPTY && imp.type_subst == TypeSubstId::EMPTY {
            let target = TermDef::Foreign(import, id);
            if let Some(pos) = self.terms.iter().position(|d| *d == target) {
                return TermRef::local(TermId(pos as u32));
            }
            let local = self.alloc_term(target);
            return TermRef::local(local);
        }
        self.materialize_import_term(import, id)
    }

    /// Build a foreign [`TypeRef`]; analogous to
    /// [`foreign_term_ref`](Self::foreign_term_ref). With empty
    /// substitutions, allocates an opaque [`TypeDef::Foreign`] leaf;
    /// with a non-empty type substitution, eagerly materialises the
    /// translated form as fresh local types.
    pub fn foreign_type_ref(&mut self, import: ImportId, id: TypeId) -> TypeRef {
        let imp = &self.imports[import.0 as usize];
        if imp.type_subst == TypeSubstId::EMPTY {
            let target = TypeDef::Foreign(import, id);
            if let Some(pos) = self.types.iter().position(|d| *d == target) {
                return TypeRef::local(TypeId(pos as u32));
            }
            let local = self.alloc_type(target);
            return TypeRef::local(local.as_local().expect("Foreign TypeDef must be local"));
        }
        self.materialize_import_type(import, id)
    }

    /// Walk the import edge's source-arena term and produce a fully
    /// substituted local term. See [`foreign_term_ref`](Self::foreign_term_ref).
    fn materialize_import_term(&mut self, import: ImportId, source_id: TermId) -> TermRef {
        let imp = self.imports[import.0 as usize].clone();
        let term_subst = self.term_substs[imp.term_subst.0 as usize].clone();
        let type_subst = self.type_substs[imp.type_subst.0 as usize].clone();
        self.materialize_term(&imp.arena, source_id, &term_subst, &type_subst)
    }

    /// Walk the import edge's source-arena type and produce a fully
    /// substituted local type. See [`foreign_type_ref`](Self::foreign_type_ref).
    fn materialize_import_type(&mut self, import: ImportId, source_id: TypeId) -> TypeRef {
        let imp = self.imports[import.0 as usize].clone();
        let type_subst = self.type_substs[imp.type_subst.0 as usize].clone();
        self.materialize_type(&imp.arena, source_id, &type_subst)
    }

    /// Translate a source-arena `TermRef` into a local `TermRef` under
    /// the given substitutions. Handles foreign refs in source by
    /// chaining through the source's own import edges (using the
    /// source's substitutions for the inner hop).
    fn materialize_term_ref(
        &mut self,
        source: &Arena,
        r: TermRef,
        term_subst: &TermSubst,
        type_subst: &TypeSubst,
    ) -> TermRef {
        let id = r.as_local().expect("TermRef must be local");
        self.materialize_term(source, id, term_subst, type_subst)
    }

    fn materialize_term(
        &mut self,
        source: &Arena,
        source_id: TermId,
        term_subst: &TermSubst,
        type_subst: &TypeSubst,
    ) -> TermRef {
        let def = *source.term_def(source_id);
        match def {
            TermDef::Bool(b) => TermRef::local(self.alloc_term(TermDef::Bool(b))),
            TermDef::Bound(i) => TermRef::local(self.alloc_term(TermDef::Bound(i))),
            TermDef::Free(name, ty) => {
                if let Some(image) = term_subst.lookup(name) {
                    return image;
                }
                let name_str = source.string(name).clone();
                let local_name = self.intern_string(name_str);
                let local_ty = self.materialize_type_ref(source, ty, type_subst);
                TermRef::local(self.alloc_term(TermDef::Free(local_name, local_ty)))
            }
            TermDef::Const(name, ty) => {
                let name_str = source.string(name).clone();
                let local_name = self.intern_string(name_str);
                let local_ty = self.materialize_type_ref(source, ty, type_subst);
                TermRef::local(self.alloc_term(TermDef::Const(local_name, local_ty)))
            }
            TermDef::Comb(f, x) => {
                let lf = self.materialize_term_ref(source, f, term_subst, type_subst);
                let lx = self.materialize_term_ref(source, x, term_subst, type_subst);
                TermRef::local(self.alloc_term(TermDef::Comb(lf, lx)))
            }
            TermDef::Lam(ty, body) => {
                let lty = self.materialize_type_ref(source, ty, type_subst);
                let lbody = self.materialize_term_ref(source, body, term_subst, type_subst);
                TermRef::local(self.alloc_term(TermDef::Lam(lty, lbody)))
            }
            TermDef::Eq(a, b) => {
                let la = self.materialize_term_ref(source, a, term_subst, type_subst);
                let lb = self.materialize_term_ref(source, b, term_subst, type_subst);
                TermRef::local(self.alloc_term(TermDef::Eq(la, lb)))
            }
            TermDef::Forall(p) => {
                let lp = self.materialize_term_ref(source, p, term_subst, type_subst);
                TermRef::local(self.alloc_term(TermDef::Forall(lp)))
            }
            TermDef::Exists(p) => {
                let lp = self.materialize_term_ref(source, p, term_subst, type_subst);
                TermRef::local(self.alloc_term(TermDef::Exists(lp)))
            }
            TermDef::Eps(ty, p) => {
                let lty = self.materialize_type_ref(source, ty, type_subst);
                let lp = self.materialize_term_ref(source, p, term_subst, type_subst);
                TermRef::local(self.alloc_term(TermDef::Eps(lty, lp)))
            }
            TermDef::Op1(op, x) => {
                let lx = self.materialize_term_ref(source, x, term_subst, type_subst);
                TermRef::local(self.alloc_term(TermDef::Op1(op, lx)))
            }
            TermDef::Op2(op, a, b) => {
                let la = self.materialize_term_ref(source, a, term_subst, type_subst);
                let lb = self.materialize_term_ref(source, b, term_subst, type_subst);
                TermRef::local(self.alloc_term(TermDef::Op2(op, la, lb)))
            }
            TermDef::NatInline(_) | TermDef::IntInline(_) => TermRef::local(self.alloc_term(def)),
            TermDef::NatStored(nid) => {
                let n = source.nat(nid).clone();
                let local_nid = self.intern_nat(n);
                TermRef::local(self.alloc_term(TermDef::NatStored(local_nid)))
            }
            TermDef::IntStored(iid) => {
                let i = source.int(iid).clone();
                let local_iid = self.intern_int(i);
                TermRef::local(self.alloc_term(TermDef::IntStored(local_iid)))
            }
            TermDef::Abs(subset_ty) => {
                let local_subset = self.materialize_type_ref(source, subset_ty, type_subst);
                TermRef::local(self.alloc_term(TermDef::Abs(local_subset)))
            }
            TermDef::Rep(subset_ty) => {
                let local_subset = self.materialize_type_ref(source, subset_ty, type_subst);
                TermRef::local(self.alloc_term(TermDef::Rep(local_subset)))
            }
            TermDef::BytesStored(bid) => {
                let bv = source.bytes_value(bid).clone();
                let local_bid = self.intern_bytes(bv);
                TermRef::local(self.alloc_term(TermDef::BytesStored(local_bid)))
            }
            TermDef::Foreign(inner_import, inner_source_id) => {
                // Source's own foreign edge — chain through using the
                // source's substitutions for the inner hop. (Composition
                // with the outer substitutions is left for a follow-up;
                // for now we honor the inner edge's substitutions
                // verbatim.)
                let inner_imp = source.imports[inner_import.0 as usize].clone();
                let inner_term_subst = source.term_substs[inner_imp.term_subst.0 as usize].clone();
                let inner_type_subst = source.type_substs[inner_imp.type_subst.0 as usize].clone();
                self.materialize_term(
                    &inner_imp.arena,
                    inner_source_id,
                    &inner_term_subst,
                    &inner_type_subst,
                )
            }
        }
    }

    fn materialize_type_ref(
        &mut self,
        source: &Arena,
        r: TypeRef,
        type_subst: &TypeSubst,
    ) -> TypeRef {
        match r.decode() {
            TypeRefKind::Builtin(_) => r,
            TypeRefKind::Local(id) => self.materialize_type(source, id, type_subst),
        }
    }

    fn materialize_type(
        &mut self,
        source: &Arena,
        source_id: TypeId,
        type_subst: &TypeSubst,
    ) -> TypeRef {
        let def = *source.type_def(source_id);
        match def {
            TypeDef::Bool => self.bool_ty(),
            TypeDef::Bytes => self.bytes_ty(),
            TypeDef::Int => self.int_ty(),
            TypeDef::Nat => self.nat_ty(),
            TypeDef::Fun(d, c) => {
                let ld = self.materialize_type_ref(source, d, type_subst);
                let lc = self.materialize_type_ref(source, c, type_subst);
                self.alloc_fun_ty(ld, lc)
            }
            TypeDef::TVar(name) => {
                if let Some(image) = type_subst.lookup(name) {
                    return image;
                }
                let name_str = source.string(name).clone();
                let local_name = self.intern_string(name_str);
                self.alloc_tvar(local_name)
            }
            TypeDef::Tyapp(name, args_id) => {
                let name_str = source.string(name).clone();
                let local_name = self.intern_string(name_str);
                let source_args: Vec<TypeRef> = source.tyargs(args_id).to_vec();
                let local_args: Vec<TypeRef> = source_args
                    .into_iter()
                    .map(|a| self.materialize_type_ref(source, a, type_subst))
                    .collect();
                let local_args_id = self.intern_tyargs(local_args);
                self.alloc_tyapp(local_name, local_args_id)
            }
            TypeDef::Subset(alpha, p) => {
                // Predicate P is closed (no free term vars) by Subset's
                // invariant — only types carried inside P need σ_ty applied.
                let local_alpha = self.materialize_type_ref(source, alpha, type_subst);
                let empty_term_subst = TermSubst::empty();
                let local_p = self
                    .materialize_term(source, p, &empty_term_subst, type_subst)
                    .as_local()
                    .expect("materialized predicate must be local");
                self.alloc_subset_ty(local_alpha, local_p)
                    .expect("subset materialisation reproduces well-formed predicate")
            }
            TypeDef::Foreign(inner_import, inner_source_id) => {
                let inner_imp = source.imports[inner_import.0 as usize].clone();
                let inner_type_subst = source.type_substs[inner_imp.type_subst.0 as usize].clone();
                self.materialize_type(&inner_imp.arena, inner_source_id, &inner_type_subst)
            }
        }
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
            TermDef::Lam(param_ty, body) => self.compute_abs(*param_ty, *body),
            TermDef::Eq(a, b) => self.compute_eq_like(*a, *b),
            TermDef::Forall(p) | TermDef::Exists(p) => self.compute_quant(*p),
            TermDef::Eps(elem_ty, p) => self.compute_eps(*elem_ty, *p),
            // ---- applied primops via signature tables ----------------------
            TermDef::Op1(op, x) => self.compute_op1(*op, *x),
            TermDef::Op2(op, a, b) => self.compute_op2(*op, *a, *b),
            // ---- subset operations ----------------------------------------
            TermDef::Abs(subset_ty) => (self.compute_subset_abs(*subset_ty), false),
            TermDef::Rep(subset_ty) => (self.compute_subset_rep(*subset_ty), false),
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

    /// Typing rule for `Abs(α, body)`. See [`TermDef::Lam`].
    /// Cached typing rule for a subset-abstraction leaf `Abs(σ)` where
    /// `σ = Subset(α, P)`. The leaf has type `α → σ`.
    fn compute_subset_abs(&mut self, subset_ty: TypeRef) -> TypeInfo {
        let alpha = match self.type_def_of(subset_ty) {
            Some(TypeDef::Subset(alpha, _)) => alpha,
            _ => return TypeInfo::ILL_TYPED,
        };
        TypeInfo::typed(self.intern_fun(alpha, subset_ty))
    }

    /// Cached typing rule for a subset-projection leaf `Rep(σ)`. The
    /// leaf has type `σ → α`.
    fn compute_subset_rep(&mut self, subset_ty: TypeRef) -> TypeInfo {
        let alpha = match self.type_def_of(subset_ty) {
            Some(TypeDef::Subset(alpha, _)) => alpha,
            _ => return TypeInfo::ILL_TYPED,
        };
        TypeInfo::typed(self.intern_fun(subset_ty, alpha))
    }

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
