//! HOL Light driver — exposes the covalence-kernel primitives that a
//! HOL Light-style API needs, as a single wrapper struct.
//!
//! The wrapper ([`HolPrim`]) owns a [`covalence_kernel::Kernel`] and a
//! small bridge state (HOL `NameId` ↔ kernel `StrId`, declared type
//! operators, declared term constants, theorem storage). Each method
//! mirrors one operation from the `HolLightTypes` / `HolLightTerms` /
//! `HolLightKernel` traits in `covalence-hol`.
//!
//! Methods that map cleanly onto the current kernel are implemented;
//! anything that needs a kernel feature that isn't yet exposed
//! returns [`HolPrimError::NotImplemented`]. This lets us write the
//! trait impl and OpenTheory integration tests today, and fill in
//! gaps as the kernel grows.
//!
//! # Architecture
//!
//! `HolPrim` is the **OpenTheory-side peer** of `KernelAletheBridge`
//! in `covalence-alethe`. Both sit *below* a clean frontend-facing
//! trait surface:
//!
//! | Frontend         | Clean surface         | Bridge (this layer)   |
//! |------------------|-----------------------|-----------------------|
//! | OpenTheory       | `HolLightKernel`      | `HolPrim`             |
//! | Alethe (SMT)     | `Prover`              | `KernelAletheBridge`  |
//!
//! Hacks (named ↔ locally-nameless conversion, `Eq` folding,
//! structural `aconv`, synthetic name minting, memoisation) live in
//! the bridge — never on the surface. When `covalence-kernel` is
//! rewritten, only the bridges churn; both surfaces stay stable.
//!
//! Right now `HolPrim` reaches directly into `KKernel` /
//! `Arena` because the [`Prover`] trait doesn't yet expose the
//! inspection primitives `HolLightKernel` needs (`dest_*` on
//! arbitrary `TermDef` shapes, `contains_free`, `subst_free`,
//! `type_kind`, `infer`, …). Migrating those to `Prover` and routing
//! `HolPrim` through the trait is a follow-up — non-blocking for
//! getting OpenTheory running.
//!
//! [`Prover`]: crate::Prover

use std::collections::HashMap;
use std::sync::Arc;

use smol_str::SmolStr;

use covalence_hol::types::{HolError, NameId};
use covalence_kernel::arena::Arena;
use covalence_kernel::id::{StrId, TyArgsId, TypeId};
use covalence_kernel::kernel::Kernel as KKernel;
use covalence_kernel::prop::{Context, Prop, ProofError, Thm};
use covalence_kernel::term::{TermDef, TermRef};
use covalence_kernel::ty::{TypeKind, TypeRef};

/// Opaque handle to a [`Thm`] stored inside a [`HolPrim`].
///
/// `Thm` itself isn't `Copy` (it carries an `Arc<Context>`), so the
/// HOL trait's `Self::Thm: Copy` requirement is satisfied via this
/// index handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ThmHandle(pub u32);

/// Errors raised by the HOL driver.
#[derive(Debug, thiserror::Error)]
pub enum HolPrimError {
    /// A feature the trait requires isn't supported by the current
    /// kernel yet. The string names the missing op so callers can
    /// grep for it.
    #[error("not implemented yet: {0}")]
    NotImplemented(&'static str),

    /// HOL-level error (type mismatch, ill-formed input, etc.).
    #[error(transparent)]
    Hol(#[from] HolError),

    /// Kernel proof rule failure.
    #[error("kernel proof error: {0:?}")]
    Proof(ProofError),

    /// The supplied [`ThmHandle`] is out of range.
    #[error("invalid theorem handle: {0}")]
    InvalidThmHandle(u32),

    /// Kernel-level union-find merge failure (used by the cong-based
    /// rules).
    #[error("kernel union error: {0:?}")]
    Union(covalence_kernel::UnionError),
}

impl From<ProofError> for HolPrimError {
    fn from(e: ProofError) -> Self {
        HolPrimError::Proof(e)
    }
}

impl From<covalence_kernel::UnionError> for HolPrimError {
    fn from(e: covalence_kernel::UnionError) -> Self {
        HolPrimError::Union(e)
    }
}

/// The driver. Owns the kernel and the bridge state.
///
/// The HOL Light `NameId` namespace is a flat `u64` index maintained
/// by the OpenTheory `NameTable`. The kernel uses its own `StrId`
/// interner. The driver keeps both directions of the mapping cached
/// so each `NameId` corresponds to one canonical `StrId` and vice
/// versa within a session.
pub struct HolPrim {
    kernel: KKernel,

    /// HOL `NameId` → kernel string identifier.
    name_to_str: HashMap<NameId, StrId>,
    /// Kernel string identifier → HOL `NameId` (inverse of
    /// [`Self::name_to_str`], populated lazily by `dest_*` paths).
    str_to_name: HashMap<StrId, NameId>,
    /// Used by [`Self::bind_name`] to mint placeholder NameIds when
    /// the driver itself needs a fresh name (e.g. `dest_abs` returning
    /// a binder name that the source never declared). Starts above
    /// any NameId the caller is likely to use; collisions are
    /// detected via [`Self::name_to_str`].
    next_synthetic_name: NameId,

    /// HOL well-known IDs for `->`, `bool`, `=`.
    fun_id: NameId,
    bool_id: NameId,
    eq_id: NameId,

    /// Declared type operators: `NameId` → arity. Includes `bool` (0)
    /// and `->` (2) registered at construction.
    type_constants: HashMap<NameId, usize>,
    /// Declared term constants: `NameId` → polymorphic generic type.
    /// Includes `=` registered at construction.
    term_constants: HashMap<NameId, TypeRef>,

    /// Theorem storage. `ThmHandle(i)` indexes into here.
    thms: Vec<Thm>,
    /// Handles of theorems introduced via `new_axiom`.
    axioms: Vec<ThmHandle>,

    /// Cached empty session context. Sharing one `Arc<Context>`
    /// across all empty-hyp Thms (refl, beta, …) keeps
    /// `Arc::ptr_eq` true between them, which is what the kernel's
    /// trans/eq_mp/cong rules require for context-match.
    empty_ctx: Arc<Context>,
}

impl HolPrim {
    /// Build a fresh driver. `fun_id` / `bool_id` / `eq_id` are the
    /// HOL `NameId`s for the three well-known constants — typically
    /// the constants `FUN_TYCON_ID`, `BOOL_TYCON_ID`, `EQ_CONST_ID`
    /// from `covalence_hol::types`, which the OpenTheory `NameTable`
    /// preregisters as 0/1/2.
    pub fn new(fun_id: NameId, bool_id: NameId, eq_id: NameId) -> Self {
        let mut kernel = KKernel::new();

        // Register the three well-known names in the kernel's string
        // interner so the bridge can translate them.
        let fun_str = kernel.arena_mut().intern_string(SmolStr::new("->"));
        let bool_str = kernel.arena_mut().intern_string(SmolStr::new("bool"));
        let eq_str = kernel.arena_mut().intern_string(SmolStr::new("="));

        let mut name_to_str = HashMap::new();
        name_to_str.insert(fun_id, fun_str);
        name_to_str.insert(bool_id, bool_str);
        name_to_str.insert(eq_id, eq_str);

        let mut str_to_name = HashMap::new();
        str_to_name.insert(fun_str, fun_id);
        str_to_name.insert(bool_str, bool_id);
        str_to_name.insert(eq_str, eq_id);

        let mut type_constants = HashMap::new();
        type_constants.insert(fun_id, 2);
        type_constants.insert(bool_id, 0);

        // `=` has generic type `α → α → bool`. We record the
        // polymorphic scheme so `mk_const_validated` can later check
        // a requested instance.
        let alpha_str = kernel.arena_mut().intern_string(SmolStr::new("A"));
        let alpha = kernel.arena_mut().alloc_tvar(alpha_str);
        let bool_ty = kernel.bool_ty();
        let alpha_bool = kernel.fun_ty(alpha, bool_ty);
        let eq_ty = kernel.fun_ty(alpha, alpha_bool);
        let mut term_constants = HashMap::new();
        term_constants.insert(eq_id, eq_ty);

        Self {
            kernel,
            name_to_str,
            str_to_name,
            next_synthetic_name: NameId::MAX / 2,
            fun_id,
            bool_id,
            eq_id,
            type_constants,
            term_constants,
            thms: Vec::new(),
            axioms: Vec::new(),
            empty_ctx: Context::empty(),
        }
    }

    // -----------------------------------------------------------------
    // Internals
    // -----------------------------------------------------------------

    /// Read-only kernel access (for tests / drivers that want to
    /// inspect the underlying kernel state).
    pub fn kernel(&self) -> &KKernel {
        &self.kernel
    }

    /// Mutable kernel access. Use sparingly — code that touches the
    /// kernel directly bypasses the bridge state.
    pub fn kernel_mut(&mut self) -> &mut KKernel {
        &mut self.kernel
    }

    fn arena(&self) -> &Arena {
        self.kernel.arena()
    }

    fn arena_mut(&mut self) -> &mut Arena {
        self.kernel.arena_mut()
    }

    /// HOL `NameId` → kernel `StrId`. Names not previously seen are
    /// minted into the kernel interner under a synthetic string so
    /// that the bridge stays total.
    fn str_of(&mut self, name: NameId) -> StrId {
        if let Some(&s) = self.name_to_str.get(&name) {
            return s;
        }
        let synthetic = SmolStr::new(format!("?n{name}"));
        let s = self.arena_mut().intern_string(synthetic);
        self.name_to_str.insert(name, s);
        self.str_to_name.insert(s, name);
        s
    }

    /// Kernel `StrId` → HOL `NameId`. Pure read; returns `None` if
    /// the string wasn't previously registered via [`Self::str_of`]
    /// or [`Self::bind_name`]. All names produced by `mk_*` methods
    /// are registered, so this is total for terms/types built
    /// through `HolPrim`.
    fn name_of(&self, s: StrId) -> Option<NameId> {
        self.str_to_name.get(&s).copied()
    }

    /// Like [`Self::name_of`] but mints a synthetic `NameId` on
    /// miss. Used by paths that legitimately need to bind a fresh
    /// name (e.g. opening a binder in `dest_abs`).
    #[allow(dead_code)]
    fn bind_name(&mut self, s: StrId) -> NameId {
        if let Some(n) = self.name_of(s) {
            return n;
        }
        let mut n = self.next_synthetic_name;
        while self.name_to_str.contains_key(&n) {
            n = n.wrapping_add(1);
        }
        self.next_synthetic_name = n.wrapping_add(1);
        self.name_to_str.insert(n, s);
        self.str_to_name.insert(s, n);
        n
    }

    fn store_thm(&mut self, thm: Thm) -> ThmHandle {
        let id = self.thms.len() as u32;
        self.thms.push(thm);
        ThmHandle(id)
    }

    fn get_thm(&self, h: ThmHandle) -> Result<&Thm, HolPrimError> {
        self.thms
            .get(h.0 as usize)
            .ok_or(HolPrimError::InvalidThmHandle(h.0))
    }

    fn clone_thm(&self, h: ThmHandle) -> Result<Thm, HolPrimError> {
        self.get_thm(h).cloned()
    }

    /// Well-known accessor for the unit `=` constant.
    pub fn eq_id(&self) -> NameId {
        self.eq_id
    }

    /// Well-known accessor for the `bool` type constructor.
    pub fn bool_id(&self) -> NameId {
        self.bool_id
    }

    /// Well-known accessor for the `->` type constructor.
    pub fn fun_id(&self) -> NameId {
        self.fun_id
    }

    // =================================================================
    // Type primitives
    // =================================================================

    /// Construct a polymorphic type variable.
    pub fn mk_tyvar(&mut self, name: NameId) -> TypeRef {
        let s = self.str_of(name);
        self.arena_mut().alloc_tvar(s)
    }

    /// Construct a type-constructor application. Handles `bool`/`->`
    /// specially; user constructors go through the kernel's nominal
    /// `Tyapp`. Does **not** check arity — see
    /// [`Self::mk_type_validated`] for that.
    pub fn mk_tyapp(&mut self, name: NameId, args: Vec<TypeRef>) -> TypeRef {
        if name == self.bool_id && args.is_empty() {
            return self.kernel.bool_ty();
        }
        if name == self.fun_id && args.len() == 2 {
            return self.kernel.fun_ty(args[0], args[1]);
        }
        let s = self.str_of(name);
        let ta = self.arena_mut().intern_tyargs(args);
        self.arena_mut().alloc_tyapp(s, ta)
    }

    /// The boolean type.
    pub fn bool_type(&self) -> TypeRef {
        self.kernel.bool_ty()
    }

    /// The function type `dom → cod`.
    pub fn fun_type(&mut self, dom: TypeRef, cod: TypeRef) -> TypeRef {
        self.kernel.fun_ty(dom, cod)
    }

    /// If `ty` is a type variable, return its HOL `NameId`.
    /// Returns `None` if the variable was built outside of this
    /// `HolPrim`'s registered names.
    pub fn dest_tyvar(&self, ty: TypeRef) -> Option<NameId> {
        match self.arena().type_ref_kind(ty)? {
            TypeKind::TVar(s) => self.name_of(s),
            _ => None,
        }
    }

    /// If `ty` is a type application, return `(constructor, args)`.
    pub fn dest_tyapp(&self, ty: TypeRef) -> Option<(NameId, Vec<TypeRef>)> {
        match self.arena().type_ref_kind(ty)? {
            TypeKind::Builtin(covalence_kernel::ty::BuiltinTy::Bool) => {
                Some((self.bool_id, Vec::new()))
            }
            TypeKind::Fun(a, b) => Some((self.fun_id, vec![a, b])),
            TypeKind::Tyapp(s, args_id) => {
                let args = self.arena().tyargs(args_id).to_vec();
                let name = self.name_of(s)?;
                Some((name, args))
            }
            _ => None,
        }
    }

    /// Structural type equality. Kernel `TypeRef`s are interned per
    /// `Arena`, so the cheap `==` is sound for types built against
    /// the same kernel — which is always the case inside one
    /// `HolPrim`.
    pub fn type_eq(&self, a: TypeRef, b: TypeRef) -> bool {
        a == b
    }

    /// All free type variables of `ty` (deduplicated, in first-seen
    /// order). Names not registered in this `HolPrim` (e.g. introduced
    /// by raw kernel allocation) are skipped silently — by contract
    /// every type built via `HolPrim` has its variables registered.
    pub fn tyvars(&self, ty: TypeRef) -> Vec<NameId> {
        let mut acc: Vec<StrId> = Vec::new();
        Self::tyvars_into(self.arena(), ty, &mut acc);
        acc.into_iter().filter_map(|s| self.name_of(s)).collect()
    }

    fn tyvars_into(arena: &Arena, ty: TypeRef, acc: &mut Vec<StrId>) {
        let Some(kind) = arena.type_ref_kind(ty) else {
            return;
        };
        match kind {
            TypeKind::Builtin(_) => {}
            TypeKind::TVar(s) => {
                if !acc.contains(&s) {
                    acc.push(s);
                }
            }
            TypeKind::Fun(a, b) => {
                Self::tyvars_into(arena, a, acc);
                Self::tyvars_into(arena, b, acc);
            }
            TypeKind::Tyapp(_, args_id) => {
                let args = arena.tyargs(args_id).to_vec();
                for a in args {
                    Self::tyvars_into(arena, a, acc);
                }
            }
            TypeKind::Subset(parent, _p) => {
                Self::tyvars_into(arena, parent, acc);
                // Predicate `p` is closed and has no free type vars
                // by construction (see `Arena::alloc_subset_ty`), so
                // we don't recurse into it.
            }
            TypeKind::Foreign(_, _) => {}
        }
    }

    /// Apply a type substitution to a type. `pairs` is
    /// `(new_type, old_tyvar_name)` — HOL Light's pair order.
    ///
    /// Not yet implemented — needs a kernel-side
    /// `Arena::apply_type_subst(TypeRef, &TypeSubst) -> TypeRef`.
    pub fn type_inst(
        &mut self,
        _ty: TypeRef,
        _pairs: &[(TypeRef, NameId)],
    ) -> Result<TypeRef, HolPrimError> {
        Err(HolPrimError::NotImplemented("type_inst"))
    }

    // =================================================================
    // Term primitives
    // =================================================================

    /// Construct a named free variable.
    pub fn mk_var(&mut self, name: NameId, ty: TypeRef) -> TermRef {
        let s = self.str_of(name);
        let id = self.arena_mut().alloc_term(TermDef::Free(s, ty));
        TermRef::local(id)
    }

    /// Construct a constant occurrence. **Unvalidated** — does not
    /// check the constant has been declared with a matching generic
    /// type. See [`Self::mk_const_validated`].
    pub fn mk_const(&mut self, name: NameId, ty: TypeRef) -> TermRef {
        let s = self.str_of(name);
        let id = self.arena_mut().alloc_term(TermDef::Const(s, ty));
        TermRef::local(id)
    }

    /// Application `f x`.
    ///
    /// Performs one shell-level rewrite for HOL-Light parity: when
    /// `f` is `Comb(Const "=", lhs)`, fold into `Eq(lhs, x)`.
    /// OpenTheory articles build equalities as `((= a) b)` via
    /// `constTerm "=" + appTerm + appTerm`, but our kernel stores
    /// equality as a primitive `Eq(_, _)` shape — folding here keeps
    /// both representations alpha-equivalent.
    pub fn mk_comb(&mut self, f: TermRef, x: TermRef) -> TermRef {
        if let Some(eq) = self.try_fold_eq(f, x) {
            return eq;
        }
        let id = self.arena_mut().alloc_term(TermDef::Comb(f, x));
        // Kernel's cached typing can't resolve Bound(_) without
        // context, so re-infer to populate the cache. `is_well_typed`
        // (which the Thm rules consult) reads only the cache.
        let _ = self.arena_mut().infer(id);
        TermRef::local(id)
    }

    /// If `f` is `Comb(Const "=", lhs)`, allocate `Eq(lhs, x)` and
    /// return it. Otherwise `None`.
    fn try_fold_eq(&mut self, f: TermRef, x: TermRef) -> Option<TermRef> {
        let f_id = f.as_local()?;
        let (g, lhs) = match *self.arena().term_def(f_id) {
            TermDef::Comb(g, lhs) => (g, lhs),
            _ => return None,
        };
        let g_id = g.as_local()?;
        let is_eq_const = match *self.arena().term_def(g_id) {
            TermDef::Const(s, _) => self.name_of(s) == Some(self.eq_id),
            _ => false,
        };
        if !is_eq_const {
            return None;
        }
        Some(self.mk_eq(lhs, x))
    }

    /// Lambda abstraction `λvar. body`. `var` must be a `Free`
    /// term; the body is closed over it (locally-nameless body).
    pub fn mk_abs(&mut self, var: TermRef, body: TermRef) -> Result<TermRef, HolPrimError> {
        let var_id = var.as_local().ok_or(HolError::NotAVariable)?;
        let (name, ty) = match *self.arena().term_def(var_id) {
            TermDef::Free(s, ty) => (s, ty),
            _ => return Err(HolError::NotAVariable.into()),
        };
        let closed_body = self.arena_mut().abstract_over(body, name, ty, 0);
        let id = self.arena_mut().alloc_term(TermDef::Lam(ty, closed_body));
        let _ = self.arena_mut().infer(id);
        Ok(TermRef::local(id))
    }

    /// Equality `lhs = rhs`.
    pub fn mk_eq(&mut self, lhs: TermRef, rhs: TermRef) -> TermRef {
        let id = self.arena_mut().alloc_term(TermDef::Eq(lhs, rhs));
        let _ = self.arena_mut().infer(id);
        TermRef::local(id)
    }

    /// If `tm` is a `Free` variable, return `(name, type)`.
    pub fn dest_var(&self, tm: TermRef) -> Option<(NameId, TypeRef)> {
        let id = tm.as_local()?;
        match *self.arena().term_def(id) {
            TermDef::Free(s, ty) => Some((self.name_of(s)?, ty)),
            _ => None,
        }
    }

    /// If `tm` is a `Const` term, return `(name, type)`.
    pub fn dest_const(&self, tm: TermRef) -> Option<(NameId, TypeRef)> {
        let id = tm.as_local()?;
        match *self.arena().term_def(id) {
            TermDef::Const(s, ty) => Some((self.name_of(s)?, ty)),
            _ => None,
        }
    }

    /// If `tm` is an application, return `(f, x)`.
    pub fn dest_comb(&self, tm: TermRef) -> Option<(TermRef, TermRef)> {
        let id = tm.as_local()?;
        match *self.arena().term_def(id) {
            TermDef::Comb(f, x) => Some((f, x)),
            _ => None,
        }
    }

    /// If `tm` is an abstraction `λ_:ty. body`, return a fresh
    /// `Var(synth_name, ty)` and the body with `Bound(0)` replaced
    /// by that var.
    ///
    /// HOL Light stores the binder name; covalence-kernel's
    /// locally-nameless `Lam(ty, body)` doesn't. We mint a synthetic
    /// HOL `NameId` per call so downstream code (e.g. OpenTheory
    /// `var` lookups) still gets a Var it can pattern-match. Alpha-
    /// equivalence isn't affected.
    pub fn dest_abs(&mut self, tm: TermRef) -> Option<(TermRef, TermRef)> {
        let id = tm.as_local()?;
        let (ty, body) = match *self.arena().term_def(id) {
            TermDef::Lam(ty, body) => (ty, body),
            _ => return None,
        };
        // Mint a fresh free variable of the right type to fill the
        // outermost binder.
        let synth = self.next_synthetic_name;
        self.next_synthetic_name = synth.wrapping_add(1);
        let var = self.mk_var(synth, ty);
        let opened = self.arena_mut().subst(body, 0, var);
        Some((var, opened))
    }

    /// If `tm` is `Eq(lhs, rhs)`, return `(lhs, rhs)`.
    pub fn dest_eq(&self, tm: TermRef) -> Option<(TermRef, TermRef)> {
        let id = tm.as_local()?;
        match *self.arena().term_def(id) {
            TermDef::Eq(a, b) => Some((a, b)),
            _ => None,
        }
    }

    /// The type of `tm`. Returns `Err` if the kernel can't infer one
    /// (ill-typed input).
    pub fn type_of(&mut self, tm: TermRef) -> Result<TypeRef, HolPrimError> {
        let id = tm.as_local().ok_or(HolError::NotACombination)?;
        self.arena_mut()
            .infer(id)
            .as_type()
            .ok_or_else(|| HolError::TypeMismatch("term is not typed".into()).into())
    }

    /// Structural term equality. Compares the `TermDef` shape
    /// recursively — `alloc_term` does not dedup, so identical
    /// shapes can sit at different `TermRef`s in the arena.
    pub fn term_eq(&self, a: TermRef, b: TermRef) -> bool {
        Self::ref_eq(self.arena(), a, b)
    }

    fn term_eq_ids(
        arena: &Arena,
        a: covalence_kernel::id::TermId,
        b: covalence_kernel::id::TermId,
    ) -> bool {
        if a == b {
            return true;
        }
        let da = *arena.term_def(a);
        let db = *arena.term_def(b);
        Self::term_def_eq(arena, da, db)
    }

    fn term_def_eq(arena: &Arena, da: TermDef, db: TermDef) -> bool {
        use TermDef::*;
        match (da, db) {
            (Comb(f1, x1), Comb(f2, x2)) => {
                Self::ref_eq(arena, f1, f2) && Self::ref_eq(arena, x1, x2)
            }
            (Eq(f1, x1), Eq(f2, x2)) => {
                Self::ref_eq(arena, f1, f2) && Self::ref_eq(arena, x1, x2)
            }
            (Lam(t1, b1), Lam(t2, b2)) => t1 == t2 && Self::ref_eq(arena, b1, b2),
            (Forall(p1), Forall(p2)) => Self::ref_eq(arena, p1, p2),
            (Exists(p1), Exists(p2)) => Self::ref_eq(arena, p1, p2),
            (Op1(o1, p1), Op1(o2, p2)) => o1 == o2 && Self::ref_eq(arena, p1, p2),
            (Op2(o1, l1, r1), Op2(o2, l2, r2)) => {
                o1 == o2 && Self::ref_eq(arena, l1, l2) && Self::ref_eq(arena, r1, r2)
            }
            (Eps(t1, p1), Eps(t2, p2)) => t1 == t2 && Self::ref_eq(arena, p1, p2),
            _ => da == db,
        }
    }

    fn ref_eq(arena: &Arena, a: TermRef, b: TermRef) -> bool {
        if a == b {
            return true;
        }
        let Some(a_id) = a.as_local() else { return false };
        let Some(b_id) = b.as_local() else { return false };
        Self::term_eq_ids(arena, a_id, b_id)
    }

    /// α-equivalence. With locally-nameless body representation,
    /// α-equivalence coincides with structural equality of the
    /// stored `TermDef`s.
    pub fn aconv(&self, a: TermRef, b: TermRef) -> bool {
        self.term_eq(a, b)
    }

    /// Collect free variables of `tm` (deduplicated, first-seen
    /// order). Returns each as a `Free(_, _)` `TermRef`.
    pub fn frees(&mut self, tm: TermRef) -> Vec<TermRef> {
        let mut acc: Vec<(StrId, TypeRef)> = Vec::new();
        Self::frees_into(self.arena(), tm, &mut acc);
        let mut out = Vec::with_capacity(acc.len());
        for (s, ty) in acc {
            let id = self.arena_mut().alloc_term(TermDef::Free(s, ty));
            out.push(TermRef::local(id));
        }
        out
    }

    fn frees_into(arena: &Arena, tm: TermRef, acc: &mut Vec<(StrId, TypeRef)>) {
        let Some(id) = tm.as_local() else { return };
        if !arena.term_props(id).has_free {
            return;
        }
        let def = *arena.term_def(id);
        if let TermDef::Free(s, ty) = def {
            if !acc.iter().any(|(s2, ty2)| *s2 == s && *ty2 == ty) {
                acc.push((s, ty));
            }
            return;
        }
        use covalence_kernel::term::Deps;
        match def.deps() {
            Deps::None => {}
            Deps::One(c) => Self::frees_into(arena, c, acc),
            Deps::Two(a, b) => {
                Self::frees_into(arena, a, acc);
                Self::frees_into(arena, b, acc);
            }
        }
    }

    /// Does the free variable `var` occur in `tm`?
    pub fn vfree_in(&self, var: TermRef, tm: TermRef) -> bool {
        let Some(var_id) = var.as_local() else {
            return false;
        };
        let (name, ty) = match *self.arena().term_def(var_id) {
            TermDef::Free(s, ty) => (s, ty),
            _ => return false,
        };
        self.arena().contains_free(tm, name, ty)
    }

    /// Term-variable substitution. `pairs` is `(new_term, old_var)`
    /// — HOL Light's pair order. Applies pairs sequentially.
    pub fn vsubst(
        &mut self,
        tm: TermRef,
        pairs: &[(TermRef, TermRef)],
    ) -> Result<TermRef, HolPrimError> {
        let mut current = tm;
        for &(new_tm, old_var) in pairs {
            let var_id = old_var.as_local().ok_or(HolError::NotAVariable)?;
            let (name, ty) = match *self.arena().term_def(var_id) {
                TermDef::Free(s, ty) => (s, ty),
                _ => return Err(HolError::NotAVariable.into()),
            };
            current = self.arena_mut().subst_free(current, name, ty, new_tm);
        }
        Ok(current)
    }

    /// Type instantiation on a term. Not yet implemented — needs the
    /// same kernel primitive as [`Self::type_inst`].
    pub fn inst_term(
        &mut self,
        _tm: TermRef,
        _pairs: &[(TypeRef, NameId)],
    ) -> Result<TermRef, HolPrimError> {
        Err(HolPrimError::NotImplemented("inst_term"))
    }

    // =================================================================
    // Theorem primitives
    // =================================================================

    /// Hypotheses of a theorem (the assumption Props' `concl`s, in
    /// context-chain order, deduplicated by `TermId` equality).
    pub fn hyps(&self, th: ThmHandle) -> Result<Vec<TermRef>, HolPrimError> {
        let thm = self.get_thm(th)?;
        let ctx = thm.context();
        let mut out = Vec::new();
        for i in 0..ctx.len() {
            let assum = ctx.assumption(i).expect("len/index invariant");
            let r = TermRef::local(assum.concl);
            if !out.contains(&r) {
                out.push(r);
            }
        }
        Ok(out)
    }

    /// Conclusion of a theorem.
    pub fn concl(&self, th: ThmHandle) -> Result<TermRef, HolPrimError> {
        let thm = self.get_thm(th)?;
        Ok(TermRef::local(thm.concl()))
    }

    /// `REFL t`: `⊢ t = t`. Built against the cached empty session
    /// context so all empty-hyp Thms share one `Arc<Context>`.
    pub fn refl(&mut self, t: TermRef) -> Result<ThmHandle, HolPrimError> {
        let id = t.as_local().ok_or(HolError::NotACombination)?;
        let ctx = self.empty_ctx.clone();
        let thm = Thm::refl(self.kernel.arena_mut(), ctx, id)?;
        Ok(self.store_thm(thm))
    }

    /// `BETA tm`: `⊢ (λx.b) x = b[x ↦ x]`. The kernel rule operates
    /// on `Comb(Lam(_, _), _)` shape directly — HOL Light's notion of
    /// "β-redex" coincides.
    pub fn beta_conv(&mut self, tm: TermRef) -> Result<ThmHandle, HolPrimError> {
        let id = tm.as_local().ok_or(HolError::NotBetaRedex)?;
        let ctx = self.empty_ctx.clone();
        let thm = Thm::beta(self.kernel.arena_mut(), ctx, id)?;
        Ok(self.store_thm(thm))
    }

    /// `ASSUME p`: `{p} ⊢ p`. Allocates a fresh assumption `Prop` in
    /// a single-assumption context whose parent is the cached empty
    /// session context.
    pub fn assume_rule(&mut self, p: TermRef) -> Result<ThmHandle, HolPrimError> {
        let id = p.as_local().ok_or(HolError::NotBoolean)?;
        let prop = Arc::new(Prop::new(self.empty_ctx.clone(), id));
        let ctx = Context::flat(vec![prop.clone()]);
        let thm = Thm::assume(self.kernel.arena(), ctx, prop)?;
        Ok(self.store_thm(thm))
    }

    /// `ABS var th`: from `⊢ s = t`, derive `⊢ (λvar. s) = (λvar. t)`.
    /// `var` must be a `Free(_, _)` term.
    pub fn abs_rule(
        &mut self,
        var: TermRef,
        th: ThmHandle,
    ) -> Result<ThmHandle, HolPrimError> {
        let var_id = var.as_local().ok_or(HolError::NotAVariable)?;
        let (name, ty) = match *self.arena().term_def(var_id) {
            TermDef::Free(s, ty) => (s, ty),
            _ => return Err(HolError::NotAVariable.into()),
        };
        let thm = self.clone_thm(th)?;
        let out = Thm::abs(self.kernel.arena_mut(), thm, name, ty)?;
        Ok(self.store_thm(out))
    }

    /// `SYM th`: from `⊢ a = b`, derive `⊢ b = a`.
    pub fn sym(&mut self, th: ThmHandle) -> Result<ThmHandle, HolPrimError> {
        let thm = self.clone_thm(th)?;
        let out = Thm::sym(self.kernel.arena_mut(), thm)?;
        Ok(self.store_thm(out))
    }

    /// `TRANS th1 th2`: from `⊢ a = b` and `⊢ b' = c` (with `b ≡ b'`
    /// at UF level 0) derive `⊢ a = c`. Contexts must currently be
    /// pointer-equal — context-set union for HOL Light-style hyp
    /// merging is a follow-up.
    pub fn trans(
        &mut self,
        th1: ThmHandle,
        th2: ThmHandle,
    ) -> Result<ThmHandle, HolPrimError> {
        let thm1 = self.clone_thm(th1)?;
        let thm2 = self.clone_thm(th2)?;
        if !Arc::ptr_eq(thm1.context(), thm2.context()) {
            return Err(HolPrimError::NotImplemented(
                "trans: context union not yet implemented",
            ));
        }
        let out = self.kernel.trans(thm1, thm2)?;
        Ok(self.store_thm(out))
    }

    /// `MK_COMB th1 th2`: from `⊢ f = g` and `⊢ x = y` derive
    /// `⊢ f x = g y`.
    ///
    /// Implemented via `union` + `cong(depth=1)`: equality of the
    /// two pairs is recorded in the session UF, then congruence
    /// closure over the `Comb` shells produces the result. This
    /// pollutes the session UF — fine for OpenTheory's linear-import
    /// model; a dedicated `Thm::mk_comb` primitive would be cleaner.
    pub fn mk_comb_rule(
        &mut self,
        th1: ThmHandle,
        th2: ThmHandle,
    ) -> Result<ThmHandle, HolPrimError> {
        let thm1 = self.clone_thm(th1)?;
        let thm2 = self.clone_thm(th2)?;
        if !Arc::ptr_eq(thm1.context(), thm2.context()) {
            return Err(HolPrimError::NotImplemented(
                "mk_comb_rule: context union not yet implemented",
            ));
        }
        let (f, g) = match *self.arena().term_def(thm1.concl()) {
            TermDef::Eq(l, r) => (l, r),
            _ => return Err(HolError::NotAnEquation.into()),
        };
        let (x, y) = match *self.arena().term_def(thm2.concl()) {
            TermDef::Eq(l, r) => (l, r),
            _ => return Err(HolError::NotAnEquation.into()),
        };
        let ctx = thm1.context().clone();
        // Record both equalities in UF so cong can chase them.
        self.kernel.union(f, g)?;
        self.kernel.union(x, y)?;
        let fx = self.mk_comb(f, x);
        let gy = self.mk_comb(g, y);
        // `Kernel::cong` builds the equality Thm against the supplied
        // context after checking UF-congruence at the depth.
        let _ = ctx;
        let out = self.kernel.cong(fx, gy, 1)?;
        Ok(self.store_thm(out))
    }

    /// `EQ_MP th1 th2`: from `⊢ p = q` and `⊢ p'` (with `p ≡ p'`)
    /// derive `⊢ q`. Same context constraint as [`Self::trans`].
    pub fn eq_mp(
        &mut self,
        th1: ThmHandle,
        th2: ThmHandle,
    ) -> Result<ThmHandle, HolPrimError> {
        let thm1 = self.clone_thm(th1)?;
        let thm2 = self.clone_thm(th2)?;
        if !Arc::ptr_eq(thm1.context(), thm2.context()) {
            return Err(HolPrimError::NotImplemented(
                "eq_mp: context union not yet implemented",
            ));
        }
        let out = self.kernel.eq_mp(thm1, thm2)?;
        Ok(self.store_thm(out))
    }

    /// `DEDUCT_ANTISYM th1 th2`: from `A1 ⊢ p` and `A2 ⊢ q`, derive
    /// `(A1 \ {q}) ∪ (A2 \ {p}) ⊢ p = q`. The kernel rule already
    /// handles arbitrary contexts via UF-canonical assumption
    /// dedup; we just forward through the kernel facade.
    pub fn deduct_antisym(
        &mut self,
        th1: ThmHandle,
        th2: ThmHandle,
    ) -> Result<ThmHandle, HolPrimError> {
        let thm_p = self.clone_thm(th1)?;
        let thm_q = self.clone_thm(th2)?;
        let out = self.kernel.deduct_antisym_rule(thm_p, thm_q)?;
        Ok(self.store_thm(out))
    }

    /// `INST pairs th`: parallel term-variable instantiation.
    /// Implemented as sequential `Thm::inst` calls for now; HOL Light
    /// requires no two pairs share an old-var, so the sequential
    /// reading is correct.
    pub fn inst_rule(
        &mut self,
        pairs: &[(TermRef, TermRef)],
        th: ThmHandle,
    ) -> Result<ThmHandle, HolPrimError> {
        let mut current = self.clone_thm(th)?;
        for &(new_tm, old_var) in pairs {
            let var_id = old_var.as_local().ok_or(HolError::NotAVariable)?;
            let (name, ty) = match *self.arena().term_def(var_id) {
                TermDef::Free(s, ty) => (s, ty),
                _ => return Err(HolError::NotAVariable.into()),
            };
            current = Thm::inst(self.kernel.arena_mut(), current, name, ty, new_tm)?;
        }
        Ok(self.store_thm(current))
    }

    /// `INST_TYPE pairs th`. Kernel doesn't have this primitive yet.
    pub fn inst_type_rule(
        &mut self,
        _pairs: &[(TypeRef, NameId)],
        _th: ThmHandle,
    ) -> Result<ThmHandle, HolPrimError> {
        Err(HolPrimError::NotImplemented("inst_type_rule"))
    }

    /// `new_axiom tm`: post a fresh axiom `⊢ tm`. Kernel doesn't
    /// have a trusted-axiom primitive yet (planned as a small
    /// addition).
    pub fn new_axiom(&mut self, _tm: TermRef) -> Result<ThmHandle, HolPrimError> {
        Err(HolPrimError::NotImplemented("new_axiom"))
    }

    /// `new_basic_definition c = t`: kernel doesn't have this
    /// primitive yet.
    pub fn new_basic_definition(&mut self, _tm: TermRef) -> Result<ThmHandle, HolPrimError> {
        Err(HolPrimError::NotImplemented("new_basic_definition"))
    }

    /// `new_basic_type_definition`: maps onto `Thm::subset_axioms`
    /// but the trait-faithful shape (HOL Light's two unconditional
    /// theorems) needs the existence-theorem-driven specialisation.
    /// Stub.
    pub fn new_basic_type_definition(
        &mut self,
        _tyname: NameId,
        _abs_name: NameId,
        _rep_name: NameId,
        _abs_var_name: NameId,
        _rep_var_name: NameId,
        _th: ThmHandle,
    ) -> Result<(ThmHandle, ThmHandle), HolPrimError> {
        Err(HolPrimError::NotImplemented("new_basic_type_definition"))
    }

    /// Register a new type constructor (shell-side bookkeeping).
    pub fn new_type(&mut self, name: NameId, arity: usize) -> Result<(), HolPrimError> {
        if self.type_constants.contains_key(&name) {
            return Err(HolError::TypeAlreadyDefined(format!("{name}")).into());
        }
        self.type_constants.insert(name, arity);
        Ok(())
    }

    /// Register a new constant with its generic type (shell-side
    /// bookkeeping).
    pub fn new_constant(&mut self, name: NameId, ty: TypeRef) -> Result<(), HolPrimError> {
        if self.term_constants.contains_key(&name) {
            return Err(HolError::ConstantAlreadyDefined(format!("{name}")).into());
        }
        self.term_constants.insert(name, ty);
        Ok(())
    }

    /// All axioms posted via [`Self::new_axiom`].
    pub fn get_axioms(&self) -> Vec<ThmHandle> {
        self.axioms.clone()
    }

    /// Construct a type application after checking the constructor
    /// is declared and the arity matches.
    pub fn mk_type_validated(
        &mut self,
        name: NameId,
        args: Vec<TypeRef>,
    ) -> Result<TypeRef, HolPrimError> {
        let arity = *self
            .type_constants
            .get(&name)
            .ok_or(HolError::UnknownTypeConstructor(name))?;
        if args.len() != arity {
            return Err(HolError::WrongTypeArity {
                expected: arity,
                got: args.len(),
            }
            .into());
        }
        Ok(self.mk_tyapp(name, args))
    }

    /// Construct a constant occurrence after checking the constant
    /// is declared. Currently does **not** verify that `ty` is an
    /// instance of the registered generic type — that needs HOL
    /// Light-style type unification, which lives in covalence-hol
    /// today and will be reimplemented here later.
    pub fn mk_const_validated(
        &mut self,
        name: NameId,
        ty: TypeRef,
    ) -> Result<TermRef, HolPrimError> {
        if !self.term_constants.contains_key(&name) {
            return Err(HolError::UnknownConstant(name).into());
        }
        // TODO: type_match check against the generic scheme. Until
        // then we accept any well-typed instance.
        let _ = self.term_constants.get(&name).copied().unwrap_or(ty);
        Ok(self.mk_const(name, ty))
    }
}

// Note on suppressed-unused warnings for now: `TyArgsId` is named in
// imports because future work (alpha-name mapping in dest_tyapp) will
// surface it. Same for the explicit `TypeId` re-export.
#[allow(dead_code)]
const _: Option<TyArgsId> = None;
#[allow(dead_code)]
const _UNUSED_TID: Option<TypeId> = None;

// =================================================================
// HolLightKernel trait implementation
// =================================================================
//
// Forwards each trait method to the matching `HolPrim` method.
// HolPrim methods that return `Result<_, HolPrimError>` are funneled
// into `HolError::Unsupported(_)` for the trait's `Result<_, HolError>`
// surface. For the handful of *infallible* trait methods that hit a
// not-yet-implemented `HolPrim` path (e.g. `type_inst`, `inst_term`),
// we panic with the missing-op label so test failures point at the
// gap instead of silently producing an ill-typed term.

impl From<HolPrimError> for HolError {
    fn from(e: HolPrimError) -> Self {
        match e {
            HolPrimError::NotImplemented(op) => HolError::Unsupported(op.into()),
            HolPrimError::Hol(h) => h,
            HolPrimError::Proof(p) => HolError::TypeMismatch(format!("kernel proof: {p:?}")),
            HolPrimError::InvalidThmHandle(i) => HolError::InvalidThmId(i),
            HolPrimError::Union(u) => HolError::TypeMismatch(format!("kernel union: {u:?}")),
        }
    }
}

fn expect<T>(r: Result<T, HolPrimError>) -> T {
    match r {
        Ok(v) => v,
        Err(HolPrimError::NotImplemented(op)) => panic!("HolPrim trait impl: {op} not implemented"),
        Err(e) => panic!("HolPrim trait impl: unexpected error: {e}"),
    }
}

impl covalence_hol::traits::HolLightTypes for HolPrim {
    type Type = TypeRef;

    fn fun_id(&self) -> NameId {
        HolPrim::fun_id(self)
    }

    fn bool_id(&self) -> NameId {
        HolPrim::bool_id(self)
    }

    fn mk_tyvar(&mut self, name: NameId) -> Self::Type {
        HolPrim::mk_tyvar(self, name)
    }

    fn mk_tyapp(&mut self, name: NameId, args: Vec<Self::Type>) -> Self::Type {
        HolPrim::mk_tyapp(self, name, args)
    }

    fn bool_type(&mut self) -> Self::Type {
        HolPrim::bool_type(self)
    }

    fn fun_type(&mut self, a: Self::Type, b: Self::Type) -> Self::Type {
        HolPrim::fun_type(self, a, b)
    }

    fn dest_tyvar(&self, ty: Self::Type) -> Option<NameId> {
        HolPrim::dest_tyvar(self, ty)
    }

    fn dest_tyapp(&self, ty: Self::Type) -> Option<(NameId, Vec<Self::Type>)> {
        HolPrim::dest_tyapp(self, ty)
    }

    fn type_eq(&self, a: Self::Type, b: Self::Type) -> bool {
        HolPrim::type_eq(self, a, b)
    }

    fn tyvars(&self, ty: Self::Type) -> Vec<NameId> {
        HolPrim::tyvars(self, ty)
    }

    fn type_inst(&mut self, ty: Self::Type, pairs: &[(Self::Type, NameId)]) -> Self::Type {
        expect(HolPrim::type_inst(self, ty, pairs))
    }
}

impl covalence_hol::traits::HolLightTerms for HolPrim {
    type Term = TermRef;

    fn eq_id(&self) -> NameId {
        HolPrim::eq_id(self)
    }

    fn mk_var(&mut self, name: NameId, ty: Self::Type) -> Self::Term {
        HolPrim::mk_var(self, name, ty)
    }

    fn mk_const(&mut self, name: NameId, ty: Self::Type) -> Self::Term {
        HolPrim::mk_const(self, name, ty)
    }

    fn mk_comb(&mut self, f: Self::Term, x: Self::Term) -> Self::Term {
        HolPrim::mk_comb(self, f, x)
    }

    fn mk_abs(&mut self, var: Self::Term, body: Self::Term) -> Self::Term {
        // Trait signature has no Result — callers expect a well-
        // formed Lam. Panic on non-Var input to make the error
        // visible (HolKernel's impl silently produced a malformed
        // Abs node; we'd rather surface it).
        expect(HolPrim::mk_abs(self, var, body))
    }

    fn mk_eq(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term {
        HolPrim::mk_eq(self, lhs, rhs)
    }

    fn dest_var(&self, tm: Self::Term) -> Option<(NameId, Self::Type)> {
        HolPrim::dest_var(self, tm)
    }

    fn dest_const(&self, tm: Self::Term) -> Option<(NameId, Self::Type)> {
        HolPrim::dest_const(self, tm)
    }

    fn dest_comb(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)> {
        HolPrim::dest_comb(self, tm)
    }

    fn dest_abs(&mut self, tm: Self::Term) -> Option<(Self::Term, Self::Term)> {
        HolPrim::dest_abs(self, tm)
    }

    fn dest_eq(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)> {
        HolPrim::dest_eq(self, tm)
    }

    fn type_of(&mut self, tm: Self::Term) -> Self::Type {
        expect(HolPrim::type_of(self, tm))
    }

    fn term_eq(&self, a: Self::Term, b: Self::Term) -> bool {
        HolPrim::term_eq(self, a, b)
    }

    fn aconv(&self, a: Self::Term, b: Self::Term) -> bool {
        HolPrim::aconv(self, a, b)
    }

    fn frees(&mut self, tm: Self::Term) -> Vec<Self::Term> {
        HolPrim::frees(self, tm)
    }

    fn vfree_in(&self, var: Self::Term, tm: Self::Term) -> bool {
        HolPrim::vfree_in(self, var, tm)
    }

    fn vsubst(
        &mut self,
        tm: Self::Term,
        pairs: &[(Self::Term, Self::Term)],
    ) -> Result<Self::Term, HolError> {
        HolPrim::vsubst(self, tm, pairs).map_err(Into::into)
    }

    fn inst_term(&mut self, tm: Self::Term, pairs: &[(Self::Type, NameId)]) -> Self::Term {
        expect(HolPrim::inst_term(self, tm, pairs))
    }
}

impl covalence_hol::traits::HolLightKernel for HolPrim {
    type Thm = ThmHandle;

    fn hyps(&self, th: Self::Thm) -> Vec<Self::Term> {
        HolPrim::hyps(self, th).unwrap_or_default()
    }

    fn concl(&self, th: Self::Thm) -> Self::Term {
        HolPrim::concl(self, th).expect("invalid ThmHandle in concl")
    }

    fn refl(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError> {
        HolPrim::refl(self, tm).map_err(Into::into)
    }

    fn trans(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, HolError> {
        HolPrim::trans(self, th1, th2).map_err(Into::into)
    }

    fn mk_comb_rule(
        &mut self,
        th1: Self::Thm,
        th2: Self::Thm,
    ) -> Result<Self::Thm, HolError> {
        HolPrim::mk_comb_rule(self, th1, th2).map_err(Into::into)
    }

    fn abs_rule(
        &mut self,
        var: Self::Term,
        th: Self::Thm,
    ) -> Result<Self::Thm, HolError> {
        HolPrim::abs_rule(self, var, th).map_err(Into::into)
    }

    fn beta_conv(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError> {
        HolPrim::beta_conv(self, tm).map_err(Into::into)
    }

    fn assume_rule(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError> {
        HolPrim::assume_rule(self, tm).map_err(Into::into)
    }

    fn eq_mp(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, HolError> {
        HolPrim::eq_mp(self, th1, th2).map_err(Into::into)
    }

    fn deduct_antisym(
        &mut self,
        th1: Self::Thm,
        th2: Self::Thm,
    ) -> Result<Self::Thm, HolError> {
        HolPrim::deduct_antisym(self, th1, th2).map_err(Into::into)
    }

    fn inst_rule(
        &mut self,
        pairs: &[(Self::Term, Self::Term)],
        th: Self::Thm,
    ) -> Result<Self::Thm, HolError> {
        HolPrim::inst_rule(self, pairs, th).map_err(Into::into)
    }

    fn inst_type_rule(
        &mut self,
        pairs: &[(Self::Type, NameId)],
        th: Self::Thm,
    ) -> Result<Self::Thm, HolError> {
        HolPrim::inst_type_rule(self, pairs, th).map_err(Into::into)
    }

    fn new_axiom(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError> {
        HolPrim::new_axiom(self, tm).map_err(Into::into)
    }

    fn new_basic_definition(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError> {
        HolPrim::new_basic_definition(self, tm).map_err(Into::into)
    }

    fn new_basic_type_definition(
        &mut self,
        tyname: NameId,
        abs_name: NameId,
        rep_name: NameId,
        abs_var_name: NameId,
        rep_var_name: NameId,
        th: Self::Thm,
    ) -> Result<(Self::Thm, Self::Thm), HolError> {
        HolPrim::new_basic_type_definition(
            self,
            tyname,
            abs_name,
            rep_name,
            abs_var_name,
            rep_var_name,
            th,
        )
        .map_err(Into::into)
    }

    fn new_type(&mut self, name: NameId, arity: usize) -> Result<(), HolError> {
        HolPrim::new_type(self, name, arity).map_err(Into::into)
    }

    fn new_constant(&mut self, name: NameId, ty: Self::Type) -> Result<(), HolError> {
        HolPrim::new_constant(self, name, ty).map_err(Into::into)
    }

    fn get_axioms(&self) -> Vec<Self::Thm> {
        HolPrim::get_axioms(self)
    }

    fn mk_type_validated(
        &mut self,
        name: NameId,
        args: Vec<Self::Type>,
    ) -> Result<Self::Type, HolError> {
        HolPrim::mk_type_validated(self, name, args).map_err(Into::into)
    }

    fn mk_const_validated(
        &mut self,
        name: NameId,
        ty: Self::Type,
    ) -> Result<Self::Term, HolError> {
        HolPrim::mk_const_validated(self, name, ty).map_err(Into::into)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol::types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID};

    fn driver() -> HolPrim {
        HolPrim::new(FUN_TYCON_ID, BOOL_TYCON_ID, EQ_CONST_ID)
    }

    #[test]
    fn types_bool_and_fun_roundtrip() {
        let mut d = driver();
        let b = d.bool_type();
        let f = d.fun_type(b, b);
        let (name, args) = d.dest_tyapp(f).unwrap();
        assert_eq!(name, FUN_TYCON_ID);
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], b);
        assert_eq!(args[1], b);
    }

    #[test]
    fn tyvar_roundtrip() {
        let mut d = driver();
        let a = d.mk_tyvar(100);
        assert_eq!(d.dest_tyvar(a), Some(100));
    }

    #[test]
    fn tyvars_lists_vars_once() {
        let mut d = driver();
        let a = d.mk_tyvar(100);
        let b = d.mk_tyvar(101);
        let aa = d.fun_type(a, a);
        let aab = d.fun_type(aa, b);
        let vs = d.tyvars(aab);
        assert_eq!(vs, vec![100, 101]);
    }

    #[test]
    fn term_var_and_eq_roundtrip() {
        let mut d = driver();
        let b = d.bool_type();
        let x = d.mk_var(10, b);
        let y = d.mk_var(11, b);
        let eq = d.mk_eq(x, y);
        let (l, r) = d.dest_eq(eq).unwrap();
        assert_eq!(l, x);
        assert_eq!(r, y);
        let (nx, tx) = d.dest_var(x).unwrap();
        assert_eq!(nx, 10);
        assert_eq!(tx, b);
    }

    #[test]
    fn refl_gives_x_eq_x() {
        let mut d = driver();
        let b = d.bool_type();
        let x = d.mk_var(10, b);
        let th = d.refl(x).unwrap();
        let hyps = d.hyps(th).unwrap();
        assert!(hyps.is_empty());
        let c = d.concl(th).unwrap();
        let (l, r) = d.dest_eq(c).unwrap();
        assert_eq!(l, x);
        assert_eq!(r, x);
    }

    #[test]
    fn beta_conv_on_identity_app() {
        let mut d = driver();
        let b = d.bool_type();
        let x = d.mk_var(10, b);
        let lam = d.mk_abs(x, x).unwrap();
        let y = d.mk_var(11, b);
        let app = d.mk_comb(lam, y);
        let th = d.beta_conv(app).unwrap();
        let c = d.concl(th).unwrap();
        let (l, r) = d.dest_eq(c).unwrap();
        assert_eq!(l, app);
        // After β, the body `x` becomes `y`.
        assert_eq!(r, y);
    }

    #[test]
    fn assume_p_has_p_as_hyp_and_concl() {
        let mut d = driver();
        let b = d.bool_type();
        let p = d.mk_var(10, b);
        let th = d.assume_rule(p).unwrap();
        let hyps = d.hyps(th).unwrap();
        assert_eq!(hyps.len(), 1);
        assert_eq!(hyps[0], p);
        assert_eq!(d.concl(th).unwrap(), p);
    }

    #[test]
    fn vfree_in_finds_free_var() {
        let mut d = driver();
        let b = d.bool_type();
        let x = d.mk_var(10, b);
        let y = d.mk_var(11, b);
        let xy = d.mk_eq(x, y);
        assert!(d.vfree_in(x, xy));
        let z = d.mk_var(99, b);
        assert!(!d.vfree_in(z, xy));
    }

    #[test]
    fn hol_prim_implements_trait_object_safe() {
        // Compile-time check that HolPrim implements the HOL Light
        // kernel trait family with the expected associated types.
        fn assert_trait<K: covalence_hol::traits::HolLightKernel>() {}
        assert_trait::<HolPrim>();
    }

    #[test]
    fn new_axiom_is_not_implemented_yet() {
        let mut d = driver();
        let b = d.bool_type();
        let p = d.mk_var(10, b);
        let r = d.new_axiom(p);
        assert!(matches!(r, Err(HolPrimError::NotImplemented(_))));
    }
}
