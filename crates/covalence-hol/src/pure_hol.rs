//! `PureHol` — HOL Light kernel on top of `covalence-pure` + `HolLightCtx`.
//!
//! Implements [`HolLightKernel`] using Pure's primitives. Each HOL Light
//! rule translates to a short derivation in Pure via the `eq_reflection`
//! axiom: forward direction turns `⊢ Trueprop (Eq a b)` into the Pure
//! meta-equality `⊢ a ≡ b`; backward direction turns Pure `≡` back into
//! HOL `=`.
//!
//! # Encoding (Isabelle/HOL shallow embedding)
//!
//! HOL types are Pure types directly:
//! - HOL `bool` = [`HolLightCtx::bool_type`] (Pure `TyConObs` at the
//!   global `HolLight::Bool` observer)
//! - HOL `α → β` = Pure `Type::fun(α, β)` (object arrow IS Pure's
//!   meta-arrow, following Isabelle/HOL)
//! - HOL `'a` = Pure `Type::tfree("a")`
//! - HOL `tyapp(name, args)` = Pure `Type::tycon(name_str, args)`
//!
//! HOL terms are Pure terms directly:
//! - HOL `Var(name, ty)` = Pure `Term::free(name_str, ty)`
//! - HOL `Const(name, ty)` = Pure `Term::const_(name_str, ty)`
//! - HOL `Comb(f, x)` = Pure `Term::app(f, x)`
//! - HOL `Abs(Var(x, τ), body)` = Pure `Term::abs("x", τ, close(body, "x"))`
//! - HOL `=` etc. are `Obs` leaves at the corresponding `HolLight::*` observer.
//!
//! HOL theorems wrap HOL bool terms in Pure `Trueprop`:
//! - HOL `Γ ⊢ p`  ↔  Pure `{Trueprop q | q ∈ Γ} ⊢ Trueprop p`
//!
//! # Stateful operations
//!
//! Type constructors, constants, and axioms live in `PureHol`'s state.
//! Names use the OpenTheory `NameId` namespace (via `register_name`),
//! kept in sync with `SmolStr` display labels used inside Pure terms.
//!
//! # Currently deferred
//!
//! - `deduct_antisym` — needs an `iff_intro` axiom in `HolLightCtx`
//!   (`(p ⟹ q) ⟹ (q ⟹ p) ⟹ Trueprop (p = q at bool)`).
//! - `new_basic_definition` — needs threading Pure `Def` through
//!   `mk_const` lookup so the defined constant has no defining-hyp.
//! - `new_basic_type_definition` — needs Pure's `new_type_definition`
//!   plus Select for the witness extraction.

use std::collections::{BTreeMap, HashMap, HashSet};

use covalence_pure::{BinderHint, Term, TermKind, Thm, Type, TypeKind, subst};
use smol_str::SmolStr;

use crate::hol_light_obs::HolLightCtx;
use crate::traits::{HolLightKernel, HolLightTerms, HolLightTypes};
use crate::types::{HolError, NameId};

// ============================================================================
// Kernel state
// ============================================================================

/// HOL Light kernel implementation on top of `covalence-pure`.
#[derive(Debug)]
pub struct PureHol {
    ctx: HolLightCtx,
    /// Registered HOL type constructors → arity.
    type_arity: HashMap<NameId, usize>,
    /// Registered HOL constants → most-general HOL type.
    constants: HashMap<NameId, Type>,
    /// Constants introduced via `new_basic_definition` *or* via the
    /// `abs/rep` slots of `new_basic_type_definition`, indexed by
    /// `NameId`. Each value is the Pure `Term::def`/`Term::obs`
    /// term that `mk_const` should return — preserving Arc identity
    /// so the defining equations and user references land on the
    /// same symbol.
    ///
    /// Polymorphic instances need no separate cache: Pure's `Def`
    /// carries `(original_Arc, instance_type)` and
    /// `subst_tfree_in_term` updates `instance_type` without
    /// rebuilding `original`, so any two paths landing at the same
    /// `(NameId, Type)` instance compare structurally equal.
    defined_constants: HashMap<NameId, Term>,
    /// Types introduced via `new_basic_type_definition`, indexed by
    /// `NameId`. Currently monomorphic only (polymorphic typedefs
    /// would need `inst_tfree`-driven instantiation against the
    /// requested args; deferred).
    defined_types: HashMap<NameId, Type>,
    /// Recorded axioms.
    axioms: Vec<Thm>,
    /// `NameId` → display string.
    names: HashMap<NameId, SmolStr>,
    /// Inverse: display string → `NameId`. Built incrementally as
    /// `register_name` is called.
    name_to_id: HashMap<SmolStr, NameId>,
    fun_id: NameId,
    bool_id: NameId,
    eq_id: NameId,
}

impl PureHol {
    pub fn new(fun_id: NameId, bool_id: NameId, eq_id: NameId) -> Self {
        let mut type_arity = HashMap::new();
        type_arity.insert(fun_id, 2);
        type_arity.insert(bool_id, 0);

        let ctx = HolLightCtx::new();

        // `=` has polymorphic type `'a → 'a → bool`.
        let alpha = Type::tfree("a");
        let bool_ty = ctx.bool_type();
        let eq_ty = Type::fun(alpha.clone(), Type::fun(alpha, bool_ty));
        let mut constants = HashMap::new();
        constants.insert(eq_id, eq_ty);

        let mut names = HashMap::new();
        let mut name_to_id = HashMap::new();
        for (id, n) in [(fun_id, "->"), (bool_id, "bool"), (eq_id, "=")] {
            let s = SmolStr::new(n);
            names.insert(id, s.clone());
            name_to_id.insert(s, id);
        }

        PureHol {
            ctx,
            type_arity,
            constants,
            defined_constants: HashMap::new(),
            defined_types: HashMap::new(),
            axioms: Vec::new(),
            names,
            name_to_id,
            fun_id,
            bool_id,
            eq_id,
        }
    }

    fn name_str(&self, id: NameId) -> &str {
        self.names.get(&id).map(|s| s.as_str()).unwrap_or("")
    }

    fn id_for(&self, name: &str) -> Option<NameId> {
        self.name_to_id.get(name).copied()
    }

    /// `true` iff `t` is the HOL `Eq` observer leaf.
    fn is_eq_obs(&self, t: &Term) -> bool {
        match t.kind() {
            TermKind::Obs(o, _) => o.ptr_id() == self.ctx.eq_obs_ptr_id(),
            _ => false,
        }
    }

    /// Decompose `App (App (Eq, lhs), rhs)` → `(lhs, rhs)`.
    fn dest_hol_eq(&self, t: &Term) -> Option<(Term, Term)> {
        let TermKind::App(head, rhs) = t.kind() else {
            return None;
        };
        let TermKind::App(eq_head, lhs) = head.kind() else {
            return None;
        };
        if self.is_eq_obs(eq_head) {
            Some((lhs.clone(), rhs.clone()))
        } else {
            None
        }
    }

    /// Strip `Trueprop` from a Pure prop, returning the wrapped HOL term.
    fn unwrap_trueprop(&self, t: &Term) -> Option<Term> {
        let TermKind::App(head, body) = t.kind() else {
            return None;
        };
        if self.ctx.is_trueprop(head) {
            Some(body.clone())
        } else {
            None
        }
    }

    /// `true` iff `t` matches the conclusion of any user-declared
    /// axiom (via `new_axiom`). Used by `hyps` to filter
    /// axiom-as-hyp residue introduced by Pure's `Thm::assume`.
    fn is_user_axiom_concl(&self, t: &Term) -> bool {
        self.axioms.iter().any(|ax| ax.concl() == t)
    }

    /// Pull `(lhs, rhs)` out of a HOL theorem's `Trueprop (Eq lhs rhs)`
    /// conclusion.
    fn dest_eq_concl(&self, th: &Thm) -> Option<(Term, Term)> {
        let p = self.unwrap_trueprop(th.concl())?;
        self.dest_hol_eq(&p)
    }
}

// ============================================================================
// Error mapping
// ============================================================================

fn pure_err(e: covalence_pure::Error) -> HolError {
    HolError::TypeMismatch(format!("pure: {e:?}"))
}

// ============================================================================
// HolLightTypes
// ============================================================================

impl HolLightTypes for PureHol {
    type Type = Type;

    fn fun_id(&self) -> NameId {
        self.fun_id
    }
    fn bool_id(&self) -> NameId {
        self.bool_id
    }

    fn register_name(&mut self, name_id: NameId, name: &str) {
        let s = SmolStr::new(name);
        self.names.insert(name_id, s.clone());
        self.name_to_id.insert(s, name_id);
    }

    fn mk_tyvar(&mut self, name: NameId) -> Type {
        Type::tfree(self.name_str(name))
    }

    fn mk_tyapp(&mut self, name: NameId, args: Vec<Type>) -> Type {
        if name == self.fun_id && args.len() == 2 {
            let mut it = args.into_iter();
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            return Type::fun(a, b);
        }
        if name == self.bool_id && args.is_empty() {
            return self.ctx.bool_type();
        }
        // Types introduced via `new_basic_type_definition` come back
        // as the stored `TyConObs` (preserving the typedef marker's
        // Arc identity). Currently monomorphic only.
        if let Some(stored) = self.defined_types.get(&name) {
            if args.is_empty() {
                return stored.clone();
            }
            // Polymorphic case deferred: instantiating the stored τ
            // requires inst_tfree by each tvar position in args.
        }
        Type::tycon(self.name_str(name), args)
    }

    fn bool_type(&mut self) -> Type {
        self.ctx.bool_type()
    }

    fn fun_type(&mut self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }

    fn dest_tyvar(&self, ty: Type) -> Option<NameId> {
        match ty.kind() {
            TypeKind::TFree(n) => self.id_for(n.as_str()),
            _ => None,
        }
    }

    fn dest_tyapp(&self, ty: Type) -> Option<(NameId, Vec<Type>)> {
        // HOL bool is a TyConObs at the global Bool observer; check
        // by structural equality with the cached bool_type.
        if ty == self.ctx.bool_type() {
            return Some((self.bool_id, vec![]));
        }
        match ty.kind() {
            TypeKind::Fun(a, b) => Some((self.fun_id, vec![a.clone(), b.clone()])),
            TypeKind::Tycon(name, args) => self.id_for(name.as_str()).map(|id| (id, args.clone())),
            // Typedef-introduced types arrive as `TyConObs` at a
            // fresh TypeDef marker; the hint string is the original
            // type's name, which we can map back via `id_for`.
            TypeKind::TyConObs(_, hint, args) => {
                self.id_for(hint.as_str()).map(|id| (id, args.clone()))
            }
            _ => None,
        }
    }

    fn type_eq(&self, a: Type, b: Type) -> bool {
        a == b
    }

    fn tyvars(&self, ty: Type) -> Vec<NameId> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for n in ty.free_tvars() {
            if seen.insert(n.clone()) {
                if let Some(id) = self.id_for(n.as_str()) {
                    out.push(id);
                }
            }
        }
        out
    }

    fn type_inst(&mut self, ty: Type, pairs: &[(Type, NameId)]) -> Type {
        let mut result = ty;
        for (new_ty, old_name) in pairs {
            let name = self.name_str(*old_name).to_owned();
            result = subst::subst_tfree_in_type(&result, &name, new_ty);
        }
        result
    }
}

// ============================================================================
// HolLightTerms
// ============================================================================

impl HolLightTerms for PureHol {
    type Term = Term;

    fn eq_id(&self) -> NameId {
        self.eq_id
    }

    fn mk_var(&mut self, name: NameId, ty: Type) -> Term {
        Term::free(self.name_str(name), ty)
    }

    fn mk_const(&mut self, name: NameId, ty: Type) -> Term {
        // HOL `=` is represented as the `Eq` Obs leaf at the
        // requested type. Articles call `constTerm "="` to build
        // equation skeletons; those must compare structurally equal
        // to the `Obs(EQ)` head our `refl` / `trans` / etc. produce.
        // The expected type for `=` is `α → α → bool`; extract `α`
        // from the requested type's first domain.
        if name == self.eq_id {
            if let TypeKind::Fun(alpha, _) = ty.kind() {
                return self.ctx.eq_at(alpha.clone());
            }
        }
        // Constants introduced via `new_basic_definition` come back
        // as the stored `Term::def(d)` (preserving Arc identity for
        // the defining equation). HOL Light constants are
        // polymorphic — the definition's type carries free TFrees,
        // and the article requests instances. Match the stored type
        // against the requested type to find the tvar substitution,
        // then apply `subst_tfree_in_term` to get the instance.
        if let Some(def_term) = self.defined_constants.get(&name).cloned() {
            let def_ty = def_term
                .type_of()
                .expect("defined-constant body is well-typed by construction");
            if def_ty == ty {
                return def_term;
            }
            // Pure's `Def` representation `(original_Arc,
            // instance_type)` makes `subst_tfree_in_term`
            // identity-preserving: the result compares equal to any
            // other mk_const at this same instance type, so no
            // explicit cache is needed here.
            let mut sub: BTreeMap<SmolStr, Type> = BTreeMap::new();
            if subst::match_types(&def_ty, &ty, &mut sub).is_ok() {
                let mut result = def_term;
                for (tv, replacement) in sub {
                    result = subst::subst_tfree_in_term(&result, tv.as_str(), &replacement);
                }
                return result;
            }
            // Match failed: fall through to a plain `Const` so the
            // downstream type check fires a clear error instead of
            // returning a silently mis-typed Def.
        }
        Term::const_(self.name_str(name), ty)
    }

    fn mk_comb(&mut self, f: Term, x: Term) -> Term {
        Term::app(f, x)
    }

    fn mk_abs(&mut self, var: Term, body: Term) -> Term {
        // `var` MUST be `Free(name, ty)` per HOL Light's invariant
        // (binder slot is always a typed named variable). Pure
        // requires the binder name + type up-front to close the
        // body via `subst::close`. If the caller passes anything
        // else, the resulting term is logically meaningless — panic
        // (matching HOL Light's `mk_abs`, which errors). Silent
        // pass-through here would hide an upstream bug.
        let (name, ty) = match var.kind() {
            TermKind::Free(n, t) => (n.clone(), t.clone()),
            _ => panic!("mk_abs: binder var must be a Free term, got {var:?}"),
        };
        let closed = subst::close(&body, name.as_str());
        Term::abs(BinderHint::new(name.as_str()), ty, closed)
    }

    fn mk_eq(&mut self, lhs: Term, rhs: Term) -> Term {
        self.ctx.mk_eq(lhs, rhs).expect("mk_eq: types must match")
    }

    fn dest_var(&self, tm: Term) -> Option<(NameId, Type)> {
        match tm.kind() {
            TermKind::Free(n, ty) => self.id_for(n.as_str()).map(|id| (id, ty.clone())),
            _ => None,
        }
    }

    fn dest_const(&self, tm: Term) -> Option<(NameId, Type)> {
        match tm.kind() {
            TermKind::Const(n, ty) => self.id_for(n.as_str()).map(|id| (id, ty.clone())),
            // Defined constants: walk back from the Def's name hint
            // to its NameId. We registered at most one Def per name,
            // so this is unambiguous.
            TermKind::Def(d) => {
                let id = self.id_for(d.name().as_str())?;
                let ty = self.constants.get(&id).cloned()?;
                Some((id, ty))
            }
            _ => None,
        }
    }

    fn dest_comb(&self, tm: Term) -> Option<(Term, Term)> {
        match tm.kind() {
            TermKind::App(f, x) => Some((f.clone(), x.clone())),
            _ => None,
        }
    }

    fn dest_abs(&mut self, tm: Term) -> Option<(Term, Term)> {
        match tm.kind() {
            TermKind::Abs(hint, ty, body) => {
                // HOL Light's `dest_abs` opens with a name that's
                // FRESH in the body (avoiding capture). Pure's
                // locally-nameless representation means the body's
                // `Bound(0)` is the bound var and named `Free`s
                // inside refer to outer-scope captures. If the
                // hint collides with such a name, generate a
                // suffix-bumped fresh name.
                let name = fresh_in_term(hint.as_str(), body);
                let var = Term::free(name.as_str(), ty.clone());
                let opened = subst::open(body, &var);
                Some((var, opened))
            }
            _ => None,
        }
    }

    fn dest_eq(&self, tm: Term) -> Option<(Term, Term)> {
        self.dest_hol_eq(&tm)
    }

    fn type_of(&mut self, tm: Term) -> Type {
        tm.type_of().unwrap_or_else(|e| {
            panic!("type_of: ill-typed HOL term: {e:?}\n  term: {tm:?}")
        })
    }

    fn term_eq(&self, a: Term, b: Term) -> bool {
        a == b
    }

    // Pure terms ARE α-equivalent under structural equality
    // (locally-nameless representation).
    fn aconv(&self, a: Term, b: Term) -> bool {
        a == b
    }

    fn frees(&mut self, tm: Term) -> Vec<Term> {
        let mut seen = HashSet::new();
        let mut out = Vec::new();
        collect_frees(&tm, &mut seen, &mut out);
        out
    }

    fn vfree_in(&self, var: Term, tm: Term) -> bool {
        let TermKind::Free(name, _) = var.kind() else {
            return false;
        };
        subst::has_free_var(&tm, name.as_str())
    }

    fn vsubst(&mut self, tm: Term, pairs: &[(Term, Term)]) -> Result<Term, HolError> {
        let mut result = tm;
        for (new_term, old_var) in pairs {
            let TermKind::Free(name, _) = old_var.kind() else {
                return Err(HolError::NotAVariable);
            };
            result = subst::subst_free(&result, name.as_str(), new_term);
        }
        Ok(result)
    }

    fn inst_term(&mut self, tm: Term, pairs: &[(Type, NameId)]) -> Term {
        let mut result = tm;
        for (new_ty, old_name) in pairs {
            let name = self.name_str(*old_name).to_owned();
            result = subst::subst_tfree_in_term(&result, &name, new_ty);
        }
        result
    }
}

/// Generate a name based on `hint` that is NOT a free variable of
/// `t`. If `hint` itself is unused, returns it unchanged; otherwise
/// appends an integer suffix (`x`, `x0`, `x1`, …) until a fresh
/// name is found. Matches HOL Light's `variant`/`mk_primed_var`
/// semantics, used by `dest_abs` to avoid name capture when opening
/// a binder under a body that happens to contain a free with the
/// same name as the binder hint.
fn fresh_in_term(hint: &str, t: &Term) -> SmolStr {
    if !subst::has_free_var(t, hint) {
        return SmolStr::new(hint);
    }
    let mut i: u32 = 0;
    loop {
        let candidate = format!("{hint}{i}");
        if !subst::has_free_var(t, &candidate) {
            return SmolStr::new(&candidate);
        }
        i += 1;
    }
}

/// Walk `t` collecting every free type variable name appearing in
/// any type annotation (Free / Const / Abs / All / Obs `ty` fields,
/// plus Def body types).
fn collect_term_tvars(t: &Term, out: &mut HashSet<SmolStr>) {
    match t.kind() {
        TermKind::Free(_, ty) | TermKind::Const(_, ty) | TermKind::Obs(_, ty) => {
            for n in ty.free_tvars() {
                out.insert(n);
            }
        }
        TermKind::Abs(_, ty, body) | TermKind::All(_, ty, body) => {
            for n in ty.free_tvars() {
                out.insert(n);
            }
            collect_term_tvars(body, out);
        }
        TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
            collect_term_tvars(a, out);
            collect_term_tvars(b, out);
        }
        TermKind::Bound(_)
        | TermKind::Blob(_)
        | TermKind::NatLit(_)
        | TermKind::IntLit(_)
        | TermKind::Prim(_) => {}
        TermKind::Def(d) => collect_term_tvars(&d.body(), out),
    }
}

/// Walk `t` collecting unique `Free` leaves into `out`.
fn collect_frees(t: &Term, seen: &mut HashSet<(SmolStr, Type)>, out: &mut Vec<Term>) {
    match t.kind() {
        TermKind::Free(n, ty) => {
            let key = (n.clone(), ty.clone());
            if seen.insert(key) {
                out.push(t.clone());
            }
        }
        TermKind::Bound(_)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::NatLit(_)
        | TermKind::IntLit(_)
        | TermKind::Prim(_)
        | TermKind::Obs(..)
        | TermKind::Def(_) => {}
        TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
            collect_frees(a, seen, out);
            collect_frees(b, seen, out);
        }
        TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => collect_frees(body, seen, out),
    }
}

// ============================================================================
// HolLightKernel — the 10 primitive rules + definitions + state
// ============================================================================

impl HolLightKernel for PureHol {
    type Thm = Thm;

    fn hyps(&self, th: Thm) -> Vec<Term> {
        // Filter out:
        //   1. Non-Trueprop-wrapped hyps. These are kernel-introduced
        //      axioms like `eq_reflection` (shape `⋀x y. … ≡ …`) and
        //      `iff_intro` (shape `⋀P Q. … ⟹ … ⟹ Trueprop (…)`);
        //      their outermost is `⋀` or `⟹`, not Trueprop. They're
        //      part of the theory, not user assumptions.
        //   2. Hyps matching a user-declared axiom's concl. HOL Light's
        //      `new_axiom` gives `⊢ φ` with no hyps; Pure's TCB requires
        //      `Thm::assume(Trueprop φ)` which adds the assumption as a
        //      hyp. PureHol tracks the axiom in `self.axioms`; we report
        //      it as not-a-hyp to match HOL Light's convention.
        th.hyps()
            .iter()
            .filter(|h| !self.is_user_axiom_concl(h))
            .filter_map(|h| self.unwrap_trueprop(h))
            .collect()
    }

    fn concl(&self, th: Thm) -> Term {
        self.unwrap_trueprop(th.concl())
            .expect("concl: theorem conclusion not Trueprop-wrapped")
    }

    /// REFL: `⊢ Trueprop (t = t)` derived via eq_reflection backward:
    /// `⊢ t ≡ t` (Pure refl) → `⊢ Trueprop (Eq t t)`.
    fn refl(&mut self, tm: Term) -> Result<Thm, HolError> {
        let ty = tm.type_of().map_err(pure_err)?;
        let pure_refl = Thm::refl(tm.clone()).map_err(pure_err)?;
        self.ctx
            .eq_reflection_axiom()
            .inst_tfree("a", ty)
            .map_err(pure_err)?
            .all_elim(tm.clone())
            .map_err(pure_err)?
            .all_elim(tm)
            .map_err(pure_err)?
            .sym()
            .map_err(pure_err)?
            .eq_mp(pure_refl)
            .map_err(pure_err)
    }

    /// TRANS: forward each `Trueprop (a = b)` to `a ≡ b`, Pure-trans,
    /// then backward to `Trueprop (a = c)`.
    fn trans(&mut self, th1: Thm, th2: Thm) -> Result<Thm, HolError> {
        let (s, t1) = self.dest_eq_concl(&th1).ok_or(HolError::NotAnEquation)?;
        let (t2, u) = self.dest_eq_concl(&th2).ok_or(HolError::NotAnEquation)?;
        let ty = s.type_of().map_err(pure_err)?;

        let axiom = self
            .ctx
            .eq_reflection_axiom()
            .inst_tfree("a", ty)
            .map_err(pure_err)?;

        // forward th1 → Pure ≡
        let pure_st = axiom
            .clone()
            .all_elim(s.clone())
            .map_err(pure_err)?
            .all_elim(t1)
            .map_err(pure_err)?
            .eq_mp(th1)
            .map_err(pure_err)?;
        // forward th2 → Pure ≡
        let pure_tu = axiom
            .clone()
            .all_elim(t2)
            .map_err(pure_err)?
            .all_elim(u.clone())
            .map_err(pure_err)?
            .eq_mp(th2)
            .map_err(pure_err)?;
        let pure_su = pure_st.trans(pure_tu).map_err(pure_err)?;

        // backward → HOL =
        axiom
            .all_elim(s)
            .map_err(pure_err)?
            .all_elim(u)
            .map_err(pure_err)?
            .sym()
            .map_err(pure_err)?
            .eq_mp(pure_su)
            .map_err(pure_err)
    }

    /// MK_COMB: forward each input, Pure cong_app, backward.
    fn mk_comb_rule(&mut self, th1: Thm, th2: Thm) -> Result<Thm, HolError> {
        let (f, g) = self.dest_eq_concl(&th1).ok_or(HolError::NotAnEquation)?;
        let (x, y) = self.dest_eq_concl(&th2).ok_or(HolError::NotAnEquation)?;
        let f_ty = f.type_of().map_err(pure_err)?;
        let x_ty = x.type_of().map_err(pure_err)?;
        // f : α → β; pull β out for the result eq_reflection step
        let TypeKind::Fun(_, beta) = f_ty.kind() else {
            return Err(HolError::TypeMismatch(format!("not a fun type: {f_ty:?}")));
        };
        let beta = beta.clone();

        let ax_f = self
            .ctx
            .eq_reflection_axiom()
            .inst_tfree("a", f_ty)
            .map_err(pure_err)?;
        let ax_x = self
            .ctx
            .eq_reflection_axiom()
            .inst_tfree("a", x_ty)
            .map_err(pure_err)?;

        let pure_fg = ax_f
            .all_elim(f.clone())
            .map_err(pure_err)?
            .all_elim(g.clone())
            .map_err(pure_err)?
            .eq_mp(th1)
            .map_err(pure_err)?;
        let pure_xy = ax_x
            .all_elim(x.clone())
            .map_err(pure_err)?
            .all_elim(y.clone())
            .map_err(pure_err)?
            .eq_mp(th2)
            .map_err(pure_err)?;
        let pure_fx_gy = pure_fg.cong_app(pure_xy).map_err(pure_err)?;

        // backward at β
        let fx = Term::app(f, x);
        let gy = Term::app(g, y);
        self.ctx
            .eq_reflection_axiom()
            .inst_tfree("a", beta)
            .map_err(pure_err)?
            .all_elim(fx)
            .map_err(pure_err)?
            .all_elim(gy)
            .map_err(pure_err)?
            .sym()
            .map_err(pure_err)?
            .eq_mp(pure_fx_gy)
            .map_err(pure_err)
    }

    /// ABS: forward, Pure cong_abs, backward at `τ → α`.
    fn abs_rule(&mut self, var: Term, th: Thm) -> Result<Thm, HolError> {
        let (name, var_ty) = match var.kind() {
            TermKind::Free(n, t) => (n.clone(), t.clone()),
            _ => return Err(HolError::NotAVariable),
        };
        let (s, t) = self.dest_eq_concl(&th).ok_or(HolError::NotAnEquation)?;
        let alpha = s.type_of().map_err(pure_err)?;

        let pure_st = self
            .ctx
            .eq_reflection_axiom()
            .inst_tfree("a", alpha.clone())
            .map_err(pure_err)?
            .all_elim(s.clone())
            .map_err(pure_err)?
            .all_elim(t.clone())
            .map_err(pure_err)?
            .eq_mp(th)
            .map_err(pure_err)?;
        let pure_abs_eq = pure_st
            .cong_abs(name.as_str(), var_ty.clone())
            .map_err(pure_err)?;

        // Result type is (var_ty → alpha)
        let result_ty = Type::fun(var_ty.clone(), alpha);
        let abs_s = Term::abs(
            BinderHint::new(name.as_str()),
            var_ty.clone(),
            subst::close(&s, name.as_str()),
        );
        let abs_t = Term::abs(
            BinderHint::new(name.as_str()),
            var_ty,
            subst::close(&t, name.as_str()),
        );

        self.ctx
            .eq_reflection_axiom()
            .inst_tfree("a", result_ty)
            .map_err(pure_err)?
            .all_elim(abs_s)
            .map_err(pure_err)?
            .all_elim(abs_t)
            .map_err(pure_err)?
            .sym()
            .map_err(pure_err)?
            .eq_mp(pure_abs_eq)
            .map_err(pure_err)
    }

    /// BETA: Pure beta_conv + backward eq_reflection.
    fn beta_conv(&mut self, tm: Term) -> Result<Thm, HolError> {
        let pure_beta = Thm::beta_conv(tm.clone()).map_err(pure_err)?;
        // pure_beta concl: (λx. body) arg ≡ body[x:=arg]
        // type-of either side is the codomain — use beta's LHS via tm itself.
        let result_ty = tm.type_of().map_err(pure_err)?;
        // Reconstruct rhs from the concl of pure_beta for the eq_reflection step.
        let TermKind::Eq(lhs, rhs) = pure_beta.concl().kind() else {
            return Err(HolError::TypeMismatch("beta_conv produced non-Eq".into()));
        };
        let (lhs, rhs) = (lhs.clone(), rhs.clone());
        self.ctx
            .eq_reflection_axiom()
            .inst_tfree("a", result_ty)
            .map_err(pure_err)?
            .all_elim(lhs)
            .map_err(pure_err)?
            .all_elim(rhs)
            .map_err(pure_err)?
            .sym()
            .map_err(pure_err)?
            .eq_mp(pure_beta)
            .map_err(pure_err)
    }

    /// ASSUME: Pure assume on `Trueprop(tm)`.
    fn assume_rule(&mut self, tm: Term) -> Result<Thm, HolError> {
        let wrapped = self.ctx.mk_trueprop(tm).map_err(pure_err)?;
        Thm::assume(wrapped).map_err(pure_err)
    }

    /// EQ_MP: forward eq_reflection on the equation, lift to Trueprop
    /// via cong_app on refl Trueprop, then Pure eq_mp.
    fn eq_mp(&mut self, th1: Thm, th2: Thm) -> Result<Thm, HolError> {
        let (p, _q) = self.dest_eq_concl(&th1).ok_or(HolError::NotAnEquation)?;
        let bool_ty = self.ctx.bool_type();

        let pure_pq = self
            .ctx
            .eq_reflection_axiom()
            .inst_tfree("a", bool_ty)
            .map_err(pure_err)?
            .all_elim(p)
            .map_err(pure_err)?
            .all_elim(_q)
            .map_err(pure_err)?
            .eq_mp(th1)
            .map_err(pure_err)?;
        // Lift to Trueprop-eq via cong_app(refl Trueprop).
        let tp_refl = Thm::refl(self.ctx.trueprop()).map_err(pure_err)?;
        let trueprop_pq = tp_refl.cong_app(pure_pq).map_err(pure_err)?;
        trueprop_pq.eq_mp(th2).map_err(pure_err)
    }

    /// DEDUCT_ANTISYM_RULE:
    ///
    /// ```text
    /// A1 ⊢ Trueprop p   A2 ⊢ Trueprop q
    /// ─────────────────────────────────
    /// (A1 - {Trueprop q}) ∪ (A2 - {Trueprop p}) ⊢ Trueprop (Eq[bool] p q)
    /// ```
    ///
    /// Discharge each conclusion as a hypothesis (`imp_intro`) and
    /// feed both directions into `HolLightCtx::iff_intro_axiom`.
    fn deduct_antisym(&mut self, th1: Thm, th2: Thm) -> Result<Thm, HolError> {
        let p = self
            .unwrap_trueprop(th1.concl())
            .ok_or(HolError::NotBoolean)?;
        let q = self
            .unwrap_trueprop(th2.concl())
            .ok_or(HolError::NotBoolean)?;

        // Build Trueprop p, Trueprop q for use as imp_intro antecedents
        // (these will appear in the iff_intro axiom's instantiated form).
        let tp_p = self.ctx.mk_trueprop(p.clone()).map_err(pure_err)?;
        let tp_q = self.ctx.mk_trueprop(q.clone()).map_err(pure_err)?;

        // th1_disc:  (A1 - {tp_q}) ⊢ tp_q ⟹ tp_p
        let th1_disc = th1.imp_intro(&tp_q).map_err(pure_err)?;
        // th2_disc:  (A2 - {tp_p}) ⊢ tp_p ⟹ tp_q
        let th2_disc = th2.imp_intro(&tp_p).map_err(pure_err)?;

        // iff_intro instantiated:
        //   ⊢ (tp_p ⟹ tp_q) ⟹ (tp_q ⟹ tp_p) ⟹ Trueprop (Eq[bool] p q)
        let axiom = self
            .ctx
            .iff_intro_axiom()
            .all_elim(p)
            .map_err(pure_err)?
            .all_elim(q)
            .map_err(pure_err)?;
        // Discharge antecedents in order: th2_disc has type (tp_p ⟹ tp_q),
        // th1_disc has type (tp_q ⟹ tp_p).
        axiom
            .imp_elim(th2_disc)
            .map_err(pure_err)?
            .imp_elim(th1_disc)
            .map_err(pure_err)
    }

    /// INST: parallel term-variable instantiation.
    ///
    /// HOL `INST [t_i / x_i]` works on theorems with `x_i` free in
    /// hyps; Pure's `all_intro` forbids that. Standard Isabelle/HOL
    /// pattern: discharge every hyp mentioning any `x_i` first
    /// (`imp_intro` chain), quantify (`all_intro` per var),
    /// instantiate (`all_elim` per witness in reverse pair order so
    /// the chain becomes the parallel-substituted form), then
    /// re-introduce each discharged hyp via `imp_elim` of an
    /// `assume(antecedent)` where `antecedent` is read directly off
    /// the chain — avoiding any need to recompute parallel
    /// substitution by hand and side-stepping the cyclic-pairs
    /// pitfall (`t_i` mentioning `x_j`, which Pure's `all_intro/elim`
    /// handles parallel-correctly by construction).
    fn inst_rule(&mut self, pairs: &[(Term, Term)], th: Thm) -> Result<Thm, HolError> {
        let mut info: Vec<(SmolStr, Type)> = Vec::with_capacity(pairs.len());
        for (_new, old) in pairs {
            let TermKind::Free(n, ty) = old.kind() else {
                return Err(HolError::NotAVariable);
            };
            info.push((n.clone(), ty.clone()));
        }

        // Hyps mentioning any substituted var must be discharged
        // before `all_intro` can quantify (Pure forbids the var
        // appearing in hyps under the quantifier).
        let mentions_any = |t: &Term| info.iter().any(|(n, _)| subst::has_free_var(t, n.as_str()));
        let hyps_to_discharge: Vec<Term> = th
            .hyps()
            .iter()
            .filter(|h| mentions_any(h))
            .cloned()
            .collect();

        let mut result = th;
        for h in &hyps_to_discharge {
            result = result.imp_intro(h).map_err(pure_err)?;
        }
        // Quantify each var in order — last `all_intro` becomes the
        // outermost binder. Then `all_elim` consumes outermost
        // first, so we walk pairs in reverse to land each new_term
        // on the right binder.
        for (n, ty) in &info {
            result = result.all_intro(n.as_str(), ty.clone()).map_err(pure_err)?;
        }
        for (new_term, _) in pairs.iter().rev() {
            result = result.all_elim(new_term.clone()).map_err(pure_err)?;
        }

        // Re-introduce each previously discharged hyp by peeling
        // antecedents off the result chain. Pure's
        // `all_intro`/`all_elim` already produced
        // `⊢ h_{n-1}[σ] ⟹ … ⟹ h_0[σ] ⟹ q[σ]` with σ as parallel
        // substitution. We read each outermost antecedent off
        // `result.concl()`, `assume` it, and `imp_elim` — no manual
        // substitution required.
        for _ in 0..hyps_to_discharge.len() {
            let antecedent = match result.concl().kind() {
                TermKind::Imp(ant, _) => ant.clone(),
                _ => {
                    return Err(HolError::Unsupported(
                        "inst_rule: expected Imp antecedent in result chain".into(),
                    ));
                }
            };
            let assumed = Thm::assume(antecedent).map_err(pure_err)?;
            result = result.imp_elim(assumed).map_err(pure_err)?;
        }
        Ok(result)
    }

    /// INST_TYPE: apply Pure `inst_tfree` for each pair.
    fn inst_type_rule(&mut self, pairs: &[(Type, NameId)], th: Thm) -> Result<Thm, HolError> {
        let mut result = th;
        for (new_ty, old_name) in pairs {
            let name = self.name_str(*old_name).to_owned();
            result = result.inst_tfree(&name, new_ty.clone()).map_err(pure_err)?;
        }
        Ok(result)
    }

    /// NEW_AXIOM: assume `Trueprop(tm)`. Records the resulting
    /// theorem in `self.axioms`. Like HOL Light's axioms, the axiom
    /// is justified by the user's act of declaring it; in our Pure
    /// encoding it shows up as a hypothesis of every derived theorem.
    fn new_axiom(&mut self, tm: Term) -> Result<Thm, HolError> {
        let wrapped = self.ctx.mk_trueprop(tm).map_err(pure_err)?;
        let thm = Thm::assume(wrapped).map_err(pure_err)?;
        self.axioms.push(thm.clone());
        Ok(thm)
    }

    /// NEW_BASIC_DEFINITION: `tm` is `Eq c body` where `c = Var(name, ty)`
    /// is a fresh variable. Register `c` as a defined constant whose
    /// future `mk_const` invocations return a Pure `Term::def(d)` for
    /// a freshly allocated `Def`. Returns `⊢ Trueprop (Eq[ty] Def body)`
    /// with EMPTY hyps (delivered by Pure's `Thm::define`).
    ///
    /// **Known limitation:** Pure's `Def` equality is Arc-pointer
    /// based, and `subst_tfree_in_term` (which `inst_type_rule` calls
    /// transitively) reallocates `Def`s per pass. The per-instance
    /// cache here makes repeated `mk_const(name, T)` lookups return
    /// the same Arc, but any path that goes through Pure's
    /// `inst_tfree` on a Thm containing a polymorphic Def will
    /// produce a Def with a fresh Arc — breaking structural equality
    /// against the cached instance. The cleanest fix is a kernel-
    /// level "named constant" definition in covalence-pure; tracked
    /// for a separate Pure change.
    ///
    /// Soundness guard: every free type variable in the body must
    /// also appear in `c`'s type.
    fn new_basic_definition(&mut self, tm: Term) -> Result<Thm, HolError> {
        let (c, body) = self
            .dest_hol_eq(&tm)
            .ok_or_else(|| HolError::BadDefinition("not an equation".into()))?;
        let (name_id, ty) = match c.kind() {
            TermKind::Free(n, t) => {
                let id = self.id_for(n.as_str()).ok_or_else(|| {
                    HolError::BadDefinition(format!("variable name not registered: {n}"))
                })?;
                (id, t.clone())
            }
            _ => {
                return Err(HolError::BadDefinition(
                    "LHS of definition must be a variable".into(),
                ));
            }
        };
        if self.constants.contains_key(&name_id) {
            return Err(HolError::ConstantAlreadyDefined(
                self.name_str(name_id).into(),
            ));
        }

        let ty_tvars: HashSet<SmolStr> = ty.free_tvars().into_iter().collect();
        let mut body_tvars = HashSet::new();
        collect_term_tvars(&body, &mut body_tvars);
        if !body_tvars.is_subset(&ty_tvars) {
            return Err(HolError::FreeTypeVarsInDefinition);
        }

        // Pure define: `⊢ Term::def(d) ≡ body` (empty hyps; d fresh).
        let pure_def_thm =
            Thm::define(self.name_str(name_id), body.clone()).map_err(pure_err)?;
        let TermKind::Eq(lhs, _) = pure_def_thm.concl().kind() else {
            unreachable!("Thm::define returns Eq");
        };
        let c_term = lhs.clone();

        self.defined_constants.insert(name_id, c_term.clone());
        self.constants.insert(name_id, ty.clone());

        // Backward eq_reflection: Pure ≡ → HOL Trueprop Eq.
        self.ctx
            .eq_reflection_axiom()
            .inst_tfree("a", ty)
            .map_err(pure_err)?
            .all_elim(c_term)
            .map_err(pure_err)?
            .all_elim(body)
            .map_err(pure_err)?
            .sym()
            .map_err(pure_err)?
            .eq_mp(pure_def_thm)
            .map_err(pure_err)
    }

    /// NEW_BASIC_TYPE_DEFINITION:
    ///
    /// OpenTheory's `defineTypeOp` passes a witness theorem
    /// `⊢ Trueprop (P t)` directly (no existential — t is already
    /// the chosen inhabitant), so this rule does NOT need Select.
    /// We wrap `P` into a Pure predicate via β (so its codomain is
    /// `prop` instead of HOL `bool`), call Pure's
    /// `Thm::new_type_definition`, then translate the three Pure
    /// outputs back to the two HOL Light theorems the OpenTheory
    /// interpreter expects:
    ///
    /// - `thm1: ⊢ Trueprop (Eq[τ] (abs (rep a)) a)` with `a : τ` free
    /// - `thm2: ⊢ Trueprop (Eq[bool] (P r) (Eq[α] (rep (abs r)) r))`
    ///   with `r : α` free
    ///
    /// The OpenTheory article spec then wraps these into lambdas at
    /// the interpreter layer (see the `opentheory-define-type-op`
    /// memory note).
    ///
    /// Currently monomorphic only: typedefs whose carrier type has
    /// free type variables would need polymorphic `mk_tyapp`
    /// support (instantiate stored `τ` via `inst_tfree` per arg).
    fn new_basic_type_definition(
        &mut self,
        tyname: NameId,
        abs_name: NameId,
        rep_name: NameId,
        abs_var_name: NameId,
        rep_var_name: NameId,
        th: Thm,
    ) -> Result<(Thm, Thm), HolError> {
        // 1. Decompose witness: ⊢ Trueprop (App P t).
        let inner = self
            .unwrap_trueprop(th.concl())
            .ok_or_else(|| HolError::BadTypeDefinition("witness concl not Trueprop".into()))?;
        let TermKind::App(p_hol, t) = inner.kind() else {
            return Err(HolError::BadTypeDefinition(
                "witness inner not App(P, t)".into(),
            ));
        };
        let (p_hol, t) = (p_hol.clone(), t.clone());
        let alpha = t.type_of().map_err(pure_err)?;

        // Reject polymorphic carriers for now (would need polymorphic mk_tyapp).
        if !alpha.free_tvars().is_empty() {
            return Err(HolError::Unsupported(
                "new_basic_type_definition: polymorphic typedefs not yet supported".into(),
            ));
        }

        // 2. Freshness checks.
        if self.type_arity.contains_key(&tyname) || self.defined_types.contains_key(&tyname) {
            return Err(HolError::TypeAlreadyDefined(
                self.name_str(tyname).into(),
            ));
        }
        if self.constants.contains_key(&abs_name) {
            return Err(HolError::ConstantAlreadyDefined(
                self.name_str(abs_name).into(),
            ));
        }
        if self.constants.contains_key(&rep_name) {
            return Err(HolError::ConstantAlreadyDefined(
                self.name_str(rep_name).into(),
            ));
        }

        // 3. Build Pure predicate `P_pure = λx:α. Trueprop (P x)`.
        let trueprop = self.ctx.trueprop();
        let p_pure_body = Term::app(
            trueprop.clone(),
            Term::app(p_hol.clone(), Term::bound(0)),
        );
        let p_pure = Term::abs(BinderHint::new("x"), alpha.clone(), p_pure_body);
        let p_pure_at_t = Term::app(p_pure.clone(), t.clone());

        // 4. Bridge witness: ⊢ Trueprop (P t) → ⊢ App(P_pure, t)
        //    via β-conv on `P_pure t ≡ Trueprop (P t)`.
        let beta_at_t = Thm::beta_conv(p_pure_at_t.clone()).map_err(pure_err)?;
        let pure_witness = beta_at_t.sym().map_err(pure_err)?.eq_mp(th).map_err(pure_err)?;

        // 5. Pure new_type_definition.
        let typedef = Thm::new_type_definition(
            self.name_str(tyname),
            self.name_str(abs_name),
            self.name_str(rep_name),
            pure_witness,
        )
        .map_err(pure_err)?;
        let tau = typedef.tau.clone();
        let abs_term = typedef.abs.clone();
        let rep_term = typedef.rep.clone();

        // 6. Register state. abs : α → τ, rep : τ → α.
        self.defined_types.insert(tyname, tau.clone());
        self.type_arity.insert(tyname, 0);
        self.defined_constants.insert(abs_name, abs_term.clone());
        self.defined_constants.insert(rep_name, rep_term.clone());
        self.constants
            .insert(abs_name, Type::fun(alpha.clone(), tau.clone()));
        self.constants
            .insert(rep_name, Type::fun(tau.clone(), alpha.clone()));

        // 7. Translate Pure outputs to HOL form.
        //    thm1: ⊢ Trueprop (Eq[τ] (abs (rep a)) a) with `a : τ` free.
        let abs_var_str = self.name_str(abs_var_name).to_owned();
        let a_free = Term::free(&abs_var_str, tau.clone());
        let pure_abs_rep_at_a = typedef
            .abs_rep
            .all_elim(a_free.clone())
            .map_err(pure_err)?;
        let abs_rep_lhs = Term::app(
            abs_term.clone(),
            Term::app(rep_term.clone(), a_free.clone()),
        );
        let thm1 = self
            .ctx
            .eq_reflection_axiom()
            .inst_tfree("a", tau.clone())
            .map_err(pure_err)?
            .all_elim(abs_rep_lhs)
            .map_err(pure_err)?
            .all_elim(a_free)
            .map_err(pure_err)?
            .sym()
            .map_err(pure_err)?
            .eq_mp(pure_abs_rep_at_a)
            .map_err(pure_err)?;

        // 8. thm2 via iff_intro applied to both directions.
        //    Build the HOL terms we'll plug into iff_intro:
        //      p_r        = HOL.eq[bool] left side: (P r) : bool
        //      eq_repr    = HOL.eq[α] (rep(abs r)) r  : bool
        //    Both are HOL bool-typed.
        let rep_var_str = self.name_str(rep_var_name).to_owned();
        let r_free = Term::free(&rep_var_str, alpha.clone());
        let p_at_r = Term::app(p_hol.clone(), r_free.clone()); // P r : bool
        let rep_abs_r = Term::app(
            rep_term.clone(),
            Term::app(abs_term.clone(), r_free.clone()),
        );
        let hol_eq_at_alpha = self.ctx.eq_at(alpha.clone());
        let eq_rep_r = Term::app(
            Term::app(hol_eq_at_alpha.clone(), rep_abs_r.clone()),
            r_free.clone(),
        );
        let tp_p_at_r = Term::app(trueprop.clone(), p_at_r.clone());
        let tp_eq_rep_r = Term::app(trueprop.clone(), eq_rep_r.clone());

        // β-conv: ⊢ App(P_pure, r) ≡ Trueprop (P r).
        let p_pure_at_r = Term::app(p_pure.clone(), r_free.clone());
        let beta_at_r = Thm::beta_conv(p_pure_at_r.clone()).map_err(pure_err)?;
        let beta_at_r_sym = beta_at_r.clone().sym().map_err(pure_err)?;

        // Forward direction: ⊢ tp_p_at_r ⟹ tp_eq_rep_r.
        let pure_fwd = typedef
            .rep_abs_fwd
            .all_elim(r_free.clone())
            .map_err(pure_err)?;
        let assume_tp_p = Thm::assume(tp_p_at_r.clone()).map_err(pure_err)?;
        // {tp_p} ⊢ App(P_pure, r)
        let p_pure_at_r_assumed = beta_at_r_sym.eq_mp(assume_tp_p).map_err(pure_err)?;
        // {tp_p} ⊢ rep(abs r) ≡ r
        let pure_eq_assumed = pure_fwd.imp_elim(p_pure_at_r_assumed).map_err(pure_err)?;
        // {tp_p} ⊢ Trueprop (Eq[α] (rep(abs r)) r)
        let hol_eq_assumed = self
            .ctx
            .eq_reflection_axiom()
            .inst_tfree("a", alpha.clone())
            .map_err(pure_err)?
            .all_elim(rep_abs_r.clone())
            .map_err(pure_err)?
            .all_elim(r_free.clone())
            .map_err(pure_err)?
            .sym()
            .map_err(pure_err)?
            .eq_mp(pure_eq_assumed)
            .map_err(pure_err)?;
        let fwd_imp = hol_eq_assumed.imp_intro(&tp_p_at_r).map_err(pure_err)?;

        // Backward direction: ⊢ tp_eq_rep_r ⟹ tp_p_at_r.
        let pure_back = typedef
            .rep_abs_back
            .all_elim(r_free.clone())
            .map_err(pure_err)?;
        let assume_tp_eq = Thm::assume(tp_eq_rep_r.clone()).map_err(pure_err)?;
        // {tp_eq_rep_r} ⊢ rep(abs r) ≡ r
        let pure_eq_assumed_b = self
            .ctx
            .eq_reflection_axiom()
            .inst_tfree("a", alpha.clone())
            .map_err(pure_err)?
            .all_elim(rep_abs_r)
            .map_err(pure_err)?
            .all_elim(r_free.clone())
            .map_err(pure_err)?
            .eq_mp(assume_tp_eq)
            .map_err(pure_err)?;
        // {tp_eq_rep_r} ⊢ App(P_pure, r)
        let p_pure_assumed = pure_back.imp_elim(pure_eq_assumed_b).map_err(pure_err)?;
        // {tp_eq_rep_r} ⊢ Trueprop (P r)
        let tp_p_assumed = beta_at_r.eq_mp(p_pure_assumed).map_err(pure_err)?;
        let back_imp = tp_p_assumed.imp_intro(&tp_eq_rep_r).map_err(pure_err)?;

        // 9. iff_intro: ⊢ Trueprop (Eq[bool] (P r) (Eq[α] (rep(abs r)) r))
        let thm2 = self
            .ctx
            .iff_intro_axiom()
            .all_elim(p_at_r)
            .map_err(pure_err)?
            .all_elim(eq_rep_r)
            .map_err(pure_err)?
            .imp_elim(fwd_imp)
            .map_err(pure_err)?
            .imp_elim(back_imp)
            .map_err(pure_err)?;

        Ok((thm1, thm2))
    }

    fn new_type(&mut self, name: NameId, arity: usize) -> Result<(), HolError> {
        if self.type_arity.contains_key(&name) {
            return Err(HolError::TypeAlreadyDefined(self.name_str(name).into()));
        }
        self.type_arity.insert(name, arity);
        Ok(())
    }

    fn new_constant(&mut self, name: NameId, ty: Type) -> Result<(), HolError> {
        if self.constants.contains_key(&name) {
            return Err(HolError::ConstantAlreadyDefined(self.name_str(name).into()));
        }
        self.constants.insert(name, ty);
        Ok(())
    }

    fn get_axioms(&self) -> Vec<Thm> {
        self.axioms.clone()
    }

    fn mk_type_validated(
        &mut self,
        name: NameId,
        args: Vec<Type>,
    ) -> Result<Type, HolError> {
        let expected = self
            .type_arity
            .get(&name)
            .copied()
            .ok_or(HolError::UnknownTypeConstructor(name))?;
        if expected != args.len() {
            return Err(HolError::WrongTypeArity {
                expected,
                got: args.len(),
            });
        }
        Ok(self.mk_tyapp(name, args))
    }

    fn mk_const_validated(&mut self, name: NameId, ty: Type) -> Result<Term, HolError> {
        let _generic = self
            .constants
            .get(&name)
            .ok_or(HolError::UnknownConstant(name))?
            .clone();
        // For now we accept any instance type (HOL Light unifies against
        // the generic type; we leave that for the validated-constructor
        // pass). The basic kernel sound rules don't require this check —
        // it's a user-experience guardrail.
        Ok(self.mk_const(name, ty))
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID};

    fn mk_kernel() -> PureHol {
        PureHol::new(FUN_TYCON_ID, BOOL_TYCON_ID, EQ_CONST_ID)
    }

    #[test]
    fn types_bool_and_fun_roundtrip() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let f = k.fun_type(b.clone(), b.clone());
        let (fun_id, args) = k.dest_tyapp(f).expect("fun is a tyapp");
        assert_eq!(fun_id, FUN_TYCON_ID);
        assert_eq!(args.len(), 2);
        assert!(k.type_eq(args[0].clone(), b));
    }

    #[test]
    fn refl_gives_x_eq_x() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        // Register a var name so dest_var can roundtrip if needed.
        k.register_name(10, "p");
        let p = k.mk_var(10, b);
        let thm = HolLightKernel::refl(&mut k, p.clone()).unwrap();
        let (l, r) = k.dest_eq_concl(&thm).unwrap();
        assert_eq!(l, p);
        assert_eq!(r, p);
    }

    #[test]
    fn trans_derives_a_eq_c() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(10, "a");
        k.register_name(11, "b");
        k.register_name(12, "c");
        let a = k.mk_var(10, b.clone());
        let bb = k.mk_var(11, b.clone());
        let c = k.mk_var(12, b);

        let ab = k.mk_eq(a.clone(), bb.clone());
        let bc = k.mk_eq(bb, c.clone());
        let h_ab = k.assume_rule(ab).unwrap();
        let h_bc = k.assume_rule(bc).unwrap();

        let h_ac = k.trans(h_ab, h_bc).unwrap();
        let (l, r) = k.dest_eq_concl(&h_ac).unwrap();
        assert_eq!(l, a);
        assert_eq!(r, c);
    }

    #[test]
    fn beta_on_identity_app() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(10, "x");
        let x = k.mk_var(10, b);
        let id_x = k.mk_abs(x.clone(), x.clone());
        let app = k.mk_comb(id_x, x.clone());
        let thm = k.beta_conv(app).unwrap();
        let (l, r) = k.dest_eq_concl(&thm).unwrap();
        // l = (λx. x) x, r = x. Compare r:
        assert_eq!(r, x);
        // l should reduce to x; structurally l is App(Abs(...), x).
        assert!(matches!(l.kind(), covalence_pure::TermKind::App(_, _)));
    }

    #[test]
    fn assume_p_has_p_as_hyp_and_concl() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(10, "p");
        let p = k.mk_var(10, b);
        let thm = k.assume_rule(p.clone()).unwrap();
        let concl = k.concl(thm.clone());
        let hyps = k.hyps(thm);
        assert_eq!(concl, p);
        assert_eq!(hyps.len(), 1);
        assert_eq!(hyps[0], p);
    }

    #[test]
    fn mk_comb_rule_derives_fx_eq_gy() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let fun_bb = k.fun_type(b.clone(), b.clone());
        k.register_name(10, "f");
        k.register_name(11, "g");
        k.register_name(12, "x");
        k.register_name(13, "y");
        let f = k.mk_var(10, fun_bb.clone());
        let g = k.mk_var(11, fun_bb);
        let x = k.mk_var(12, b.clone());
        let y = k.mk_var(13, b);

        let fg = k.mk_eq(f.clone(), g.clone());
        let xy = k.mk_eq(x.clone(), y.clone());
        let h_fg = k.assume_rule(fg).unwrap();
        let h_xy = k.assume_rule(xy).unwrap();
        let thm = k.mk_comb_rule(h_fg, h_xy).unwrap();
        let (l, r) = k.dest_eq_concl(&thm).unwrap();
        assert_eq!(l, k.mk_comb(f, x));
        assert_eq!(r, k.mk_comb(g, y));
    }

    #[test]
    fn new_axiom_records_and_returns() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(10, "p");
        let p = k.mk_var(10, b);
        let ax = HolLightKernel::new_axiom(&mut k, p.clone()).unwrap();
        assert_eq!(k.concl(ax.clone()), p);
        assert_eq!(k.get_axioms().len(), 1);
    }

    #[test]
    fn inst_rule_replaces_free_variables() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(10, "x");
        k.register_name(11, "y");
        let x = k.mk_var(10, b.clone());
        let y = k.mk_var(11, b);
        let xx = k.mk_eq(x.clone(), x.clone());
        let h = k.assume_rule(xx).unwrap();
        let h2 = k.inst_rule(&[(y.clone(), x)], h).unwrap();
        let (l, r) = k.dest_eq_concl(&h2).unwrap();
        assert_eq!(l, y);
        assert_eq!(r, y);
    }

    #[test]
    fn new_basic_type_definition_unit_type() {
        // The HOL Light "unit" type: defined by the predicate
        // `λx:bool. x = T`, witness `T`. Resulting typedef gives us
        // a new singleton type `unit` with `one_abs : bool → unit`
        // and `one_rep : unit → bool`.
        let mut k = mk_kernel();
        let bool_ty = k.bool_type();

        // Register names for the typedef.
        k.register_name(60, "unit");
        k.register_name(61, "one_abs");
        k.register_name(62, "one_rep");
        k.register_name(63, "a"); // abs var
        k.register_name(64, "r"); // rep var
        k.register_name(70, "x"); // P's bound

        // Build P = λx:bool. (x = T).
        // We need a closed lambda where the body uses Bound(0).
        // mk_abs takes a Free var, so build using the named-var path.
        let x = k.mk_var(70, bool_ty.clone());
        let t_const = k.ctx.t(); // HOL T : bool
        let eq_x_t = k.mk_eq(x.clone(), t_const.clone());
        let p_lambda = k.mk_abs(x, eq_x_t); // λx:bool. x = T  : bool → bool

        // Witness: T. So P T : bool unfolds to T = T (after β); but we
        // only need a Trueprop-wrapped witness. We construct it by
        // first reflecting on T (⊢ Trueprop (T = T)) and then noting
        // that P T β-reduces to T = T — i.e., we need the witness
        // theorem in the form ⊢ Trueprop (P T), not the unfolded form.
        //
        // We get this by: refl gives ⊢ Trueprop (T = T). Then we'd
        // need to rewrap as ⊢ Trueprop (P T) via β-back. Easier path:
        // just `assume` ⊢ Trueprop (P T) directly for the test (the
        // typedef machinery doesn't require the witness to be
        // assumption-free; it propagates hyps).
        let p_at_t = k.mk_comb(p_lambda.clone(), t_const.clone()); // (λx. x=T) T : bool
        let witness = k.assume_rule(p_at_t).unwrap(); // {tp(P T)} ⊢ tp(P T)

        // Run the typedef.
        let (thm1, thm2) = k
            .new_basic_type_definition(60, 61, 62, 63, 64, witness)
            .unwrap();

        // Verify thm1 = ⊢ Trueprop (Eq[unit] (abs (rep a)) a) for some a:unit.
        let (l1, r1) = k.dest_eq_concl(&thm1).unwrap();
        // r1 should be `a` of type unit (the typedef).
        // l1 should be abs(rep a).
        let unit_ty = k.mk_tyapp(60, vec![]);
        assert_eq!(r1.type_of().unwrap(), unit_ty);
        assert!(matches!(l1.kind(), TermKind::App(_, _)));

        // Verify thm2 = ⊢ Trueprop (Eq[bool] (P r) (Eq[α] (rep(abs r)) r)).
        let (lhs2, _rhs2) = k.dest_eq_concl(&thm2).unwrap();
        // lhs2 = (P r), so applying P_lambda to r.
        assert!(matches!(lhs2.kind(), TermKind::App(_, _)));

        // After typedef: mk_type(60) gives unit; mk_const(61, bool→unit)
        // gives the same `abs` term referenced in thm1.
        let abs_ty = k.fun_type(bool_ty.clone(), unit_ty.clone());
        let _abs_term = k.mk_const(61, abs_ty);
        let rep_ty = k.fun_type(unit_ty, bool_ty);
        let _rep_term = k.mk_const(62, rep_ty);
    }

    #[test]
    fn new_basic_definition_introduces_constant() {
        // Define `t_const = T` (i.e., a constant t_const : bool defined
        // to equal HOL T). After definition, `mk_const(t_const, bool)`
        // returns the same Pure Def term as the LHS of the theorem.
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(50, "t_const");

        // Build "Eq[bool] t_const T" where t_const is a Var (HOL form
        // for new_basic_definition input).
        let c_var = k.mk_var(50, b.clone());
        let t_const_body = k.ctx.t(); // HOL T : bool
        let def_eq = k.mk_eq(c_var.clone(), t_const_body.clone());

        let thm = k.new_basic_definition(def_eq).unwrap();
        // The theorem's RHS should be HOL T.
        let (lhs, rhs) = k.dest_eq_concl(&thm).unwrap();
        assert_eq!(rhs, t_const_body);

        // mk_const(50, bool) returns the same Def-wrapped term as the
        // LHS of the defining equation.
        let c_term = k.mk_const(50, b);
        assert_eq!(c_term, lhs);

        // dest_const round-trips the NameId.
        let (id, _) = k.dest_const(c_term).unwrap();
        assert_eq!(id, 50);
    }

    #[test]
    fn new_basic_definition_rejects_redefinition() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(50, "c");
        let c_var = k.mk_var(50, b);
        let t = k.ctx.t();
        let def_eq = k.mk_eq(c_var.clone(), t.clone());
        k.new_basic_definition(def_eq.clone()).unwrap();
        let err = k.new_basic_definition(def_eq).unwrap_err();
        assert!(matches!(err, HolError::ConstantAlreadyDefined(_)));
    }

    #[test]
    fn deduct_antisym_derives_iff_from_mutual_implication() {
        // Set up: assume both p and q (as separate theorems whose hyp
        // sets contain the OTHER side after deduct's discharge).
        //   th1 = {p, q} ⊢ p
        //   th2 = {p, q} ⊢ q
        // deduct_antisym: ⊢ p ⟺ q with hyps {} after both q (from th1)
        // and p (from th2) are discharged.
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(10, "p");
        k.register_name(11, "q");
        let p = k.mk_var(10, b.clone());
        let q = k.mk_var(11, b);

        // th1 = {p, q} ⊢ p, th2 = {p, q} ⊢ q via assume + add_hyp.
        // Simpler: just use two separate assumes and combine their hyps
        // by chaining through imp_intro/imp_elim. For the basic
        // round-trip, we test assume(p) and assume(q) — discharge gives
        // exact iff form.
        let th_p = k.assume_rule(p.clone()).unwrap();
        let th_q = k.assume_rule(q.clone()).unwrap();
        let iff = k.deduct_antisym(th_p, th_q).unwrap();

        // Conclusion is Trueprop (Eq[bool] p q).
        let (l, r) = k.dest_eq_concl(&iff).unwrap();
        assert_eq!(l, p);
        assert_eq!(r, q);
    }

    #[test]
    fn dest_abs_freshens_name_when_hint_collides_with_free_in_body() {
        // Construct `λx:bool. p` where `p` is a free `x:bool` in the
        // body (so the body's free `x` would shadow the binder if we
        // opened with the literal hint name).
        let mut k = mk_kernel();
        let b = k.bool_type();
        // Bound(0) refers to the lambda's binder; a Free("x", ...)
        // in the body refers to OUTER scope.
        let body = Term::free("x", b.clone()); // outer-scope `x`
        let abs = Term::abs(BinderHint::new("x"), b.clone(), body);
        let (var, opened) = k.dest_abs(abs).unwrap();
        // The new var must NOT be the outer-scope `x` (no capture).
        match var.kind() {
            TermKind::Free(n, _) => {
                assert_ne!(n.as_str(), "x", "dest_abs must rename to avoid capture");
            }
            _ => panic!("expected Free var from dest_abs"),
        }
        // The body's outer-scope `x` must remain unaffected.
        assert_eq!(opened, Term::free("x", b));
    }

    #[test]
    fn inst_rule_parallel_substitution_handles_cross_references() {
        // Pairs `[(y, x), (x, y)]` SWAP x and y. HOL Light treats
        // this as parallel substitution: original x's → y, original
        // y's → x. (NOT chained: if it were chained x→y then y→x,
        // the result would have only y's.) Pure's all_intro/elim
        // chain does the parallel substitution natively; this test
        // pins that property at the PureHol surface.
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(10, "x");
        k.register_name(11, "y");
        let x = k.mk_var(10, b.clone());
        let y = k.mk_var(11, b.clone());

        // Build {tp(x = y)} ⊢ tp(x = y).
        let eq_xy = k.mk_eq(x.clone(), y.clone());
        let h = k.assume_rule(eq_xy).unwrap();

        // Swap: pairs = [(y, x), (x, y)].
        let h_swapped = k
            .inst_rule(&[(y.clone(), x.clone()), (x.clone(), y.clone())], h)
            .unwrap();

        // Concl should be tp(y = x) (swapped).
        let (l, r) = k.dest_eq_concl(&h_swapped).unwrap();
        assert_eq!(l, y);
        assert_eq!(r, x);
        // Hyps should include tp(y = x) (the substituted form of
        // tp(x = y) under the swap).
        let hyps = k.hyps(h_swapped);
        let expected_hyp = k.mk_eq(y, x);
        assert_eq!(hyps.len(), 1);
        assert_eq!(hyps[0], expected_hyp);
    }

    #[test]
    fn inst_rule_multi_hyp_substitution_preserves_order() {
        // Build {tp(p), tp(q)} ⊢ tp(p) via a derivation chain so we
        // exercise multi-hyp imp_intro/imp_elim ordering:
        //   th = `⊢ p ⟹ q ⟹ p` (tautology) via two imp_intros
        //   imp_elim with {tp(p)} ⊢ tp(p)
        //   imp_elim with {tp(q)} ⊢ tp(q)
        //   ⇒ {tp(p), tp(q)} ⊢ tp(p)
        // Then INST [(a, p), (b, q)] should give {tp(a), tp(b)} ⊢ tp(a),
        // EXERCISING the multi-hyp imp_intro→all_intro→all_elim→imp_elim
        // chain in inst_rule. If imp_elim runs in the wrong order the
        // antecedent mismatch surfaces as an ImpAntecedentMismatch.
        let mut k = mk_kernel();
        let b = k.bool_type();
        k.register_name(10, "p");
        k.register_name(11, "q");
        k.register_name(20, "a");
        k.register_name(21, "b");
        let p = k.mk_var(10, b.clone());
        let q = k.mk_var(11, b.clone());
        let a = k.mk_var(20, b.clone());
        let bb = k.mk_var(21, b);

        let assume_p = k.assume_rule(p.clone()).unwrap(); // {tp(p)} ⊢ tp(p)
        let assume_q = k.assume_rule(q.clone()).unwrap(); // {tp(q)} ⊢ tp(q)

        // Build ⊢ p ⟹ q ⟹ p by two imp_intros on assume_p.
        let tp_p = k.ctx.mk_trueprop(p.clone()).unwrap();
        let tp_q = k.ctx.mk_trueprop(q.clone()).unwrap();
        let step1 = assume_p.clone().imp_intro(&tp_q).unwrap(); // {tp(p)} ⊢ tp(q) ⟹ tp(p)
        let chain = step1.imp_intro(&tp_p).unwrap(); // ⊢ tp(p) ⟹ tp(q) ⟹ tp(p)
        // Modus ponens twice.
        let step2 = chain.imp_elim(assume_p).unwrap(); // {tp(p)} ⊢ tp(q) ⟹ tp(p)
        let two_hyp_thm = step2.imp_elim(assume_q).unwrap(); // {tp(p), tp(q)} ⊢ tp(p)

        // INST [(a, p), (b, q)].
        let inst = k.inst_rule(&[(a.clone(), p), (bb.clone(), q)], two_hyp_thm).unwrap();
        let concl = k.concl(inst.clone());
        let hyps = k.hyps(inst);
        assert_eq!(concl, a);
        assert_eq!(hyps.len(), 2);
        assert!(hyps.contains(&a));
        assert!(hyps.contains(&bb));
    }

    #[test]
    fn inst_type_rule_replaces_type_variables() {
        let mut k = mk_kernel();
        k.register_name(20, "a");
        let alpha = k.mk_tyvar(20);
        k.register_name(10, "x");
        let x = k.mk_var(10, alpha);
        let xx = k.mk_eq(x.clone(), x);
        let h = k.assume_rule(xx).unwrap();
        let b = k.bool_type();
        let h2 = k.inst_type_rule(&[(b.clone(), 20)], h).unwrap();
        // After inst_type, x : 'a becomes x : bool.
        let (l, _) = k.dest_eq_concl(&h2).unwrap();
        assert_eq!(l.type_of().unwrap(), b);
    }
}
