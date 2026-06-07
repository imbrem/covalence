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

use std::collections::{HashMap, HashSet};

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
            Type::fun(a, b)
        } else if name == self.bool_id && args.is_empty() {
            self.ctx.bool_type()
        } else {
            Type::tycon(self.name_str(name), args)
        }
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
        Term::const_(self.name_str(name), ty)
    }

    fn mk_comb(&mut self, f: Term, x: Term) -> Term {
        Term::app(f, x)
    }

    fn mk_abs(&mut self, var: Term, body: Term) -> Term {
        // `var` is `Free(name, ty)`; close `body` over `name`.
        let (name, ty) = match var.kind() {
            TermKind::Free(n, t) => (n.clone(), t.clone()),
            _ => return body, // ill-formed; HOL Light would panic. Caller checks.
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
                // Open with a Free at the binder's hint name.
                let var = Term::free(hint.as_str(), ty.clone());
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
        tm.type_of()
            .unwrap_or_else(|e| panic!("type_of: ill-typed HOL term: {e:?}"))
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
        th.hyps()
            .iter()
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

    /// DEDUCT_ANTISYM_RULE — needs the `iff_intro` axiom in
    /// `HolLightCtx`. Tracked as the next addition.
    fn deduct_antisym(&mut self, _th1: Thm, _th2: Thm) -> Result<Thm, HolError> {
        Err(HolError::Unsupported(
            "deduct_antisym: needs HolLightCtx iff_intro axiom".into(),
        ))
    }

    /// INST: parallel term-variable instantiation.
    ///
    /// HOL `INST [t_i / x_i]` works on theorems with `x_i` free in
    /// hyps; Pure's `all_intro` forbids that. Standard Isabelle/HOL
    /// pattern: discharge every hyp mentioning any `x_i` first
    /// (`imp_intro` chain), quantify (`all_intro` per var),
    /// instantiate (`all_elim` per witness, reversed), then
    /// re-introduce each discharged hyp at its substituted form
    /// (`imp_elim` of `assume(h[σ])`).
    ///
    /// Substitution is conservative: rejects "cyclic" pair sets
    /// (where some `t_i` mentions another `x_j`) since reapplying
    /// sequential substitution to the regenerated hyps would lose
    /// parallel-substitution semantics. HOL Light's INST does not
    /// permit such pairs in practice; OpenTheory does not generate
    /// them.
    fn inst_rule(&mut self, pairs: &[(Term, Term)], th: Thm) -> Result<Thm, HolError> {
        let mut info: Vec<(SmolStr, Type)> = Vec::with_capacity(pairs.len());
        for (_new, old) in pairs {
            let TermKind::Free(n, ty) = old.kind() else {
                return Err(HolError::NotAVariable);
            };
            info.push((n.clone(), ty.clone()));
        }

        // Reject cyclic pair sets where some `t_i` mentions any `x_j`.
        for (new_term, _) in pairs {
            for (n, _) in &info {
                if subst::has_free_var(new_term, n.as_str()) {
                    return Err(HolError::Unsupported(
                        "inst_rule: cyclic substitution (t_i mentions x_j) not supported".into(),
                    ));
                }
            }
        }

        // Hyps mentioning any substituted var must be discharged.
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
        // Quantify each var in order. Outermost = first pair after
        // the final reversed elim, so we elim in reverse to land
        // each new_term on the matching var.
        for (n, ty) in &info {
            result = result.all_intro(n.as_str(), ty.clone()).map_err(pure_err)?;
        }
        for (new_term, _) in pairs.iter().rev() {
            result = result.all_elim(new_term.clone()).map_err(pure_err)?;
        }
        // Re-introduce each previously discharged hyp at its
        // substituted form. Sequential substitution is correct here
        // because the cyclic guard above ensures the substituted
        // names never appear in any `t_i`.
        for h in &hyps_to_discharge {
            let mut h_subst = h.clone();
            for (new_term, old_var) in pairs {
                let TermKind::Free(name, _) = old_var.kind() else {
                    unreachable!("checked above");
                };
                h_subst = subst::subst_free(&h_subst, name.as_str(), new_term);
            }
            let assumed = Thm::assume(h_subst).map_err(pure_err)?;
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

    fn new_basic_definition(&mut self, _tm: Term) -> Result<Thm, HolError> {
        Err(HolError::Unsupported(
            "new_basic_definition: defer until Pure Def is threaded through mk_const".into(),
        ))
    }

    fn new_basic_type_definition(
        &mut self,
        _tyname: NameId,
        _abs_name: NameId,
        _rep_name: NameId,
        _abs_var_name: NameId,
        _rep_var_name: NameId,
        _th: Thm,
    ) -> Result<(Thm, Thm), HolError> {
        Err(HolError::Unsupported(
            "new_basic_type_definition: defer until Select witness extraction is wired".into(),
        ))
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
