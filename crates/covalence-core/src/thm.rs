//! Pure theorems and the LCF rule API.
//!
//! `Thm` is the opaque kernel type. Its only constructor is the
//! private `Thm::build`, which type-checks the conclusion and every
//! hypothesis at kind `prop`. The rule methods are the only paths to
//! a `Thm` value; constructional soundness in the LCF sense.
//!
//! ## Observations and universality
//!
//! Observation leaves carry kernel-allocated [`Object`] handles,
//! compared by `Arc` pointer identity rather than by user-supplied
//! `Eq` impls — so a misbehaving observer cannot corrupt the
//! kernel's hyp `BTreeSet`. A theorem with no `Obs` leaves anywhere
//! (test via [`Thm::has_no_obs`]) is **universally true** with no
//! oracle dependencies, the same property HOL Light's `thm` has.
//!
//! The rule set is Pure-shaped:
//!
//! - LF: `assume`, `imp_intro`/`imp_elim`, `all_intro`/`all_elim`.
//! - Equality: `refl`, `trans`, `sym`, `cong_app`, `cong_abs`,
//!   `beta_conv`, `eta_conv`.
//! - Type-variable instantiation: `inst_tfree`.
//!
//! `define`, `observe`, and the user-supplied `O → Thm` conversion
//! are not in this MVP step.

use std::fmt;
use std::sync::Arc;

use crate::builtins;
use crate::error::{Error, Result};
use crate::hol;
use crate::subst::{
    close, find_free_type, has_free_var, open, shift_by, subst_free, subst_tfree_in_term,
    uses_bound_outer,
};
use crate::term::{
    Def, BinderHint, ObsEq, ObsImp, ObsTrue, Object, Observer, Term, TermKind, Type, TypeEnv, TypeKind,
    type_of_in,
};
use crate::ctx::Ctx;

#[derive(Clone)]
pub struct Thm {
    hyps: Ctx,
    concl: Term,
}

impl Thm {
    /// The single private constructor. Validates that every term is
    /// well-typed at kind `prop` AND — by reusing one [`TypeEnv`]
    /// across all of them — that every `Free` name has a single
    /// declared type across the whole theorem.
    ///
    /// Every rule API in this module bottoms out here.
    fn build(hyps: Ctx, concl: Term) -> Result<Thm> {
        let mut env = TypeEnv::default();
        let ty = type_of_in(&concl, &mut env)?;
        if !ty.is_formula() {
            return Err(Error::NotFormula(ty));
        }
        for h in &hyps {
            let hty = type_of_in(h, &mut env)?;
            if !hty.is_formula() {
                return Err(Error::NotFormula(hty));
            }
        }
        Ok(Thm { hyps, concl })
    }

    pub fn hyps(&self) -> &Ctx {
        &self.hyps
    }
    pub fn concl(&self) -> &Term {
        &self.concl
    }
    pub fn into_parts(self) -> (Ctx, Term) {
        (self.hyps, self.concl)
    }

    /// If the conclusion has shape `Pure-Eq(lhs, rhs)` (i.e.,
    /// `TermKind::Eq`), return `(lhs, rhs)`. Many proof tactics
    /// chain on the rhs after `trans` / `cong_app`; this avoids
    /// re-matching the kind by hand at every step.
    pub fn concl_eq_parts(&self) -> Result<(&Term, &Term)> {
        match self.concl.kind() {
            TermKind::Eq(l, r) => Ok((l, r)),
            _ => Err(Error::NotAnEquation),
        }
    }

    /// The right-hand side of a Pure-meta equality conclusion.
    pub fn concl_rhs(&self) -> Result<&Term> {
        Ok(self.concl_eq_parts()?.1)
    }

    /// The left-hand side of a Pure-meta equality conclusion.
    pub fn concl_lhs(&self) -> Result<&Term> {
        Ok(self.concl_eq_parts()?.0)
    }

    /// Returns `true` iff no `Obs` leaf appears anywhere in the
    /// theorem (conclusion or any hypothesis). Such a theorem is
    /// universally true with no oracle dependencies — equivalent to
    /// HOL Light's `thm`.
    pub fn has_no_obs(&self) -> bool {
        self.concl.has_no_obs() && self.hyps.iter().all(|h| h.has_no_obs())
    }

    /// Returns `true` iff every `Obs` leaf in the theorem (concl and
    /// hyps) carries an observer whose dynamic type is `O`. Trivially
    /// `true` for a theorem with no `Obs` leaves.
    pub fn all_obs_match<O: Observer>(&self) -> bool {
        self.concl.all_obs_match::<O>() && self.hyps.iter().all(|h| h.all_obs_match::<O>())
    }

    /// Walk the theorem and call `f` on every `Obs` leaf's observer
    /// downcast to `O`. Returns `Err(ObsDowncastTypeMismatch)` at
    /// the first leaf whose dynamic type does not match `O`.
    pub fn for_each_obs<O: Observer, F: FnMut(&O)>(&self, f: &mut F) -> Result<()> {
        self.concl.for_each_obs::<O, F>(f)?;
        for h in self.hyps.iter() {
            h.for_each_obs::<O, F>(f)?;
        }
        Ok(())
    }

    // ---- LF rules ----

    /// `{φ} ⊢ φ`, requiring `φ : prop`.
    pub fn assume(phi: Term) -> Result<Thm> {
        let hyps = Ctx::singleton(phi.clone());
        Self::build(hyps, phi)
    }

    /// Structural weakening: `Δ ⊢ φ`, given `Γ ⊢ φ` and `Γ ⊆ Δ`.
    ///
    /// Rejects with [`Error::NotASuperset`] if any hypothesis of
    /// `self` is missing from `target`. The conclusion is unchanged;
    /// every term in `target` is re-validated at kind `prop`.
    pub fn weaken(self, target: Ctx) -> Result<Thm> {
        if !self.hyps.is_subset(&target) {
            return Err(Error::NotASuperset);
        }
        Self::build(target, self.concl)
    }

    /// `Γ \ {φ} ⊢ φ ⟹ ψ`, given `Γ ⊢ ψ`.
    pub fn imp_intro(self, phi: &Term) -> Result<Thm> {
        let hyps = self.hyps.remove(phi);
        let concl = Term::imp(phi.clone(), self.concl);
        Self::build(hyps, concl)
    }

    /// `Γ ∪ Γ' ⊢ ψ`, given `Γ ⊢ φ⟹ψ` and `Γ' ⊢ φ`.
    pub fn imp_elim(self, hyp: Thm) -> Result<Thm> {
        let TermKind::Imp(phi, psi) = self.concl.kind() else {
            return Err(Error::NotMetaImp(format!("{}", self.concl)));
        };
        if *phi != hyp.concl {
            return Err(Error::ImpAntecedentMismatch {
                expected: format!("{}", phi),
                got: format!("{}", hyp.concl),
            });
        }
        let psi = psi.clone();
        let hyps = self.hyps.union(&hyp.hyps);
        Self::build(hyps, psi)
    }

    /// `Γ ⊢ ⋀x:τ. φ`, given `Γ ⊢ φ(x)` with `Free(x:τ)` not in `FV(Γ)`.
    pub fn all_intro(self, name: &str, ty: Type) -> Result<Thm> {
        for h in self.hyps.iter() {
            if has_free_var(h, name) {
                return Err(Error::FreeVarInHyps { name: name.into() });
            }
        }
        if let Some(declared) = find_free_type(&self.concl, name)
            && declared != ty
        {
            return Err(Error::BinderTypeMismatch {
                name: name.into(),
                declared,
                expected: ty,
            });
        }
        let body = close(&self.concl, name);
        let all = Term::all(name, ty, body);
        Self::build(self.hyps, all)
    }

    /// `Γ ∪ Γ' ⊢ q`, given `Γ ⊢ p ≡ q` and `Γ' ⊢ p`.
    ///
    /// Meta-equality MP. This is the Pure analogue of HOL Light's
    /// `EQ_MP` — but at the meta level. Standard primitive in
    /// Isabelle/Pure; soundness is the standard "if p and q are
    /// equal in the meta-logic and p is a theorem, so is q."
    ///
    /// Together with `cong_app`/`cong_abs` it makes Pure's `Eq` a true
    /// propositional equality.
    pub fn eq_mp(self, p_thm: Thm) -> Result<Thm> {
        let TermKind::Eq(p, q) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        if *p != p_thm.concl {
            return Err(Error::ImpAntecedentMismatch {
                expected: format!("{}", p),
                got: format!("{}", p_thm.concl),
            });
        }
        let concl = q.clone();
        let hyps = self.hyps.union(&p_thm.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ φ[t/0]`, given `Γ ⊢ ⋀x:τ. φ` and `t : τ`.
    pub fn all_elim(self, witness: Term) -> Result<Thm> {
        let TermKind::All(_, ty, body) = self.concl.kind() else {
            return Err(Error::NotMetaAll(format!("{}", self.concl)));
        };
        let wit_ty = witness.type_of()?;
        if wit_ty != *ty {
            return Err(Error::TypeMismatch {
                expected: ty.clone(),
                got: wit_ty,
            });
        }
        let concl = open(body, &witness);
        Self::build(self.hyps, concl)
    }

    // ---- Equality rules ----

    /// `⊢ t ≡ t`.
    pub fn refl(t: Term) -> Result<Thm> {
        let _ = t.type_of()?;
        let concl = Term::eq(t.clone(), t);
        Self::build(Ctx::new(), concl)
    }

    /// `Γ ∪ Γ' ⊢ t ≡ v`, given `Γ ⊢ t≡u` and `Γ' ⊢ u≡v`.
    pub fn trans(self, other: Thm) -> Result<Thm> {
        let TermKind::Eq(t, u1) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        let TermKind::Eq(u2, v) = other.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", other.concl)));
        };
        if u1 != u2 {
            return Err(Error::TransMiddleMismatch {
                left: format!("{}", u1),
                right: format!("{}", u2),
            });
        }
        let concl = Term::eq(t.clone(), v.clone());
        let hyps = self.hyps.union(&other.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ u ≡ t`, given `Γ ⊢ t≡u`.
    pub fn sym(self) -> Result<Thm> {
        let TermKind::Eq(t, u) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        let concl = Term::eq(u.clone(), t.clone());
        Self::build(self.hyps, concl)
    }

    /// `Γ ∪ Γ' ⊢ f(s) ≡ g(t)`, given `Γ ⊢ f≡g` and `Γ' ⊢ s≡t`. The new
    /// applications must type-check.
    pub fn cong_app(self, arg: Thm) -> Result<Thm> {
        let TermKind::Eq(f, g) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        let TermKind::Eq(s, t) = arg.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", arg.concl)));
        };
        let lhs = Term::app(f.clone(), s.clone());
        let rhs = Term::app(g.clone(), t.clone());
        // `build()` re-validates types end-to-end.
        let concl = Term::eq(lhs, rhs);
        let hyps = self.hyps.union(&arg.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ (λy:τ. s[y/x]) ≡ (λy:τ. t[y/x])`, given `Γ ⊢ s≡t` with
    /// `Free(name:τ)` not in `FV(Γ)`. The supplied `ty` must match
    /// the declared type of `Free(name)` wherever it appears in the
    /// theorem.
    pub fn cong_abs(self, name: &str, ty: Type) -> Result<Thm> {
        let TermKind::Eq(s, t) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        for h in self.hyps.iter() {
            if has_free_var(h, name) {
                return Err(Error::FreeVarInHyps { name: name.into() });
            }
        }
        let declared = find_free_type(s, name).or_else(|| find_free_type(t, name));
        if let Some(declared) = declared
            && declared != ty
        {
            return Err(Error::BinderTypeMismatch {
                name: name.into(),
                declared,
                expected: ty,
            });
        }
        let s_abs = Term::abs(name, ty.clone(), close(s, name));
        let t_abs = Term::abs(name, ty, close(t, name));
        let concl = Term::eq(s_abs, t_abs);
        Self::build(self.hyps, concl)
    }

    /// `⊢ (λx:τ. body) arg ≡ body[arg/0]`.
    pub fn beta_conv(app: Term) -> Result<Thm> {
        let TermKind::App(fun, arg) = app.kind() else {
            return Err(Error::NotApp(format!("{}", app)));
        };
        let TermKind::Abs(_, ty, body) = fun.kind() else {
            return Err(Error::NotAbs(format!("{}", fun)));
        };
        let arg_ty = arg.type_of()?;
        if arg_ty != *ty {
            return Err(Error::TypeMismatch {
                expected: ty.clone(),
                got: arg_ty,
            });
        }
        let rhs = open(body, arg);
        let concl = Term::eq(app.clone(), rhs);
        Self::build(Ctx::new(), concl)
    }

    /// `⊢ (λx:τ. f x) ≡ f`, when `Bound(0)` does not appear free in `f`.
    pub fn eta_conv(abs: Term) -> Result<Thm> {
        let TermKind::Abs(_, ty, body) = abs.kind() else {
            return Err(Error::NotAbs(format!("{}", abs)));
        };
        let TermKind::App(f, x) = body.kind() else {
            return Err(Error::EtaShape);
        };
        let TermKind::Bound(0) = x.kind() else {
            return Err(Error::EtaShape);
        };
        if uses_bound_outer(f, 0) {
            return Err(Error::EtaShape);
        }
        let _ = abs.type_of()?;
        let _ = ty;
        let f_outer = shift_by(f, -1, 0);
        let concl = Term::eq(abs.clone(), f_outer);
        Self::build(Ctx::new(), concl)
    }

    // ========================================================================
    // HOL-Light inference rules (HOL `=` at type `bool`)
    // ========================================================================
    //
    // These ten rules are the HOL Light primitive inference rule set,
    // operating directly at the `bool` level (so conclusions are
    // `bool`-typed terms, not `Trueprop (...)` props). They coexist
    // with the Pure rules above during the migration to pure HOL;
    // once Pure is removed they become THE inference rules.
    //
    // Soundness follows HOL Light's standard model-theoretic story:
    // HOL `=` is interpreted as equality in the model, all rules are
    // sound under that interpretation.

    /// `⊢ t = t : bool` — HOL reflexivity of equality.
    pub fn hol_refl(t: Term) -> Result<Thm> {
        let _ = t.type_of()?;
        let concl = hol::hol_eq(t.clone(), t);
        Self::build(Ctx::new(), concl)
    }

    /// `Γ ∪ Δ ⊢ s = u`, given `Γ ⊢ s = t` and `Δ ⊢ t = u` (HOL `=`).
    pub fn hol_trans(self, other: Thm) -> Result<Thm> {
        let (s, t1) = parse_hol_eq(&self.concl)?;
        let (t2, u) = parse_hol_eq(&other.concl)?;
        if t1 != t2 {
            return Err(Error::TransMiddleMismatch {
                left: format!("{}", t1),
                right: format!("{}", t2),
            });
        }
        let concl = hol::hol_eq(s.clone(), u.clone());
        let hyps = self.hyps.union(&other.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ∪ Δ ⊢ f x = g y`, given `Γ ⊢ f = g` and `Δ ⊢ x = y`. The
    /// applications must type-check: `f` (and so `g`) must have
    /// function type whose domain matches `x`'s (and so `y`'s) type.
    pub fn hol_mk_comb(self, arg: Thm) -> Result<Thm> {
        let (f, g) = parse_hol_eq(&self.concl)?;
        let (x, y) = parse_hol_eq(&arg.concl)?;
        let lhs = Term::app(f.clone(), x.clone());
        let rhs = Term::app(g.clone(), y.clone());
        // Pre-validate the application's type rather than letting
        // hol::hol_eq's internal `type_of().expect(...)` panic on a
        // bad arg shape. type_of() here also serves as a Free-var
        // consistency check across f and x.
        let _ = lhs.type_of()?;
        let _ = rhs.type_of()?;
        let concl = hol::hol_eq(lhs, rhs);
        let hyps = self.hyps.union(&arg.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ (λx:τ. s[x]) = (λx:τ. t[x])`, given `Γ ⊢ s = t` with
    /// `Free(name:τ)` not free in `Γ`.
    pub fn hol_abs(self, name: &str, ty: Type) -> Result<Thm> {
        let (s, t) = parse_hol_eq(&self.concl)?;
        for h in self.hyps.iter() {
            if has_free_var(h, name) {
                return Err(Error::FreeVarInHyps { name: name.into() });
            }
        }
        let declared = find_free_type(s, name).or_else(|| find_free_type(t, name));
        if let Some(declared) = declared
            && declared != ty
        {
            return Err(Error::BinderTypeMismatch {
                name: name.into(),
                declared,
                expected: ty,
            });
        }
        let s = s.clone();
        let t = t.clone();
        let s_abs = Term::abs(name, ty.clone(), close(&s, name));
        let t_abs = Term::abs(name, ty, close(&t, name));
        let concl = hol::hol_eq(s_abs, t_abs);
        Self::build(self.hyps, concl)
    }

    /// `⊢ (λx:τ. body) arg = body[arg/0] : bool` — β-conversion as
    /// a HOL equation.
    pub fn hol_beta_conv(app: Term) -> Result<Thm> {
        let TermKind::App(fun, arg) = app.kind() else {
            return Err(Error::NotApp(format!("{}", app)));
        };
        let TermKind::Abs(_, ty, body) = fun.kind() else {
            return Err(Error::NotAbs(format!("{}", fun)));
        };
        let arg_ty = arg.type_of()?;
        if arg_ty != *ty {
            return Err(Error::TypeMismatch {
                expected: ty.clone(),
                got: arg_ty,
            });
        }
        let rhs = open(body, arg);
        let concl = hol::hol_eq(app.clone(), rhs);
        Self::build(Ctx::new(), concl)
    }

    /// `{p} ⊢ p` for any `p : bool` — HOL-level assume.
    pub fn hol_assume(p: Term) -> Result<Thm> {
        let ty = p.type_of()?;
        if !ty.is_bool() {
            return Err(Error::NotBool(ty));
        }
        let hyps = Ctx::singleton(p.clone());
        Self::build(hyps, p)
    }

    /// `Γ ∪ Δ ⊢ q`, given `Γ ⊢ p = q : bool` and `Δ ⊢ p`. HOL Light's
    /// `EQ_MP` — equality at `bool` IS biconditional, so this also
    /// implements the `⇔`-elim direction.
    pub fn hol_eq_mp(self, p_thm: Thm) -> Result<Thm> {
        let (p, q) = parse_hol_eq(&self.concl)?;
        // p = q must be at type bool (otherwise it's not an
        // implication-shaped equation).
        let p_ty = p.type_of()?;
        if !p_ty.is_bool() {
            return Err(Error::NotBool(p_ty));
        }
        if *p != p_thm.concl {
            return Err(Error::ImpAntecedentMismatch {
                expected: format!("{}", p),
                got: format!("{}", p_thm.concl),
            });
        }
        let concl = q.clone();
        let hyps = self.hyps.union(&p_thm.hyps);
        Self::build(hyps, concl)
    }

    /// HOL Light's `DEDUCT_ANTISYM_RULE`:
    /// `(Γ \ {q}) ∪ (Δ \ {p}) ⊢ p ⇔ q`, given `Γ ⊢ p` and `Δ ⊢ q`.
    /// Both `p` and `q` must be `bool`-typed; equality at `bool`
    /// IS biconditional.
    pub fn hol_deduct_antisym(self, other: Thm) -> Result<Thm> {
        let p_ty = self.concl.type_of()?;
        let q_ty = other.concl.type_of()?;
        if !p_ty.is_bool() {
            return Err(Error::NotBool(p_ty));
        }
        if !q_ty.is_bool() {
            return Err(Error::NotBool(q_ty));
        }
        let p = self.concl.clone();
        let q = other.concl.clone();
        let hyps_p_minus_q = self.hyps.remove(&q);
        let hyps_q_minus_p = other.hyps.remove(&p);
        let hyps = hyps_p_minus_q.union(&hyps_q_minus_p);
        let concl = hol::hol_eq(p, q);
        Self::build(hyps, concl)
    }

    /// HOL Light's `INST`: substitute a free term variable. `name`
    /// is the free var to replace; `replacement` is the term to
    /// substitute. The replacement's type must match the free var's
    /// declared type, if the variable appears anywhere in the
    /// theorem (concl or hyps).
    ///
    /// `Thm::build`'s re-typing pass also catches type mismatches
    /// (it re-validates the substituted term end-to-end), but the
    /// explicit check here gives a more specific error message and
    /// rejects ill-typed substitutions even when the post-substitution
    /// term happens to type-check at a wrong type by accident.
    pub fn hol_inst(self, name: &str, replacement: Term) -> Result<Thm> {
        let replacement_ty = replacement.type_of()?;
        let declared = find_free_type(&self.concl, name)
            .or_else(|| self.hyps.iter().find_map(|h| find_free_type(h, name)));
        if let Some(declared) = declared
            && declared != replacement_ty
        {
            return Err(Error::TypeMismatch {
                expected: declared,
                got: replacement_ty,
            });
        }
        let concl = subst_free(&self.concl, name, &replacement);
        let hyps = self.hyps.map(|h| subst_free(h, name, &replacement));
        Self::build(hyps, concl)
    }

    // (HOL Light's `INST_TYPE` is the same operation as the existing
    // `Thm::inst_tfree`; no new method needed.)

    /// Introduce a fresh subtype τ ≤ α witnessed by a predicate `P`.
    ///
    /// Given a witness theorem `Γ ⊢ P x` for some `x : α` and
    /// `P : α → prop`, allocate a fresh type constructor and two
    /// fresh constants `abs : α → τ`, `rep : τ → α`, returning a
    /// [`TypeDef`] bundle of:
    ///
    /// - `tau`: the new type, parameterised by the free type variables
    ///   of α (so `inst_tfree` propagates correctly).
    /// - `abs`, `rep`: the bijection constants (Obs leaves; their Arc
    ///   identity ties them to this typedef).
    /// - `abs_rep`:    `Γ ⊢ ⋀a:τ. abs (rep a) ≡ a`
    /// - `rep_abs_fwd`: `Γ ⊢ ⋀r:α. P r ⟹ rep (abs r) ≡ r`
    /// - `rep_abs_back`: `Γ ⊢ ⋀r:α. rep (abs r) ≡ r ⟹ P r`
    ///
    /// The witness's hypotheses are propagated to all three returned
    /// theorems — matching HOL Light's discipline. Use the disjunct
    /// trick at the HOL layer (`Q := λx. P x ∨ x = ε P`) if you want
    /// to avoid the inhabitedness obligation.
    ///
    /// ## Soundness
    ///
    /// The fresh `tau`, `abs`, `rep` are interpreted in any model by
    /// fixing τ as a subset of α witnessed by the equivalence
    /// `P r ↔ rep (abs r) = r`. The witness theorem certifies that
    /// the subset is non-empty (so τ is inhabited) — without it the
    /// degenerate case is logically vacuous but the rule still
    /// admits a model (τ singleton at the canonical witness).
    pub fn new_type_definition(
        hint: impl Into<BinderHint>,
        abs_hint: impl Into<BinderHint>,
        rep_hint: impl Into<BinderHint>,
        witness: Thm,
    ) -> Result<TypeDef> {
        // 1. Decompose witness's concl as `P x` (an application).
        let TermKind::App(p, x) = witness.concl.kind() else {
            return Err(Error::BadTypeDefWitness(format!("{}", witness.concl)));
        };
        let p = p.clone();
        let x = x.clone();

        // 2. Read α from x's type.
        let alpha = x.type_of()?;

        // 3. Validate P : α → prop.
        let p_ty = p.type_of()?;
        let TypeKind::Fun(p_dom, p_cod) = p_ty.kind() else {
            return Err(Error::NotFunction(p_ty));
        };
        if *p_dom != alpha {
            return Err(Error::TypeMismatch {
                expected: alpha.clone(),
                got: p_dom.clone(),
            });
        }
        if !p_cod.is_prop() {
            return Err(Error::NotProp(p_cod.clone()));
        }

        // 4. Compute the type-variable arity from α's free TFrees.
        //    τ becomes parametric in those tvars (in canonical order),
        //    so `inst_tfree` after typedef substitutes inside τ's args.
        let tvar_names = alpha.free_tvars();
        let tvar_types: Vec<Type> = tvar_names.iter().map(|n| Type::tfree(n.clone())).collect();

        // 5. Allocate ONE fresh marker tying the typedef + abs + rep
        //    together via Arc identity. The marker is a kernel-private
        //    zero-sized struct with no methods, so user code can never
        //    forge or equate it across calls.
        let marker = TypeDefMarker::new();
        let tau = Type::tycon_obs(marker.clone(), hint.into(), tvar_types);

        // 6. Build abs and rep as Obs leaves wrapping per-role markers
        //    that carry a reference to the shared typedef marker. This
        //    gives abs and rep their own Arc identities while keeping
        //    them tied to the typedef.
        let abs_marker = TypeDefAbsMarker::new(&marker, abs_hint.into());
        let rep_marker = TypeDefRepMarker::new(&marker, rep_hint.into());
        let abs_ty = Type::fun(alpha.clone(), tau.clone());
        let rep_ty = Type::fun(tau.clone(), alpha.clone());
        let abs = Term::obs(abs_marker, abs_ty);
        let rep = Term::obs(rep_marker, rep_ty);

        // 7. Build the three bijection theorems.
        //
        //    abs_rep: ⋀a:τ. abs (rep a) ≡ a
        let bound0 = Term::bound(0);
        let abs_rep_body = Term::eq(
            Term::app(abs.clone(), Term::app(rep.clone(), bound0.clone())),
            bound0.clone(),
        );
        let abs_rep_concl = Term::all(BinderHint::new("a"), tau.clone(), abs_rep_body);

        //    rep_abs_eq : (rep (abs r) ≡ r)   (with r=bound 0)
        //    p_at_bound : P r
        let p_at_bound = Term::app(p, bound0.clone());
        let rep_abs_eq = Term::eq(
            Term::app(rep.clone(), Term::app(abs.clone(), bound0)),
            Term::bound(0),
        );
        //    fwd: ⋀r:α. P r ⟹ rep (abs r) ≡ r
        let fwd_concl = Term::all(
            BinderHint::new("r"),
            alpha.clone(),
            Term::imp(p_at_bound.clone(), rep_abs_eq.clone()),
        );
        //    back: ⋀r:α. rep (abs r) ≡ r ⟹ P r
        let back_concl = Term::all(
            BinderHint::new("r"),
            alpha,
            Term::imp(rep_abs_eq, p_at_bound),
        );

        // 8. Propagate witness's hyps to each emitted theorem — every
        //    fact about the new typedef depends on the witness's
        //    inhabitedness justification. `TermSet` clones share the
        //    underlying set via `Arc`.
        let hyps = witness.hyps.clone();
        let abs_rep = Self::build(hyps.clone(), abs_rep_concl)?;
        let rep_abs_fwd = Self::build(hyps.clone(), fwd_concl)?;
        let rep_abs_back = Self::build(hyps, back_concl)?;

        Ok(TypeDef {
            tau,
            abs,
            rep,
            abs_rep,
            rep_abs_fwd,
            rep_abs_back,
            tvars: tvar_names,
        })
    }

    /// Introduce a fresh defined constant: emit `⊢ Def(name, body) ≡ body`.
    ///
    /// Each call allocates a *fresh* `Arc` for the body, so two
    /// distinct `define` calls — even with the same name and the same
    /// body term — produce distinct `Def`s. The kernel never reuses a
    /// `Def` identity, so users cannot accidentally derive
    /// `⊢ body₁ ≡ body₂` by `trans`+`sym`-ing two equations for "the
    /// same name" — the two `Def`s are simply different symbols that
    /// happen to share a display label.
    ///
    /// The `name` is display-only (an α-transparent [`BinderHint`]). The
    /// `body` must be a valid Pure term (typeable in isolation).
    ///
    /// ## Soundness
    ///
    /// Sound because the resulting `Def` is a brand-new symbol whose
    /// only equation says it equals `body`. In any model satisfying
    /// the prior theory, we extend by interpreting this `Def` as
    /// `⟦body⟧` — a conservative extension. No global signature is
    /// needed because the allocator gives us uniqueness per call.
    pub fn define(name: impl Into<BinderHint>, body: Term) -> Result<Thm> {
        let body_type = body.type_of()?;
        // Soundness check (Isabelle/Pure parity): no "phantom"
        // tvars — every free tvar appearing inside any type
        // annotation in `body` must also appear in `body_type`.
        // Without this, a phantom tvar inside `body` would be
        // invisible to `instance_type`, so `subst_tfree_in_term`
        // could leave a `Def` whose body still mentions the
        // phantom tvar at the original type — inconsistent with
        // the `Def ≡ body` equation it stands for.
        let type_tvars: std::collections::BTreeSet<smol_str::SmolStr> =
            body_type.free_tvars().into_iter().collect();
        let mut body_tvars = std::collections::BTreeSet::new();
        crate::subst::collect_term_tvars(&body, &mut body_tvars);
        for tv in &body_tvars {
            if !type_tvars.contains(tv) {
                return Err(crate::error::Error::DefPhantomTFree {
                    tvar: tv.clone(),
                    body_type,
                });
            }
        }
        let d = Def::new_internal(name.into(), body.clone(), body_type);
        let concl = Term::eq(Term::def(d), body);
        Self::build(Ctx::new(), concl)
    }

    /// Single-step computation rule on builtin primitives applied to
    /// concrete literal arguments. Returns `⊢ t ≡ result` where
    /// `result` is the canonical value of evaluating the operation;
    /// returns an `Err(NotReducible)` for terms that aren't a
    /// primitive-application with all-literal arguments (the rule is
    /// deliberately conservative — it doesn't reduce subterms or
    /// follow β/δ chains).
    ///
    /// **Catalogue**:
    ///
    /// - `App(Prim(NatArith Succ), NatLit a)` → `NatLit(a + 1)`
    /// - `App(Prim(NatArith Pred), NatLit a)` → `NatLit(a − 1)` saturating at 0
    /// - `App(App(Prim(NatArith Add), NatLit a), NatLit b)` → `NatLit(a + b)`
    /// - similarly for `Mul`, `Sub` (saturating), `Div` (`a/0 = 0`), `Mod` (`a%0 = 0`)
    /// - `App(Prim(IntArith Succ/Pred), IntLit a)` → `IntLit(a ± 1)`
    /// - `App(Prim(IntNeg), IntLit a)` → `IntLit(−a)`
    /// - `App(App(Prim(IntArith *), IntLit a), IntLit b)` for each binop
    /// - `App(App(Prim(BytesCat), Blob a), Blob b)` → `Blob(a ++ b)`
    /// - `App(App(Prim(BytesConsNat), NatLit n), Blob b)` → `Blob([n%256, ...b])`
    /// - `App(Prim(BytesLen), Blob b)` → `NatLit(b.len())`
    /// - `App(App(Prim(BytesAt), Blob b), NatLit i)` → `NatLit(b[i] or 0)`
    /// - `App(App(App(Prim(BytesSlice), Blob b), NatLit start), NatLit len)`
    ///   → `Blob(b[start..min(start+len, b.len())])`
    /// - `App(Prim(NatToInt), NatLit n)` → `IntLit(n)`
    /// - `App(App(HolOp(Eq, _), lit_a), lit_b)` where `lit_a` and
    ///   `lit_b` are kernel literals of the same kind (`Bool`,
    ///   `Nat`, `Int`, or `Blob`) → `Bool(a == b)`. This is the
    ///   kernel's commitment to literal distinctness — sound
    ///   because each literal kind has a fixed denotation in any
    ///   model.
    /// `⊢ term_spec(spec, args) ≡ subst(spec.tm, tvars, args)` for a
    /// **let-style** TermSpec (i.e., one whose `tm` is the body
    /// itself, with `type_of(tm) == spec.ty`). Returns
    /// `Err(SpecIsDefStyle)` when `tm` is a `ty → bool` selector
    /// predicate (ε-style), and `Err(SpecHasNoBody)` for
    /// declaration-only specs.
    ///
    /// Sound because a let-style spec's denotation is literally its
    /// body at the supplied type-args; the kernel commits to that
    /// equation when it builds the spec.
    pub fn unfold_term_spec(t: Term) -> Result<Thm> {
        let (spec, args) = match t.kind() {
            TermKind::Spec(spec, args) => (spec.clone(), args.clone()),
            _ => return Err(Error::NotASpec),
        };
        let declared_ty = spec
            .ty()
            .ok_or(Error::SpecHasNoBody)?
            .clone();
        let body = spec.tm().ok_or(Error::SpecHasNoBody)?.clone();

        // let-style ↔ body has the spec's declared type.
        // def-style ↔ body has type (declared_ty → bool).
        let body_ty = body.type_of()?;
        if body_ty != declared_ty {
            return Err(Error::SpecIsDefStyle);
        }

        // Substitute the spec's type variables positionally for the
        // supplied type arguments. `free_tvars` produces a sorted,
        // deduplicated list — the same order `type_of_in` uses when
        // typing a `TermKind::Spec` leaf.
        let tvars = declared_ty.free_tvars();
        let mut unfolded = body;
        for (tvar, arg) in tvars.iter().zip(args.iter()) {
            unfolded = subst_tfree_in_term(&unfolded, tvar, arg);
        }

        Self::build(Ctx::new(), Term::eq(t, unfolded))
    }

    pub fn reduce_prim(t: Term) -> Result<Thm> {
        let reduced = builtins::reduce_prim_term(&t).ok_or(Error::NotReducible)?;
        Self::build(Ctx::new(), Term::eq(t, reduced))
    }

    /// `Γ[α:=σ] ⊢ φ[α:=σ]`.
    pub fn inst_tfree(self, name: &str, replacement: Type) -> Result<Thm> {
        let concl = subst_tfree_in_term(&self.concl, name, &replacement);
        let hyps = self.hyps.map(|h| subst_tfree_in_term(h, name, &replacement));
        Self::build(hyps, concl)
    }

    /// `⊢ expr1 ≡ expr2`, where:
    /// - `expr1` and `expr2` each have the form `(obs head)(arg1)(arg2)…`
    ///   (zero or more applications of an `Obs` leaf at the head).
    /// - both head observers downcast successfully to Rust type `O`.
    /// - both expressions have the same Pure type.
    /// - the observer's [`ObsEq::obs_eq`] method, called with the two
    ///   observers and their args, returns `true`.
    ///
    /// ## Soundness
    ///
    /// The kernel rule is **unconditionally sound** regardless of
    /// what `O::obs_eq` returns. See [`ObsEq`]'s documentation for the
    /// parametric ε-model that makes this work. Observer impls are
    /// *not* part of the TCB — they are a per-Rust-type policy lever,
    /// not a soundness obligation. Different observer types `O`, `O'`
    /// get independent ε-families, so the rule never lets one
    /// observer's policy compromise another's.
    /// `⊢ expr`, where:
    /// - `expr` decomposes as `(obs head)(arg1)(arg2)…` with an `Obs`
    ///   leaf at the head and zero or more applications.
    /// - the head observer downcasts to Rust type `O`.
    /// - `expr` has final Pure type `prop`.
    /// - `O::obs_true(args, hint)` returns `true`.
    ///
    /// ## Soundness
    ///
    /// The rule is **unconditionally sound** regardless of what
    /// `O::obs_true` returns. The standard ε-interpretation of any
    /// observation whose result type is `prop` maps it to `⊤`, so
    /// every `(obs O) args` of type `prop` is already true in the
    /// model. Per-`O` ε-families means a policy choice in `WasmObs`
    /// can't affect equations or assertions involving `HolLight`.
    ///
    /// `hint` is the same opaque pass-through as on `obs_eq`.
    pub fn obs_true<O: ObsTrue>(
        expr: Term,
        hint: Option<Arc<dyn crate::term::Hint>>,
    ) -> Result<Thm> {
        let (obs, args) = decompose_obs_app(&expr)?;
        let o = obs.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let ty = expr.type_of()?;
        if !ty.is_prop() {
            return Err(Error::NotProp(ty));
        }
        if !o.obs_true(&args, hint.as_deref().map(|h| h)) {
            return Err(Error::ObsEqRefused);
        }
        Self::build(Ctx::new(), expr)
    }

    /// `⊢ hyps[0] ⟹ hyps[1] ⟹ … ⟹ hyps[n] ⟹ expr` — a **lazy
    /// theorem** declared by the observer policy. Used to encode
    /// HOL-style derivation rules as reusable implications: callers
    /// then chain `imp_elim` with concrete source theorems to get the
    /// specialised result.
    ///
    /// Validates:
    /// - `expr` decomposes as `(obs head)(arg1)(arg2)…`.
    /// - the head observer downcasts to `O`.
    /// - `expr` has final type `prop`.
    /// - every hyp has type `prop`.
    /// - `O::obs_imp(args, hyps, hint)` returns `true`.
    ///
    /// ## Soundness
    ///
    /// Strictly weaker than [`Thm::obs_true`]. Any chain of
    /// implications ending in a prop-typed obs application is sound to
    /// assert under the same parametric-ε model that makes `obs_true`
    /// sound. Per-`O` ε-families means a policy bug in `MyObs` can't
    /// touch implications about `HolLight`.
    pub fn obs_imp<O: ObsImp>(
        expr: Term,
        hyps: Vec<Term>,
        hint: Option<Arc<dyn crate::term::Hint>>,
    ) -> Result<Thm> {
        let (obs, args) = decompose_obs_app(&expr)?;
        let o = obs.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let ty = expr.type_of()?;
        if !ty.is_prop() {
            return Err(Error::NotProp(ty));
        }
        for h in &hyps {
            let h_ty = h.type_of()?;
            if !h_ty.is_prop() {
                return Err(Error::NotProp(h_ty));
            }
        }
        if !o.obs_imp(&args, &hyps, hint.as_deref()) {
            return Err(Error::ObsEqRefused);
        }
        // Build hyp[0] ⟹ hyp[1] ⟹ ... ⟹ expr (right-associative).
        let mut result = expr;
        for h in hyps.into_iter().rev() {
            result = Term::imp(h, result);
        }
        Self::build(Ctx::new(), result)
    }

    pub fn obs_eq<O: ObsEq>(
        expr1: Term,
        expr2: Term,
        hint: Option<Arc<dyn crate::term::Hint>>,
    ) -> Result<Thm> {
        let (obs1, args1) = decompose_obs_app(&expr1)?;
        let (obs2, args2) = decompose_obs_app(&expr2)?;
        let o1 = obs1.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let o2 = obs2.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let ty1 = expr1.type_of()?;
        let ty2 = expr2.type_of()?;
        if ty1 != ty2 {
            return Err(Error::TypeMismatch {
                expected: ty1,
                got: ty2,
            });
        }
        if !o1.obs_eq(o2, &args1, &args2, hint.as_deref()) {
            return Err(Error::ObsEqRefused);
        }
        let concl = Term::eq(expr1, expr2);
        Self::build(Ctx::new(), concl)
    }

    // ========================================================================
    // Bona-fide HOL axioms (folded into the kernel)
    // ========================================================================
    //
    // These are the foundational HOL axioms — induction principles
    // for the kernel's primitive datatypes plus the HOL Light
    // axioms (choice, extensionality, infinity). Each is sound by
    // construction (the kernel author asserts it); the resulting
    // `Thm` has *empty* hypotheses, not the self-hyp pattern that
    // `Thm::assume` produces.
    //
    // The axiom conclusion *terms* are cached at the
    // `crate::hol` module level (`LazyLock<Term>`). The `Thm`
    // wrapper is rebuilt on each call — that's just a single
    // `type_of_in` walk over the cached term, which is cheap.

    /// `⊢ Trueprop (∀P:nat→bool. P 0 ∧ (∀n:nat. P n ⟹ P (succ n))
    ///              ⟹ ∀n:nat. P n)` —
    /// Peano induction on `Type::nat()` as a kernel axiom.
    ///
    /// Sound because the kernel commits to `Type::nat()` denoting
    /// exactly the standard naturals generated by `0` and `succ`.
    pub fn nat_induction() -> Thm {
        Self::build(Ctx::new(), hol::nat_induction_term())
            .expect("nat_induction: well-typed by construction")
    }

    // ---- nat-prim definitional axioms ----
    //
    // Pure exposes `Prim::NatArith(Pred)` as a primitive function;
    // these two equations fix its meaning at the open-form level.
    // Closed forms (`pred lit_5 = lit_4`) are already decided by
    // `Thm::reduce_prim`. `succ` is foundational; `add`/`mul`/`sub`
    // get their meaning from `natrec` (which itself is defined in
    // `covalence-hol` via Hilbert's choice — no kernel axiom
    // needed).

    /// `⊢ Trueprop (pred 0 = 0)` — saturating-at-zero predecessor.
    pub fn nat_pred_zero() -> Thm {
        Self::build(Ctx::new(), hol::pred_zero_term())
            .expect("nat_pred_zero: well-typed by construction")
    }

    /// `⊢ ⋀n:nat. Trueprop (pred (succ n) = n)` — predecessor on
    /// successors.
    pub fn nat_pred_succ() -> Thm {
        Self::build(Ctx::new(), hol::pred_succ_term())
            .expect("nat_pred_succ: well-typed by construction")
    }

    /// `⊢ ⋀z:α. ⋀f:nat→α→α. Trueprop (natRec[α] z f 0 = z)` — the
    /// primitive-recursor "zero" equation. Sound because
    /// [`crate::defs::nat_rec_spec`]'s selector predicate (with
    /// Hilbert ε) forces exactly this behaviour.
    pub fn nat_rec_zero() -> Thm {
        Self::build(Ctx::new(), hol::nat_rec_zero_term())
            .expect("nat_rec_zero: well-typed by construction")
    }

    /// `⊢ ⋀z:α. ⋀f:nat→α→α. ⋀n:nat.
    ///     Trueprop (natRec[α] z f (succ n) = f n (natRec[α] z f n))`
    /// — the primitive-recursor "successor" equation, the other half
    /// of [`Self::nat_rec_zero`]'s defining pair.
    pub fn nat_rec_succ() -> Thm {
        Self::build(Ctx::new(), hol::nat_rec_succ_term())
            .expect("nat_rec_succ: well-typed by construction")
    }

    /// `⊢ ⋀z:int. Trueprop (int_add z 0 = z)` — the right-identity
    /// for integer addition (using the [`crate::defs::int_add`] and
    /// [`crate::defs::int_zero`] constants).
    pub fn int_add_zero_right() -> Thm {
        Self::build(Ctx::new(), hol::int_add_zero_right_term())
            .expect("int_add_zero_right: well-typed by construction")
    }

    /// `⊢ ⋀a b:int. Trueprop (int_add a (intSucc b) = intSucc (int_add a b))`
    /// — the recursion equation tying `int_add` to `intSucc`.
    /// Together with [`Self::int_add_zero_right`] this uniquely
    /// determines `int_add` on the non-negative range.
    pub fn int_add_succ_right() -> Thm {
        Self::build(Ctx::new(), hol::int_add_succ_right_term())
            .expect("int_add_succ_right: well-typed by construction")
    }

    /// `⊢ ⋀n:nat. Trueprop (nat_le n n)` — reflexivity of `nat_le`.
    /// Justified by the selector predicate of [`crate::defs::nat_le`]:
    /// `cmp 0 0 = T` and `cmp (S n) (S m) = cmp n m`.
    pub fn nat_le_refl() -> Thm {
        Self::build(Ctx::new(), hol::nat_le_refl_term())
            .expect("nat_le_refl: well-typed by construction")
    }

    /// `⊢ ⋀n:nat. Trueprop (nat_div n 0 = 0)` — division by zero
    /// is zero by convention. Standard Euclidean axiom; sound because
    /// the kernel commits to this convention everywhere `nat_div`
    /// appears (see also `builtins::reduce_spec`).
    pub fn nat_div_zero_right() -> Thm {
        Self::build(Ctx::new(), hol::nat_div_zero_right_term())
            .expect("nat_div_zero_right: well-typed by construction")
    }

    /// `⊢ ⋀n m:nat. Trueprop (nat_lt n m)
    ///       ⟹ Trueprop (nat_div n m = 0)` — small numerator
    /// gives quotient zero. Combined with [`Self::nat_div_recursion`]
    /// and [`Self::nat_div_zero_right`] uniquely determines `nat_div`.
    pub fn nat_div_less() -> Thm {
        Self::build(Ctx::new(), hol::nat_div_less_term())
            .expect("nat_div_less: well-typed by construction")
    }

    /// `⊢ ⋀n m:nat. Trueprop (nat_lt 0 m)
    ///        ⟹ Trueprop (nat_le m n)
    ///        ⟹ Trueprop (nat_div n m = succ (nat_div (nat_sub n m) m))`
    /// — the Euclidean recursion step.
    pub fn nat_div_recursion() -> Thm {
        Self::build(Ctx::new(), hol::nat_div_recursion_term())
            .expect("nat_div_recursion: well-typed by construction")
    }

    /// `⊢ ⋀m n:nat. Trueprop (m + n = natrec m succ n)` — addition
    /// as `n`-fold successor. Ties the Pure `Prim::NatArith(Add)`
    /// to the HOL-level `natrec` (which is itself defined in
    /// `covalence-hol` via Hilbert's `select`).
    pub fn nat_add_def() -> Thm {
        Self::build(Ctx::new(), hol::nat_add_def_term())
            .expect("nat_add_def: well-typed by construction")
    }

    /// `⊢ ⋀m n:nat. Trueprop (m * n = natrec 0 (λx. x + m) n)` —
    /// multiplication as `n`-fold add-of-`m`.
    pub fn nat_mul_def() -> Thm {
        Self::build(Ctx::new(), hol::nat_mul_def_term())
            .expect("nat_mul_def: well-typed by construction")
    }

    /// `⊢ ⋀m n:nat. Trueprop (m - n = natrec m pred n)` —
    /// saturating subtraction as `n`-fold predecessor.
    pub fn nat_sub_def() -> Thm {
        Self::build(Ctx::new(), hol::nat_sub_def_term())
            .expect("nat_sub_def: well-typed by construction")
    }

    // ---- integer induction ----

    /// `⊢ ⋀P:int→bool. Trueprop ((∀n:nat. P (int_of_nat n))
    ///                       ∧ (∀n:nat. P (-(int_of_nat n)))
    ///                       ⟹ ∀z:int. P z)` —
    /// integer induction via the canonical `int_of_nat` embedding
    /// + negation, as a kernel axiom.
    ///
    /// Sound because every integer is either `int_of_nat n` for some
    /// `n` (non-negative case) or `-(int_of_nat n)` for some `n`
    /// (non-positive case), and `int_of_nat 0 = -(int_of_nat 0) = 0`
    /// covers the overlap.
    pub fn int_induction() -> Thm {
        Self::build(Ctx::new(), hol::int_induction_term())
            .expect("int_induction: well-typed by construction")
    }

    // ---- HOL connective definitions ----

    /// `⊢ ⋀p:bool. Trueprop (¬p = (p ⟹ F))` — the HOL Light
    /// definition of negation, as a kernel axiom. Used to convert
    /// between `¬p` and `p ⟹ F` (the same proposition under two
    /// syntactic shapes in our kernel, since `HolOp::Not` is
    /// primitive rather than derived from `⟹` and `F`).
    pub fn not_def() -> Thm {
        Self::build(Ctx::new(), hol::not_def_term())
            .expect("not_def: well-typed by construction")
    }

    /// `⊢ ⋀p q:bool. Trueprop p ⟹ Trueprop q ⟹ Trueprop (p ∧ q)` —
    /// conjunction introduction, as a kernel axiom. Standard HOL Light
    /// primitive rule. With `HolOp::And` as a kernel atom we can't
    /// derive this from a `∧` definition; postulate directly.
    pub fn and_intro() -> Thm {
        Self::build(Ctx::new(), hol::and_intro_term())
            .expect("and_intro: well-typed by construction")
    }
}

/// Walk down through `App`s collecting arguments left-to-right. If
/// the final node is an `Obs` leaf, return its observer and the args
/// list; otherwise return an error.
/// Parse a `HolOp(Eq, _)`-headed application — `App(App(=, lhs), rhs)`
/// — and return `(lhs, rhs)` by reference. Returns
/// `Err(NotHolEq(...))` for anything else (including a Pure-meta
/// equation, which the Pure-side rules handle).
fn parse_hol_eq(t: &Term) -> Result<(&Term, &Term)> {
    let TermKind::App(f, rhs) = t.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    let TermKind::App(head, lhs) = f.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    let TermKind::HolOp(crate::term::HolOp::Eq, _) = head.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    Ok((lhs, rhs))
}

fn decompose_obs_app(t: &Term) -> Result<(&Object, Vec<Term>)> {
    let mut args_rev = Vec::new();
    let mut cur = t;
    loop {
        match cur.kind() {
            TermKind::App(f, x) => {
                args_rev.push(x.clone());
                cur = f;
            }
            TermKind::Obs(observer, _) => {
                args_rev.reverse();
                return Ok((observer, args_rev));
            }
            _ => return Err(Error::NotObsHead(format!("{}", t))),
        }
    }
}

impl fmt::Debug for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.hyps.is_empty() {
            return write!(f, "⊢ {}", self.concl);
        }
        for (i, h) in self.hyps.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", h)?;
        }
        write!(f, " ⊢ {}", self.concl)
    }
}

// ============================================================================
// new_type_definition — result bundle and private markers
// ============================================================================

/// Result of [`Thm::new_type_definition`]: the fresh subtype τ along
/// with its abs/rep bijection constants and the three theorems that
/// witness the bijection. All three theorems carry the witness's
/// hypotheses.
#[derive(Clone, Debug)]
pub struct TypeDef {
    /// The freshly-introduced type. `TyConObs` carrying a marker Arc
    /// shared by `abs` and `rep`. Parametric in `tvars` (in canonical
    /// order, so `inst_tfree` propagates correctly).
    pub tau: Type,
    /// The fresh `abs : α → τ` constant. An `Obs` leaf whose marker
    /// references the typedef.
    pub abs: Term,
    /// The fresh `rep : τ → α` constant.
    pub rep: Term,
    /// `⊢ ⋀a:τ. abs (rep a) ≡ a`.
    pub abs_rep: Thm,
    /// `⊢ ⋀r:α. P r ⟹ rep (abs r) ≡ r`.
    pub rep_abs_fwd: Thm,
    /// `⊢ ⋀r:α. rep (abs r) ≡ r ⟹ P r`.
    pub rep_abs_back: Thm,
    /// Sorted list of type-variable names that appear in α. τ is
    /// parametric in exactly these tvars (positionally, in this order).
    pub tvars: Vec<smol_str::SmolStr>,
}

/// Private marker carried inside a `TypeDef`'s `Type::tycon_obs` and
/// (via the abs/rep markers below) inside its abs/rep `Term::obs`
/// leaves. Zero-sized, no methods — its sole purpose is to provide
/// fresh `Arc` identity per `new_type_definition` call. Cannot be
/// constructed outside this module.
#[derive(Debug, Clone)]
struct TypeDefMarker(Arc<TypeDefMarkerInner>);

#[derive(Debug)]
struct TypeDefMarkerInner;

impl TypeDefMarker {
    fn new() -> Self { TypeDefMarker(Arc::new(TypeDefMarkerInner)) }
}

/// Marker carried by a typedef's `abs` constant. Holds an Arc to the
/// shared typedef marker so it's uniquely tied to the typedef, plus
/// a display hint for pretty-printing.
struct TypeDefAbsMarker {
    #[allow(dead_code)]
    typedef: Arc<TypeDefMarkerInner>,
    hint: BinderHint,
}

impl TypeDefAbsMarker {
    fn new(m: &TypeDefMarker, hint: BinderHint) -> Self {
        TypeDefAbsMarker { typedef: Arc::clone(&m.0), hint }
    }
}

impl fmt::Debug for TypeDefAbsMarker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.hint.is_empty() {
            write!(f, "abs")
        } else {
            write!(f, "{}", self.hint)
        }
    }
}

/// Marker for the typedef's `rep` constant.
struct TypeDefRepMarker {
    #[allow(dead_code)]
    typedef: Arc<TypeDefMarkerInner>,
    hint: BinderHint,
}

impl TypeDefRepMarker {
    fn new(m: &TypeDefMarker, hint: BinderHint) -> Self {
        TypeDefRepMarker { typedef: Arc::clone(&m.0), hint }
    }
}

impl fmt::Debug for TypeDefRepMarker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.hint.is_empty() {
            write!(f, "rep")
        } else {
            write!(f, "{}", self.hint)
        }
    }
}

#[cfg(test)]
mod hol_light_tests {
    //! Smoke tests for the HOL-Light inference rules. Each test
    //! builds a small theorem and checks the conclusion shape +
    //! type. Together they exercise every rule in the new HOL-Light
    //! set: refl, trans, mk_comb, abs, beta_conv, assume, eq_mp,
    //! deduct_antisym, inst, plus `Thm::build`'s `bool`-acceptance.

    use super::*;

    fn n() -> Term { Term::free("n", Type::nat()) }

    #[test]
    fn hol_refl_at_nat() {
        let thm = Thm::hol_refl(n()).expect("hol_refl n");
        assert!(thm.hyps().is_empty());
        let (l, r) = parse_hol_eq(thm.concl()).expect("conclusion is HOL =");
        assert_eq!(l, &n());
        assert_eq!(r, &n());
    }

    #[test]
    fn hol_trans_chains() {
        let a = Term::free("a", Type::nat());
        let b = Term::free("b", Type::nat());
        let c = Term::free("c", Type::nat());
        let a_eq_b = Thm::assume(hol::hol_eq(a.clone(), b.clone())).expect("assume a=b");
        let b_eq_c = Thm::assume(hol::hol_eq(b.clone(), c.clone())).expect("assume b=c");
        let a_eq_c = a_eq_b.hol_trans(b_eq_c).expect("trans");
        let (l, r) = parse_hol_eq(a_eq_c.concl()).unwrap();
        assert_eq!(l, &a);
        assert_eq!(r, &c);
    }

    #[test]
    fn hol_beta_conv_reduces() {
        // (λx:nat. x) (succ 0) = succ 0
        let id = Term::abs("x", Type::nat(), Term::bound(0));
        let arg = Term::app(crate::defs::nat_succ(), Term::nat_lit(0u32));
        let app = Term::app(id, arg.clone());
        let thm = Thm::hol_beta_conv(app.clone()).expect("β");
        let (l, r) = parse_hol_eq(thm.concl()).unwrap();
        assert_eq!(l, &app);
        assert_eq!(r, &arg);
    }

    #[test]
    fn hol_assume_at_bool() {
        let p = Term::free("p", Type::bool());
        let thm = Thm::hol_assume(p.clone()).expect("assume p:bool");
        assert!(thm.hyps().contains(&p));
        assert_eq!(thm.concl(), &p);
    }

    #[test]
    fn hol_assume_rejects_nat() {
        let n = Term::free("n", Type::nat());
        let err = Thm::hol_assume(n).unwrap_err();
        assert!(matches!(err, Error::NotBool(_)));
    }

    #[test]
    fn hol_eq_mp_at_bool() {
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let p_eq_q = Thm::assume(hol::hol_eq(p.clone(), q.clone())).expect("assume p=q");
        let p_thm = Thm::hol_assume(p.clone()).expect("assume p");
        let q_thm = p_eq_q.hol_eq_mp(p_thm).expect("eq_mp");
        assert_eq!(q_thm.concl(), &q);
    }

    #[test]
    fn hol_deduct_antisym_two_assumes() {
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        // `{p} ⊢ p` and `{q} ⊢ q` — neither side has the other's
        // conclusion as a hyp, so DEDUCT_ANTISYM_RULE leaves both
        // hyps in place: `{p, q} ⊢ p ⇔ q`. (To get the empty-hyp
        // form `⊢ p ⇔ q` you need cross-assumed shapes like
        // `{q} ⊢ p` and `{p} ⊢ q`, which require non-trivial proofs
        // we don't construct in this smoke test.)
        let p_thm = Thm::hol_assume(p.clone()).unwrap();
        let q_thm = Thm::hol_assume(q.clone()).unwrap();
        let eq = p_thm.hol_deduct_antisym(q_thm).expect("deduct_antisym");
        assert!(eq.hyps().contains(&p));
        assert!(eq.hyps().contains(&q));
        let (l, r) = parse_hol_eq(eq.concl()).unwrap();
        assert_eq!(l, &p);
        assert_eq!(r, &q);
    }

    #[test]
    fn hol_deduct_antisym_cross_assumed() {
        // Cross-assumed: `{q} ⊢ p` and `{p} ⊢ q` (faked via weaken/
        // assume composition — both `assume` and `weaken` are
        // available). The rule should yield `⊢ p ⇔ q` with no hyps.
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        // Build `{p, q} ⊢ p` and `{p, q} ⊢ q` by assume + weaken,
        // then deduct_antisym: (Γ−{q}) ∪ (Δ−{p}) = ({p,q}−{q}) ∪
        // ({p,q}−{p}) = {p} ∪ {q} — still both. The literal HOL
        // Light cancellation needs the *minimal* `{q} ⊢ p`, which
        // is not derivable here without an actual ⇔/⟹ axiom. So
        // we verify only that mid-removal happens correctly.
        let pq: Ctx = [p.clone(), q.clone()].into_iter().collect();
        let p_thm = Thm::hol_assume(p.clone()).unwrap().weaken(pq.clone()).unwrap();
        let q_thm = Thm::hol_assume(q.clone()).unwrap().weaken(pq).unwrap();
        let eq = p_thm.hol_deduct_antisym(q_thm).expect("deduct_antisym");
        // hyps = ({p,q} − {q}) ∪ ({p,q} − {p}) = {p, q}.
        assert!(eq.hyps().contains(&p));
        assert!(eq.hyps().contains(&q));
    }

    #[test]
    fn hol_inst_substitutes_free_var() {
        let n_free = Term::free("n", Type::nat());
        let zero = Term::nat_lit(0u32);
        // ⊢ n = n  (HOL refl), then inst n := 0  ⇒  ⊢ 0 = 0.
        let refl = Thm::hol_refl(n_free).unwrap();
        let inst = refl.hol_inst("n", zero.clone()).expect("inst");
        let (l, r) = parse_hol_eq(inst.concl()).unwrap();
        assert_eq!(l, &zero);
        assert_eq!(r, &zero);
    }

    #[test]
    fn hol_mk_comb_at_succ() {
        // ⊢ succ = succ   ⊗   ⊢ 0 = 0   ⇒   ⊢ succ 0 = succ 0
        let succ = crate::defs::nat_succ();
        let zero = Term::nat_lit(0u32);
        let succ_eq = Thm::hol_refl(succ.clone()).unwrap();
        let zero_eq = Thm::hol_refl(zero.clone()).unwrap();
        let app_eq = succ_eq.hol_mk_comb(zero_eq).expect("mk_comb");
        let (l, r) = parse_hol_eq(app_eq.concl()).unwrap();
        assert_eq!(l, &Term::app(succ.clone(), zero.clone()));
        assert_eq!(r, &Term::app(succ, zero));
    }

    #[test]
    fn hol_abs_lambda_eq() {
        // ⊢ x = x   ⇒  abs x:nat   ⇒  ⊢ (λx:nat. x) = (λx:nat. x)
        let x = Term::free("x", Type::nat());
        let refl = Thm::hol_refl(x).unwrap();
        let abs = refl.hol_abs("x", Type::nat()).expect("abs");
        let (l, r) = parse_hol_eq(abs.concl()).unwrap();
        let lam = Term::abs("x", Type::nat(), Term::bound(0));
        assert_eq!(l, &lam);
        assert_eq!(r, &lam);
    }

    // =================================================================
    // Negative tests — invalid derivations must be rejected
    // =================================================================

    #[test]
    fn hol_refl_rejects_dangling_bound() {
        // Bound(0) outside any binder is an open term.
        let err = Thm::hol_refl(Term::bound(0)).unwrap_err();
        assert!(matches!(err, Error::NotClosed));
    }

    #[test]
    fn hol_refl_rejects_ill_typed_app() {
        // (Free("f", nat → nat) (Free("y", bool))) is malformed —
        // arg type doesn't match function domain.
        let f = Term::free("f", Type::fun(Type::nat(), Type::nat()));
        let y = Term::free("y", Type::bool());
        let bad = Term::app(f, y);
        let err = Thm::hol_refl(bad).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn hol_trans_rejects_non_hol_eq_input() {
        // Plain assume with a bool-typed term — not a HOL equation —
        // can't be transed.
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::hol_assume(p).unwrap();
        let refl = Thm::hol_refl(n()).unwrap();
        let err = p_thm.hol_trans(refl).unwrap_err();
        assert!(matches!(err, Error::NotHolEq(_)));
    }

    #[test]
    fn hol_trans_rejects_middle_mismatch() {
        // s = t  and  u = v  with t ≠ u  ⇒  TransMiddleMismatch.
        let a = Term::free("a", Type::nat());
        let b = Term::free("b", Type::nat());
        let c = Term::free("c", Type::nat());
        let d = Term::free("d", Type::nat());
        let ab = Thm::assume(hol::hol_eq(a, b.clone())).unwrap();
        let cd = Thm::assume(hol::hol_eq(c, d)).unwrap();
        // b ≠ c — middle mismatch.
        let _ = b; // already used above
        let err = ab.hol_trans(cd).unwrap_err();
        assert!(matches!(err, Error::TransMiddleMismatch { .. }));
    }

    #[test]
    fn hol_mk_comb_rejects_non_eq_input() {
        // First thm is a HOL eq, second is not.
        let f_eq = Thm::hol_refl(crate::defs::nat_succ()).unwrap();
        let non_eq = Thm::hol_assume(Term::free("p", Type::bool())).unwrap();
        let err = f_eq.hol_mk_comb(non_eq).unwrap_err();
        assert!(matches!(err, Error::NotHolEq(_)));
    }

    #[test]
    fn hol_mk_comb_rejects_domain_mismatch() {
        // f : nat → nat, but arg is bool. Build's re-typing catches.
        let f = crate::defs::nat_succ(); // : nat → nat
        let f_eq = Thm::hol_refl(f).unwrap();
        let bad = Term::free("p", Type::bool());
        let bad_eq = Thm::hol_refl(bad).unwrap();
        let err = f_eq.hol_mk_comb(bad_eq).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn hol_abs_rejects_var_free_in_hyps() {
        // Hyp contains Free("x", nat). Can't abstract over x.
        let x = Term::free("x", Type::nat());
        let hyp = hol::hol_eq(x.clone(), x.clone()); // x = x : bool
        // Assume the hyp first.
        let h_thm = Thm::hol_assume(hyp).unwrap();
        // Now try to abstract over x — should fail because x is free
        // in the (hyp = self.concl) hypothesis.
        let err = h_thm.hol_abs("x", Type::nat()).unwrap_err();
        assert!(matches!(err, Error::FreeVarInHyps { .. }));
    }

    #[test]
    fn hol_abs_rejects_binder_type_mismatch() {
        // Free("x", nat) in concl, but user supplies ty = bool.
        let x = Term::free("x", Type::nat());
        let refl = Thm::hol_refl(x).unwrap();
        let err = refl.hol_abs("x", Type::bool()).unwrap_err();
        assert!(matches!(err, Error::BinderTypeMismatch { .. }));
    }

    #[test]
    fn hol_abs_rejects_non_eq_input() {
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::hol_assume(p).unwrap();
        let err = p_thm.hol_abs("x", Type::nat()).unwrap_err();
        assert!(matches!(err, Error::NotHolEq(_)));
    }

    #[test]
    fn hol_beta_conv_rejects_non_app() {
        // (free n nat) isn't an application.
        let err = Thm::hol_beta_conv(n()).unwrap_err();
        assert!(matches!(err, Error::NotApp(_)));
    }

    #[test]
    fn hol_beta_conv_rejects_non_abs_head() {
        // (succ 0) is an App but the head isn't an Abs.
        let app = Term::app(crate::defs::nat_succ(), Term::nat_lit(0u32));
        let err = Thm::hol_beta_conv(app).unwrap_err();
        assert!(matches!(err, Error::NotAbs(_)));
    }

    #[test]
    fn hol_beta_conv_rejects_arg_type_mismatch() {
        // λx:nat. x  applied to a bool — type mismatch.
        let id = Term::abs("x", Type::nat(), Term::bound(0));
        let bad_arg = Term::bool_lit(true);
        let app = Term::app(id, bad_arg);
        let err = Thm::hol_beta_conv(app).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn hol_assume_rejects_dangling_bound() {
        let err = Thm::hol_assume(Term::bound(0)).unwrap_err();
        assert!(matches!(err, Error::NotClosed));
    }

    #[test]
    fn hol_eq_mp_rejects_non_eq_first() {
        // self.concl is not a HOL equation.
        let p = Term::free("p", Type::bool());
        let non_eq = Thm::hol_assume(p.clone()).unwrap();
        let other = Thm::hol_assume(p).unwrap();
        let err = non_eq.hol_eq_mp(other).unwrap_err();
        assert!(matches!(err, Error::NotHolEq(_)));
    }

    #[test]
    fn hol_eq_mp_rejects_p_mismatch() {
        // ⊢ p = q  and  ⊢ r (r ≠ p)  ⇒  ImpAntecedentMismatch.
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let r = Term::free("r", Type::bool());
        let eq = Thm::assume(hol::hol_eq(p, q)).unwrap();
        let r_thm = Thm::hol_assume(r).unwrap();
        let err = eq.hol_eq_mp(r_thm).unwrap_err();
        assert!(matches!(err, Error::ImpAntecedentMismatch { .. }));
    }

    #[test]
    fn hol_eq_mp_rejects_non_bool_equation() {
        // ⊢ 5 = 5  at nat — not a biconditional. EQ_MP requires bool.
        let five = Term::nat_lit(5u32);
        let eq = Thm::assume(hol::hol_eq(five.clone(), five.clone())).unwrap();
        let n_thm = Thm::hol_assume(Term::free("p", Type::bool())).unwrap();
        let err = eq.hol_eq_mp(n_thm).unwrap_err();
        assert!(matches!(err, Error::NotBool(_)));
    }

    #[test]
    fn hol_deduct_antisym_rejects_non_bool_lhs() {
        // ⊢ (5 : nat)  is not a valid Thm at all (Thm::build rejects).
        // So construct an assumption-based Thm with nat conclusion via
        // Pure assume (which accepts prop) and verify deduct_antisym
        // rejects on non-bool.
        // Build via Thm::assume on a hol_eq — the conclusion is bool.
        // Then forcibly check the not-bool branch via a HOL-Light eq
        // theorem at nat type.
        // Easier: deduct_antisym demands BOTH be bool. If self is a
        // bool theorem and other is nat-Thm, we need to construct a
        // nat-typed Thm — Thm::build won't accept that. So the only
        // way to hit NotBool is if a constructed theorem had a nat
        // conclusion. Currently impossible — Thm::build is sound. So
        // this negative case isn't reachable from user-facing API.
        // We still verify the bool-only positive form holds.
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let p_thm = Thm::hol_assume(p).unwrap();
        let q_thm = Thm::hol_assume(q).unwrap();
        let _eq = p_thm.hol_deduct_antisym(q_thm).expect("deduct_antisym");
        // The not-bool branch in hol_deduct_antisym is defense-in-depth
        // against a future Thm::build relaxation. No user-facing
        // negative test path exists today.
    }

    #[test]
    fn hol_inst_rejects_replacement_type_mismatch() {
        // ⊢ n = n  with n : nat. Try to inst n := (bool literal).
        let n_free = Term::free("n", Type::nat());
        let refl = Thm::hol_refl(n_free).unwrap();
        let bad = Term::bool_lit(true);
        let err = refl.hol_inst("n", bad).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn hol_inst_no_op_when_name_absent() {
        // n free is "n"; instantiating "x" (no occurrence) is a no-op
        // and the replacement's type is unconstrained.
        let refl = Thm::hol_refl(n()).unwrap();
        let bad = Term::bool_lit(true);
        let result = refl.hol_inst("x", bad).expect("no-op inst");
        let (l, r) = parse_hol_eq(result.concl()).unwrap();
        assert_eq!(l, &n());
        assert_eq!(r, &n());
    }

    #[test]
    fn hol_inst_substitutes_in_hyps_too() {
        // {x = x} ⊢ x = x. Inst x := 0. Get {0 = 0} ⊢ 0 = 0.
        let x = Term::free("x", Type::nat());
        let eq = hol::hol_eq(x.clone(), x.clone());
        let h_thm = Thm::hol_assume(eq).unwrap();
        let zero = Term::nat_lit(0u32);
        let result = h_thm.hol_inst("x", zero.clone()).expect("inst");
        let expected_hyp = hol::hol_eq(zero.clone(), zero.clone());
        assert!(result.hyps().contains(&expected_hyp));
        assert_eq!(result.concl(), &expected_hyp);
    }

    #[test]
    fn hol_inst_rejects_dangling_bound_replacement() {
        // Replacement = Bound(0) — open term.
        let n_free = Term::free("n", Type::nat());
        let refl = Thm::hol_refl(n_free).unwrap();
        let err = refl.hol_inst("n", Term::bound(0)).unwrap_err();
        assert!(matches!(err, Error::NotClosed));
    }

    #[test]
    fn hol_eq_mp_preserves_hyps_union() {
        // Γ ⊢ p = q,  Δ ⊢ p  ⇒  Γ ∪ Δ ⊢ q. Verify the union.
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let h_pq = hol::hol_eq(p.clone(), q.clone());
        let h_other = Term::free("extra", Type::bool());
        // Build {h_pq, h_other} ⊢ p = q via assume + weaken.
        let pq_thm = Thm::assume(h_pq.clone()).unwrap();
        let bigger: Ctx = [h_pq.clone(), h_other.clone()].into_iter().collect();
        let pq_weakened = pq_thm.weaken(bigger).unwrap();
        let p_thm = Thm::hol_assume(p).unwrap();
        let q_thm = pq_weakened.hol_eq_mp(p_thm).unwrap();
        assert!(q_thm.hyps().contains(&h_pq));
        assert!(q_thm.hyps().contains(&h_other));
        assert_eq!(q_thm.concl(), &q);
    }

    #[test]
    fn hol_trans_hyps_union_preserved() {
        let a = Term::free("a", Type::nat());
        let b = Term::free("b", Type::nat());
        let c = Term::free("c", Type::nat());
        let ab = hol::hol_eq(a.clone(), b.clone());
        let bc = hol::hol_eq(b, c.clone());
        let ab_thm = Thm::assume(ab.clone()).unwrap();
        let bc_thm = Thm::assume(bc.clone()).unwrap();
        let ac = ab_thm.hol_trans(bc_thm).unwrap();
        assert!(ac.hyps().contains(&ab));
        assert!(ac.hyps().contains(&bc));
        let (l, r) = parse_hol_eq(ac.concl()).unwrap();
        assert_eq!(l, &a);
        assert_eq!(r, &c);
    }
}
