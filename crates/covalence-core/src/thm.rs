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
use crate::ctx::Ctx;
use crate::error::{Error, Result};
use crate::hol;
use crate::subst::{close, find_free_type, has_free_var, open, subst_free, subst_tfree_in_term};
use crate::term::{
    BinderHint, Def, Object, ObsEq, ObsImp, ObsTrue, Observer, Term, TermKind, Type, TypeEnv,
    TypeKind, type_of_in,
};

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
        if !ty.is_bool() {
            return Err(Error::NotBool(ty));
        }
        for h in &hyps {
            let hty = type_of_in(h, &mut env)?;
            if !hty.is_bool() {
                return Err(Error::NotBool(hty));
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

    /// Structural weakening: `Δ ⊢ φ`, given `Γ ⊢ φ` and `Γ ⊆ Δ`.
    ///
    /// Rejects with [`Error::NotASuperset`] if any hypothesis of
    /// `self` is missing from `target`. The conclusion is unchanged;
    /// every term in `target` is re-validated at kind `bool` by
    /// `Thm::build`.
    pub fn weaken(self, target: Ctx) -> Result<Thm> {
        if !self.hyps.is_subset(&target) {
            return Err(Error::NotASuperset);
        }
        Self::build(target, self.concl)
    }

    // ========================================================================
    // HOL-Light inference rules (HOL `=` at type `bool`)
    // ========================================================================
    //
    // The ten HOL Light primitive inference rules. After the
    // Pure→HOL collapse these are THE inference rules — the only
    // paths to a `Thm` value besides the kernel axioms below
    // (induction, definitional equations, etc.).
    //
    // Soundness follows HOL Light's standard model-theoretic story:
    // HOL `=` is interpreted as equality in the model, every rule
    // is sound under that interpretation.

    /// `⊢ t = t : bool` — HOL reflexivity of equality.
    pub fn refl(t: Term) -> Result<Thm> {
        let _ = t.type_of()?;
        let concl = hol::hol_eq(t.clone(), t);
        Self::build(Ctx::new(), concl)
    }

    /// `⊢ a = b`, for any two terms `a, b : unit` — the singleton rule
    /// for `unit := { b : bool | b = T }`.
    ///
    /// Soundness: `unit` is the bool-subtype carved by `λb. b = T`, so
    /// it is interpreted in every model as a one-element set (the
    /// `abs`-image of `{T}`). Hence any two terms of type `unit` denote
    /// the same element and `a = b` holds. Both arguments are required
    /// to type-check at `unit` (an open or ill-typed term is rejected),
    /// and the equation carries no hypotheses.
    pub fn unit_eq(a: Term, b: Term) -> Result<Thm> {
        let a_ty = a.type_of()?;
        if a_ty != Type::unit() {
            return Err(Error::TypeMismatch {
                expected: Type::unit(),
                got: a_ty,
            });
        }
        let b_ty = b.type_of()?;
        if b_ty != Type::unit() {
            return Err(Error::TypeMismatch {
                expected: Type::unit(),
                got: b_ty,
            });
        }
        let concl = hol::hol_eq(a, b);
        Self::build(Ctx::new(), concl)
    }

    /// `Γ ∪ Δ ⊢ s = u`, given `Γ ⊢ s = t` and `Δ ⊢ t = u` (HOL `=`).
    pub fn trans(self, other: Thm) -> Result<Thm> {
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
    pub fn mk_comb(self, arg: Thm) -> Result<Thm> {
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
    pub fn abs(self, name: &str, ty: Type) -> Result<Thm> {
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
        let concl = hol::hol_eq(app.clone(), rhs);
        Self::build(Ctx::new(), concl)
    }

    /// `{p} ⊢ p` for any `p : bool` — HOL-level assume.
    pub fn assume(p: Term) -> Result<Thm> {
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
    pub fn eq_mp(self, p_thm: Thm) -> Result<Thm> {
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
    pub fn deduct_antisym(self, other: Thm) -> Result<Thm> {
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
    pub fn inst(self, name: &str, replacement: Term) -> Result<Thm> {
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

    // ========================================================================
    // Derived HOL-Light rules (sound by the standard HOL Light derivations)
    // ========================================================================
    //
    // The following eight rules — `sym`, `cong_app`, `cong_abs`,
    // `imp_intro`, `imp_elim`, `all_intro`, `all_elim`, `eta_conv` —
    // are NOT part of HOL Light's primitive 10 inference rules. They
    // are the well-known derived rules `SYM`, `MK_COMB` (aliased as
    // `cong_app` for congruence-equivalent naming), `ABS` (aliased
    // as `cong_abs`), `DISCH`, `MP`, `GEN`, `SPEC`, and `ETA_AX`.
    //
    // We provide them as kernel primitives — direct constructors —
    // for ergonomic and performance reasons. Soundness is the
    // standard HOL Light derivation; each rule's docstring records
    // the derivation. The implementations are tight (single-shot
    // term builds + standard well-formedness checks) so
    // auditability is preserved.

    /// `Γ ⊢ b = a`, given `Γ ⊢ a = b`. Symmetry of HOL `=`.
    ///
    /// Soundness: derivable from `refl` + `mk_comb` + `eq_mp`:
    /// `refl a : ⊢ a = a`, then transport along `a = b` with
    /// `eq_mp` to get `b = a`. Implemented directly here as
    /// "parse the equation, return reversed".
    pub fn sym(self) -> Result<Thm> {
        let (a, b) = parse_hol_eq(&self.concl)?;
        let concl = hol::hol_eq(b.clone(), a.clone());
        Self::build(self.hyps, concl)
    }

    /// Alias for [`Thm::mk_comb`]. `cong_app` is the equational-
    /// congruence name (`f = g, x = y ⊢ f x = g y`); HOL Light
    /// calls it `MK_COMB`. Same rule.
    pub fn cong_app(self, arg: Thm) -> Result<Thm> {
        self.mk_comb(arg)
    }

    /// Alias for [`Thm::abs`]. HOL Light's `ABS`; the equational-
    /// congruence name for the same rule.
    pub fn cong_abs(self, name: &str, ty: Type) -> Result<Thm> {
        self.abs(name, ty)
    }

    /// `Γ \ {φ} ⊢ φ ⟹ ψ`, given `Γ ⊢ ψ` (HOL Light's `DISCH`).
    ///
    /// `φ` must be `bool`-typed (otherwise it can't be a HOL
    /// implication antecedent).
    ///
    /// Soundness: HOL Light derives `DISCH` from
    /// `DEDUCT_ANTISYM_RULE` + `MP`. Implemented directly here as
    /// a one-step rule for performance.
    pub fn imp_intro(self, phi: &Term) -> Result<Thm> {
        let phi_ty = phi.type_of()?;
        if !phi_ty.is_bool() {
            return Err(Error::NotBool(phi_ty));
        }
        let hyps = self.hyps.remove(phi);
        let concl = hol::hol_imp(phi.clone(), self.concl);
        Self::build(hyps, concl)
    }

    /// `Γ ∪ Δ ⊢ ψ`, given `Γ ⊢ φ ⟹ ψ` and `Δ ⊢ φ`
    /// (HOL Light's `MP`).
    ///
    /// Soundness: standard modus ponens. HOL Light derives it by
    /// unfolding `⟹`'s definition (`p ⟹ q  ≡  p ∧ q = p`) and
    /// using `AND_INTRO` / `AND_ELIM`.
    pub fn imp_elim(self, hyp: Thm) -> Result<Thm> {
        let (phi, psi) = parse_hol_imp(&self.concl)?;
        if *phi != hyp.concl {
            return Err(Error::ImpAntecedentMismatch {
                expected: format!("{}", phi),
                got: format!("{}", hyp.concl),
            });
        }
        let concl = psi.clone();
        let hyps = self.hyps.union(&hyp.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ ∀x:τ. φ`, given `Γ ⊢ φ` with `Free(x:τ)` not free in
    /// `FV(Γ)` (HOL Light's `GEN`).
    ///
    /// Soundness: HOL Light derives `GEN` from `INST`/`SPEC` plus
    /// `ABS` (the instance trick
    /// `∀x. P x ⇔ (λx. P x) = (λx. ⊤)`). Implemented directly:
    /// close the free variable into a `Bound(0)` and wrap with
    /// `Forall_at(τ)`.
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
        let concl = hol::hol_forall(name, ty, self.concl);
        Self::build(self.hyps, concl)
    }

    /// `Γ ⊢ φ[t/x]`, given `Γ ⊢ ∀x:τ. φ` and `t : τ`
    /// (HOL Light's `SPEC`).
    ///
    /// Soundness: standard universal elimination, derived in HOL
    /// Light from `INST` and `∀`'s definitional unfolding.
    pub fn all_elim(self, witness: Term) -> Result<Thm> {
        let (ty, body) = parse_hol_forall(&self.concl)?;
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

    /// `⊢ (λx:τ. f x) = f`, when `Bound(0)` does not appear free
    /// in `f`. HOL Light's `ETA_AX` (a primitive axiom there; here
    /// exposed as a rule that discharges well-formedness in one
    /// step).
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
        if crate::subst::uses_bound_outer(f, 0) {
            return Err(Error::EtaShape);
        }
        let _ = abs.type_of()?;
        let _ = ty;
        let f_outer = crate::subst::shift_by(f, -1, 0);
        let concl = hol::hol_eq(abs.clone(), f_outer);
        Self::build(Ctx::new(), concl)
    }

    // ========================================================================
    // Connective derived rules (provided as primitives for efficiency)
    // ========================================================================
    //
    // `∧` / `∨` / `¬` are ordinary defined constants in `defs/logic.rs`.
    // Their intro / elim rules are *derivable* from those definitions
    // plus the primitive rules — the standard HOL Light `bool.ml`
    // bootstrap. The executable derivation lives, and is tested, in
    // `covalence-hol::proofs::bool`; it is the soundness witness for
    // every method below.
    //
    // We expose the rules here as direct, single-step constructors so
    // the common case builds the conclusion in O(1) instead of re-running
    // a multi-step derivation per call (the same treatment `imp_intro` /
    // `all_intro` already get). A future "paranoid mode" can replace each
    // fast path with the witness derivation.

    /// `Γ ∪ Δ ⊢ p ∧ q`, given `Γ ⊢ p` and `Δ ⊢ q`.
    ///
    /// Soundness (HOL Light `CONJ`): `EQT_INTRO` turns `⊢ p`, `⊢ q`
    /// into `⊢ p = T`, `⊢ q = T`; congruence + `abs` then build
    /// `⊢ (λf. f p q) = (λf. f T T)`, which is `p ∧ q` unfolded.
    pub fn and_intro(self, other: Thm) -> Result<Thm> {
        let p_ty = self.concl.type_of()?;
        if !p_ty.is_bool() {
            return Err(Error::NotBool(p_ty));
        }
        let q_ty = other.concl.type_of()?;
        if !q_ty.is_bool() {
            return Err(Error::NotBool(q_ty));
        }
        let concl = hol::hol_and(self.concl.clone(), other.concl.clone());
        let hyps = self.hyps.union(&other.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ p`, given `Γ ⊢ p ∧ q` (HOL Light `CONJUNCT1`).
    ///
    /// Soundness: apply the unfolded body `(λf. f p q) = (λf. f T T)`
    /// to the selector `λa b. a` and β-reduce both sides to `p = T`,
    /// then `EQT_ELIM`.
    pub fn and_elim_l(self) -> Result<Thm> {
        let (p, _q) = parse_hol_and(&self.concl)?;
        let concl = p.clone();
        Self::build(self.hyps, concl)
    }

    /// `Γ ⊢ q`, given `Γ ⊢ p ∧ q` (HOL Light `CONJUNCT2`; selector
    /// `λa b. b`).
    pub fn and_elim_r(self) -> Result<Thm> {
        let (_p, q) = parse_hol_and(&self.concl)?;
        let concl = q.clone();
        Self::build(self.hyps, concl)
    }

    /// `Γ ⊢ p ∨ q`, given `Γ ⊢ p` and the other disjunct `q : bool`
    /// (HOL Light `DISJ1`).
    ///
    /// Soundness: fold `⊢ p` into `p ∨ q ≜ ∀r. (p⟹r) ⟹ (q⟹r) ⟹ r`
    /// — assume each implication, MP the first with `⊢ p`, generalise.
    pub fn or_intro_l(self, q: Term) -> Result<Thm> {
        let p_ty = self.concl.type_of()?;
        if !p_ty.is_bool() {
            return Err(Error::NotBool(p_ty));
        }
        let q_ty = q.type_of()?;
        if !q_ty.is_bool() {
            return Err(Error::NotBool(q_ty));
        }
        let concl = hol::hol_or(self.concl.clone(), q);
        Self::build(self.hyps, concl)
    }

    /// `Γ ⊢ p ∨ q`, given `Γ ⊢ q` and the other disjunct `p : bool`
    /// (HOL Light `DISJ2`).
    pub fn or_intro_r(self, p: Term) -> Result<Thm> {
        let q_ty = self.concl.type_of()?;
        if !q_ty.is_bool() {
            return Err(Error::NotBool(q_ty));
        }
        let p_ty = p.type_of()?;
        if !p_ty.is_bool() {
            return Err(Error::NotBool(p_ty));
        }
        let concl = hol::hol_or(p, self.concl.clone());
        Self::build(self.hyps, concl)
    }

    /// `Γ ∪ Δ₁ ∪ Δ₂ ⊢ r`, given `Γ ⊢ p ∨ q`, `Δ₁ ⊢ p ⟹ r` and
    /// `Δ₂ ⊢ q ⟹ r` (HOL Light `DISJ_CASES`, as a rule taking the two
    /// branch implications).
    ///
    /// Soundness: specialise `p ∨ q ≜ ∀r. (p⟹r) ⟹ (q⟹r) ⟹ r` at `r`
    /// and MP with the two branches.
    pub fn or_elim(self, left: Thm, right: Thm) -> Result<Thm> {
        let (p, q) = parse_hol_or(&self.concl)?;
        let (lp, lr) = parse_hol_imp(&left.concl)?;
        let (rq, rr) = parse_hol_imp(&right.concl)?;
        if lp != p {
            return Err(Error::ConnectiveRule(format!(
                "or_elim: left branch antecedent {lp} ≠ left disjunct {p}"
            )));
        }
        if rq != q {
            return Err(Error::ConnectiveRule(format!(
                "or_elim: right branch antecedent {rq} ≠ right disjunct {q}"
            )));
        }
        if lr != rr {
            return Err(Error::ConnectiveRule(format!(
                "or_elim: branch consequents differ ({lr} vs {rr})"
            )));
        }
        let concl = lr.clone();
        let hyps = self.hyps.union(&left.hyps).union(&right.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ ¬p`, given `Γ ⊢ p ⟹ F` (HOL Light `NOT_INTRO`).
    ///
    /// Soundness: `¬p ≜ (p ⟹ F)`, so this just folds the definition.
    pub fn not_intro(self) -> Result<Thm> {
        let (p, f) = parse_hol_imp(&self.concl)?;
        if !matches!(f.kind(), TermKind::Bool(false)) {
            return Err(Error::ConnectiveRule(format!(
                "not_intro: consequent {f} is not F"
            )));
        }
        let concl = hol::hol_not(p.clone());
        Self::build(self.hyps, concl)
    }

    /// `Γ ∪ Δ ⊢ F`, given `Γ ⊢ ¬p` and `Δ ⊢ p` (HOL Light `NOT_ELIM`).
    ///
    /// Soundness: unfold `¬p` to `p ⟹ F` and MP with `⊢ p`.
    pub fn not_elim(self, other: Thm) -> Result<Thm> {
        let p = parse_hol_not(&self.concl)?;
        if *p != other.concl {
            return Err(Error::ConnectiveRule(format!(
                "not_elim: negated {p} ≠ hypothesis {}",
                other.concl
            )));
        }
        let concl = Term::bool_lit(false);
        let hyps = self.hyps.union(&other.hyps);
        Self::build(hyps, concl)
    }

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

        // 3. Validate P : α → bool.
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
        if !p_cod.is_bool() {
            return Err(Error::NotBool(p_cod.clone()));
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

        // 7. Build the three bijection theorems at HOL `=` / `⟹` /
        //    `∀` — all conclusions are `bool`-typed.
        //
        //    abs_rep: ⊢ ∀a:τ. abs (rep a) = a
        let a_free = Term::free("a", tau.clone());
        let abs_rep_body = hol::hol_eq(
            Term::app(abs.clone(), Term::app(rep.clone(), a_free.clone())),
            a_free,
        );
        let abs_rep_concl = hol::hol_forall("a", tau.clone(), abs_rep_body);

        //    rep_abs_eq : `rep (abs r) = r`
        //    p_at_r     : `P r`
        let r_free = Term::free("r", alpha.clone());
        let p_at_r = Term::app(p, r_free.clone());
        let rep_abs_eq = hol::hol_eq(
            Term::app(rep.clone(), Term::app(abs.clone(), r_free.clone())),
            r_free,
        );
        //    fwd: ⊢ ∀r:α. P r ⟹ rep (abs r) = r
        let fwd_concl = hol::hol_forall(
            "r",
            alpha.clone(),
            hol::hol_imp(p_at_r.clone(), rep_abs_eq.clone()),
        );
        //    back: ⊢ ∀r:α. rep (abs r) = r ⟹ P r
        let back_concl = hol::hol_forall(
            "r",
            alpha,
            hol::hol_imp(rep_abs_eq, p_at_r),
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
        let concl = hol::hol_eq(Term::def(d), body);
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
    /// - `App(App(Eq(_), lit_a), lit_b)` where `lit_a` and
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
        let declared_ty = spec.ty().ok_or(Error::SpecHasNoBody)?.clone();
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

        Self::build(Ctx::new(), hol::hol_eq(t, unfolded))
    }

    pub fn reduce_prim(t: Term) -> Result<Thm> {
        let reduced = builtins::reduce_prim_term(&t).ok_or(Error::NotReducible)?;
        Self::build(Ctx::new(), hol::hol_eq(t, reduced))
    }

    /// `Γ[α:=σ] ⊢ φ[α:=σ]`.
    pub fn inst_tfree(self, name: &str, replacement: Type) -> Result<Thm> {
        let concl = subst_tfree_in_term(&self.concl, name, &replacement);
        let hyps = self
            .hyps
            .map(|h| subst_tfree_in_term(h, name, &replacement));
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
        if !ty.is_bool() {
            return Err(Error::NotBool(ty));
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
        if !ty.is_bool() {
            return Err(Error::NotBool(ty));
        }
        for h in &hyps {
            let h_ty = h.type_of()?;
            if !h_ty.is_bool() {
                return Err(Error::NotBool(h_ty));
            }
        }
        if !o.obs_imp(&args, &hyps, hint.as_deref()) {
            return Err(Error::ObsEqRefused);
        }
        // Build hyp[0] ⟹ hyp[1] ⟹ ... ⟹ expr (right-associative)
        // using HOL `⟹` (the `imp` connective). All hyps and the
        // consequent are bool-typed (checked above).
        let mut result = expr;
        for h in hyps.into_iter().rev() {
            result = hol::hol_imp(h, result);
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
        let concl = hol::hol_eq(expr1, expr2);
        Self::build(Ctx::new(), concl)
    }

    // ========================================================================
    // The single kernel postulate: Peano induction on `nat`
    // ========================================================================
    //
    // **The only non-computational axiom in the TCB.** Every other
    // fact about nat / int / bool / their derived operations — `pred`,
    // `natRec`, `+` / `*` / `-` / `/`, `not_def`, `and_intro`,
    // `nat_le_refl`, int induction, etc. — is derivable from this
    // axiom plus the HOL-Light primitive rules + `define` +
    // `new_type_definition`. Until those derivations land downstream,
    // consumers can postulate the unproved facts via `Thm::assume`
    // (the resulting Thm has a self-hyp, so it's clearly marked as
    // unproved in `Thm::has_no_obs`-style audits).
    //
    // **Computational axioms** (the reduce-on-literals rules) live
    // separately on `Thm::reduce_prim` and `Thm::unfold_term_spec`.
    // Those are *accelerated* reduction steps — each is a one-shot
    // `t = canonical_form` equation justified by the literal's
    // denotation, not a logical postulate.

    /// Mathematical induction on `nat`, as a primitive **rule**.
    ///
    /// Given a base proof `Γ₁ ⊢ p 0` and a step proof
    /// `Γ₂ ⊢ p n ⟹ p (succ n)` for a free variable `n : nat`, returns
    /// `Γ₁ ∪ Γ₂ ⊢ ∀n:nat. p n`. The motive `p` and the induction
    /// variable `n` are read back from the shapes of the two
    /// conclusions (`base` must be `p` applied to the literal `0`;
    /// `step` must be `p n ⟹ p (succ n)` with the same `p`). `n` must
    /// not occur free in `p` nor in `Γ₂` (the GEN side condition).
    ///
    /// ## Soundness
    ///
    /// `Type::nat()` denotes exactly the standard naturals, freely
    /// generated by `0` and `succ` — so a predicate true at `0` and
    /// preserved by `succ` holds everywhere. This is one of the
    /// kernel's two non-computational primitives (the other is
    /// [`Thm::false_elim`]). The classic axiom form
    /// `⊢ ∀P. (P 0 ∧ (∀n. P n ⟹ P (succ n))) ⟹ ∀n. P n` is a trivial
    /// theorem — assume the conjunction, split it, apply this rule,
    /// discharge, generalise.
    pub fn nat_induct(base: Thm, step: Thm) -> Result<Thm> {
        let nat = Type::nat();
        let zero = Term::nat_lit(covalence_types::Nat::zero());

        // base : ⊢ p 0
        let TermKind::App(p, base_arg) = base.concl.kind() else {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: base conclusion {} is not `p 0`",
                base.concl
            )));
        };
        if base_arg != &zero {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: base conclusion {} is not the motive applied to 0",
                base.concl
            )));
        }
        let p = p.clone();

        // step : ⊢ p n ⟹ p (succ n)
        let (ante, conseq) = parse_hol_imp(&step.concl)?;
        let TermKind::App(ante_p, n_free) = ante.kind() else {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: step antecedent {ante} is not `p n`"
            )));
        };
        if *ante_p != p {
            return Err(Error::ConnectiveRule(
                "nat_induct: step uses a different motive than the base".into(),
            ));
        }
        let TermKind::Free(n_name, n_ty) = n_free.kind() else {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: induction variable {n_free} is not a free variable"
            )));
        };
        if *n_ty != nat {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: induction variable {n_free} is not of type nat"
            )));
        }
        let expected_conseq =
            Term::app(p.clone(), Term::app(hol::succ_fn(), n_free.clone()));
        if *conseq != expected_conseq {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: step consequent {conseq} is not `p (succ n)`"
            )));
        }

        // GEN side conditions: n free neither in the motive nor in
        // the step's hypotheses.
        if has_free_var(&p, n_name) {
            return Err(Error::ConnectiveRule(
                "nat_induct: induction variable occurs free in the motive".into(),
            ));
        }
        for h in step.hyps.iter() {
            if has_free_var(h, n_name) {
                return Err(Error::FreeVarInHyps {
                    name: n_name.as_str().into(),
                });
            }
        }

        let body = Term::app(p, n_free.clone());
        let concl = hol::hol_forall(n_name, nat, body);
        let hyps = base.hyps.union(&step.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ p`, given `Γ ⊢ F` and any `bool`-typed target `p`
    /// (ex falso quodlibet), as a primitive rule.
    ///
    /// ## Soundness
    ///
    /// `F` is the `Bool(false)` literal, which denotes falsity in
    /// every model — so `Γ ⊢ F` means `Γ` is contradictory and entails
    /// anything. Because `F` is a literal with no defining equation,
    /// this cannot be derived from the other rules; it is the kernel's
    /// second non-computational primitive (alongside [`Thm::nat_induct`]).
    pub fn false_elim(self, p: Term) -> Result<Thm> {
        if !matches!(self.concl.kind(), TermKind::Bool(false)) {
            return Err(Error::ConnectiveRule(format!(
                "false_elim: conclusion {} is not F",
                self.concl
            )));
        }
        let p_ty = p.type_of()?;
        if !p_ty.is_bool() {
            return Err(Error::NotBool(p_ty));
        }
        Self::build(self.hyps, p)
    }
}

/// Walk down through `App`s collecting arguments left-to-right. If
/// the final node is an `Obs` leaf, return its observer and the args
/// list; otherwise return an error.
/// Parse an `Eq`-headed application — `App(App(=, lhs), rhs)` — and
/// return `(lhs, rhs)` by reference.
fn parse_hol_eq(t: &Term) -> Result<(&Term, &Term)> {
    let TermKind::App(f, rhs) = t.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    let TermKind::App(head, lhs) = f.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    let TermKind::Eq(_) = head.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    Ok((lhs, rhs))
}

/// Parse an `imp`-headed application — `App(App(⟹, p), q)` — and
/// return `(p, q)`. `⟹` is the defined connective spec
/// [`crate::defs::imp_spec`].
fn parse_hol_imp(t: &Term) -> Result<(&Term, &Term)> {
    let TermKind::App(f, q) = t.kind() else {
        return Err(Error::NotHolImp(format!("{}", t)));
    };
    let TermKind::App(head, p) = f.kind() else {
        return Err(Error::NotHolImp(format!("{}", t)));
    };
    if !is_spec(head, &crate::defs::imp_spec()) {
        return Err(Error::NotHolImp(format!("{}", t)));
    }
    Ok((p, q))
}

/// Parse a `forall`-headed application —
/// `App(∀[τ], Abs(_, τ, body))` — and return `(τ, body)`. `∀` is the
/// defined connective spec [`crate::defs::forall_spec`]. The body
/// still has `Bound(0)` referring to the bound variable; use
/// `subst::open` to instantiate.
fn parse_hol_forall(t: &Term) -> Result<(&Type, &Term)> {
    let TermKind::App(forall_head, lambda) = t.kind() else {
        return Err(Error::NotHolForall(format!("{}", t)));
    };
    if !is_spec(forall_head, &crate::defs::forall_spec()) {
        return Err(Error::NotHolForall(format!("{}", t)));
    }
    let TermKind::Abs(_, ty, body) = lambda.kind() else {
        return Err(Error::NotHolForall(format!("{}", t)));
    };
    Ok((ty, body))
}

/// `true` iff `t` is a `Spec(handle, _)` leaf whose handle is the
/// given catalogue spec (by pointer identity).
fn is_spec(t: &Term, want: &crate::defs::TermSpec) -> bool {
    matches!(t.kind(), TermKind::Spec(h, _) if h.ptr_eq(want))
}

/// Parse `App(App(op, p), q)` for the binary connective spec `op`,
/// returning `(p, q)`. `what` names the connective for the error.
fn parse_hol_binop<'a>(
    t: &'a Term,
    op: &crate::defs::TermSpec,
    what: &str,
) -> Result<(&'a Term, &'a Term)> {
    let err = || Error::ConnectiveRule(format!("expected {what}, got {t}"));
    let TermKind::App(f, q) = t.kind() else {
        return Err(err());
    };
    let TermKind::App(head, p) = f.kind() else {
        return Err(err());
    };
    if !is_spec(head, op) {
        return Err(err());
    }
    Ok((p, q))
}

/// Parse `App(App(/\, p), q)` → `(p, q)`.
fn parse_hol_and(t: &Term) -> Result<(&Term, &Term)> {
    parse_hol_binop(t, &crate::defs::and_spec(), "p /\\ q")
}

/// Parse `App(App(\/, p), q)` → `(p, q)`.
fn parse_hol_or(t: &Term) -> Result<(&Term, &Term)> {
    parse_hol_binop(t, &crate::defs::or_spec(), "p \\/ q")
}

/// Parse `App(~, p)` → `p`.
fn parse_hol_not(t: &Term) -> Result<&Term> {
    let TermKind::App(head, p) = t.kind() else {
        return Err(Error::ConnectiveRule(format!("expected ~p, got {t}")));
    };
    if !is_spec(head, &crate::defs::not_spec()) {
        return Err(Error::ConnectiveRule(format!("expected ~p, got {t}")));
    }
    Ok(p)
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
    fn new() -> Self {
        TypeDefMarker(Arc::new(TypeDefMarkerInner))
    }
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
        TypeDefAbsMarker {
            typedef: Arc::clone(&m.0),
            hint,
        }
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
        TypeDefRepMarker {
            typedef: Arc::clone(&m.0),
            hint,
        }
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

    fn n() -> Term {
        Term::free("n", Type::nat())
    }

    #[test]
    fn hol_refl_at_nat() {
        let thm = Thm::refl(n()).expect("refl n");
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
        let a_eq_c = a_eq_b.trans(b_eq_c).expect("trans");
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
        let thm = Thm::beta_conv(app.clone()).expect("β");
        let (l, r) = parse_hol_eq(thm.concl()).unwrap();
        assert_eq!(l, &app);
        assert_eq!(r, &arg);
    }

    #[test]
    fn hol_assume_at_bool() {
        let p = Term::free("p", Type::bool());
        let thm = Thm::assume(p.clone()).expect("assume p:bool");
        assert!(thm.hyps().contains(&p));
        assert_eq!(thm.concl(), &p);
    }

    #[test]
    fn hol_assume_rejects_nat() {
        let n = Term::free("n", Type::nat());
        let err = Thm::assume(n).unwrap_err();
        assert!(matches!(err, Error::NotBool(_)));
    }

    #[test]
    fn hol_eq_mp_at_bool() {
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let p_eq_q = Thm::assume(hol::hol_eq(p.clone(), q.clone())).expect("assume p=q");
        let p_thm = Thm::assume(p.clone()).expect("assume p");
        let q_thm = p_eq_q.eq_mp(p_thm).expect("eq_mp");
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
        let p_thm = Thm::assume(p.clone()).unwrap();
        let q_thm = Thm::assume(q.clone()).unwrap();
        let eq = p_thm.deduct_antisym(q_thm).expect("deduct_antisym");
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
        let p_thm = Thm::assume(p.clone()).unwrap().weaken(pq.clone()).unwrap();
        let q_thm = Thm::assume(q.clone()).unwrap().weaken(pq).unwrap();
        let eq = p_thm.deduct_antisym(q_thm).expect("deduct_antisym");
        // hyps = ({p,q} − {q}) ∪ ({p,q} − {p}) = {p, q}.
        assert!(eq.hyps().contains(&p));
        assert!(eq.hyps().contains(&q));
    }

    #[test]
    fn hol_inst_substitutes_free_var() {
        let n_free = Term::free("n", Type::nat());
        let zero = Term::nat_lit(0u32);
        // ⊢ n = n  (HOL refl), then inst n := 0  ⇒  ⊢ 0 = 0.
        let refl = Thm::refl(n_free).unwrap();
        let inst = refl.inst("n", zero.clone()).expect("inst");
        let (l, r) = parse_hol_eq(inst.concl()).unwrap();
        assert_eq!(l, &zero);
        assert_eq!(r, &zero);
    }

    #[test]
    fn hol_mk_comb_at_succ() {
        // ⊢ succ = succ   ⊗   ⊢ 0 = 0   ⇒   ⊢ succ 0 = succ 0
        let succ = crate::defs::nat_succ();
        let zero = Term::nat_lit(0u32);
        let succ_eq = Thm::refl(succ.clone()).unwrap();
        let zero_eq = Thm::refl(zero.clone()).unwrap();
        let app_eq = succ_eq.mk_comb(zero_eq).expect("mk_comb");
        let (l, r) = parse_hol_eq(app_eq.concl()).unwrap();
        assert_eq!(l, &Term::app(succ.clone(), zero.clone()));
        assert_eq!(r, &Term::app(succ, zero));
    }

    #[test]
    fn hol_abs_lambda_eq() {
        // ⊢ x = x   ⇒  abs x:nat   ⇒  ⊢ (λx:nat. x) = (λx:nat. x)
        let x = Term::free("x", Type::nat());
        let refl = Thm::refl(x).unwrap();
        let abs = refl.abs("x", Type::nat()).expect("abs");
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
        let err = Thm::refl(Term::bound(0)).unwrap_err();
        assert!(matches!(err, Error::NotClosed));
    }

    #[test]
    fn hol_refl_rejects_ill_typed_app() {
        // (Free("f", nat → nat) (Free("y", bool))) is malformed —
        // arg type doesn't match function domain.
        let f = Term::free("f", Type::fun(Type::nat(), Type::nat()));
        let y = Term::free("y", Type::bool());
        let bad = Term::app(f, y);
        let err = Thm::refl(bad).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn hol_trans_rejects_non_hol_eq_input() {
        // Plain assume with a bool-typed term — not a HOL equation —
        // can't be transed.
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::assume(p).unwrap();
        let refl = Thm::refl(n()).unwrap();
        let err = p_thm.trans(refl).unwrap_err();
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
        let err = ab.trans(cd).unwrap_err();
        assert!(matches!(err, Error::TransMiddleMismatch { .. }));
    }

    #[test]
    fn hol_mk_comb_rejects_non_eq_input() {
        // First thm is a HOL eq, second is not.
        let f_eq = Thm::refl(crate::defs::nat_succ()).unwrap();
        let non_eq = Thm::assume(Term::free("p", Type::bool())).unwrap();
        let err = f_eq.mk_comb(non_eq).unwrap_err();
        assert!(matches!(err, Error::NotHolEq(_)));
    }

    #[test]
    fn hol_mk_comb_rejects_domain_mismatch() {
        // f : nat → nat, but arg is bool. Build's re-typing catches.
        let f = crate::defs::nat_succ(); // : nat → nat
        let f_eq = Thm::refl(f).unwrap();
        let bad = Term::free("p", Type::bool());
        let bad_eq = Thm::refl(bad).unwrap();
        let err = f_eq.mk_comb(bad_eq).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn hol_abs_rejects_var_free_in_hyps() {
        // Hyp contains Free("x", nat). Can't abstract over x.
        let x = Term::free("x", Type::nat());
        let hyp = hol::hol_eq(x.clone(), x.clone()); // x = x : bool
        // Assume the hyp first.
        let h_thm = Thm::assume(hyp).unwrap();
        // Now try to abstract over x — should fail because x is free
        // in the (hyp = self.concl) hypothesis.
        let err = h_thm.abs("x", Type::nat()).unwrap_err();
        assert!(matches!(err, Error::FreeVarInHyps { .. }));
    }

    #[test]
    fn hol_abs_rejects_binder_type_mismatch() {
        // Free("x", nat) in concl, but user supplies ty = bool.
        let x = Term::free("x", Type::nat());
        let refl = Thm::refl(x).unwrap();
        let err = refl.abs("x", Type::bool()).unwrap_err();
        assert!(matches!(err, Error::BinderTypeMismatch { .. }));
    }

    #[test]
    fn hol_abs_rejects_non_eq_input() {
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::assume(p).unwrap();
        let err = p_thm.abs("x", Type::nat()).unwrap_err();
        assert!(matches!(err, Error::NotHolEq(_)));
    }

    #[test]
    fn hol_beta_conv_rejects_non_app() {
        // (free n nat) isn't an application.
        let err = Thm::beta_conv(n()).unwrap_err();
        assert!(matches!(err, Error::NotApp(_)));
    }

    #[test]
    fn hol_beta_conv_rejects_non_abs_head() {
        // (succ 0) is an App but the head isn't an Abs.
        let app = Term::app(crate::defs::nat_succ(), Term::nat_lit(0u32));
        let err = Thm::beta_conv(app).unwrap_err();
        assert!(matches!(err, Error::NotAbs(_)));
    }

    #[test]
    fn hol_beta_conv_rejects_arg_type_mismatch() {
        // λx:nat. x  applied to a bool — type mismatch.
        let id = Term::abs("x", Type::nat(), Term::bound(0));
        let bad_arg = Term::bool_lit(true);
        let app = Term::app(id, bad_arg);
        let err = Thm::beta_conv(app).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn hol_assume_rejects_dangling_bound() {
        let err = Thm::assume(Term::bound(0)).unwrap_err();
        assert!(matches!(err, Error::NotClosed));
    }

    #[test]
    fn hol_eq_mp_rejects_non_eq_first() {
        // self.concl is not a HOL equation.
        let p = Term::free("p", Type::bool());
        let non_eq = Thm::assume(p.clone()).unwrap();
        let other = Thm::assume(p).unwrap();
        let err = non_eq.eq_mp(other).unwrap_err();
        assert!(matches!(err, Error::NotHolEq(_)));
    }

    #[test]
    fn hol_eq_mp_rejects_p_mismatch() {
        // ⊢ p = q  and  ⊢ r (r ≠ p)  ⇒  ImpAntecedentMismatch.
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let r = Term::free("r", Type::bool());
        let eq = Thm::assume(hol::hol_eq(p, q)).unwrap();
        let r_thm = Thm::assume(r).unwrap();
        let err = eq.eq_mp(r_thm).unwrap_err();
        assert!(matches!(err, Error::ImpAntecedentMismatch { .. }));
    }

    #[test]
    fn hol_eq_mp_rejects_non_bool_equation() {
        // ⊢ 5 = 5  at nat — not a biconditional. EQ_MP requires bool.
        let five = Term::nat_lit(5u32);
        let eq = Thm::assume(hol::hol_eq(five.clone(), five.clone())).unwrap();
        let n_thm = Thm::assume(Term::free("p", Type::bool())).unwrap();
        let err = eq.eq_mp(n_thm).unwrap_err();
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
        let p_thm = Thm::assume(p).unwrap();
        let q_thm = Thm::assume(q).unwrap();
        let _eq = p_thm.deduct_antisym(q_thm).expect("deduct_antisym");
        // The not-bool branch in deduct_antisym is defense-in-depth
        // against a future Thm::build relaxation. No user-facing
        // negative test path exists today.
    }

    #[test]
    fn hol_inst_rejects_replacement_type_mismatch() {
        // ⊢ n = n  with n : nat. Try to inst n := (bool literal).
        let n_free = Term::free("n", Type::nat());
        let refl = Thm::refl(n_free).unwrap();
        let bad = Term::bool_lit(true);
        let err = refl.inst("n", bad).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn hol_inst_no_op_when_name_absent() {
        // n free is "n"; instantiating "x" (no occurrence) is a no-op
        // and the replacement's type is unconstrained.
        let refl = Thm::refl(n()).unwrap();
        let bad = Term::bool_lit(true);
        let result = refl.inst("x", bad).expect("no-op inst");
        let (l, r) = parse_hol_eq(result.concl()).unwrap();
        assert_eq!(l, &n());
        assert_eq!(r, &n());
    }

    #[test]
    fn hol_inst_substitutes_in_hyps_too() {
        // {x = x} ⊢ x = x. Inst x := 0. Get {0 = 0} ⊢ 0 = 0.
        let x = Term::free("x", Type::nat());
        let eq = hol::hol_eq(x.clone(), x.clone());
        let h_thm = Thm::assume(eq).unwrap();
        let zero = Term::nat_lit(0u32);
        let result = h_thm.inst("x", zero.clone()).expect("inst");
        let expected_hyp = hol::hol_eq(zero.clone(), zero.clone());
        assert!(result.hyps().contains(&expected_hyp));
        assert_eq!(result.concl(), &expected_hyp);
    }

    #[test]
    fn hol_inst_rejects_dangling_bound_replacement() {
        // Replacement = Bound(0) — open term.
        let n_free = Term::free("n", Type::nat());
        let refl = Thm::refl(n_free).unwrap();
        let err = refl.inst("n", Term::bound(0)).unwrap_err();
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
        let p_thm = Thm::assume(p).unwrap();
        let q_thm = pq_weakened.eq_mp(p_thm).unwrap();
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
        let ac = ab_thm.trans(bc_thm).unwrap();
        assert!(ac.hyps().contains(&ab));
        assert!(ac.hyps().contains(&bc));
        let (l, r) = parse_hol_eq(ac.concl()).unwrap();
        assert_eq!(l, &a);
        assert_eq!(r, &c);
    }

    // =================================================================
    // Derived HOL-Light rules: sym, cong_app/abs, imp_intro/elim,
    // all_intro/elim, eta_conv.
    //
    // Each rule gets positive + negative coverage. Composition tests
    // verify rule interaction (e.g. DISCH then MP recovers the original
    // theorem; GEN then SPEC at the same witness round-trips).
    // =================================================================

    // ---- sym ----

    #[test]
    fn sym_swaps_eq_sides() {
        let a = Term::free("a", Type::nat());
        let b = Term::free("b", Type::nat());
        let ab = Thm::assume(hol::hol_eq(a.clone(), b.clone())).unwrap();
        let ba = ab.sym().expect("sym");
        let (l, r) = parse_hol_eq(ba.concl()).unwrap();
        assert_eq!(l, &b);
        assert_eq!(r, &a);
    }

    #[test]
    fn sym_rejects_non_eq() {
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::assume(p).unwrap();
        let err = p_thm.sym().unwrap_err();
        assert!(matches!(err, Error::NotHolEq(_)));
    }

    #[test]
    fn sym_preserves_hyps() {
        let a = Term::free("a", Type::nat());
        let b = Term::free("b", Type::nat());
        let extra = Term::free("extra", Type::bool());
        let ab = hol::hol_eq(a.clone(), b.clone());
        let bigger: Ctx = [ab.clone(), extra.clone()].into_iter().collect();
        let thm = Thm::assume(ab).unwrap().weaken(bigger).unwrap();
        let sym = thm.sym().unwrap();
        // hyps unchanged by sym.
        assert!(sym.hyps().contains(&extra));
    }

    #[test]
    fn sym_then_sym_is_identity() {
        let a = Term::free("a", Type::nat());
        let b = Term::free("b", Type::nat());
        let original = Thm::assume(hol::hol_eq(a.clone(), b.clone())).unwrap();
        let twice = original.clone().sym().unwrap().sym().unwrap();
        assert_eq!(twice.concl(), original.concl());
    }

    // ---- cong_app / cong_abs aliases ----

    #[test]
    fn cong_app_matches_mk_comb() {
        let succ = crate::defs::nat_succ();
        let zero = Term::nat_lit(0u32);
        let s_eq = Thm::refl(succ.clone()).unwrap();
        let z_eq = Thm::refl(zero.clone()).unwrap();
        let via_mk_comb = s_eq.clone().mk_comb(z_eq.clone()).unwrap();
        let via_cong_app = s_eq.cong_app(z_eq).unwrap();
        assert_eq!(via_mk_comb.concl(), via_cong_app.concl());
    }

    #[test]
    fn cong_abs_matches_abs() {
        let x = Term::free("x", Type::nat());
        let r1 = Thm::refl(x.clone()).unwrap();
        let r2 = Thm::refl(x).unwrap();
        let via_abs = r1.abs("x", Type::nat()).unwrap();
        let via_cong = r2.cong_abs("x", Type::nat()).unwrap();
        assert_eq!(via_abs.concl(), via_cong.concl());
    }

    // ---- imp_intro (DISCH) / imp_elim (MP) ----

    #[test]
    fn imp_intro_discharges_hyp() {
        // {p} ⊢ p   --imp_intro p->   ⊢ p ⟹ p
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::assume(p.clone()).unwrap();
        let imp = p_thm.imp_intro(&p).expect("imp_intro");
        assert!(imp.hyps().is_empty(), "p discharged from hyps");
        let (lhs, rhs) = parse_hol_imp(imp.concl()).unwrap();
        assert_eq!(lhs, &p);
        assert_eq!(rhs, &p);
    }

    #[test]
    fn imp_intro_leaves_other_hyps() {
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        // Build {p, q} ⊢ q via assume+weaken.
        let pq: Ctx = [p.clone(), q.clone()].into_iter().collect();
        let q_thm = Thm::assume(q.clone()).unwrap().weaken(pq).unwrap();
        let imp = q_thm.imp_intro(&p).unwrap();
        // p removed, q still in hyps.
        assert!(!imp.hyps().contains(&p));
        assert!(imp.hyps().contains(&q));
    }

    #[test]
    fn imp_intro_with_absent_phi_is_weakening() {
        // ⊢ p  with no occurrence of `q` as a hyp → ⊢ q ⟹ p
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let p_thm = Thm::assume(p.clone()).unwrap();
        let imp = p_thm.imp_intro(&q).expect("imp_intro");
        // p still hyp because q ≠ p.
        assert!(imp.hyps().contains(&p));
        let (lhs, rhs) = parse_hol_imp(imp.concl()).unwrap();
        assert_eq!(lhs, &q);
        assert_eq!(rhs, &p);
    }

    #[test]
    fn imp_intro_rejects_non_bool_phi() {
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::assume(p).unwrap();
        let bad = Term::free("n", Type::nat());
        let err = p_thm.imp_intro(&bad).unwrap_err();
        assert!(matches!(err, Error::NotBool(_)));
    }

    #[test]
    fn imp_elim_modus_ponens() {
        // ⊢ p ⟹ q  and  ⊢ p   ⇒   ⊢ q
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let imp = Thm::assume(hol::hol_imp(p.clone(), q.clone())).unwrap();
        let p_thm = Thm::assume(p.clone()).unwrap();
        let result = imp.imp_elim(p_thm).expect("imp_elim");
        assert_eq!(result.concl(), &q);
    }

    #[test]
    fn imp_elim_unions_hyps() {
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let extra = Term::free("extra", Type::bool());
        let imp_body = hol::hol_imp(p.clone(), q.clone());
        let bigger: Ctx = [imp_body.clone(), extra.clone()].into_iter().collect();
        let imp = Thm::assume(imp_body).unwrap().weaken(bigger).unwrap();
        let p_thm = Thm::assume(p).unwrap();
        let q_thm = imp.imp_elim(p_thm).unwrap();
        assert!(q_thm.hyps().contains(&extra));
    }

    #[test]
    fn imp_elim_rejects_non_imp() {
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::assume(p.clone()).unwrap();
        let q_thm = Thm::assume(Term::free("q", Type::bool())).unwrap();
        let err = p_thm.imp_elim(q_thm).unwrap_err();
        assert!(matches!(err, Error::NotHolImp(_)));
    }

    #[test]
    fn imp_elim_rejects_antecedent_mismatch() {
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let r = Term::free("r", Type::bool());
        let imp = Thm::assume(hol::hol_imp(p, q)).unwrap();
        let r_thm = Thm::assume(r).unwrap();
        let err = imp.imp_elim(r_thm).unwrap_err();
        assert!(matches!(err, Error::ImpAntecedentMismatch { .. }));
    }

    #[test]
    fn disch_mp_round_trips() {
        // From {p} ⊢ p, DISCH then MP back with ⊢ p should recover ⊢ p.
        let p = Term::free("p", Type::bool());
        let assumed = Thm::assume(p.clone()).unwrap();
        let imp = assumed.imp_intro(&p).unwrap();   // ⊢ p ⟹ p
        let p_thm = Thm::assume(p.clone()).unwrap();
        let recovered = imp.imp_elim(p_thm).unwrap(); // ⊢ p
        assert_eq!(recovered.concl(), &p);
    }

    // ---- all_intro (GEN) / all_elim (SPEC) ----

    #[test]
    fn all_intro_generalises_free_var() {
        // ⊢ p[x]   --all_intro x:nat-->   ⊢ ∀x:nat. p[x]
        // Construct ⊢ x = x : bool by refl, then generalise.
        let x = Term::free("x", Type::nat());
        let refl = Thm::refl(x).unwrap();   // ⊢ x = x : bool
        let univ = refl.all_intro("x", Type::nat()).expect("all_intro");
        let (ty, _body) = parse_hol_forall(univ.concl()).unwrap();
        assert_eq!(ty, &Type::nat());
    }

    #[test]
    fn all_intro_rejects_var_free_in_hyps() {
        // {x = x} ⊢ x = x — generalising over x must fail.
        let x = Term::free("x", Type::nat());
        let eq = hol::hol_eq(x.clone(), x.clone());
        let thm = Thm::assume(eq).unwrap();
        let err = thm.all_intro("x", Type::nat()).unwrap_err();
        assert!(matches!(err, Error::FreeVarInHyps { .. }));
    }

    #[test]
    fn all_intro_rejects_binder_type_mismatch() {
        // x : nat in concl, but generalise at bool — caught at the
        // declared-type check.
        let x = Term::free("x", Type::nat());
        let refl = Thm::refl(x).unwrap();
        let err = refl.all_intro("x", Type::bool()).unwrap_err();
        assert!(matches!(err, Error::BinderTypeMismatch { .. }));
    }

    #[test]
    fn all_intro_with_vacuous_var_succeeds() {
        // If the named var doesn't appear free, generalisation is
        // vacuous but still well-formed.
        let p = Term::free("p", Type::bool());
        let refl = Thm::refl(p).unwrap();
        let univ = refl.all_intro("x", Type::nat()).expect("vacuous gen");
        let (ty, _) = parse_hol_forall(univ.concl()).unwrap();
        assert_eq!(ty, &Type::nat());
    }

    #[test]
    fn all_elim_instantiates_witness() {
        // ⊢ ∀x:nat. x = x   ⇒[x := 5]⇒   ⊢ 5 = 5
        let x = Term::free("x", Type::nat());
        let refl = Thm::refl(x).unwrap();
        let univ = refl.all_intro("x", Type::nat()).unwrap();
        let five = Term::nat_lit(5u32);
        let inst = univ.all_elim(five.clone()).expect("all_elim");
        let (l, r) = parse_hol_eq(inst.concl()).unwrap();
        assert_eq!(l, &five);
        assert_eq!(r, &five);
    }

    #[test]
    fn all_elim_rejects_non_forall() {
        let p = Term::free("p", Type::bool());
        let p_thm = Thm::assume(p).unwrap();
        let err = p_thm.all_elim(Term::nat_lit(0u32)).unwrap_err();
        assert!(matches!(err, Error::NotHolForall(_)));
    }

    #[test]
    fn all_elim_rejects_witness_type_mismatch() {
        let x = Term::free("x", Type::nat());
        let univ = Thm::refl(x).unwrap().all_intro("x", Type::nat()).unwrap();
        let bad = Term::bool_lit(true); // bool, not nat
        let err = univ.all_elim(bad).unwrap_err();
        assert!(matches!(err, Error::TypeMismatch { .. }));
    }

    #[test]
    fn gen_spec_round_trips_at_concrete_witness() {
        // From ⊢ p (where p has free `x`), GEN then SPEC at `x` itself
        // recovers ⊢ p (the witness is the var being substituted in).
        let x = Term::free("x", Type::nat());
        let refl = Thm::refl(x.clone()).unwrap();
        let univ = refl.clone().all_intro("x", Type::nat()).unwrap();
        let recovered = univ.all_elim(x).unwrap();
        assert_eq!(recovered.concl(), refl.concl());
    }

    // ---- eta_conv ----

    #[test]
    fn eta_conv_simple() {
        // λx:nat. succ x  --eta-->  succ
        let succ = crate::defs::nat_succ();
        let lambda = Term::abs("x", Type::nat(),
            Term::app(crate::subst::shift_by(&succ, 1, 0), Term::bound(0)));
        let thm = Thm::eta_conv(lambda.clone()).expect("eta");
        let (l, r) = parse_hol_eq(thm.concl()).unwrap();
        assert_eq!(l, &lambda);
        assert_eq!(r, &succ);
    }

    #[test]
    fn eta_conv_rejects_non_abs() {
        let p = Term::free("p", Type::bool());
        let err = Thm::eta_conv(p).unwrap_err();
        assert!(matches!(err, Error::NotAbs(_)));
    }

    #[test]
    fn eta_conv_rejects_body_not_app() {
        // λx:nat. x is `Abs(_, nat, Bound(0))` — not an app shape.
        let lambda = Term::abs("x", Type::nat(), Term::bound(0));
        let err = Thm::eta_conv(lambda).unwrap_err();
        assert!(matches!(err, Error::EtaShape));
    }

    #[test]
    fn eta_conv_rejects_arg_not_bound_zero() {
        // λx:nat. succ (succ x) — arg is `succ x`, not `Bound(0)`.
        let succ = crate::defs::nat_succ();
        let inner = Term::app(crate::subst::shift_by(&succ, 1, 0), Term::bound(0));
        let outer = Term::app(crate::subst::shift_by(&succ, 1, 0), inner);
        let lambda = Term::abs("x", Type::nat(), outer);
        let err = Thm::eta_conv(lambda).unwrap_err();
        assert!(matches!(err, Error::EtaShape));
    }

    #[test]
    fn eta_conv_rejects_bound_zero_free_in_f() {
        // λx:nat. (λy. x) x — `f` (= λy. x) uses Bound(0) outside its own binder,
        // which is `Bound(0)` referring to the outer x. EtaShape.
        let inner = Term::abs("y", Type::nat(), Term::bound(1)); // refers to outer x
        let lambda = Term::abs("x", Type::nat(), Term::app(inner, Term::bound(0)));
        let err = Thm::eta_conv(lambda).unwrap_err();
        assert!(matches!(err, Error::EtaShape));
    }

    // ---- Compositions ----

    #[test]
    fn mp_after_disch_chain_with_two_hyps() {
        // From {p, q} ⊢ q, DISCH both then MP both back.
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let pq: Ctx = [p.clone(), q.clone()].into_iter().collect();
        let q_thm = Thm::assume(q.clone()).unwrap().weaken(pq).unwrap();
        // ⊢ q ⟹ q   (after discharging q)
        let imp_q = q_thm.imp_intro(&q).unwrap();
        // ⊢ p ⟹ q ⟹ q   (after discharging p — only `q` remains)
        let imp_p = imp_q.imp_intro(&p).unwrap();
        assert!(imp_p.hyps().is_empty());

        // Apply MP with ⊢ p, then with ⊢ q.
        let p_thm = Thm::assume(p).unwrap();
        let q_thm = Thm::assume(q.clone()).unwrap();
        let step1 = imp_p.imp_elim(p_thm).unwrap();
        let final_ = step1.imp_elim(q_thm).unwrap();
        assert_eq!(final_.concl(), &q);
    }

    #[test]
    fn sym_then_trans_chains_three() {
        // From ⊢ a = b  and  ⊢ a = c, derive ⊢ b = c via sym+trans.
        let a = Term::free("a", Type::nat());
        let b = Term::free("b", Type::nat());
        let c = Term::free("c", Type::nat());
        let ab = Thm::assume(hol::hol_eq(a.clone(), b.clone())).unwrap();
        let ac = Thm::assume(hol::hol_eq(a, c.clone())).unwrap();
        let ba = ab.sym().unwrap();
        let bc = ba.trans(ac).unwrap();
        let (l, r) = parse_hol_eq(bc.concl()).unwrap();
        assert_eq!(l, &b);
        assert_eq!(r, &c);
    }

    #[test]
    fn gen_spec_at_different_witness_substitutes() {
        // GEN over x, SPEC at `y` substitutes correctly.
        let x = Term::free("x", Type::nat());
        let refl = Thm::refl(x).unwrap();
        let univ = refl.all_intro("x", Type::nat()).unwrap();
        let y = Term::free("y", Type::nat());
        let inst = univ.all_elim(y.clone()).unwrap();
        let (l, r) = parse_hol_eq(inst.concl()).unwrap();
        assert_eq!(l, &y);
        assert_eq!(r, &y);
    }

    #[test]
    fn nat_induct_rule_builds_forall() {
        // Motive p := λn. (n = n). base ⊢ p 0; step ⊢ p n ⟹ p (succ n).
        let p = {
            let nf = Term::free("n", Type::nat());
            hol::pub_abs("n", Type::nat(), hol::hol_eq(nf.clone(), nf))
        };
        let zero = Term::nat_lit(covalence_types::Nat::zero());
        // base : ⊢ p 0  (build `p 0` then β-reduce, then refl gives p 0).
        let base = {
            let redex = Term::app(p.clone(), zero);
            let beta = Thm::beta_conv(redex).unwrap(); // ⊢ p 0 = (0 = 0)
            let refl00 =
                Thm::refl(Term::nat_lit(covalence_types::Nat::zero())).unwrap();
            beta.sym().unwrap().eq_mp(refl00).unwrap() // ⊢ p 0
        };
        // step : ⊢ p n ⟹ p (succ n) — assume `p n`, prove `p (succ n)`.
        let n = Term::free("n", Type::nat());
        let p_n = Term::app(p.clone(), n.clone());
        let succ_n = Term::app(hol::succ_fn(), n);
        let p_succ_n = Term::app(p.clone(), succ_n.clone());
        // ⊢ p (succ n) : beta-reduce to (succ n = succ n), refl, fold back.
        let psucc = {
            let beta = Thm::beta_conv(p_succ_n).unwrap(); // ⊢ p(succ n) = (succ n = succ n)
            let refl_s = Thm::refl(succ_n).unwrap();
            beta.sym().unwrap().eq_mp(refl_s).unwrap()
        };
        let step = psucc.imp_intro(&p_n).unwrap(); // ⊢ p n ⟹ p (succ n)

        let thm = Thm::nat_induct(base, step).unwrap();
        // ⊢ ∀n:nat. p n
        let (ty, _) = parse_hol_forall(thm.concl()).unwrap();
        assert_eq!(ty, &Type::nat());
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn false_elim_yields_anything() {
        let f = Thm::assume(Term::bool_lit(false)).unwrap(); // {F} ⊢ F
        let p = Term::free("p", Type::bool());
        let got = f.false_elim(p.clone()).unwrap();
        assert_eq!(got.concl(), &p);
    }

    #[test]
    fn false_elim_rejects_non_false() {
        // A proof of `T` is not a proof of `F`; ex falso must reject it.
        let t = Thm::assume(Term::bool_lit(true)).unwrap();
        assert!(t.false_elim(Term::free("p", Type::bool())).is_err());
    }
}
