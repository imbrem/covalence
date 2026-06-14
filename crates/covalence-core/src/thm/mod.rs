//! Core theorems and the LCF rule API.
//!
//! `Thm` is the opaque kernel type. Its only constructor is the
//! module-private `Thm::build`, which type-checks the conclusion and
//! every hypothesis at kind `prop`. The rule methods are the only
//! paths to a `Thm` value; constructional soundness in the LCF sense.
//!
//! The rules are split across the `thm/` module: the equality /
//! connective / quantifier / reduction / observation rules live here;
//! the conservative-extension primitives (`define`,
//! `new_type_definition`) live in [`typedef`]. Because `build` is
//! private to the `thm` module, **only `thm/` can mint a `Thm`** —
//! the submodules reach `build` as descendants, nothing outside can.
//! That makes the whole `thm/` directory the auditable TCB boundary.
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
//! The rule set is Core-shaped:
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
    Object, ObsEq, ObsImp, ObsTrue, Observer, Term, TermKind, Type, TypeEnv, type_of_in,
};

mod typedef;
pub use typedef::TypeDef;

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
    // Core→HOL collapse these are THE inference rules — the only
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
        let s_abs = Term::abs(ty.clone(), close(&s, name));
        let t_abs = Term::abs(ty, close(&t, name));
        let concl = hol::hol_eq(s_abs, t_abs);
        Self::build(self.hyps, concl)
    }

    /// `⊢ (λx:τ. body) arg = body[arg/0]` — one β-step as a HOL
    /// equation, with no hypotheses.
    ///
    /// Spec — exactly one outermost β-contraction:
    /// - `app` must be syntactically `App(Abs(τ, body), arg)`, and
    ///   `arg` must type-check at `τ`; otherwise this errors
    ///   ([`Error::NotApp`] / [`Error::NotAbs`] / [`Error::TypeMismatch`]).
    /// - It fires the *top* redex only — it does **not** recurse into
    ///   `body` or `arg`, so redexes nested in either are preserved.
    /// - β only: it performs no δ-unfolding (see
    ///   [`Thm::unfold_term_spec`]), no literal/primitive computation
    ///   (see [`Thm::reduce_prim`] — e.g. `(λx. x) (2 + 3)` reduces to
    ///   `2 + 3`, *not* `5`), and no η-contraction (see
    ///   [`Thm::eta_conv`]).
    pub fn beta_conv(app: Term) -> Result<Thm> {
        let TermKind::App(fun, arg) = app.kind() else {
            return Err(Error::NotApp(format!("{}", app)));
        };
        let TermKind::Abs(ty, body) = fun.kind() else {
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
        let TermKind::Abs(ty, body) = abs.kind() else {
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
    /// - both expressions have the same Core type.
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
    /// - `expr` has final Core type `prop`.
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
    let TermKind::Abs(ty, body) = lambda.kind() else {
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


#[cfg(test)]
mod hol_light_tests;
