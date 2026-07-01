//! Core theorems and the LCF rule API.
//!
//! `Thm` is the opaque kernel certificate. Every public method here is thin glue
//! over the sound rule catalogue in [`rules`]: it pulls the inner `pure::Thm`s out
//! of its premise `core::Thm`s and mints through [`covalence_pure::apply`] on the
//! admitted rule, which DERIVES the conclusion. Soundness rests on `admits()` alone
//! (see [`lang`] and [`rules`]) — no method may forge a `Thm`, and the inner field
//! is hygiene-only.
//!
//! The rules are split across the `thm/` module: the equality / connective /
//! quantifier / reduction / observation rules' glue lives here; the
//! conservative-extension primitives (`define`, `new_type_definition`) live in
//! [`typedef`]; every rule's ZST + `decide` (the fine-grained TCB) lives in
//! [`rules`].
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

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use smol_str::SmolStr;

use crate::ctx::Ctx;
use crate::error::{Error, Result};
use crate::subst::subst_tfrees_in_term;

use crate::term::{
    Object, ObsEq, ObsImp, ObsTrue, Observer, Term, TermKind, TrustedCons, Type, TypeKind,
};
use crate::ty::{TypeList, TypeSpec};

mod lang;
mod rules;
mod typedef;
pub use typedef::TypeDef;

use lang::{CoreLang, CoreProp};
use rules::*;

/// The kernel certificate. A newtype over a `covalence_pure` theorem carrying the
/// structured proposition `IsThm(Γ, φ)` in the crate-private [`CoreLang`]; see
/// [`lang`] for the admits-only soundness argument and [`rules`] for the
/// fine-grained rule catalogue that mints it.
///
/// The inner `pure::Thm` field is **hygiene-only**: it keeps `pure::Thm`/`CoreLang`
/// out of the public signature and preserves `Arc`-identity, but it is NOT
/// load-bearing for soundness. Soundness rests on `admits()` alone — every rule
/// [`CoreLang`] admits derives its conclusion from unforgeable premise `pure::Thm`s
/// and is sound on all inputs — so even a hypothetically-public field could only
/// wrap already-true theorems.
#[derive(Clone)]
pub struct Thm(covalence_pure::Thm<CoreLang, CoreProp>);

impl Thm {
    pub fn hyps(&self) -> &Ctx {
        &self.0.prop().1.0.0
    }
    pub fn concl(&self) -> &Term {
        &self.0.prop().1.1.0
    }
    pub fn into_parts(self) -> (Ctx, Term) {
        let p = self.0.prop();
        (p.1.0.0.clone(), p.1.1.0.clone())
    }

    /// Returns `true` iff no `Obs` leaf appears anywhere in the
    /// theorem (conclusion or any hypothesis). Such a theorem is
    /// universally true with no oracle dependencies — equivalent to
    /// HOL Light's `thm`.
    pub fn has_no_obs(&self) -> bool {
        self.concl().has_no_obs() && self.hyps().iter().all(|h| h.has_no_obs())
    }

    /// Returns `true` iff every `Obs` leaf in the theorem (concl and
    /// hyps) carries an observer whose dynamic type is `O`. Trivially
    /// `true` for a theorem with no `Obs` leaves.
    pub fn all_obs_match<O: Observer>(&self) -> bool {
        self.concl().all_obs_match::<O>() && self.hyps().iter().all(|h| h.all_obs_match::<O>())
    }

    /// Walk the theorem and call `f` on every `Obs` leaf's observer
    /// downcast to `O`. Returns `Err(ObsDowncastTypeMismatch)` at
    /// the first leaf whose dynamic type does not match `O`.
    pub fn for_each_obs<O: Observer, F: FnMut(&O)>(&self, f: &mut F) -> Result<()> {
        self.concl().for_each_obs::<O, F>(f)?;
        for h in self.hyps().iter() {
            h.for_each_obs::<O, F>(f)?;
        }
        Ok(())
    }

    /// Structural weakening: `Δ ⊢ φ`, given `Γ ⊢ φ` and `Γ ⊆ Δ`.
    ///
    /// Rejects with [`Error::NotASuperset`] if any hypothesis of
    /// `self` is missing from `target`. The conclusion is unchanged;
    /// every term in `target` is re-validated at kind `bool` by the
    /// [`rules::Weaken`] rule's `seq` floor.
    pub fn weaken(self, target: Ctx) -> Result<Thm> {
        mint!(Weaken, (self.0.clone(), target.clone()), (self.0, target))
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
        Self::refl_with(t, &mut ())
    }

    /// [`refl`](Self::refl) building its `t = t` equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`refl`](Self::refl); the cons only shares
    /// the `Arc`s of the conclusion's spine (the `TrustedCons` contract
    /// guarantees a structurally-equal result), so it has no soundness role.
    pub fn refl_with<C: TrustedCons + ?Sized>(t: Term, cons: &mut C) -> Result<Thm> {
        let thm = mint!(Refl, (t.clone(),), (t,))?;
        intern_concl(&thm, cons);
        Ok(thm)
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
        mint!(UnitEq, (a.clone(), b.clone()), (a, b))
    }

    /// `Γ ∪ Δ ⊢ s = u`, given `Γ ⊢ s = t` and `Δ ⊢ t = u` (HOL `=`).
    pub fn trans(self, other: Thm) -> Result<Thm> {
        self.trans_with(other, &mut ())
    }

    /// [`trans`](Self::trans) building its `s = u` equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`trans`](Self::trans); the cons only shares
    /// the `Arc`s of the conclusion's spine, with no soundness role.
    pub fn trans_with<C: TrustedCons + ?Sized>(self, other: Thm, cons: &mut C) -> Result<Thm> {
        let thm = mint!(Trans, (self.0.clone(), other.0.clone()), (self.0, other.0))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `Γ ∪ Δ ⊢ f x = g y`, given `Γ ⊢ f = g` and `Δ ⊢ x = y`. The
    /// applications must type-check: `f` (and so `g`) must have
    /// function type whose domain matches `x`'s (and so `y`'s) type.
    pub fn mk_comb(self, arg: Thm) -> Result<Thm> {
        self.mk_comb_with(arg, &mut ())
    }

    /// [`mk_comb`](Self::mk_comb) building its two applications and the
    /// result equation through a caller-supplied [`TrustedCons`]. This is
    /// the congruence rule the rewrite engine drives, so threading a
    /// [`crate::term::HashCons`] here shares the rewritten spine (`f x` /
    /// `g y` and the equation around them) across a whole rewrite sequence.
    ///
    /// Soundness: identical to [`mk_comb`](Self::mk_comb); the cons only
    /// shares the `Arc`s of the freshly built `App` nodes — the
    /// `TrustedCons` contract guarantees they are structurally equal to the
    /// un-interned builds — so it has no soundness role.
    pub fn mk_comb_with<C: TrustedCons + ?Sized>(self, arg: Thm, cons: &mut C) -> Result<Thm> {
        let thm = mint!(MkComb, (self.0.clone(), arg.0.clone()), (self.0, arg.0))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `Γ ⊢ (λx:τ. s[x]) = (λx:τ. t[x])`, given `Γ ⊢ s = t` with
    /// `Free(name:τ)` not free in `Γ`.
    pub fn abs(self, name: &str, ty: Type) -> Result<Thm> {
        self.abs_with(name, ty, &mut ())
    }

    /// [`abs`](Self::abs) building its two abstractions and the result
    /// equation through a caller-supplied [`TrustedCons`] — the cons-aware
    /// congruence-under-binder rule the rewrite engine drives when it
    /// re-abstracts a rewritten body.
    ///
    /// Soundness: identical to [`abs`](Self::abs); the cons only shares the
    /// `Arc`s of the freshly built `Abs` nodes and the equation around them,
    /// with no soundness role.
    pub fn abs_with<C: TrustedCons + ?Sized>(
        self,
        name: &str,
        ty: Type,
        cons: &mut C,
    ) -> Result<Thm> {
        let n = SmolStr::from(name);
        let thm = mint!(
            Abs,
            (self.0.clone(), n.clone(), ty.clone()),
            (self.0, n, ty)
        )?;
        intern_concl(&thm, cons);
        Ok(thm)
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
        Self::beta_conv_with(app, &mut ())
    }

    /// [`beta_conv`](Self::beta_conv) building the contracted right-hand
    /// side (the `open` substitution) and the result equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`beta_conv`](Self::beta_conv); `open_with`
    /// offers its reconstructed nodes to `cons`, which the `TrustedCons`
    /// contract guarantees returns structurally-equal terms, so the
    /// conclusion is the same `(λx. body) arg = body[arg/0]` regardless of
    /// the interning policy — sharing only, no soundness role.
    pub fn beta_conv_with<C: TrustedCons + ?Sized>(app: Term, cons: &mut C) -> Result<Thm> {
        let thm = mint!(BetaConv, (app.clone(),), (app,))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `{p} ⊢ p` for any `p : bool` — HOL-level assume.
    pub fn assume(p: Term) -> Result<Thm> {
        mint!(Assume, (p.clone(),), (p,))
    }

    /// `Γ ∪ Δ ⊢ q`, given `Γ ⊢ p = q : bool` and `Δ ⊢ p`. HOL Light's
    /// `EQ_MP` — equality at `bool` IS biconditional, so this also
    /// implements the `⇔`-elim direction.
    pub fn eq_mp(self, p_thm: Thm) -> Result<Thm> {
        self.eq_mp_with(p_thm, &mut ())
    }

    /// [`eq_mp`](Self::eq_mp) with a caller-supplied [`TrustedCons`] for
    /// API uniformity with the other cons-aware congruence rules.
    ///
    /// `eq_mp` builds **no new `Term` nodes** — its conclusion `q` is taken
    /// directly from the input equation — so the cons is unused. It is
    /// accepted only so a rewrite driver can thread one cons uniformly
    /// through `trans` / `mk_comb` / `eq_mp`. No soundness role.
    pub fn eq_mp_with<C: TrustedCons + ?Sized>(self, p_thm: Thm, _cons: &mut C) -> Result<Thm> {
        mint!(EqMp, (self.0.clone(), p_thm.0.clone()), (self.0, p_thm.0))
    }

    /// HOL Light's `DEDUCT_ANTISYM_RULE`:
    /// `(Γ \ {q}) ∪ (Δ \ {p}) ⊢ p ⇔ q`, given `Γ ⊢ p` and `Δ ⊢ q`.
    /// Both `p` and `q` must be `bool`-typed; equality at `bool`
    /// IS biconditional.
    pub fn deduct_antisym(self, other: Thm) -> Result<Thm> {
        mint!(
            DeductAntisym,
            (self.0.clone(), other.0.clone()),
            (self.0, other.0)
        )
    }

    /// HOL Light's `INST`: substitute the free variable `(name,
    /// replacement_ty)` — identified by name **and** type — with
    /// `replacement`. A same-named variable at a different type is a
    /// distinct variable and is left untouched (so a type-mismatched
    /// substitution is a no-op, as in HOL Light's `vsubst`).
    pub fn inst(self, name: &str, replacement: Term) -> Result<Thm> {
        let n = SmolStr::from(name);
        mint!(
            Inst,
            (self.0.clone(), n.clone(), replacement.clone()),
            (self.0, n, replacement)
        )
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
        mint!(Sym, (self.0.clone(),), (self.0,))
    }

    /// Alias for [`Thm::mk_comb`]. `cong_app` is the equational-
    /// congruence name (`f = g, x = y ⊢ f x = g y`); HOL Light
    /// calls it `MK_COMB`. Same rule.
    pub fn cong_app(self, arg: Thm) -> Result<Thm> {
        self.mk_comb(arg)
    }

    /// Alias for [`Thm::mk_comb_with`] — the cons-aware
    /// [`cong_app`](Self::cong_app).
    pub fn cong_app_with<C: TrustedCons + ?Sized>(self, arg: Thm, cons: &mut C) -> Result<Thm> {
        self.mk_comb_with(arg, cons)
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
        mint!(
            ImpIntro,
            (self.0.clone(), phi.clone()),
            (self.0, phi.clone())
        )
    }

    /// `Γ ∪ Δ ⊢ ψ`, given `Γ ⊢ φ ⟹ ψ` and `Δ ⊢ φ`
    /// (HOL Light's `MP`).
    ///
    /// Soundness: standard modus ponens. HOL Light derives it by
    /// unfolding `⟹`'s definition (`p ⟹ q  ≡  p ∧ q = p`) and
    /// using `AND_INTRO` / `AND_ELIM`.
    pub fn imp_elim(self, hyp: Thm) -> Result<Thm> {
        mint!(ImpElim, (self.0.clone(), hyp.0.clone()), (self.0, hyp.0))
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
        let n = SmolStr::from(name);
        mint!(
            AllIntro,
            (self.0.clone(), n.clone(), ty.clone()),
            (self.0, n, ty)
        )
    }

    /// `Γ ⊢ φ[t/x]`, given `Γ ⊢ ∀x:τ. φ` and `t : τ`
    /// (HOL Light's `SPEC`).
    ///
    /// Soundness: standard universal elimination, derived in HOL
    /// Light from `INST` and `∀`'s definitional unfolding.
    pub fn all_elim(self, witness: Term) -> Result<Thm> {
        self.all_elim_with(witness, &mut ())
    }

    /// [`all_elim`](Self::all_elim) routing the substituted term through a
    /// caller-supplied [`TrustedCons`] (e.g. a [`crate::term::HashCons`]).
    ///
    /// Soundness: identical to [`all_elim`](Self::all_elim) — the only change
    /// is that `open`'s reconstructed nodes are offered to `cons`, which the
    /// `TrustedCons` contract guarantees returns structurally-equal terms. So
    /// the conclusion is the same `φ[t/x]` regardless of the interning policy;
    /// interning only shares `Arc`s. This is the cons-aware entry point the
    /// Metamath replay threads to keep substitution instances a shared DAG (at
    /// `open`'s depth-0 the witness is inserted by reference, so an
    /// already-interned witness is reused, not copied).
    pub fn all_elim_with<C: TrustedCons + ?Sized>(
        self,
        witness: Term,
        cons: &mut C,
    ) -> Result<Thm> {
        let thm = mint!(
            AllElim,
            (self.0.clone(), witness.clone()),
            (self.0, witness)
        )?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `⊢ (λx:τ. f x) = f`, when `Bound(0)` does not appear free
    /// in `f`. HOL Light's `ETA_AX` (a primitive axiom there; here
    /// exposed as a rule that discharges well-formedness in one
    /// step).
    pub fn eta_conv(abs: Term) -> Result<Thm> {
        mint!(EtaConv, (abs.clone(),), (abs,))
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
        mint!(
            AndIntro,
            (self.0.clone(), other.0.clone()),
            (self.0, other.0)
        )
    }

    /// `Γ ⊢ p`, given `Γ ⊢ p ∧ q` (HOL Light `CONJUNCT1`).
    ///
    /// Soundness: apply the unfolded body `(λf. f p q) = (λf. f T T)`
    /// to the selector `λa b. a` and β-reduce both sides to `p = T`,
    /// then `EQT_ELIM`.
    pub fn and_elim_l(self) -> Result<Thm> {
        mint!(AndElimL, (self.0.clone(),), (self.0,))
    }

    /// `Γ ⊢ q`, given `Γ ⊢ p ∧ q` (HOL Light `CONJUNCT2`; selector
    /// `λa b. b`).
    pub fn and_elim_r(self) -> Result<Thm> {
        mint!(AndElimR, (self.0.clone(),), (self.0,))
    }

    /// `Γ ⊢ p ∨ q`, given `Γ ⊢ p` and the other disjunct `q : bool`
    /// (HOL Light `DISJ1`).
    ///
    /// Soundness: fold `⊢ p` into `p ∨ q ≜ ∀r. (p⟹r) ⟹ (q⟹r) ⟹ r`
    /// — assume each implication, MP the first with `⊢ p`, generalise.
    pub fn or_intro_l(self, q: Term) -> Result<Thm> {
        mint!(OrIntroL, (self.0.clone(), q.clone()), (self.0, q))
    }

    /// `Γ ⊢ p ∨ q`, given `Γ ⊢ q` and the other disjunct `p : bool`
    /// (HOL Light `DISJ2`).
    pub fn or_intro_r(self, p: Term) -> Result<Thm> {
        mint!(OrIntroR, (self.0.clone(), p.clone()), (self.0, p))
    }

    /// `Γ ∪ Δ₁ ∪ Δ₂ ⊢ r`, given `Γ ⊢ p ∨ q`, `Δ₁ ⊢ p ⟹ r` and
    /// `Δ₂ ⊢ q ⟹ r` (HOL Light `DISJ_CASES`, as a rule taking the two
    /// branch implications).
    ///
    /// Soundness: specialise `p ∨ q ≜ ∀r. (p⟹r) ⟹ (q⟹r) ⟹ r` at `r`
    /// and MP with the two branches.
    pub fn or_elim(self, left: Thm, right: Thm) -> Result<Thm> {
        mint!(
            OrElim,
            (self.0.clone(), left.0.clone(), right.0.clone()),
            (self.0, left.0, right.0)
        )
    }

    /// `Γ ⊢ ¬p`, given `Γ ⊢ p ⟹ F` (HOL Light `NOT_INTRO`).
    ///
    /// Soundness: `¬p ≜ (p ⟹ F)`, so this just folds the definition.
    pub fn not_intro(self) -> Result<Thm> {
        mint!(NotIntro, (self.0.clone(),), (self.0,))
    }

    /// `Γ ∪ Δ ⊢ F`, given `Γ ⊢ ¬p` and `Δ ⊢ p` (HOL Light `NOT_ELIM`).
    ///
    /// Soundness: unfold `¬p` to `p ⟹ F` and MP with `⊢ p`.
    pub fn not_elim(self, other: Thm) -> Result<Thm> {
        mint!(
            NotElim,
            (self.0.clone(), other.0.clone()),
            (self.0, other.0)
        )
    }

    /// `⊢ Spec(spec, args) = subst(spec.tm, tvars, args)` for a
    /// **let-style** `TermSpec` — one whose body `tm` has the spec's own
    /// declared type (`type_of(tm) == spec.ty`). The spec's type
    /// variables (in `free_tvars()` canonical order) are substituted
    /// positionally by `args`.
    ///
    /// Errors:
    /// - [`Error::NotASpec`] if `t` is not a `TermKind::Spec` leaf.
    /// - [`Error::SpecHasNoBody`] for a declaration-only spec (`tm = None`).
    /// - [`Error::SpecIsDefStyle`] if `tm` is a `ty → bool` selector
    ///   predicate (ε-style) rather than the body itself.
    ///
    /// ## Soundness
    ///
    /// A let-style spec's denotation *is* its body at the supplied
    /// type-args — that is the definitional equation the kernel commits
    /// to when the spec is built. This holds for any body, including
    /// user-constructed `TermSpec`s, so the rule needs no trust in the
    /// catalogue. (Note: when a spec is **also** in `reduce_prim`'s table
    /// — e.g. `nat.add`, `nat.mod` — the two rules commit two facts about
    /// it, so the body MUST denote the same function `reduce_prim`
    /// computes; see `audit_reduce::audit_reduce_matches_body_nat_ops`.)
    pub fn unfold_term_spec(t: Term) -> Result<Thm> {
        mint!(UnfoldTermSpec, (t.clone(),), (t,))
    }

    /// `⊢ (p w) ⟹ p(t)` for a **def-style** TermSpec leaf
    /// `t = Spec(spec, args)` with selector predicate `p` (its `tm` at
    /// the supplied type args) and any witness `w` of the spec's
    /// carrier type. The def-style analogue of [`Thm::select_ax`]: each
    /// *named* def-spec is its OWN choice — if `p` is inhabited
    /// (witnessed by `w`), then `t` satisfies `p`.
    ///
    /// Returns [`Error::SpecIsLetStyle`] for a let-style spec,
    /// [`Error::SpecHasNoBody`] for a declaration-only one,
    /// [`Error::NotASpec`] for a non-spec term, and a type mismatch if
    /// `w` is not of the carrier type.
    ///
    /// ## Soundness
    ///
    /// Unconditionally sound, exactly like [`Thm::select_ax`]. If `p`
    /// is inhabited, the kernel interprets the def-spec as some element
    /// satisfying `p`, so `p(t)` holds; if `p` is empty, the premise
    /// `p w` is false for every `w` and the implication is vacuous.
    ///
    /// Crucially this does **not** equate `t` with `ε p` or with any
    /// other spec sharing `p`: distinct named def-specs are
    /// independent choices. Think of `ε` / [`TermKind::Select`] as the
    /// single distinguished *anonymous* def-spec, whose choice axiom is
    /// [`Thm::select_ax`]; every named def-spec gets its own via this
    /// rule.
    ///
    /// (A *let*-style spec `c ≡ body` is the special case whose
    /// predicate is `λx. x = body`: `spec_ax` then yields
    /// `(body = body) ⟹ (c = body)`, and `refl` discharges the
    /// premise — exactly [`Thm::unfold_term_spec`]. The two spec kinds
    /// will eventually be consolidated on this footing.)
    pub fn spec_ax(t: Term, w: Term) -> Result<Thm> {
        mint!(SpecAx, (t.clone(), w.clone()), (t, w))
    }

    /// `⊢ (p x) ⟹ (p (ε p))` — Hilbert's choice axiom (HOL Light's
    /// `SELECT_AX`), the characterising rule of the `ε` primitive
    /// ([`TermKind::Select`]). `p` must have a function type
    /// `α → bool` and `x : α`; then `ε p = Select(p) : α`.
    ///
    /// ## Soundness
    ///
    /// `ε p` denotes *some* element satisfying `p` whenever one exists,
    /// so if `p` holds at the witness `x` it holds at `ε p`. This is
    /// the standard Hilbert-choice interpretation of `Select`. Combined with
    /// the connective definitions it yields the existence form
    /// `(∃x. p x) ⟹ p (ε p)` downstream.
    pub fn select_ax(p: Term, x: Term) -> Result<Thm> {
        mint!(SelectAx, (p.clone(), x.clone()), (p, x))
    }

    // ========================================================================
    // Derived-type (TypeSpec abs/rep) laws
    // ========================================================================
    //
    // A `TypeSpec` introduces a derived type `τ := { x : carrier | P x }`
    // carved from its `carrier` by the predicate `P = spec.tm()` (a
    // `newtype` is the special case `P = λ_. T`). The kernel's typed
    // coercions `abs : carrier → τ` ([`Term::spec_abs`]) and
    // `rep : τ → carrier` ([`Term::spec_rep`]) carry no theorems on their
    // own; the three rules below are the *witness-free* bijection laws that
    // characterise them. They are the `TypeSpec` analogue of the
    // [`TypeDef`] theorems [`Thm::new_type_definition`] mints — but here
    // **no non-emptiness witness is supplied**, so the "back" direction is
    // correspondingly weakened (see [`Thm::spec_rep_abs_back`]).
    //
    // ## The total interpretation these are sound under
    //
    // Fix a model. Let `A = ⟦carrier⟧` and `S = { x ∈ A | ⟦P⟧ x }`.
    // - If `S ≠ ∅`: `⟦τ⟧ = S`, `⟦rep⟧` is the inclusion `S ↪ A`, and
    //   `⟦abs⟧` is a retraction `A ↠ S` (the identity on `S`, sending the
    //   rest of `A` to an arbitrary fixed element of `S`).
    // - If `S = ∅`: `τ` must still be non-empty (HOL types are), so
    //   `⟦τ⟧ = A` with `⟦abs⟧ = ⟦rep⟧ = id`.
    // Every other kernel rule treats `abs`/`rep` as uninterpreted symbols,
    // so committing to this interpretation is consistent. (The `TypeSpec`
    // coercions are entirely separate from the obs-leaf abs/rep that
    // `new_type_definition` introduces, so the two never interfere.)

    /// `⊢ abs (rep a) = a`, for any `a : τ` of a carrier-bearing
    /// [`TypeSpec`] `(spec, args)` — the **unconditional** round-trip on
    /// the wrapper side.
    ///
    /// ## Soundness
    ///
    /// Holds in both cases of the [interpretation](#) above: when `S ≠ ∅`,
    /// `rep a ∈ S` and `abs` is the identity on `S`, so `abs (rep a) = a`;
    /// when `S = ∅`, `abs` and `rep` are the identity. It needs no
    /// predicate, so it is equally valid for `newtype`s, `subtype`s, and
    /// quotient specs (where `abs ∘ rep = id` on the quotient likewise
    /// holds). Errors with [`Error::SpecHasNoCarrier`] if the spec has no
    /// carrier, and a [type mismatch](Error::TypeMismatch) unless
    /// `a : τ = spec args`.
    pub fn spec_abs_rep(spec: TypeSpec, args: impl Into<TypeList>, a: Term) -> Result<Thm> {
        let args = args.into();
        mint!(
            SpecAbsRep,
            (spec.clone(), args.clone(), a.clone()),
            (spec, args, a)
        )
    }

    /// `⊢ P a ⟹ rep (abs a) = a`, for `a : carrier` of a **subtype**
    /// [`TypeSpec`] with selector predicate `P = spec.tm()` — the
    /// *conditional* round-trip on the carrier side.
    ///
    /// For a `newtype` (`P = λ_. T`) the premise `P a` reduces to `T`, so
    /// discharging it (β + `truth`) yields the unconditional
    /// `⊢ rep (abs a) = a`.
    ///
    /// ## Soundness
    ///
    /// Assume `⟦P⟧ a`. Then `a ∈ S`, so `S ≠ ∅`; `abs` is the identity on
    /// `S` and `rep` the inclusion, hence `rep (abs a) = a`. If `¬⟦P⟧ a`
    /// the implication is vacuous. Errors with [`Error::NotASubtype`]
    /// unless `spec.tm()` is a `carrier → bool` predicate (so quotient
    /// specs, whose `tm` is a relation, are rejected), and with a type
    /// mismatch unless `a : carrier`.
    pub fn spec_rep_abs_fwd(spec: TypeSpec, args: impl Into<TypeList>, a: Term) -> Result<Thm> {
        let args = args.into();
        mint!(
            SpecRepAbsFwd,
            (spec.clone(), args.clone(), a.clone()),
            (spec, args, a)
        )
    }

    /// `⊢ rep (abs a) = a ⟹ (P a ∨ ¬∃x. P x)`, for `a : carrier` of a
    /// **subtype** [`TypeSpec`] — the *witness-free* converse of
    /// [`spec_rep_abs_fwd`](Thm::spec_rep_abs_fwd).
    ///
    /// With a non-emptiness witness this would be the clean
    /// `rep (abs a) = a ⟹ P a` (HOL Light's `rep_abs` back direction).
    /// Lacking one, the predicate may be *empty*, in which case `τ`
    /// collapses to the whole carrier and `rep (abs a) = a` holds for
    /// every `a` without `P a`; the extra disjunct `¬∃x. P x` is exactly
    /// that escape hatch.
    ///
    /// ## Soundness
    ///
    /// Assume `rep (abs a) = a`. If `S = ∅` then `¬∃x. ⟦P⟧ x`, the right
    /// disjunct. If `S ≠ ∅` then `abs a ∈ S` and `rep` is injective with
    /// image `S`, so `a = rep (abs a) ∈ S`, giving `⟦P⟧ a`, the left
    /// disjunct. Same shape/error conditions as
    /// [`spec_rep_abs_fwd`](Thm::spec_rep_abs_fwd).
    pub fn spec_rep_abs_back(spec: TypeSpec, args: impl Into<TypeList>, a: Term) -> Result<Thm> {
        let args = args.into();
        mint!(
            SpecRepAbsBack,
            (spec.clone(), args.clone(), a.clone()),
            (spec, args, a)
        )
    }

    /// Single-step closed-form computation: `⊢ t = result` where `t` is a
    /// kernel literal operation applied to all-literal arguments, and
    /// `result` is the computed value. Returns [`Error::NotReducible`] for
    /// any other shape — the rule is deliberately conservative: it does
    /// not reduce subterms or follow β/δ chains.
    ///
    /// The catalogue (dispatched by `builtins::reduce_prim_term`):
    ///
    /// - HOL `=` over two same-kind literals (`Bool`/`Nat`/`Int`/
    ///   `SmallInt`/`Blob`) → `Bool(a == b)`.
    /// - the `nat.*` / `int.*` / `bytes.*` arithmetic, comparison, bitwise
    ///   and conversion specs (see `builtins::Prim` for the full list),
    ///   and the fixed-width `uN`/`sN` ops (`defs::int_ops`).
    ///
    /// Conventions worth noting: nat `sub`/`pred` saturate at 0; `n/0 = 0`
    /// and `n mod 0 = n` (the latter forced by `nat.mod`'s body — see
    /// `builtins::eval_prim`); fixed-width arithmetic wraps mod `2^width`.
    ///
    /// ## Soundness
    ///
    /// Each reduction is `t = canonical_value`, true by the literals'
    /// fixed denotation in every model — not a logical postulate. (The
    /// literal-distinctness case `Nat(5) = Nat(6) → F` is the kernel's
    /// denotational commitment that distinct literals denote distinct
    /// values.)
    pub fn reduce_prim(t: Term) -> Result<Thm> {
        Self::reduce_prim_with(t, &mut ())
    }

    /// [`reduce_prim`](Self::reduce_prim) building its `t = result`
    /// equation through a caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`reduce_prim`](Self::reduce_prim); the cons
    /// only shares the `Arc`s of the result equation's spine (the computed
    /// literal `result` and the `=` around it), with no soundness role. It
    /// lets a reduction driver thread one cons uniformly through
    /// `beta_conv` / `reduce_prim` / `trans`.
    pub fn reduce_prim_with<C: TrustedCons + ?Sized>(t: Term, cons: &mut C) -> Result<Thm> {
        let thm = mint!(ReducePrim, (t.clone(),), (t,))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `Γ[α:=σ] ⊢ φ[α:=σ]`.
    pub fn inst_tfree(self, name: &str, replacement: Type) -> Result<Thm> {
        let n = SmolStr::from(name);
        mint!(
            InstTFree,
            (self.0.clone(), n.clone(), replacement.clone()),
            (self.0, n, replacement)
        )
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
        // Untrusted per-`O` policy filter, applied BEFORE the sound rule fires.
        // The rule ([`rules::ObsTrueRule`]) is unconditionally sound for any `O`;
        // this oracle only gates whether it fires.
        let (obs, args) = decompose_obs_app(&expr)?;
        let o = obs.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let ty = expr.type_of()?;
        if !ty.is_bool() {
            return Err(Error::NotBool(ty));
        }
        if !o.obs_true(&args, hint.as_deref()) {
            return Err(Error::ObsEqRefused);
        }
        mint!(ObsTrueRule, (expr.clone(),), (expr,))
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
        // Untrusted per-`O` policy filter, applied BEFORE the sound rule fires.
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
        mint!(ObsImpRule, (expr.clone(), hyps.clone()), (expr, hyps))
    }

    pub fn obs_eq<O: ObsEq>(
        expr1: Term,
        expr2: Term,
        hint: Option<Arc<dyn crate::term::Hint>>,
    ) -> Result<Thm> {
        // Untrusted per-`O` policy filter, applied BEFORE the sound rule fires.
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
        mint!(ObsEqRule, (expr1.clone(), expr2.clone()), (expr1, expr2))
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
        mint!(
            NatInduct,
            (base.0.clone(), step.0.clone()),
            (base.0, step.0)
        )
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
        mint!(FalseElim, (self.0.clone(), p.clone()), (self.0, p))
    }

    // ========================================================================
    // nat freeness (the constructors `0` / `succ` are free)
    // ========================================================================
    //
    // `nat` is the kernel's freely-generated naturals: the `Nat`
    // literals are the `0`/`succ`-numerals and [`Term::succ`]
    // ([`TermKind::Succ`]) is the successor constructor. "Freely
    // generated" is exactly the commitment [`Thm::nat_induct`] already
    // relies on; these two rules expose its other half — that distinct
    // constructor expressions denote distinct numbers — as
    // non-computational primitives (the literal cases already reduce
    // via [`Thm::reduce_prim`]; these cover *open* terms).

    /// `⊢ (succ m = succ n) ⟹ (m = n)` — successor injectivity. `m`
    /// and `n` must type-check at `nat`.
    ///
    /// ## Soundness
    ///
    /// `Type::nat()` denotes the standard naturals, freely generated by
    /// `0` and `succ`; a free constructor is injective. Sound in every
    /// model the kernel admits (the same `nat` semantics
    /// [`Thm::nat_induct`] and [`Thm::zero_ne_succ`] rest on).
    pub fn succ_inj(m: Term, n: Term) -> Result<Thm> {
        mint!(SuccInj, (m.clone(), n.clone()), (m, n))
    }

    /// `⊢ ¬(0 = succ n)` — zero is not a successor. `n` must type-check
    /// at `nat`.
    ///
    /// ## Soundness
    ///
    /// As [`Thm::succ_inj`]: `0` and `succ _` are distinct constructors
    /// of the freely-generated `nat`, so they never denote the same
    /// number.
    pub fn zero_ne_succ(n: Term) -> Result<Thm> {
        mint!(ZeroNeSucc, (n.clone(),), (n,))
    }

    /// `⊢ p ∨ ¬p`, for any `p : bool` — the law of excluded middle, as
    /// a primitive rule. No hypotheses.
    ///
    /// ## Soundness
    ///
    /// This is the kernel's classicality axiom. HOL `=` and the `Bool`
    /// literals are interpreted in the standard two-valued model, where
    /// every `bool`-typed term denotes either `T` or `F`; in either case
    /// `p ∨ ¬p` holds. Equivalently it is HOL Light's `EXCLUDED_MIDDLE`,
    /// which is *derivable* there from the choice/`ε` infrastructure
    /// (`Select`) together with extensionality and `deduct_antisym` —
    /// the kernel already has every ingredient. It is exposed here as a
    /// direct constructor for simplicity and efficiency; replacing it
    /// with that derivation (and dropping it from the axiom surface) is
    /// a standing cleanup, mirroring the connective fast-rules whose
    /// soundness witnesses live in `covalence-hol::proofs`.
    pub fn lem(p: Term) -> Result<Thm> {
        mint!(Lem, (p.clone(),), (p,))
    }
}

/// Walk down through `App`s collecting arguments left-to-right. If
/// the final node is an `Obs` leaf, return its observer and the args
/// list; otherwise return an error.
/// Parse an `Eq`-headed application — `App(App(=, lhs), rhs)` — and
/// return `(lhs, rhs)` by reference.
/// Build the typed `abs`/`rep` coercions of a `TypeSpec` at `args` and
/// recover its `(carrier, wrapper)` types. The shared front-end of the
/// `spec_*` subtype laws. Errors with [`Error::SpecHasNoCarrier`] for a
/// carrier-less spec.
/// Populate `cons` with the theorem's conclusion spine — the `_with` interning
/// contract. The rule already derived (and the mint already blessed) the sound
/// conclusion; deep-interning that result into the caller's [`TrustedCons`] table
/// lets subsequent cons-aware builds dedup structurally-equal subterms (the
/// rewrite-engine / Metamath-replay sharing path). Pure sharing, no soundness role.
fn intern_concl<C: TrustedCons + ?Sized>(thm: &Thm, cons: &mut C) {
    let _ = thm.concl().cons_with(cons);
}

fn spec_coercions(spec: &TypeSpec, args: &TypeList) -> Result<(Term, Term, Type, Type)> {
    let abs = Term::spec_abs(spec.clone(), args.clone());
    let rep = Term::spec_rep(spec.clone(), args.clone());
    // `abs : carrier → wrapper`; its `type_of` errors if no carrier.
    let TypeKind::Fun(carrier, wrapper) = abs.type_of()?.kind().clone() else {
        return Err(Error::SpecHasNoCarrier);
    };
    Ok((abs, rep, carrier, wrapper))
}

/// The selector predicate `P : carrier → bool` of a **subtype**
/// `TypeSpec`, instantiated positionally at `args` (the same
/// substitution [`Thm::unfold_term_spec`] / [`Thm::spec_ax`] use).
/// Errors with [`Error::NotASubtype`] unless the spec's `tm` is present
/// and types as `carrier → bool` — rejecting carrier-less specs and
/// quotient specs (whose `tm` is a `carrier → carrier → bool` relation).
/// Positionally instantiate a spec's type variables — the sorted,
/// deduplicated `free_tvars` of its declared type — with the supplied
/// instance `args`, **simultaneously**. A sequential fold would cascade
/// an argument swap like `{a:=b, b:=a}` into `{a:=a, b:=a}` (the second
/// substitution rewriting the `b`s the first one just introduced), so a
/// two-type-parameter spec instantiated with its parameters swapped
/// would collapse both to one type. `subst_tfrees_in_term` applies the
/// whole map in a single pass and avoids that.
fn inst_spec_tvars(body: &Term, tvars: &[SmolStr], args: &TypeList) -> Term {
    let sub: BTreeMap<SmolStr, Type> = tvars.iter().cloned().zip(args.iter().cloned()).collect();
    subst_tfrees_in_term(body, &sub)
}

fn subtype_pred(spec: &TypeSpec, args: &TypeList, carrier: &Type) -> Result<Term> {
    let body = spec.tm().ok_or(Error::NotASubtype)?.clone();
    let tvars = spec.ty().ok_or(Error::SpecHasNoCarrier)?.free_tvars();
    let pred = inst_spec_tvars(&body, &tvars, args);
    if pred.type_of()? != Type::fun(carrier.clone(), Type::bool()) {
        return Err(Error::NotASubtype);
    }
    Ok(pred)
}

fn parse_hol_eq(t: &Term) -> Result<(&Term, &Term)> {
    let (lhs, rhs, _) = parse_hol_eq_at(t)?;
    Ok((lhs, rhs))
}

/// Like [`parse_hol_eq`] but also returns the element type `alpha` read
/// directly off the `Eq(alpha)` head — no `type_of` walk. For a validly
/// built theorem `⊢ lhs = rhs`, `alpha` is exactly the (shared) type of
/// `lhs` and `rhs`, so rules can reuse it to construct their result
/// equation instead of recomputing it.
fn parse_hol_eq_at(t: &Term) -> Result<(&Term, &Term, &Type)> {
    let TermKind::App(f, rhs) = t.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    let TermKind::App(head, lhs) = f.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    let TermKind::Eq(alpha) = head.kind() else {
        return Err(Error::NotHolEq(format!("{}", t)));
    };
    Ok((lhs, rhs, alpha))
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
        if self.hyps().is_empty() {
            return write!(f, "⊢ {}", self.concl());
        }
        for (i, h) in self.hyps().iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", h)?;
        }
        write!(f, " ⊢ {}", self.concl())
    }
}

#[cfg(test)]
mod hol_light_tests;
