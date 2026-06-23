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

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use smol_str::SmolStr;

use crate::builtins;
use crate::ctx::Ctx;
use crate::error::{Error, Result};
use crate::hol;
use crate::subst::{
    close_var, has_free_var_typed, open_with, subst_free, subst_tfree_in_term, subst_tfrees_in_term,
};

use crate::term::{
    Object, ObsEq, ObsImp, ObsTrue, Observer, Term, TermKind, TrustedCons, Type, TypeKind, Var,
};
use crate::ty::{TypeList, TypeSpec};

mod typedef;
pub use typedef::TypeDef;

#[derive(Clone)]
pub struct Thm {
    hyps: Ctx,
    concl: Term,
}

impl Thm {
    /// The single private constructor. Validates that the conclusion and every
    /// hypothesis is well-typed at kind `prop` (`bool`).
    ///
    /// Each check is a single [`Term::type_of`], which reads the type **cached**
    /// on the node (`TermInfo::Wf`) in O(1) for the common well-typed case and
    /// re-derives only to produce a specific error for an open / ill-typed term.
    /// So `build` is O(#hyps), not O(Σ term sizes) — and every rule bottoms out
    /// here.
    ///
    /// There is **no** cross-term `Free`-name consistency check: variables are
    /// type-carrying (`Free(Var{name, ty})`), so `x:nat` and `x:bool` are simply
    /// distinct variables (HOL Light's model). A term well-typed in isolation
    /// cannot create a cross-term inconsistency — every variable operation keys
    /// on the whole `(name, type)` — so there is nothing left to enforce.
    fn build(hyps: Ctx, concl: Term) -> Result<Thm> {
        let ty = concl.type_of()?;
        if !ty.is_bool() {
            return Err(Error::NotBool(ty));
        }
        for h in &hyps {
            let hty = h.type_of()?;
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
        Self::refl_with(t, &mut ())
    }

    /// [`refl`](Self::refl) building its `t = t` equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`refl`](Self::refl); the cons only shares
    /// the `Arc`s of the conclusion's spine (the `TrustedCons` contract
    /// guarantees a structurally-equal result), so it has no soundness role.
    pub fn refl_with<C: TrustedCons + ?Sized>(t: Term, cons: &mut C) -> Result<Thm> {
        let _ = t.type_of()?;
        let concl = hol::hol_eq_with(t.clone(), t, cons);
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
        self.trans_with(other, &mut ())
    }

    /// [`trans`](Self::trans) building its `s = u` equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`trans`](Self::trans); the cons only shares
    /// the `Arc`s of the conclusion's spine, with no soundness role.
    pub fn trans_with<C: TrustedCons + ?Sized>(self, other: Thm, cons: &mut C) -> Result<Thm> {
        let (s, t1, alpha) = parse_hol_eq_at(&self.concl)?;
        let (t2, u) = parse_hol_eq(&other.concl)?;
        if t1 != t2 {
            return Err(Error::TransMiddleMismatch {
                left: format!("{}", t1),
                right: format!("{}", t2),
            });
        }
        // `alpha` is `s`'s element type, read off the `Eq` head — no walk.
        let concl = hol::hol_eq_at_with(alpha.clone(), s.clone(), u.clone(), cons);
        let hyps = self.hyps.union(&other.hyps);
        Self::build(hyps, concl)
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
        let (f, g, funty) = parse_hol_eq_at(&self.concl)?;
        let (x, y) = parse_hol_eq(&arg.concl)?;
        // The result `f x = g y` has element type = codomain of `f`'s
        // (function) type, which is the `Eq` head's type argument on the
        // input theorem — no `type_of` walk. If `f` is not a function the
        // application is ill-typed; report it directly (as the old
        // `lhs.type_of()` path did).
        let TypeKind::Fun(_dom, cod) = funty.kind() else {
            return Err(Error::NotFunction(funty.clone()));
        };
        let cod = cod.clone();
        let lhs = Term::app_with(f.clone(), x.clone(), cons);
        let rhs = Term::app_with(g.clone(), y.clone(), cons);
        // `Self::build` re-validates the whole conclusion end-to-end —
        // argument-domain match, and Free-var consistency across f/g/x/y
        // — so the previous per-side `type_of` pre-checks were redundant.
        let concl = hol::hol_eq_at_with(cod, lhs, rhs, cons);
        let hyps = self.hyps.union(&arg.hyps);
        Self::build(hyps, concl)
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
        let (s, t, alpha) = parse_hol_eq_at(&self.concl)?;
        let alpha = alpha.clone();
        let var = Var::new(name, ty.clone());
        // The bound variable `var` must not be free in the hypotheses
        // (HOL Light's ABS side-condition).
        for h in self.hyps.iter() {
            if has_free_var_typed(h, &var) {
                return Err(Error::FreeVarInHyps { name: name.into() });
            }
        }
        let s = s.clone();
        let t = t.clone();
        // Bind exactly the variable `var`; a same-named variable at a
        // different type is untouched.
        let s_abs = Term::abs_with(ty.clone(), close_var(&s, &var), cons);
        let t_abs = Term::abs_with(ty.clone(), close_var(&t, &var), cons);
        // The abstractions have type `ty → alpha` (alpha = the bodies'
        // shared element type from the input `Eq` head), so that is the
        // result equation's element type — no walk.
        let concl = hol::hol_eq_at_with(Type::fun(ty, alpha), s_abs, t_abs, cons);
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
        let rhs = open_with(body, arg, cons);
        let concl = hol::hol_eq_with(app.clone(), rhs, cons);
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
        let (p, q, alpha) = parse_hol_eq_at(&self.concl)?;
        // p = q must be at type bool (otherwise it's not an
        // implication-shaped equation). `alpha` is p's type, read off the
        // `Eq` head — no walk.
        if !alpha.is_bool() {
            return Err(Error::NotBool(alpha.clone()));
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

    /// HOL Light's `INST`: substitute the free variable `(name,
    /// replacement_ty)` — identified by name **and** type — with
    /// `replacement`. A same-named variable at a different type is a
    /// distinct variable and is left untouched (so a type-mismatched
    /// substitution is a no-op, as in HOL Light's `vsubst`).
    pub fn inst(self, name: &str, replacement: Term) -> Result<Thm> {
        let var = Var::new(name, replacement.type_of()?);
        let concl = subst_free(&self.concl, &var, &replacement);
        let hyps = self.hyps.map(|h| subst_free(h, &var, &replacement));
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
        let (a, b, alpha) = parse_hol_eq_at(&self.concl)?;
        let concl = hol::hol_eq_at(alpha.clone(), b.clone(), a.clone());
        Self::build(self.hyps, concl)
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
        // The generalised variable `(name, ty)` must not be free in the
        // hypotheses.
        let var = Var::new(name, ty.clone());
        for h in self.hyps.iter() {
            if has_free_var_typed(h, &var) {
                return Err(Error::FreeVarInHyps { name: name.into() });
            }
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
        let (ty, body) = parse_hol_forall(&self.concl)?;
        let wit_ty = witness.type_of()?;
        if wit_ty != *ty {
            return Err(Error::TypeMismatch {
                expected: ty.clone(),
                got: wit_ty,
            });
        }
        let concl = open_with(body, &witness, cons);
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
        // typing a `TermKind::Spec` leaf. The substitution must be
        // simultaneous (see [`inst_spec_tvars`]): a sequential fold
        // would mangle a parameter swap.
        let tvars = declared_ty.free_tvars();
        let unfolded = inst_spec_tvars(&body, &tvars, &args);

        Self::build(Ctx::new(), hol::hol_eq(t, unfolded))
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
        let (spec, args) = match t.kind() {
            TermKind::Spec(spec, args) => (spec.clone(), args.clone()),
            _ => return Err(Error::NotASpec),
        };
        let declared_ty = spec.ty().ok_or(Error::SpecHasNoBody)?.clone();
        let body = spec.tm().ok_or(Error::SpecHasNoBody)?.clone();

        // def-style ↔ body : declared_ty → bool (let-style ↔ body :
        // declared_ty, handled by `unfold_term_spec`).
        let body_ty = body.type_of()?;
        if body_ty != Type::fun(declared_ty.clone(), Type::bool()) {
            return Err(Error::SpecIsLetStyle);
        }

        // Instantiate the predicate at the supplied type args — same
        // positional order as `unfold_term_spec` / `type_of_in`, and
        // simultaneously (see [`inst_spec_tvars`]).
        let tvars = declared_ty.free_tvars();
        let pred = inst_spec_tvars(&body, &tvars, &args);

        // `w` must inhabit the spec's carrier (= `t`'s type), so that
        // both `p w` and `p t` type-check at `bool`.
        let carrier = t.type_of()?;
        let w_ty = w.type_of()?;
        if w_ty != carrier {
            return Err(Error::TypeMismatch {
                expected: carrier,
                got: w_ty,
            });
        }

        let prem = Term::app(pred.clone(), w);
        let concl = Term::app(pred, t.clone());
        Self::build(Ctx::new(), hol::hol_imp(prem, concl))
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
    /// the standard Hilbert-choice interpretation of `Select` (the
    /// axiom that was previously declared-but-unexposed). Combined with
    /// the connective definitions it yields the existence form
    /// `(∃x. p x) ⟹ p (ε p)` downstream.
    pub fn select_ax(p: Term, x: Term) -> Result<Thm> {
        let p_ty = p.type_of()?;
        let TypeKind::Fun(dom, cod) = p_ty.kind() else {
            return Err(Error::NotFunction(p_ty));
        };
        if !cod.is_bool() {
            return Err(Error::NotBool(cod.clone()));
        }
        let x_ty = x.type_of()?;
        if *dom != x_ty {
            return Err(Error::TypeMismatch {
                expected: dom.clone(),
                got: x_ty,
            });
        }
        let choice = Term::app(Term::select_op(dom.clone()), p.clone());
        let prem = Term::app(p.clone(), x);
        let concl = Term::app(p, choice);
        Self::build(Ctx::new(), hol::hol_imp(prem, concl))
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
        let (abs, rep, _carrier, wrapper) = spec_coercions(&spec, &args)?;
        let a_ty = a.type_of()?;
        if a_ty != wrapper {
            return Err(Error::TypeMismatch {
                expected: wrapper,
                got: a_ty,
            });
        }
        let lhs = Term::app(abs, Term::app(rep, a.clone()));
        Self::build(Ctx::new(), hol::hol_eq(lhs, a))
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
        let (abs, rep, carrier, _wrapper) = spec_coercions(&spec, &args)?;
        let a_ty = a.type_of()?;
        if a_ty != carrier {
            return Err(Error::TypeMismatch {
                expected: carrier,
                got: a_ty,
            });
        }
        let pred = subtype_pred(&spec, &args, &carrier)?;
        let prem = Term::app(pred, a.clone());
        let eq = hol::hol_eq(Term::app(rep, Term::app(abs, a.clone())), a);
        Self::build(Ctx::new(), hol::hol_imp(prem, eq))
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
        let (abs, rep, carrier, _wrapper) = spec_coercions(&spec, &args)?;
        let a_ty = a.type_of()?;
        if a_ty != carrier {
            return Err(Error::TypeMismatch {
                expected: carrier,
                got: a_ty,
            });
        }
        let pred = subtype_pred(&spec, &args, &carrier)?;
        let prem = hol::hol_eq(Term::app(rep, Term::app(abs, a.clone())), a.clone());
        let pa = Term::app(pred.clone(), a);
        let some_x = hol::hol_exists(
            "x",
            carrier.clone(),
            Term::app(pred, Term::free("x", carrier)),
        );
        let disj = hol::hol_or(pa, hol::hol_not(some_x));
        Self::build(Ctx::new(), hol::hol_imp(prem, disj))
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
        // Type-check `t` up front. `reduce_prim_term` matches purely on
        // shape and would happily "reduce" an ill-typed application such
        // as `Eq(nat)` applied to two `bool` literals; building the
        // conclusion via `hol::hol_eq` would then panic on `t`'s bad
        // type. Validating here turns that into a clean `Err`.
        let _ = t.type_of()?;
        let reduced = builtins::reduce_prim_term(&t).ok_or(Error::NotReducible)?;
        Self::build(Ctx::new(), hol::hol_eq_with(t, reduced, cons))
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
        let TermKind::Free(nv) = n_free.kind() else {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: induction variable {n_free} is not a free variable"
            )));
        };
        if *nv.ty() != nat {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: induction variable {n_free} is not of type nat"
            )));
        }
        let expected_conseq = Term::app(p.clone(), Term::app(hol::succ_fn(), n_free.clone()));
        if *conseq != expected_conseq {
            return Err(Error::ConnectiveRule(format!(
                "nat_induct: step consequent {conseq} is not `p (succ n)`"
            )));
        }

        // GEN side conditions: the variable `nv` free neither in the
        // motive nor in the step's hypotheses.
        if has_free_var_typed(&p, nv) {
            return Err(Error::ConnectiveRule(
                "nat_induct: induction variable occurs free in the motive".into(),
            ));
        }
        for h in step.hyps.iter() {
            if has_free_var_typed(h, nv) {
                return Err(Error::FreeVarInHyps {
                    name: nv.name().into(),
                });
            }
        }

        let n_name = nv.name().to_string();
        let body = Term::app(p, n_free.clone());
        let concl = hol::hol_forall(&n_name, nat, body);
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
        let nat = Type::nat();
        for t in [&m, &n] {
            let ty = t.type_of()?;
            if ty != nat {
                return Err(Error::TypeMismatch {
                    expected: nat.clone(),
                    got: ty,
                });
            }
        }
        let prem = hol::hol_eq(
            Term::app(Term::succ(), m.clone()),
            Term::app(Term::succ(), n.clone()),
        );
        let concl = hol::hol_eq(m, n);
        Self::build(Ctx::new(), hol::hol_imp(prem, concl))
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
        let nat = Type::nat();
        let n_ty = n.type_of()?;
        if n_ty != nat {
            return Err(Error::TypeMismatch {
                expected: nat,
                got: n_ty,
            });
        }
        let zero = Term::nat_lit(covalence_types::Nat::zero());
        let eq = hol::hol_eq(zero, Term::app(Term::succ(), n));
        Self::build(Ctx::new(), hol::hol_not(eq))
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
        let p_ty = p.type_of()?;
        if !p_ty.is_bool() {
            return Err(Error::NotBool(p_ty));
        }
        let concl = hol::hol_or(p.clone(), hol::hol_not(p));
        Self::build(Ctx::new(), concl)
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
