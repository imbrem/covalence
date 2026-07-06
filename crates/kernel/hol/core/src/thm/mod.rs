//! Core theorems and the LCF rule API.
//!
//! `Thm` is the opaque kernel certificate. Every public method here is thin glue
//! over the sound rule catalogue in `rules`: it pulls the inner `pure::Thm`s out
//! of its premise `core::Thm`s and mints through [`covalence_pure::apply`] on the
//! admitted rule, which DERIVES the conclusion. Soundness rests on `admits()` alone
//! (see `lang` and `rules`) — no method may forge a `Thm`, and the inner field
//! is hygiene-only.
//!
//! The rules are split across the `thm/` module: the equality-core rules'
//! glue lives here; the conservative-extension primitives (`define`,
//! `new_type_definition`) live in `typedef`; every rule's ZST + `decide`
//! (the fine-grained TCB) lives in `rules`. The connective / quantifier
//! rules and excluded middle are NOT here: since stage L2 they are
//! zero-TCB derivations (`covalence-hol-eval::derived::DerivedRules`).
//!
//! ## Universality
//!
//! Every `Thm` is oracle-free: the observer rules and their `Obs`
//! leaves were deleted in the toHOL purge, so a theorem is
//! **universally true** with no oracle dependencies — the same
//! property HOL Light's `thm` has. `new_type_definition`'s freshness
//! now rides the dedicated `FreshConst`/`FreshTyCon` leaves (private
//! `FreshId` tokens, allocated only inside the rule).
//!
//! The rule set is Core-shaped:
//!
//! - LF: `assume`, `eq_mp`, `deduct_antisym`.
//! - Equality: `refl`, `trans`, `sym`, `cong_app`, `cong_abs`,
//!   `beta_conv`, `eta_conv`.
//! - Substitution: `inst`, `inst_tfree`.

use std::collections::BTreeMap;
use std::fmt;

use smol_str::SmolStr;

use crate::ctx::Ctx;
use crate::error::{Error, Result};
use crate::subst::subst_tfrees_in_term;

use crate::term::{Term, TermKind, TrustedCons, Type, TypeKind};
use crate::ty::{TypeList, TypeSpec};

pub(crate) mod lang;
pub(crate) mod lit;
pub(crate) mod rules;
mod typedef;
pub use typedef::TypeDef;

use covalence_pure::{Expr, Val};

use lang::{CoreLang, HolTier, IsThmProp};
use rules::*;

/// The kernel certificate, generic over its **tier** `L` (default
/// [`CoreLang`], the pure-HOL tier). A newtype over a `covalence_pure`
/// theorem carrying the structured proposition `IsThm(Γ, φ)` at tier `L`;
/// see `lang` for the admits-only soundness argument and `rules` for the
/// fine-grained rule catalogue that mints it.
///
/// ## Tiers
///
/// The tier parameter is a *trust declaration*, not a proof mechanism:
/// `Thm<CoreLang>` certifies derivability from the HOL rule catalogue alone
/// (no computation axioms), while a higher tier (a [`HolTier`] language that
/// `extends` `CoreLang` and admits additional rules — the planned `CoreEval`
/// in `covalence-hol-eval`) certifies derivability from that tier's larger
/// admitted set. Low-tier theorems enter a higher tier via [`Thm::lift`];
/// there is no path down. Every rule constructor below is tier-generic and
/// mints at `L::default()` — the gate is always `admits` on the rule's own
/// `TypeId`, so a tier proves nothing it does not itself admit.
///
/// The inner `pure::Thm` field is **hygiene-only**: it keeps `pure::Thm`/the
/// tier language out of the public signature and preserves `Arc`-identity, but
/// it is NOT load-bearing for soundness. Soundness rests on `admits()` alone —
/// every rule a tier admits derives its conclusion from unforgeable premise
/// `pure::Thm`s and is sound on all inputs — so even a hypothetically-public
/// field could only wrap already-true theorems.
///
/// ## The conclusion operand `C` (the literal-endgame mechanism)
///
/// The second parameter `C` (default `Val<Term>`) is the **conclusion
/// operand** of the carried proposition `IsThm(Γ, φ)` — see [`IsThmProp`].
/// `Thm<L>` still means `Thm<L, Val<Term>>` (a *concrete* term conclusion),
/// so the entire HOL rule catalogue and every accessor below live in
/// `impl<L: HolTier> Thm<L>` and resolve to the default operand **unchanged**.
///
/// A non-default `C` is a *symbolic* conclusion — e.g. `Thm<CoreEval,
/// NatAddEqE>` carries `nat.add (toHOL a) (toHOL b) = toHOL (a+b)` with the
/// naturals held as native `Val<Nat>` leaves under the uninterpreted
/// `ToHolNat` op, so a big value's succ-tower is **never materialized**
/// (design: `notes/vibes/literal-endgame-design.md`). Symbolic theorems are
/// landed via [`Thm::from_pure_sym`] and read via [`Thm::sym_concl`]; the base
/// `eq_mp`/`trans`/`cong` calculus already transports the `App`/`Val` operand
/// shapes, so the mechanism adds **zero** base-TCB machinery.
#[derive(Clone)]
pub struct Thm<L: HolTier = CoreLang, C = Val<Term>>(covalence_pure::Thm<L, IsThmProp<C>>)
where
    C: Expr<Ty = Term>;

/// The **symbolic-conclusion** surface, generic over the operand `C` (the
/// literal-endgame mechanism). Available at every `C: Expr<Ty = Term>` —
/// including the default `C = Val<Term>`, where it coexists with the concrete
/// [`concl`](Thm::concl)/[`hyps`](Thm::hyps) accessors below.
impl<L: HolTier, C: Expr<Ty = Term>> Thm<L, C> {
    /// Wrap an already-minted pure theorem `⊢ IsThm(Γ, φ)` **whose conclusion
    /// operand `φ` is the symbolic expression `C`** (never materialized) as a
    /// kernel [`Thm<L, C>`] — the literal-endgame landing constructor (design:
    /// `notes/vibes/literal-endgame-design.md`, stage EG1).
    ///
    /// ## Why there is no sequent floor here (and why that is sound)
    ///
    /// [`from_pure`](Thm::from_pure) re-runs `check_sequent` on the *concrete*
    /// `Term` conclusion. That cannot be done here without **forcing** the
    /// symbolic operand into a concrete term (materializing the very
    /// succ-tower the mechanism exists to avoid), so this constructor does
    /// **not** re-check well-typedness. It is sound on exactly the same
    /// footing `from_pure`'s docstring already relies on — *soundness rests on
    /// `admits()` alone*:
    ///
    /// A `pure::Thm<L, IsThmProp<C>>` (an `IsThm`-headed proposition) can only
    /// have come from (a) an admitted rule whose `decide` **derives** the
    /// whole conclusion — the only such rules with an `IsThm`-headed `Concl`
    /// are the eval-tier certificate rules, each of which builds a
    /// well-typed sequent (`NatAddCert` via `nat_add_eq_expr`, the others via
    /// their `seq` floor) — or (b) the ungated equality/bool calculus
    /// (`eq_mp`/`trans`/`cong`/…) transporting such a theorem, which preserves
    /// well-typedness. No `refl`/`of_eq`/bool-theory mint produces an
    /// `IsThm`-headed prop. So the landed theorem is already a true, well-typed
    /// sequent of tier `L`; wrapping it adds nothing, exactly as for
    /// `from_pure`. (The non-forcing well-typedness of a symbolic conclusion is
    /// demonstrated machine-checkably in
    /// `covalence-hol-eval`'s `nat_add_symbolic_never_materializes` test, which
    /// walks the operand and confirms it holds **no** materialized numeral.)
    ///
    /// **WIDENED TRUST OBLIGATION (audit):** unlike [`from_pure`](Thm::from_pure), this does NOT
    /// re-run `check_sequent` (it cannot, without forcing the symbolic operand —
    /// the whole point). Its soundness therefore rests on the invariant that
    /// EVERY admitted rule reachable to produce an `IsThm`-headed `Thm<L,
    /// IsThmProp<C>>` self-floors to a well-typed HOL-bool sequent. Each symbolic
    /// lander MUST carry a well-typedness witness (a floored concrete sibling, or
    /// equivalent proof); see `covalence-hol-eval`'s
    /// `nat_add_symbolic_lander_self_floors`. A future cert family that could mint
    /// a non-bool / malformed `IsThm` conclusion MUST NOT be landed through here
    /// without such a witness.
    pub fn from_pure_sym(t: covalence_pure::Thm<L, IsThmProp<C>>) -> Thm<L, C> {
        Thm(t)
    }

    /// The **symbolic conclusion operand** `φ : Term` — the expression `C`,
    /// read by reference (reading never mints, and never forces). For the
    /// default `C = Val<Term>` this is the concrete-term leaf; for a symbolic
    /// `C` (e.g. `NatAddEqE`) it is the un-materialized `toHOL` expression an
    /// inspector can walk without building any succ-tower.
    pub fn sym_concl(&self) -> &C {
        &self.0.prop().1.1
    }

    /// The hypotheses `Γ`, read by reference. Always a concrete `Val<Ctx>`
    /// regardless of the conclusion operand `C`, so this works at every tier
    /// and every operand shape.
    pub fn sym_hyps(&self) -> &Ctx {
        &self.0.prop().1.0.0
    }
}

impl<L: HolTier> Thm<L> {
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

    /// Wrap an already-minted pure theorem `⊢ IsThm(Γ, φ)` at tier `L`
    /// as a kernel [`Thm`] — the core-on-pure seam's landing constructor
    /// (see [`crate::seam`]). This is how a toHOL fact, reified to the
    /// concrete `CoreProp` shape and transported with the base `eq_mp`,
    /// re-enters the ordinary `Thm` API.
    ///
    /// **The sequent floor is enforced here**: the conclusion and every
    /// hypothesis are re-checked well-typed at kind `bool` (the same
    /// `rules::check_sequent` helper every sequent rule's `seq` floor
    /// runs), so no landing path bypasses `seq()`. Rejects with
    /// [`Error::NotBool`] (or a typing error) otherwise.
    ///
    /// Soundness: trivial. The inner `pure::Thm` field is hygiene-only —
    /// soundness rests on `admits()` alone (see `lang`/`rules`): a
    /// `pure::Thm<L, CoreProp>` can only ever have been minted by a rule
    /// the tier `L` admits (or by the ungated equality/propositional
    /// calculus from such mints), so it is already a true theorem *of that
    /// tier*; wrapping it adds nothing.
    pub fn from_pure(t: covalence_pure::Thm<L, lang::CoreProp>) -> Result<Thm<L>> {
        {
            let (hyps, concl) = rules::parts(&t);
            rules::check_sequent(hyps, concl)?;
        }
        Ok(Thm(t))
    }

    /// Re-home this theorem at tier `L2`, where `L2` **directly extends**
    /// `L` (runtime-checked via [`covalence_pure::Language::extends`]) —
    /// the low→high tier coercion (there is no path down). Delegates to
    /// [`covalence_pure::Thm::lift`]; errors with [`Error::Pure`] if `L2`
    /// does not extend `L`.
    ///
    /// Soundness: `extends` guarantees `tree(L) ⊆ tree(L2)`, so a theorem
    /// derivable at `L` is derivable at `L2` — lifting adds no strength.
    pub fn lift<L2: HolTier>(self) -> Result<Thm<L2>> {
        self.0
            .lift(L2::default())
            .map(Thm)
            .map_err(|e| Error::Pure(format!("{e:?}")))
    }

    /// Structural weakening: `Δ ⊢ φ`, given `Γ ⊢ φ` and `Γ ⊆ Δ`.
    ///
    /// Rejects with [`Error::NotASuperset`] if any hypothesis of
    /// `self` is missing from `target`. The conclusion is unchanged;
    /// every term in `target` is re-validated at kind `bool` by the
    /// `rules::Weaken` rule's `seq` floor.
    pub fn weaken(self, target: Ctx) -> Result<Thm<L>> {
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
    pub fn refl(t: Term) -> Result<Thm<L>> {
        Self::refl_with(t, &mut ())
    }

    /// [`refl`](Self::refl) building its `t = t` equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`refl`](Self::refl); the cons only shares
    /// the `Arc`s of the conclusion's spine (the `TrustedCons` contract
    /// guarantees a structurally-equal result), so it has no soundness role.
    pub fn refl_with<C: TrustedCons + ?Sized>(t: Term, cons: &mut C) -> Result<Thm<L>> {
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
    pub fn unit_eq(a: Term, b: Term) -> Result<Thm<L>> {
        Self::unit_eq_with(a, b, &mut ())
    }

    /// [`unit_eq`](Self::unit_eq) building its `a = b` equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`unit_eq`](Self::unit_eq); the cons only
    /// shares the `Arc`s of the conclusion's spine, with no soundness role.
    pub fn unit_eq_with<C: TrustedCons + ?Sized>(a: Term, b: Term, cons: &mut C) -> Result<Thm<L>> {
        let thm = mint!(UnitEq, (a.clone(), b.clone()), (a, b))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `Γ ∪ Δ ⊢ s = u`, given `Γ ⊢ s = t` and `Δ ⊢ t = u` (HOL `=`).
    pub fn trans(self, other: Thm<L>) -> Result<Thm<L>> {
        self.trans_with(other, &mut ())
    }

    /// [`trans`](Self::trans) building its `s = u` equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`trans`](Self::trans); the cons only shares
    /// the `Arc`s of the conclusion's spine, with no soundness role.
    pub fn trans_with<C: TrustedCons + ?Sized>(
        self,
        other: Thm<L>,
        cons: &mut C,
    ) -> Result<Thm<L>> {
        let thm = mint!(Trans, (self.0.clone(), other.0.clone()), (self.0, other.0))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `Γ ∪ Δ ⊢ f x = g y`, given `Γ ⊢ f = g` and `Δ ⊢ x = y`. The
    /// applications must type-check: `f` (and so `g`) must have
    /// function type whose domain matches `x`'s (and so `y`'s) type.
    pub fn mk_comb(self, arg: Thm<L>) -> Result<Thm<L>> {
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
    pub fn mk_comb_with<C: TrustedCons + ?Sized>(
        self,
        arg: Thm<L>,
        cons: &mut C,
    ) -> Result<Thm<L>> {
        let thm = mint!(MkComb, (self.0.clone(), arg.0.clone()), (self.0, arg.0))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `Γ ⊢ (λx:τ. s[x]) = (λx:τ. t[x])`, given `Γ ⊢ s = t` with
    /// `Free(name:τ)` not free in `Γ`.
    pub fn abs(self, name: &str, ty: Type) -> Result<Thm<L>> {
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
    ) -> Result<Thm<L>> {
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
    ///   (that lives in the certificate path driven by
    ///   `covalence-hol-eval` — e.g. `(λx. x) (2 + 3)` reduces to
    ///   `2 + 3`, *not* `5`), and no η-contraction (see
    ///   [`Thm::eta_conv`]).
    pub fn beta_conv(app: Term) -> Result<Thm<L>> {
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
    pub fn beta_conv_with<C: TrustedCons + ?Sized>(app: Term, cons: &mut C) -> Result<Thm<L>> {
        let thm = mint!(BetaConv, (app.clone(),), (app,))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// `{p} ⊢ p` for any `p : bool` — HOL-level assume.
    pub fn assume(p: Term) -> Result<Thm<L>> {
        mint!(Assume, (p.clone(),), (p,))
    }

    /// `Γ ∪ Δ ⊢ q`, given `Γ ⊢ p = q : bool` and `Δ ⊢ p`. HOL Light's
    /// `EQ_MP` — equality at `bool` IS biconditional, so this also
    /// implements the `⇔`-elim direction.
    pub fn eq_mp(self, p_thm: Thm<L>) -> Result<Thm<L>> {
        self.eq_mp_with(p_thm, &mut ())
    }

    /// [`eq_mp`](Self::eq_mp) with a caller-supplied [`TrustedCons`] for
    /// API uniformity with the other cons-aware congruence rules.
    ///
    /// `eq_mp` builds **no new `Term` nodes** — its conclusion `q` is taken
    /// directly from the input equation — so the cons is unused. It is
    /// accepted only so a rewrite driver can thread one cons uniformly
    /// through `trans` / `mk_comb` / `eq_mp`. No soundness role.
    pub fn eq_mp_with<C: TrustedCons + ?Sized>(
        self,
        p_thm: Thm<L>,
        _cons: &mut C,
    ) -> Result<Thm<L>> {
        mint!(EqMp, (self.0.clone(), p_thm.0.clone()), (self.0, p_thm.0))
    }

    /// HOL Light's `DEDUCT_ANTISYM_RULE`:
    /// `(Γ \ {q}) ∪ (Δ \ {p}) ⊢ p ⇔ q`, given `Γ ⊢ p` and `Δ ⊢ q`.
    /// Both `p` and `q` must be `bool`-typed; equality at `bool`
    /// IS biconditional.
    pub fn deduct_antisym(self, other: Thm<L>) -> Result<Thm<L>> {
        self.deduct_antisym_with(other, &mut ())
    }

    /// [`deduct_antisym`](Self::deduct_antisym) building its `p ⇔ q`
    /// equation through a caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`deduct_antisym`](Self::deduct_antisym);
    /// the cons only shares the `Arc`s of the conclusion's spine, with no
    /// soundness role.
    pub fn deduct_antisym_with<C: TrustedCons + ?Sized>(
        self,
        other: Thm<L>,
        cons: &mut C,
    ) -> Result<Thm<L>> {
        let thm = mint!(
            DeductAntisym,
            (self.0.clone(), other.0.clone()),
            (self.0, other.0)
        )?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// HOL Light's `INST`: substitute the free variable `(name,
    /// replacement_ty)` — identified by name **and** type — with
    /// `replacement`. A same-named variable at a different type is a
    /// distinct variable and is left untouched (so a type-mismatched
    /// substitution is a no-op, as in HOL Light's `vsubst`).
    pub fn inst(self, name: &str, replacement: Term) -> Result<Thm<L>> {
        self.inst_with(name, replacement, &mut ())
    }

    /// [`inst`](Self::inst) interning its substituted conclusion **and
    /// hypotheses** (both are freshly rebuilt by the substitution) through
    /// a caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`inst`](Self::inst); the cons only shares
    /// the `Arc`s of the rebuilt spines, with no soundness role.
    pub fn inst_with<C: TrustedCons + ?Sized>(
        self,
        name: &str,
        replacement: Term,
        cons: &mut C,
    ) -> Result<Thm<L>> {
        let n = SmolStr::from(name);
        let thm = mint!(
            Inst,
            (self.0.clone(), n.clone(), replacement.clone()),
            (self.0, n, replacement)
        )?;
        intern_thm(&thm, cons);
        Ok(thm)
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
    pub fn sym(self) -> Result<Thm<L>> {
        self.sym_with(&mut ())
    }

    /// [`sym`](Self::sym) building its reversed `b = a` equation through a
    /// caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`sym`](Self::sym); the cons only shares the
    /// `Arc`s of the conclusion's spine, with no soundness role.
    pub fn sym_with<C: TrustedCons + ?Sized>(self, cons: &mut C) -> Result<Thm<L>> {
        let thm = mint!(Sym, (self.0.clone(),), (self.0,))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    /// Alias for [`Thm::mk_comb`]. `cong_app` is the equational-
    /// congruence name (`f = g, x = y ⊢ f x = g y`); HOL Light
    /// calls it `MK_COMB`. Same rule.
    pub fn cong_app(self, arg: Thm<L>) -> Result<Thm<L>> {
        self.mk_comb(arg)
    }

    /// Alias for [`Thm::mk_comb_with`] — the cons-aware
    /// [`cong_app`](Self::cong_app).
    pub fn cong_app_with<C: TrustedCons + ?Sized>(
        self,
        arg: Thm<L>,
        cons: &mut C,
    ) -> Result<Thm<L>> {
        self.mk_comb_with(arg, cons)
    }

    /// Alias for [`Thm::abs`]. HOL Light's `ABS`; the equational-
    /// congruence name for the same rule.
    pub fn cong_abs(self, name: &str, ty: Type) -> Result<Thm<L>> {
        self.abs(name, ty)
    }

    /// Alias for [`Thm::abs_with`] — the cons-aware
    /// [`cong_abs`](Self::cong_abs).
    pub fn cong_abs_with<C: TrustedCons + ?Sized>(
        self,
        name: &str,
        ty: Type,
        cons: &mut C,
    ) -> Result<Thm<L>> {
        self.abs_with(name, ty, cons)
    }

    /// `⊢ (λx:τ. f x) = f`, when `Bound(0)` does not appear free
    /// in `f`. HOL Light's `ETA_AX` (a primitive axiom there; here
    /// exposed as a rule that discharges well-formedness in one
    /// step).
    pub fn eta_conv(abs: Term) -> Result<Thm<L>> {
        Self::eta_conv_with(abs, &mut ())
    }

    /// [`eta_conv`](Self::eta_conv) building its `(λx. f x) = f` equation
    /// (including the un-shifted `f` on the right) through a caller-supplied
    /// [`TrustedCons`].
    ///
    /// Soundness: identical to [`eta_conv`](Self::eta_conv); the cons only
    /// shares the `Arc`s of the conclusion's spine, with no soundness role.
    pub fn eta_conv_with<C: TrustedCons + ?Sized>(abs: Term, cons: &mut C) -> Result<Thm<L>> {
        let thm = mint!(EtaConv, (abs.clone(),), (abs,))?;
        intern_concl(&thm, cons);
        Ok(thm)
    }

    // ========================================================================
    // Connective / quantifier rules: DERIVED, not kernel (stage L2)
    // ========================================================================
    //
    // `∧` / `∨` / `¬` / `⟹` / `∀` are ordinary defined constants in
    // `defs/logic.rs`; their intro / elim rules (and excluded middle)
    // are *derivations* over the equality-core rules above — the
    // standard HOL Light `bool.ml` bootstrap. They live, with the same
    // signatures, in `covalence-hol-eval::derived::DerivedRules`
    // (eval tier: the bootstrap's `⊢ T` comes from the certificate
    // path). Zero TCB: nothing connective-shaped is admitted here.

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
    /// catalogue. (Note: when a spec is **also** decided by the family
    /// certificate rules — e.g. `nat.add`, `nat.mod` — the two paths
    /// commit two facts about it, so the body MUST denote the same
    /// function the certificates compute; see
    /// `covalence-hol-eval`'s `tests/audit_reduce.rs::audit_reduce_matches_body`.)
    pub fn unfold_term_spec(t: Term) -> Result<Thm<L>> {
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
    pub fn spec_ax(t: Term, w: Term) -> Result<Thm<L>> {
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
    pub fn select_ax(p: Term, x: Term) -> Result<Thm<L>> {
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
    // coercions are entirely separate from the fresh-const abs/rep that
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
    pub fn spec_abs_rep(spec: TypeSpec, args: impl Into<TypeList>, a: Term) -> Result<Thm<L>> {
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
    pub fn spec_rep_abs_fwd(spec: TypeSpec, args: impl Into<TypeList>, a: Term) -> Result<Thm<L>> {
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
    pub fn spec_rep_abs_back(spec: TypeSpec, args: impl Into<TypeList>, a: Term) -> Result<Thm<L>> {
        let args = args.into();
        mint!(
            SpecRepAbsBack,
            (spec.clone(), args.clone(), a.clone()),
            (spec, args, a)
        )
    }

    /// `Γ[α:=σ] ⊢ φ[α:=σ]`.
    pub fn inst_tfree(self, name: &str, replacement: Type) -> Result<Thm<L>> {
        self.inst_tfree_with(name, replacement, &mut ())
    }

    /// [`inst_tfree`](Self::inst_tfree) interning its substituted conclusion
    /// **and hypotheses** (both are freshly rebuilt by the type
    /// substitution) through a caller-supplied [`TrustedCons`].
    ///
    /// Soundness: identical to [`inst_tfree`](Self::inst_tfree); the cons
    /// only shares the `Arc`s of the rebuilt spines, with no soundness role.
    pub fn inst_tfree_with<C: TrustedCons + ?Sized>(
        self,
        name: &str,
        replacement: Type,
        cons: &mut C,
    ) -> Result<Thm<L>> {
        let n = SmolStr::from(name);
        let thm = mint!(
            InstTFree,
            (self.0.clone(), n.clone(), replacement.clone()),
            (self.0, n, replacement)
        )?;
        intern_thm(&thm, cons);
        Ok(thm)
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
    // unproved in hypothesis audits).
    //
    // **Computational axioms** (the reduce-on-literals rules) live
    // separately: `Thm::unfold_term_spec` plus the per-family
    // certificate rules (driven by `covalence-hol-eval`). Those are
    // *accelerated* reduction steps — each is a one-shot
    // `t = canonical_form` equation justified by the literal's
    // denotation, not a logical postulate.

    /// Mathematical induction on `nat`, as a primitive **rule** in
    /// connective-free **sequent form**.
    ///
    /// Given a proposition `p : bool` (with the induction variable
    /// `x : nat` free), a base proof `Γ_b ⊢ p[0/x]`, and a step proof
    /// `Γ_s ⊢ p[succ x/x]` whose hypotheses contain `p` itself (the
    /// discharged induction hypothesis), returns
    /// `Γ_b ∪ (Γ_s \ {p}) ⊢ p` — `x` stays free in the conclusion,
    /// universal by genericity. The substituted instances are computed
    /// here (single-variable [`crate::subst::subst_free`], `succ` =
    /// [`crate::hol::succ_fn`], `0` = the `Nat` literal) and compared
    /// syntactically against the two premises' conclusions.
    ///
    /// Side conditions:
    /// - `x` must NOT occur free in `Γ_s \ {p}` (soundness-critical, see
    ///   below); it MAY occur free in `Γ_b` and, of course, in `p`.
    /// - `x` need not actually occur in `p`: then `p[0/x] = p[succ x/x]
    ///   = p` and the rule degenerates to weakening the base by
    ///   `Γ_s \ {p}` — sound.
    ///
    /// The old formula form (base `⊢ p 0`, step `⊢ p n ⟹ p (succ n)`,
    /// conclusion `⊢ ∀n. p n`) is a short derivation over this rule plus
    /// `assume`/`imp_elim`/`all_intro`; `covalence-init` ships it as
    /// `init::ext::nat_induct`, a drop-in replacement.
    ///
    /// ## Soundness
    ///
    /// `Type::nat()` denotes exactly the standard naturals, freely
    /// generated by `0` and `succ` — every element is reached from `0`
    /// by finitely many `succ` steps (the same commitment
    /// [`Thm::succ_inj`] / [`Thm::zero_ne_succ`] rest on); and
    /// [`crate::hol::succ_fn`] (`defs::nat_succ`) denotes that successor
    /// (the commitment the pre-reshape rule already made by accepting
    /// steps stated with it).
    ///
    /// Fix a valuation `v` of the free (type) variables with
    /// `v ⊨ Γ_b ∪ (Γ_s \ {p})`; let `k = v(x)` and write `v_j` for
    /// `v[x ↦ j]`. By the substitution lemma, `w ⊨ p[t/x]` iff
    /// `w[x ↦ ⟦t⟧w] ⊨ p` for any valuation `w`:
    ///
    /// - **Base.** `v ⊨ Γ_b` gives `v ⊨ p[0/x]`, i.e. `v_0 ⊨ p`. (This
    ///   uses the base *at `v` itself* — which is why `x` free in `Γ_b`
    ///   is harmless: no re-instantiation of the base ever happens.)
    /// - **Step.** For any `j`: `v_j ⊨ Γ_s \ {p}` because `x` is not
    ///   free there and `v ⊨` them (the side condition — dropping it
    ///   admits e.g. `Γ_s = {x = 0, p}` steps that only work at one
    ///   point). So if `v_j ⊨ p` then `v_j ⊨ Γ_s`, hence
    ///   `v_j ⊨ p[succ x/x]`, i.e. `v_{j+1} ⊨ p`.
    /// - **Induction** (in the metatheory, on the standard naturals):
    ///   `v_j ⊨ p` for every `j`; at `j = k`, `v_k = v`, so `v ⊨ p`. ∎
    ///
    /// This is one of the kernel's two non-computational primitives (the
    /// other is [`Thm::false_elim`]).
    pub fn nat_induct(base: Thm<L>, step: Thm<L>, p: Term, x: &str) -> Result<Thm<L>> {
        Self::nat_induct_with(base, step, p, x, &mut ())
    }

    /// [`nat_induct`](Self::nat_induct) building its substituted premise
    /// instances (`p[0/x]`, `p[succ x/x]`) through a caller-supplied
    /// [`TrustedCons`]-interned conclusion share.
    ///
    /// Soundness: identical to [`nat_induct`](Self::nat_induct); the cons
    /// only shares the `Arc`s of the conclusion's spine, with no soundness
    /// role.
    pub fn nat_induct_with<C: TrustedCons + ?Sized>(
        base: Thm<L>,
        step: Thm<L>,
        p: Term,
        x: &str,
        cons: &mut C,
    ) -> Result<Thm<L>> {
        let n = SmolStr::from(x);
        let thm = mint!(
            NatInduct,
            (base.0.clone(), step.0.clone(), p.clone(), n.clone()),
            (base.0, step.0, p, n)
        )?;
        intern_concl(&thm, cons);
        Ok(thm)
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
    pub fn false_elim(self, p: Term) -> Result<Thm<L>> {
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
    // via the certificate path; these cover *open* terms).

    /// `⊢ (succ m = succ n) ⟹ (m = n)` — successor injectivity. `m`
    /// and `n` must type-check at `nat`.
    ///
    /// ## Soundness
    ///
    /// `Type::nat()` denotes the standard naturals, freely generated by
    /// `0` and `succ`; a free constructor is injective. Sound in every
    /// model the kernel admits (the same `nat` semantics
    /// [`Thm::nat_induct`] and [`Thm::zero_ne_succ`] rest on).
    pub fn succ_inj(m: Term, n: Term) -> Result<Thm<L>> {
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
    pub fn zero_ne_succ(n: Term) -> Result<Thm<L>> {
        mint!(ZeroNeSucc, (n.clone(),), (n,))
    }

    // (Excluded middle — `⊢ p ∨ ¬p` — is no longer a kernel rule: it is
    // derived from `select_ax` the standard HOL way in
    // `covalence-hol-eval::derived::DerivedRules::lem`, closing the
    // long-standing "derivable from ε" cleanup.)
}

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
fn intern_concl<L: HolTier, C: TrustedCons + ?Sized>(thm: &Thm<L>, cons: &mut C) {
    let _ = thm.concl().cons_with(cons);
}

/// [`intern_concl`] plus the hypotheses — for the substitution rules
/// (`inst_with` / `inst_tfree_with`), whose hypotheses are freshly rebuilt
/// alongside the conclusion and so are equally worth sharing. Pure sharing,
/// no soundness role.
fn intern_thm<L: HolTier, C: TrustedCons + ?Sized>(thm: &Thm<L>, cons: &mut C) {
    intern_concl(thm, cons);
    for h in thm.hyps().iter() {
        let _ = h.cons_with(cons);
    }
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

impl<L: HolTier> fmt::Debug for Thm<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<L: HolTier> fmt::Display for Thm<L> {
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
