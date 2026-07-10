//! The defined-`T`/`F` ↔ `Bool`-literal **bridge** (stage EG3b) —
//! untrusted derivations, eval tier.
//!
//! Since EG3b the connective calculus runs over the *defined* constants
//! [`defs::tru`] / [`defs::fal`] (`T ≡ (λp.p)=(λp.p)`, `F ≡ ∀p:bool.p`),
//! while the transitional `TermKind::Bool` literals `⌜T⌝` / `⌜F⌝` remain
//! the certificate path's output currency (`⊢ (2+2=4) = ⌜T⌝`, …) until
//! the literal-leaf endgame (EG5). This module derives the two
//! coexistence equations — **zero new TCB**; every step is an admitted
//! kernel mint, so nothing here can forge:
//!
//! - [`tru_eq_lit`] `⊢ T = ⌜T⌝` — `deduct_antisym` of the two truths
//!   (`⊢ T` at the pure tier, `⊢ ⌜T⌝` via `LitEqCert`).
//! - [`fal_eq_lit`] `⊢ F = ⌜F⌝` — `deduct_antisym` of `{F} ⊢ ⌜F⌝`
//!   (unfold `F`, `∀`-elim at `⌜F⌝`) and `{⌜F⌝} ⊢ F`
//!   ([`fal_from_lit`]).
//!
//! The interesting direction is the **literal ex falso** inside
//! [`fal_from_lit`]: the literal `⌜F⌝` has no defining equation, so its
//! only eliminable content is what the certificate family committed to.
//! The derivation routes through nat freeness:
//!
//! 1. `⊢ (⌜0⌝ = ⌜1⌝) = ⌜F⌝`      (`LitEqCert` disequality)
//! 2. `Γ ⊢ ⌜0⌝ = ⌜1⌝`             (`sym` + `eq_mp` with `Γ ⊢ ⌜F⌝`)
//! 3. `⊢ succ ⌜0⌝ = ⌜1⌝`          (`SuccCert`)
//! 4. `Γ ⊢ ⌜0⌝ = succ ⌜0⌝`        (`trans` with `sym` of 3)
//! 5. `⊢ ¬(⌜0⌝ = succ ⌜0⌝)`       (kernel `zero_ne_succ`)
//! 6. `Γ ⊢ F`                     (derived `not_elim` of 5 against 4)
//!
//! This is necessarily an **eval-tier** derivation (steps 1/3 are cert
//! mints), which is exactly the coexistence contract: at the pure
//! `CoreLang` tier the literals carry no commitments at all.

use std::sync::LazyLock;

use covalence_core::seam::Lit;
use covalence_core::{Error, Result, Term, TermKind};
use covalence_types::Nat;

use crate::derived::{self, DerivedRules};
use crate::{EvalThm, defs, mint, rules};

/// `⊢ T = ⌜T⌝` — the defined truth equals the transitional literal
/// (cached). Derived: `deduct_antisym(⊢ T, ⊢ ⌜T⌝)`.
pub fn tru_eq_lit() -> Result<EvalThm> {
    static S: LazyLock<EvalThm> = LazyLock::new(|| {
        (|| -> Result<EvalThm> {
            let t_def = derived::truth::<crate::CoreEval>()?; // ⊢ T (pure-tier derivation, lifted)
            let t_lit = crate::lit_truth()?; // ⊢ ⌜T⌝ (LitEqCert)
            t_def.deduct_antisym(t_lit) // ⊢ T = ⌜T⌝
        })()
        .expect("boolean: ⊢ T = ⌜T⌝")
    });
    Ok(S.clone())
}

/// `Γ ⊢ F` (the **defined** `F`), given `Γ ⊢ ⌜F⌝` (the literal) — the
/// literal ex falso, derived through nat freeness (see the module docs).
pub fn fal_from_lit(th: EvalThm) -> Result<EvalThm> {
    if !matches!(th.concl().kind(), TermKind::Bool(false)) {
        return Err(Error::ConnectiveRule(format!(
            "fal_from_lit: conclusion {} is not the literal ⌜F⌝",
            th.concl()
        )));
    }
    let zero = Lit::Nat(Nat::zero()).to_term();
    // 1-2. Γ ⊢ ⌜0⌝ = ⌜1⌝.
    let diseq = mint(
        rules::LitEqCert,
        (Lit::Nat(Nat::zero()), Lit::Nat(Nat::from(1u32))),
    )
    .ok_or(Error::NotReducible)?; // ⊢ (⌜0⌝ = ⌜1⌝) = ⌜F⌝
    let zero_eq_one = diseq.sym()?.eq_mp(th)?; // Γ ⊢ ⌜0⌝ = ⌜1⌝
    // 3-4. Γ ⊢ ⌜0⌝ = succ ⌜0⌝.
    let succ = mint(rules::SuccCert, Nat::zero()).ok_or(Error::NotReducible)?; // ⊢ succ ⌜0⌝ = ⌜1⌝
    let zero_eq_succ = zero_eq_one.trans(succ.sym()?)?; // Γ ⊢ ⌜0⌝ = succ ⌜0⌝
    // 5-6. Γ ⊢ F.
    let neg = EvalThm::zero_ne_succ(zero)?; // ⊢ ¬(⌜0⌝ = succ ⌜0⌝)
    neg.not_elim(zero_eq_succ) // Γ ⊢ F  (derived ¬-elim concludes the defined F)
}

/// `⊢ F = ⌜F⌝` — the defined falsity equals the transitional literal
/// (cached). Derived: `deduct_antisym({⌜F⌝} ⊢ F, {F} ⊢ ⌜F⌝)`, both
/// halves themselves derivations (see the module docs).
pub fn fal_eq_lit() -> Result<EvalThm> {
    static S: LazyLock<EvalThm> = LazyLock::new(|| {
        (|| -> Result<EvalThm> {
            // {F} ⊢ ⌜F⌝: unfold F to ∀p:bool. p, then ∀-elim at ⌜F⌝.
            let unfold = crate::delta(&defs::fal())?; // ⊢ F = (∀p:bool. p)
            let all = unfold.eq_mp(EvalThm::assume(defs::fal())?)?; // {F} ⊢ ∀p:bool. p
            let f_lit = all.all_elim(Term::bool_lit(false))?; // {F} ⊢ ⌜F⌝
            // {⌜F⌝} ⊢ F: the literal ex falso.
            let f_def = fal_from_lit(EvalThm::assume(Term::bool_lit(false))?)?;
            f_def.deduct_antisym(f_lit) // ⊢ F = ⌜F⌝
        })()
        .expect("boolean: ⊢ F = ⌜F⌝")
    });
    Ok(S.clone())
}

/// `Γ ⊢ ⌜F⌝`, given `Γ ⊢ F` (the defined constant) — the other
/// direction of the bridge, one `eq_mp` against [`fal_eq_lit`].
pub fn fal_to_lit(th: EvalThm) -> Result<EvalThm> {
    fal_eq_lit()?.eq_mp(th)
}

/// `Γ ⊢ ⌜T⌝`, given `Γ ⊢ T` (the defined constant) — one `eq_mp`
/// against [`tru_eq_lit`].
pub fn tru_to_lit(th: EvalThm) -> Result<EvalThm> {
    tru_eq_lit()?.eq_mp(th)
}

/// `Γ ⊢ T`, given `Γ ⊢ ⌜T⌝` — one `eq_mp` against the `sym` of
/// [`tru_eq_lit`].
pub fn tru_from_lit(th: EvalThm) -> Result<EvalThm> {
    tru_eq_lit()?.sym()?.eq_mp(th)
}
