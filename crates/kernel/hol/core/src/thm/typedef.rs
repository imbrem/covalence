//! Conservative-extension primitives: `Thm::define` (fresh defined
//! constants) and `Thm::new_type_definition` (fresh subtypes), plus
//! the [`TypeDef`] result bundle.
//!
//! Both are the admits-only glue over the generative rules in [`super::rules`]:
//! all fresh identity (the `Def`, and the τ/abs/rep markers) is allocated INSIDE
//! the rules' `decide`, never taken as an input, so an adversary cannot force a
//! collision. `new_type_definition` mints a single conjunction
//! `abs_rep ∧ (fwd ∧ back)` and splits it with core's own admitted `and_elim`
//! rules, recovering τ/abs/rep by shape-parsing the returned theorem.

use smol_str::SmolStr;

use crate::error::{Error, Result};
use crate::term::{Term, TermKind, Type};

use super::Thm;
use super::rules::{Define, NewTypeDefRule, mint};

impl Thm {
    pub fn new_type_definition(
        hint: impl Into<SmolStr>,
        abs_hint: impl Into<SmolStr>,
        rep_hint: impl Into<SmolStr>,
        witness: Thm,
    ) -> Result<TypeDef> {
        // The τ name hint is display-only; the fresh τ marker carries none.
        let _ = hint.into();
        let abs_hint = abs_hint.into();
        let rep_hint = rep_hint.into();

        // Mint the bijection conjunction `abs_rep ∧ (fwd ∧ back)` for a FRESH
        // subtype (all freshness allocated inside `NewTypeDefRule::decide`).
        let big: Thm = mint!(
            NewTypeDefRule,
            (witness.0.clone(), abs_hint.clone(), rep_hint.clone()),
            (witness.0, abs_hint, rep_hint)
        )?;

        // Split via core's own admitted `and_elim` rules.
        let abs_rep = big.clone().and_elim_l()?;
        let rest = big.and_elim_r()?;
        let rep_abs_fwd = rest.clone().and_elim_l()?;
        let rep_abs_back = rest.and_elim_r()?;

        // Recover τ / abs / rep from `abs_rep`'s conclusion `∀a:τ. abs (rep a) = a`,
        // and α (⇒ tvars) from `fwd`'s `∀r:α. P r ⟹ …`. This shape is exactly
        // what the rule built, so a malformed parse is an internal invariant break.
        let (tau, abs, rep) = parse_typedef_bijection(abs_rep.concl())?;
        let (alpha, _body) = super::parse_hol_forall(rep_abs_fwd.concl())?;
        let tvars = alpha.free_tvars();

        Ok(TypeDef {
            tau,
            abs,
            rep,
            abs_rep,
            rep_abs_fwd,
            rep_abs_back,
            tvars,
        })
    }

    /// Introduce a fresh defined constant: emit `⊢ Def(name, body) ≡ body`.
    ///
    /// The fresh `Def` is allocated INSIDE `super::rules::Define`'s `decide`
    /// (never a caller-supplied `Def`), so two distinct `define` calls — even with
    /// the same name and body — produce distinct `Def`s. The kernel never reuses a
    /// `Def` identity, so users cannot derive `⊢ body₁ ≡ body₂` by `trans`+`sym`.
    ///
    /// The `name` is a display-only label; the `body` must be a valid Core term
    /// (typeable in isolation, with no phantom type variables).
    ///
    /// ## Soundness
    ///
    /// Sound because the resulting `Def` is a brand-new symbol whose only equation
    /// says it equals `body` — a conservative extension. No global signature is
    /// needed because the allocator gives uniqueness per call.
    pub fn define(name: impl Into<SmolStr>, body: Term) -> Result<Thm> {
        let name = name.into();
        mint!(Define, (name.clone(), body.clone()), (name, body))
    }
}

/// Shape-parse a typedef `abs_rep` conclusion `∀a:τ. abs (rep a) = a`, returning
/// `(τ, abs, rep)`. The theorem was just minted by [`super::rules::NewTypeDefRule`]
/// in exactly this shape, so a parse failure indicates an internal invariant break.
fn parse_typedef_bijection(concl: &Term) -> Result<(Type, Term, Term)> {
    let malformed =
        || Error::BadTypeDefWitness(format!("internal: malformed typedef bijection {concl}"));
    let (tau, body) = super::parse_hol_forall(concl)?;
    let (lhs, _rhs) = super::parse_hol_eq(body)?;
    // lhs = App(abs, App(rep, Bound(0)))
    let TermKind::App(abs, inner) = lhs.kind() else {
        return Err(malformed());
    };
    let TermKind::App(rep, _) = inner.kind() else {
        return Err(malformed());
    };
    Ok((tau.clone(), abs.clone(), rep.clone()))
}

// ============================================================================
// new_type_definition — result bundle
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
