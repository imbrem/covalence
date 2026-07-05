//! Conservative-extension primitives: `Thm::define` (fresh defined
//! constants) and `Thm::new_type_definition` (fresh subtypes), plus
//! the [`TypeDef`] result bundle.
//!
//! Both are the admits-only glue over the generative rules in [`super::rules`]:
//! all fresh identity (the `Def`, and the τ/abs/rep markers) is allocated INSIDE
//! the rules' `decide`, never taken as an input, so an adversary cannot force a
//! collision. `new_type_definition` mints a single conjunction
//! `abs_rep ∧ (fwd ∧ back)` and returns it **unsplit** (the connective
//! rules that used to split it left the kernel in stage L2 — consumers
//! project the three laws with `covalence-hol-eval::derived::TypeDefExt`),
//! recovering τ/abs/rep by shape-parsing the conjunction (reading mints
//! nothing).

use smol_str::SmolStr;

use crate::error::{Error, Result};
use crate::term::{Term, TermKind, Type};

use super::Thm;
use super::lang::{CoreLang, HolTier};
use super::rules::{Define, NewTypeDefRule, mint};

impl<L: HolTier> Thm<L> {
    pub fn new_type_definition(
        hint: impl Into<SmolStr>,
        abs_hint: impl Into<SmolStr>,
        rep_hint: impl Into<SmolStr>,
        witness: Thm<L>,
    ) -> Result<TypeDef<L>> {
        // The τ name hint is display-only; the fresh τ marker carries none.
        let _ = hint.into();
        let abs_hint = abs_hint.into();
        let rep_hint = rep_hint.into();

        // Mint the bijection conjunction `abs_rep ∧ (fwd ∧ back)` for a FRESH
        // subtype (all freshness allocated inside `NewTypeDefRule::decide`).
        let bijection: Thm<L> = mint!(
            NewTypeDefRule,
            (witness.0.clone(), abs_hint.clone(), rep_hint.clone()),
            (witness.0, abs_hint, rep_hint)
        )?;

        // Recover τ / abs / rep from the first conjunct's conclusion
        // `∀a:τ. abs (rep a) = a`, and α (⇒ tvars) from τ's construction —
        // pure shape-parsing of the term the rule just built (a malformed
        // parse is an internal invariant break; no theorem is minted).
        let (abs_rep_c, _rest) = parse_conj(bijection.concl())?;
        let (tau, abs, rep) = parse_typedef_bijection(abs_rep_c)?;
        // α is `abs`'s domain: abs : α → τ.
        let abs_ty = abs.type_of()?;
        let crate::term::TypeKind::Fun(alpha, _) = abs_ty.kind() else {
            return Err(Error::BadTypeDefWitness(format!(
                "internal: typedef abs not a function: {abs_ty}"
            )));
        };
        let tvars = alpha.free_tvars();

        Ok(TypeDef {
            tau,
            abs,
            rep,
            bijection,
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
    pub fn define(name: impl Into<SmolStr>, body: Term) -> Result<Thm<L>> {
        let name = name.into();
        mint!(Define, (name.clone(), body.clone()), (name, body))
    }
}

/// Shape-parse an `∧`-headed application `App(App(∧, a), b)` → `(a, b)`.
/// Read-only (used to recover the typedef identity from the conjunction).
fn parse_conj(t: &Term) -> Result<(&Term, &Term)> {
    let malformed = || Error::BadTypeDefWitness(format!("internal: malformed typedef conj {t}"));
    let TermKind::App(f, b) = t.kind() else {
        return Err(malformed());
    };
    let TermKind::App(head, a) = f.kind() else {
        return Err(malformed());
    };
    let TermKind::Spec(h, _) = head.kind() else {
        return Err(malformed());
    };
    if !h.ptr_eq(&crate::defs::and_spec()) {
        return Err(malformed());
    }
    Ok((a, b))
}

/// Shape-parse a typedef `abs_rep` conclusion `∀a:τ. abs (rep a) = a`, returning
/// `(τ, abs, rep)`. The term was just minted by [`super::rules::NewTypeDefRule`]
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

/// Result of [`Thm::new_type_definition`]: the fresh subtype τ along with
/// its abs/rep bijection constants and the single conjunction theorem that
/// witnesses the bijection. The theorem carries the witness's hypotheses.
///
/// The three individual laws are *derived* projections of [`bijection`]
/// (`covalence-hol-eval::derived::TypeDefExt::{abs_rep, rep_abs_fwd,
/// rep_abs_back}`) — the kernel no longer ships the `and_elim` rules that
/// used to split the conjunction here.
///
/// [`bijection`]: TypeDef::bijection
#[derive(Clone, Debug)]
pub struct TypeDef<L: HolTier = CoreLang> {
    /// The freshly-introduced type. A `FreshTyCon` carrying a private
    /// `FreshId` token allocated inside the rule. Parametric in
    /// `tvars` (in canonical order, so `inst_tfree` propagates
    /// correctly).
    pub tau: Type,
    /// The fresh `abs : α → τ` constant. A `FreshConst` leaf with its
    /// own `FreshId` token.
    pub abs: Term,
    /// The fresh `rep : τ → α` constant.
    pub rep: Term,
    /// `⊢ (∀a:τ. abs (rep a) = a) ∧ ((∀r:α. P r ⟹ rep (abs r) = r) ∧
    /// (∀r:α. rep (abs r) = r ⟹ P r))` — the three bijection laws as one
    /// conjunction, exactly as the generative typedef rule minted it.
    pub bijection: Thm<L>,
    /// Sorted list of type-variable names that appear in α. τ is
    /// parametric in exactly these tvars (positionally, in this order).
    pub tvars: Vec<smol_str::SmolStr>,
}
