//! The **`Hol` interface** — the value-typed HOL Light surface the inductive
//! engine is being ported onto, so the *same* engine can drive any HOL
//! backend: our native kernel today, an internal / object-level HOL later
//! (the "prove induction *inside* HOL" goal).
//!
//! ## Why a new trait
//!
//! `covalence-hol` already has [`HolLightKernel`](crate::HolLightKernel), but
//! that is the **arena**-style primitive interface (`&mut self`, `NameId`
//! handles — for OpenTheory-shaped backends). The inductive engine works with
//! *value-typed* terms / theorems (`Clone`, immutable, structural equality),
//! and with the **derived** HOL Light rules (`all_intro`, `imp_elim`,
//! `and_intro`, …) rather than only the 10 primitives. `Hol` is that
//! higher-level, value-typed surface.
//!
//! ## What a backend supplies
//!
//! Associated `Type` / `Term` / `Thm`, the logical-constant builders, and the
//! HOL Light rule set the engine uses. Our [`NativeHol`] forwards each to the
//! fast `covalence-core` constructor / rule; an internal-HOL backend would
//! build object-level proofs the same shape. The engine itself adds no
//! axioms — type-specific facts (induction, freeness) stay behind
//! [`Inductive`](super::Inductive).
//!
//! ## Porting status
//!
//! Ported so far: the **conjunction-proof plumbing** ([`conj`] / [`project`] /
//! [`and_all`] / [`discharge_conj`]) — generic over `Hol`, with the concrete
//! `util` / `graph` functions now thin [`NativeHol`] shims. The remaining
//! engine modules (`graph` term builders, `existence`, `uniqueness`,
//! `determinacy`, `recursor`) port the same way; the trait grows to cover
//! their surface as each lands. See `SKELETONS.md`.

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::TermExt;

/// The value-typed HOL Light surface the inductive engine reasons through.
///
/// Only the slice the **conjunction plumbing** needs is declared so far; it
/// grows method-by-method as the engine modules port (see the [module
/// docs](self)). The full intended surface is the HOL Light connective
/// builders + rule set + β / ∃ derived helpers.
pub trait Hol {
    /// HOL types.
    type Type: Clone + PartialEq + std::fmt::Debug;
    /// HOL terms.
    type Term: Clone + PartialEq + std::fmt::Debug;
    /// HOL theorems.
    type Thm: Clone + std::fmt::Debug;

    /// `a ∧ b`.
    fn and(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;

    /// `ASSUME t`: `{t} ⊢ t`.
    fn assume(&self, t: Self::Term) -> Result<Self::Thm>;

    /// `⊢ a` + `⊢ b` → `⊢ a ∧ b`.
    fn and_intro(&self, a: Self::Thm, b: Self::Thm) -> Result<Self::Thm>;

    /// `⊢ a ∧ b` → `⊢ a`.
    fn and_elim_l(&self, th: Self::Thm) -> Result<Self::Thm>;

    /// `⊢ a ∧ b` → `⊢ b`.
    fn and_elim_r(&self, th: Self::Thm) -> Result<Self::Thm>;

    /// `Γ ⊢ q` → `Γ\{p} ⊢ p ⟹ q` (DISCH).
    fn imp_intro(&self, th: Self::Thm, h: &Self::Term) -> Result<Self::Thm>;

    /// `⊢ p ⟹ q` + `⊢ p` → `⊢ q` (MP).
    fn imp_elim(&self, imp: Self::Thm, ante: Self::Thm) -> Result<Self::Thm>;
}

/// The **native** backend: `Hol` over `covalence-core`'s value-typed kernel,
/// each method forwarding to the corresponding fast constructor / rule.
#[derive(Clone, Copy, Default, Debug)]
pub struct NativeHol;

impl Hol for NativeHol {
    type Type = Type;
    type Term = Term;
    type Thm = Thm;

    fn and(&self, a: Term, b: Term) -> Result<Term> {
        a.and(b)
    }
    fn assume(&self, t: Term) -> Result<Thm> {
        Thm::assume(t)
    }
    fn and_intro(&self, a: Thm, b: Thm) -> Result<Thm> {
        a.and_intro(b)
    }
    fn and_elim_l(&self, th: Thm) -> Result<Thm> {
        th.and_elim_l()
    }
    fn and_elim_r(&self, th: Thm) -> Result<Thm> {
        th.and_elim_r()
    }
    fn imp_intro(&self, th: Thm, h: &Term) -> Result<Thm> {
        th.imp_intro(h)
    }
    fn imp_elim(&self, imp: Thm, ante: Thm) -> Result<Thm> {
        imp.imp_elim(ante)
    }
}

// ============================================================================
// Conjunction-proof plumbing — generic over any `Hol`
// ============================================================================

/// Right-associated conjunction `t₀ ∧ (t₁ ∧ … ∧ tₙ)`. Errors on an empty
/// slice (the engine never builds an empty conjunction).
pub fn conj<H: Hol>(hol: &H, ts: &[H::Term]) -> Result<H::Term> {
    match ts {
        [] => Err(Error::ConnectiveRule(
            "inductive::hol: empty conjunction".into(),
        )),
        [last] => Ok(last.clone()),
        [head, rest @ ..] => hol.and(head.clone(), conj(hol, rest)?),
    }
}

/// Project conjunct `i` out of a proof of a right-associated conjunction
/// `c₀ ∧ (c₁ ∧ … ∧ c_{k-1})`.
pub fn project<H: Hol>(hol: &H, c: H::Thm, i: usize, k: usize) -> Result<H::Thm> {
    let mut t = c;
    for _ in 0..i {
        t = hol.and_elim_r(t)?;
    }
    if i + 1 < k { hol.and_elim_l(t) } else { Ok(t) }
}

/// `⊢ ⋀ thms` — the right-associated conjunction of the given proofs. Caller
/// guarantees a non-empty slice.
pub fn and_all<H: Hol>(hol: &H, thms: &[H::Thm]) -> Result<H::Thm> {
    let mut acc = thms[thms.len() - 1].clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = hol.and_intro(t.clone(), acc)?;
    }
    Ok(acc)
}

/// Discharge hypotheses `hyps` from `thm` as a single conjunctive antecedent:
/// `{h₀,…,hₙ} ⊢ c` ↦ `⊢ (⋀ hᵢ) ⟹ c`. Empty → unchanged; singleton → a plain
/// `imp_intro`.
pub fn discharge_conj<H: Hol>(hol: &H, thm: H::Thm, hyps: &[H::Term]) -> Result<H::Thm> {
    match hyps {
        [] => Ok(thm),
        [h] => hol.imp_intro(thm, h),
        _ => {
            // `⊢ hₙ ⟹ … ⟹ h₀ ⟹ c` (all hyps curried off), then cut each back
            // against its projection out of the assumed `⋀ hᵢ`.
            let mut curried = thm;
            for h in hyps {
                curried = hol.imp_intro(curried, h)?;
            }
            let conj_term = conj(hol, hyps)?;
            let assumed = hol.assume(conj_term.clone())?;
            let mut cut = curried;
            for i in (0..hyps.len()).rev() {
                cut = hol.imp_elim(cut, project(hol, assumed.clone(), i, hyps.len())?)?;
            }
            hol.imp_intro(cut, &conj_term)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(name: &str) -> Term {
        Term::free(name, Type::bool())
    }

    /// `discharge_conj` over `NativeHol` turns `{A, B} ⊢ A` into
    /// `⊢ (A ∧ B) ⟹ A` — exercises the trait + native impl + generic plumbing
    /// end to end.
    #[test]
    fn discharge_conj_native_round_trips() {
        let hol = NativeHol;
        let (a, b) = (p("A"), p("B"));
        // {A, B} ⊢ A.
        let thm = hol.assume(a.clone()).unwrap();
        let thm = hol.imp_intro(thm, &b).unwrap(); // {A} ⊢ B ⟹ A
        let thm = hol.imp_elim(thm, hol.assume(b.clone()).unwrap()).unwrap(); // {A,B} ⊢ A
        assert_eq!(thm.hyps().len(), 2);

        let out = discharge_conj(&hol, thm, &[a.clone(), b.clone()]).unwrap();
        assert!(
            out.hyps().is_empty(),
            "the conjunctive antecedent is discharged"
        );
        let expected = conj(&hol, &[a.clone(), b]).unwrap().imp(a).unwrap();
        assert_eq!(out.concl(), &expected);
    }
}
