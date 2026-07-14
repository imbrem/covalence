//! Reusable **matching tactics**: recognising that an imported OpenTheory
//! statement denotes the same proposition as a native theorem, and
//! transporting a proof of one to the other.
//!
//! The design is generic along two axes, so the API is stable as the internal
//! logic evolves:
//!
//! - [`MatchLogic`] abstracts the **HOL representation being matched** — the
//!   "thing being matched" (covalence-HOL via [`HolMatch`] today; a
//!   metamath-HOL backend would add its own impl). A `MatchLogic` supplies the
//!   handful of equational primitives a strategy needs (α-equality, β/δ
//!   normalisation as `⊢ t = nf` theorems, and `refl`/`sym`/`trans`/`eq_mp`).
//! - [`MatchStrategy`] abstracts **how** two terms are recognised as equal and
//!   how a proof is carried across that equivalence: [`Structural`] (α only),
//!   [`UpToBeta`], [`UpToDelta`] (unfold definitions, no β), [`UpToBetaDelta`].
//!   A strategy only has to define `normalize` (`⊢ t = nf`); the shared
//!   `transport` does the rest.
//!
//! Transport is sound by construction: it only ever composes the backend's own
//! equational theorems (`⊢ native = target`) and discharges with `eq_mp`, so a
//! returned theorem is a real kernel theorem of exactly `target`.
//!
//! The motivating use is discharging OpenTheory axioms against a native theory
//! (see [`crate::infinity`]): the axiom statement is fully δ-inlined
//! Church-encoded HOL, while a native proof is stated with the kernel's
//! definitional connectives — [`UpToDelta`] bridges them.

#![cfg(feature = "native")]

use std::collections::BTreeSet;

use smol_str::SmolStr;

use covalence_core::{Error, Result, Term, TermKind, subst};
use covalence_hol_api::{Hol, NativeHol};
use covalence_hol_eval::EvalThm;

// ===========================================================================
// MatchLogic — the HOL representation being matched
// ===========================================================================

/// The equational primitives a [`MatchStrategy`] needs, abstracted over the
/// underlying HOL representation. Implement this once per backend (covalence-HOL
/// → [`HolMatch`]; a future metamath-HOL backend adds its own) and every
/// strategy works over it unchanged.
pub trait MatchLogic {
    /// Term representation.
    type Term: Clone;
    /// Theorem (certificate) representation.
    type Thm: Clone;
    /// Error type of the underlying rules.
    type Error;

    /// The conclusion of a theorem.
    fn concl(&self, th: &Self::Thm) -> Self::Term;

    /// α-equivalence of two terms.
    fn alpha_eq(&self, a: &Self::Term, b: &Self::Term) -> bool;

    /// The right-hand side of an equational theorem `⊢ a = b`, or `None` if it
    /// is not an equation.
    fn eq_rhs(&self, th: &Self::Thm) -> Option<Self::Term>;

    /// `⊢ t = t`.
    fn refl(&self, t: Self::Term) -> std::result::Result<Self::Thm, Self::Error>;
    /// `⊢ a = b` → `⊢ b = a`.
    fn sym(&self, th: Self::Thm) -> std::result::Result<Self::Thm, Self::Error>;
    /// `⊢ a = b`, `⊢ b = c` → `⊢ a = c`.
    fn trans(&self, a: Self::Thm, b: Self::Thm) -> std::result::Result<Self::Thm, Self::Error>;
    /// `⊢ a = b`, `⊢ a` → `⊢ b`.
    fn eq_mp(&self, eq: Self::Thm, p: Self::Thm) -> std::result::Result<Self::Thm, Self::Error>;

    /// `⊢ t = nf` where `nf` is the **β-normal form** of `t`.
    fn beta_normalize(&self, t: &Self::Term) -> std::result::Result<Self::Thm, Self::Error>;
    /// `⊢ t = nf` where `nf` is `t` with all **definitions unfolded (δ)**, and
    /// crucially *without* β-reducing (so the shape of a δ-inlined
    /// Church-encoded statement is preserved).
    fn delta_normalize(&self, t: &Self::Term) -> std::result::Result<Self::Thm, Self::Error>;
}

// ===========================================================================
// MatchStrategy — how terms are recognised equal + proofs transported
// ===========================================================================

/// A strategy for recognising that a native theorem proves the same
/// proposition as a target term, and transporting the proof. A strategy only
/// defines [`normalize`](MatchStrategy::normalize); the shared
/// [`transport`](MatchStrategy::transport) composes the two normal-form
/// equations and discharges with `eq_mp`.
pub trait MatchStrategy<L: MatchLogic> {
    /// `⊢ t = nf(t)` — the normal form of `t` under this strategy.
    fn normalize(&self, logic: &L, t: &L::Term) -> std::result::Result<L::Thm, L::Error>;

    /// If `⊢ native` and `target` share a normal form under this strategy,
    /// return `⊢ target`; otherwise `None`. `Some(Err(_))` signals a rule
    /// failure while normalising/transporting (not a mismatch).
    fn transport(
        &self,
        logic: &L,
        native: L::Thm,
        target: &L::Term,
    ) -> Option<std::result::Result<L::Thm, L::Error>> {
        let native_concl = logic.concl(&native);
        let nn = match self.normalize(logic, &native_concl) {
            Ok(x) => x,
            Err(e) => return Some(Err(e)),
        };
        let tn = match self.normalize(logic, target) {
            Ok(x) => x,
            Err(e) => return Some(Err(e)),
        };
        // `⊢ native_concl = A` and `⊢ target = B`; match iff A ≡ B.
        let a = logic.eq_rhs(&nn)?;
        let b = logic.eq_rhs(&tn)?;
        if !logic.alpha_eq(&a, &b) {
            return None;
        }
        // `⊢ native_concl = target` = trans(nn, sym(tn)); then eq_mp `native`.
        Some((|| {
            let tn_sym = logic.sym(tn)?;
            let eq = logic.trans(nn, tn_sym)?;
            logic.eq_mp(eq, native)
        })())
    }
}

/// Terms must be syntactically α-equal.
pub struct Structural;
/// Terms must be equal after **β-normalisation**.
pub struct UpToBeta;
/// Terms must be equal after **δ-unfolding** all definitions (no β).
pub struct UpToDelta;
/// Terms must be equal after **βδ-normalisation**.
pub struct UpToBetaDelta;

impl<L: MatchLogic> MatchStrategy<L> for Structural {
    fn normalize(&self, logic: &L, t: &L::Term) -> std::result::Result<L::Thm, L::Error> {
        logic.refl(t.clone())
    }
}

impl<L: MatchLogic> MatchStrategy<L> for UpToBeta {
    fn normalize(&self, logic: &L, t: &L::Term) -> std::result::Result<L::Thm, L::Error> {
        logic.beta_normalize(t)
    }
}

impl<L: MatchLogic> MatchStrategy<L> for UpToDelta {
    fn normalize(&self, logic: &L, t: &L::Term) -> std::result::Result<L::Thm, L::Error> {
        logic.delta_normalize(t)
    }
}

impl<L: MatchLogic> MatchStrategy<L> for UpToBetaDelta {
    fn normalize(&self, logic: &L, t: &L::Term) -> std::result::Result<L::Thm, L::Error> {
        // δ then β: `⊢ t = δnf` then `⊢ δnf = βδnf`, composed.
        let d = logic.delta_normalize(t)?;
        match logic.eq_rhs(&d) {
            Some(rhs) => {
                let b = logic.beta_normalize(&rhs)?;
                logic.trans(d, b)
            }
            None => Ok(d),
        }
    }
}

// ===========================================================================
// HolMatch — the covalence-HOL implementation
// ===========================================================================

/// [`MatchLogic`] over covalence-HOL (`covalence_core::Term` /
/// `covalence_hol_eval::EvalThm`). A zero-sized handle; all work goes through
/// the audited kernel rules and [`NativeHol`].
#[derive(Clone, Copy, Default, Debug)]
pub struct HolMatch;

impl MatchLogic for HolMatch {
    type Term = Term;
    type Thm = EvalThm;
    type Error = Error;

    fn concl(&self, th: &EvalThm) -> Term {
        th.concl().clone()
    }

    fn alpha_eq(&self, a: &Term, b: &Term) -> bool {
        // De Bruijn binders ⇒ structural equality is α-equivalence.
        a == b
    }

    fn eq_rhs(&self, th: &EvalThm) -> Option<Term> {
        th.concl().as_eq().map(|(_, b)| b.clone())
    }

    fn refl(&self, t: Term) -> Result<EvalThm> {
        EvalThm::refl(t)
    }
    fn sym(&self, th: EvalThm) -> Result<EvalThm> {
        th.sym()
    }
    fn trans(&self, a: EvalThm, b: EvalThm) -> Result<EvalThm> {
        a.trans(b)
    }
    fn eq_mp(&self, eq: EvalThm, p: EvalThm) -> Result<EvalThm> {
        eq.eq_mp(p)
    }

    fn beta_normalize(&self, t: &Term) -> Result<EvalThm> {
        NativeHol.beta_nf(t.clone())
    }

    fn delta_normalize(&self, t: &Term) -> Result<EvalThm> {
        full_delta(t)
    }
}

/// `⊢ t = δnf(t)`: recursively unfold every `TermKind::Spec` to its body
/// (`covalence_hol_eval::delta` = one head-spec unfold) via congruence,
/// **without** β-reducing. Leaves the connective applications as unreduced
/// β-redexes, matching an OpenTheory article's δ-inlined form.
fn full_delta(t: &Term) -> Result<EvalThm> {
    match t.kind() {
        TermKind::Spec(..) => match covalence_hol_eval::delta(t) {
            // `⊢ t = body`; recurse into `body` (it may hold more specs).
            Ok(step) => match step.concl().as_eq().map(|(_, b)| b.clone()) {
                Some(rhs) => step.trans(full_delta(&rhs)?),
                None => EvalThm::refl(t.clone()),
            },
            // A def-style / bodyless spec is a leaf.
            Err(_) => EvalThm::refl(t.clone()),
        },
        TermKind::App(f, x) => {
            // `⊢ f = f'`, `⊢ x = x'` ⇒ `⊢ f x = f' x'` (MK_COMB).
            let ef = full_delta(f)?;
            let ex = full_delta(x)?;
            ef.mk_comb(ex)
        }
        TermKind::Abs(ty, body) => {
            // Open under a fresh var, normalise, re-close via ABS congruence.
            let mut avoid = BTreeSet::new();
            collect_free_names(body, &mut avoid);
            let name = fresh_avoiding(&avoid);
            let fresh = Term::free(name.as_str(), ty.clone());
            let body_open = subst::open(body, &fresh);
            let rec = full_delta(&body_open)?;
            rec.abs(name.as_str(), ty.clone())
        }
        // Var / Const / Eq / Select / literals: nothing to unfold.
        _ => EvalThm::refl(t.clone()),
    }
}

fn collect_free_names(t: &Term, out: &mut BTreeSet<SmolStr>) {
    match t.kind() {
        TermKind::Free(v) => {
            out.insert(SmolStr::new(v.name()));
        }
        TermKind::App(a, b) => {
            collect_free_names(a, out);
            collect_free_names(b, out);
        }
        TermKind::Abs(_, b) => collect_free_names(b, out),
        _ => {}
    }
}

fn fresh_avoiding(avoid: &BTreeSet<SmolStr>) -> SmolStr {
    for i in 0u64.. {
        let n = SmolStr::new(format!("%d{i}"));
        if !avoid.contains(&n) {
            return n;
        }
    }
    unreachable!("u64 space exhausted")
}

// ===========================================================================
// Convenience
// ===========================================================================

/// Transport `native` to `⊢ target` under `strategy`, over covalence-HOL.
/// Thin wrapper around [`MatchStrategy::transport`] with [`HolMatch`].
pub fn transport_hol<S: MatchStrategy<HolMatch>>(
    strategy: &S,
    native: EvalThm,
    target: &Term,
) -> Option<Result<EvalThm>> {
    strategy.transport(&HolMatch, native, target)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::Type;

    fn ty_bool() -> Type {
        Type::bool()
    }

    #[test]
    fn structural_matches_alpha_equal() {
        // `⊢ x = x`; transporting to the identical target returns it.
        let x = Term::free("x", ty_bool());
        let native = EvalThm::refl(x.clone()).unwrap();
        let target = NativeHol.eq(x.clone(), x).unwrap();
        let out = transport_hol(&Structural, native, &target)
            .expect("match")
            .expect("proof");
        assert_eq!(out.concl(), &target);
    }

    #[test]
    fn structural_rejects_distinct() {
        let x = Term::free("x", ty_bool());
        let y = Term::free("y", ty_bool());
        let native = EvalThm::refl(x.clone()).unwrap(); // ⊢ x = x
        let target = NativeHol.eq(y.clone(), y).unwrap(); // y = y
        assert!(transport_hol(&Structural, native, &target).is_none());
    }

    #[test]
    fn delta_unfolds_a_connective() {
        // `∀x:bool. x = x` built with the kernel's `∀`/`=` specs; δ-normalising
        // must unfold the `∀` (and the `T` inside its definition) to a
        // spec-free, un-β-reduced Church form — i.e. contain no `Spec` nodes.
        let h = NativeHol;
        let body = h.eq(h.var("x", ty_bool()), h.var("x", ty_bool())).unwrap();
        let all = h.forall("x", ty_bool(), body).unwrap();
        let eqthm = full_delta(&all).unwrap();
        let (lhs, rhs) = eqthm.concl().as_eq().expect("δ gives an equation");
        assert_eq!(lhs, &all, "lhs is the original");
        assert!(!contains_spec(rhs), "δ-normal form has no Spec nodes");
        assert!(contains_spec(&all), "the original did have a Spec");
    }

    fn contains_spec(t: &Term) -> bool {
        match t.kind() {
            TermKind::Spec(..) => true,
            TermKind::App(a, b) => contains_spec(a) || contains_spec(b),
            TermKind::Abs(_, b) => contains_spec(b),
            _ => false,
        }
    }
}
