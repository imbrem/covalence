//! The propositional connectives: the `defs/logic.rs` *definitions*
//! re-exported, plus the *proved* properties the kernel deliberately
//! omits.
//!
//! `covalence_core::defs::logic` only **defines** `∧ ∨ ¬ ⟹ ⟺ ∀ ∃`
//! (each as a `TermSpec` body); the kernel-separation discipline
//! forbids it from proving anything. This is where the expected facts
//! — `⊢ T`, commutativity of `∧` / `∨`, … — get **derived**, using the
//! high-level [`TermExt`] / [`ThmExt`] API so the proofs survive churn
//! in `covalence-core`.
//!
//! The intro / elim rules themselves are already kernel primitives
//! ([`Thm::and_intro`], [`Thm::or_elim`], …) — call them directly. The
//! derived *rules* here ([`and_sym`], [`or_sym`]) return [`Result`] and
//! thread errors with `?`. The closed *theorems* ([`truth`],
//! [`and_comm`], [`or_comm`]) are `init` proofs: they return [`Thm`]
//! and `expect` on failure, since a failure is a build-time bug. See
//! [`crate::proofs::bool`] for the *derivations* witnessing the
//! connective primitives' soundness.

pub use covalence_core::defs::{
    and, and_spec, exists, exists_spec, forall, forall_spec, iff, iff_spec, imp, imp_spec, not,
    not_spec, or, or_spec,
};

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::{TermExt, ThmExt};

// ============================================================================
// Truth
// ============================================================================

/// `⊢ T`. Derived (no postulate): [`Thm::reduce_prim`] decides
/// `(T = T) = T` on the closed literals, and `refl T : ⊢ T = T`
/// discharges the antecedent via [`Thm::eq_mp`].
pub fn truth() -> Thm {
    let t = Term::bool_lit(true);
    let refl_t = Thm::refl(t).expect("truth: refl T");
    let t_eq_t = refl_t.concl().clone();
    let reduced = Thm::reduce_prim(t_eq_t).expect("truth: reduce_prim (T=T)");
    reduced.eq_mp(refl_t).expect("truth: eq_mp")
}

// ============================================================================
// Conjunction
// ============================================================================

/// `⊢ p ∧ q` → `⊢ q ∧ p`. The hypotheses of the input carry through.
pub fn and_sym(pq: Thm) -> Result<Thm> {
    let (p, q) = pq.conjuncts()?;
    q.and_intro(p)
}

/// `⊢ (p ∧ q) ⟹ (q ∧ p)` for free `p`, `q : bool` — commutativity of
/// `∧` as a closed, hypothesis-free theorem. Assume `p ∧ q`, swap with
/// [`and_sym`], discharge.
pub fn and_comm() -> Thm {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let pq = p.and(q).expect("and_comm: build p ∧ q");
    let assumed = Thm::assume(pq.clone()).expect("and_comm: assume p ∧ q");
    and_sym(assumed)
        .and_then(|swapped| swapped.imp_intro(&pq))
        .expect("and_comm: discharge into (p∧q) ⟹ (q∧p)")
}

// ============================================================================
// Disjunction
// ============================================================================

/// `⊢ p ∨ q` → `⊢ q ∨ p`. The hypotheses of the input carry through.
///
/// Eliminate the disjunction into the goal `q ∨ p`: the `p` branch
/// re-injects on the right ([`Thm::or_intro_r`]), the `q` branch on the
/// left ([`Thm::or_intro_l`]).
pub fn or_sym(pq: Thm) -> Result<Thm> {
    let (p, q) = parse_or(pq.concl()).ok_or_else(|| {
        Error::ConnectiveRule(format!("or_sym: conclusion is not `p ∨ q`: {}", pq.concl()))
    })?;
    let left = Thm::assume(p.clone())?.or_intro_r(q.clone())?.imp_intro(&p)?;
    let right = Thm::assume(q.clone())?.or_intro_l(p.clone())?.imp_intro(&q)?;
    pq.or_elim(left, right)
}

/// `⊢ (p ∨ q) ⟹ (q ∨ p)` for free `p`, `q : bool` — commutativity of
/// `∨` as a closed, hypothesis-free theorem.
pub fn or_comm() -> Thm {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let pq = p.or(q).expect("or_comm: build p ∨ q");
    let assumed = Thm::assume(pq.clone()).expect("or_comm: assume p ∨ q");
    or_sym(assumed)
        .and_then(|swapped| swapped.imp_intro(&pq))
        .expect("or_comm: discharge into (p∨q) ⟹ (q∨p)")
}

/// Parse `App(App(\/, p), q)` → `(p, q)`. Returns `None` unless the
/// head is the `or` connective spec. Uses the [`Term`] structural
/// accessors rather than matching `TermKind`.
fn parse_or(t: &Term) -> Option<(Term, Term)> {
    let (f, q) = t.as_app()?;
    let (head, p) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.ptr_eq(&or_spec()).then(|| (p.clone(), q.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truth_is_axiom_free() {
        let t = truth();
        assert!(t.hyps().is_empty(), "TRUTH must be axiom-free");
        assert_eq!(t.concl(), &Term::bool_lit(true));
    }

    #[test]
    fn and_comm_is_an_axiom_free_implication() {
        let thm = and_comm();
        assert!(thm.hyps().is_empty(), "and_comm must be axiom-free");
        assert!(thm.has_no_obs(), "and_comm must be oracle-free");
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let expected = p.clone().and(q.clone()).unwrap().imp(q.and(p).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn or_comm_is_an_axiom_free_implication() {
        let thm = or_comm();
        assert!(thm.hyps().is_empty(), "or_comm must be axiom-free");
        assert!(thm.has_no_obs(), "or_comm must be oracle-free");
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let expected = p.clone().or(q.clone()).unwrap().imp(q.or(p).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn and_sym_swaps_a_conjunction() {
        let p = Thm::assume(Term::bool_lit(true)).unwrap();
        let q = Thm::assume(Term::bool_lit(false)).unwrap();
        let conj = p.and_intro(q).unwrap(); // ⊢ T ∧ F (with hyps)
        let swapped = and_sym(conj).unwrap();
        // Now `F ∧ T`.
        let (f, r) = swapped.concl().as_app().unwrap();
        let (_head, l) = f.as_app().unwrap();
        assert_eq!(l, &Term::bool_lit(false));
        assert_eq!(r, &Term::bool_lit(true));
    }
}
