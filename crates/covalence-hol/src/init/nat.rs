//! `nat` theorems: the `defs/nat.rs` catalogue re-exported, plus the
//! proved Peano properties of HOL `nat` — mirroring how [`init::logic`]
//! pairs the connective definitions with their proved facts.
//!
//! [`init::logic`]: crate::init::logic
//!
//! This module is the home of the *theorems*; the **shallow embedding**
//! of Peano arithmetic into HOL (the [`Peano`] trait impl) lives in
//! [`crate::peano::shallow`] and reads its axioms from here.
//!
//! ## Status
//!
//! - **Genuine** (hypothesis-free): [`succ_inj`] / [`zero_ne_succ`]
//!   (kernel freeness primitives generalised with `all_intro`), and
//!   induction directly via `Thm::nat_induct`.
//! - **Postulated** (`Thm::assume`, flagged in `SKELETONS.md`): the
//!   four recursion equations [`add_base`] / [`add_step`] / [`mul_base`]
//!   / [`mul_step`]. The goal (option **B**) is to discharge these by
//!   proving the **recursion theorem** [`nat_recursion`] outright — the
//!   recursor exists (`∃r. P_rec r`), so `spec_ax(natRec, ·)` +
//!   `select`/choice + induction give `natRec`'s equations, and the
//!   `add`/`mul` equations follow by unfolding. Until that lands these
//!   four are the only `nat` postulates.

use covalence_core::{Term, Thm, Type};
use covalence_types::Nat;

use crate::init::ext::TermExt;

// Re-export the `defs/nat.rs` term catalogue (the operations; the
// `*_spec` handles stay in `covalence_core::defs`).
pub use covalence_core::defs::{
    iter, nat_add, nat_div, nat_le, nat_lt, nat_mod, nat_mul, nat_pow, nat_pred, nat_rec, nat_sub,
    nat_succ, nat_to_int,
};

// ============================================================================
// Small term helpers (private — the public surface is theorems)
// ============================================================================

fn nat() -> Type {
    Type::nat()
}

pub(crate) fn zero() -> Term {
    Term::nat_lit(Nat::zero())
}

pub(crate) fn succ(n: Term) -> Term {
    Term::app(nat_succ(), n)
}

pub(crate) fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add(), a), b)
}

pub(crate) fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_mul(), a), b)
}

fn var(name: &str) -> Term {
    Term::free(name, nat())
}

/// Postulate a `nat` axiom: `{t} ⊢ t`. The self-hypothesis is the audit
/// trail — every proof built on it carries it, flagging the unproved
/// leaf until [`nat_recursion`] discharges it.
fn axiom(t: Term) -> Thm {
    Thm::assume(t).expect("init::nat::axiom: term must be bool-typed")
}

// ============================================================================
// Freeness — genuine, from the kernel primitives
// ============================================================================

/// `⊢ ∀m n. (S m = S n) ⟹ (m = n)` — successor injectivity.
pub fn succ_inj() -> Thm {
    Thm::succ_inj(var("m"), var("n"))
        .and_then(|t| t.all_intro("n", nat()))
        .and_then(|t| t.all_intro("m", nat()))
        .expect("succ_inj: kernel freeness rule")
}

/// `⊢ ∀n. ¬(0 = S n)` — zero is not a successor.
pub fn zero_ne_succ() -> Thm {
    Thm::zero_ne_succ(var("n"))
        .and_then(|t| t.all_intro("n", nat()))
        .expect("zero_ne_succ: kernel freeness rule")
}

// ============================================================================
// Recursion equations — postulated, pending the recursion theorem (B)
// ============================================================================

/// `⊢ ∀m. 0 + m = m`.
pub fn add_base() -> Thm {
    let m = var("m");
    let eq = add(zero(), m.clone()).equals(m).expect("add_base: 0 + m = m");
    axiom(eq.forall("m", nat()).expect("add_base: ∀m"))
}

/// `⊢ ∀n m. S n + m = S (n + m)`.
pub fn add_step() -> Thm {
    let n = var("n");
    let m = var("m");
    let lhs = add(succ(n.clone()), m.clone());
    let rhs = succ(add(n, m.clone()));
    let eq = lhs.equals(rhs).expect("add_step: S n + m = S (n + m)");
    let term = eq
        .forall("m", nat())
        .and_then(|t| t.forall("n", nat()))
        .expect("add_step: ∀n m");
    axiom(term)
}

/// `⊢ ∀m. 0 * m = 0`.
pub fn mul_base() -> Thm {
    let m = var("m");
    let eq = mul(zero(), m).equals(zero()).expect("mul_base: 0 * m = 0");
    axiom(eq.forall("m", nat()).expect("mul_base: ∀m"))
}

/// `⊢ ∀n m. S n * m = m + n * m`.
pub fn mul_step() -> Thm {
    let n = var("n");
    let m = var("m");
    let lhs = mul(succ(n.clone()), m.clone());
    let rhs = add(m.clone(), mul(n, m));
    let eq = lhs.equals(rhs).expect("mul_step: S n * m = m + n * m");
    let term = eq
        .forall("m", nat())
        .and_then(|t| t.forall("n", nat()))
        .expect("mul_step: ∀n m");
    axiom(term)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn freeness_theorems_are_genuine() {
        assert!(succ_inj().hyps().is_empty(), "succ_inj is proved");
        assert!(zero_ne_succ().hyps().is_empty(), "zero_ne_succ is proved");
        assert!(succ_inj().concl().type_of().unwrap().is_bool());
        assert!(zero_ne_succ().concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn recursion_equations_are_postulated() {
        for ax in [add_base(), add_step(), mul_base(), mul_step()] {
            assert!(ax.concl().type_of().unwrap().is_bool());
            assert!(
                ax.hyps().iter().any(|h| h == ax.concl()),
                "a postulated axiom carries itself as a hypothesis"
            );
        }
    }

    #[test]
    fn add_base_specialises() {
        // ∀m. 0 + m = m  ⟹(spec k)  0 + k = k.
        let inst = add_base().all_elim(var("k")).expect("specialize add_base");
        let expected = add(zero(), var("k")).equals(var("k")).unwrap();
        assert_eq!(inst.concl(), &expected);
    }
}
