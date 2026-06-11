//! Theorems about `nat_add`.
//!
//! Recall `natAdd n m ≔ iter n succ m`. The basic equations follow
//! by unfolding + the iter equations:
//!
//! - [`nat_add_zero_left`] — `0 + m ≡ m` (just one β-cascade)
//! - [`nat_add_zero_right`] — `n + 0 ≡ n` (requires induction)
//! - [`nat_add_comm`] — `n + m ≡ m + n` (requires induction)
//!
//! Associativity is a stretch goal; not yet implemented.

use crate::defs;
use crate::error::Result;
use crate::hol;
use crate::term::{Term, Type};
use crate::thm::Thm;

use super::{apply_eq, beta_at};
use super::iter::iter_zero_eq_at;

fn trans_then_beta(eq: Thm, beta_lhs: Term) -> Result<Thm> {
    let beta = beta_at(beta_lhs)?;
    eq.trans(beta)
}

/// `⊢ defs::nat_add() 0 m ≡ m`, for any concrete `m:nat`.
///
/// Proof: unfold `nat_add`'s body (`λn m. iter n succ m`), apply
/// at `0` and `m`, β-reduce both, then close with [`iter_zero_eq_at`]
/// at α = nat with f = succ.
pub fn nat_add_zero_left(m: Term) -> Result<Thm> {
    assert_eq!(m.type_of()?, Type::nat(), "nat_add_zero_left: m : nat");

    let zero = hol::zero();
    let nat_add = defs::nat_add();

    // 1. nat_add ≡ body  (let-style unfold).
    let unfold = Thm::unfold_term_spec(nat_add.clone())?;

    // 2. nat_add 0 ≡ body 0.
    let after_0 = apply_eq(unfold, zero.clone())?;
    let body_at_0 = after_0.concl_rhs()?.clone();
    let after_0_beta = trans_then_beta(after_0, body_at_0)?;

    // 3. nat_add 0 m ≡ (... m).
    let after_m = apply_eq(after_0_beta, m.clone())?;
    let after_m_lhs = after_m.concl_rhs()?.clone();
    let after_m_beta = trans_then_beta(after_m, after_m_lhs)?;
    // after_m_beta: nat_add 0 m ≡ iter[nat] 0 succ m

    // 4. iter[nat] 0 succ m ≡ m.
    let succ = hol::succ_fn();
    let iter_eq = iter_zero_eq_at(Type::nat(), succ, m)?;

    after_m_beta.trans(iter_eq)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermKind;

    #[test]
    fn zero_left_at_free_var() {
        let m = Term::free("m", Type::nat());
        let thm = nat_add_zero_left(m.clone()).expect("0 + m ≡ m");
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &m),
            other => panic!("expected Eq with m on the rhs, got {other:?}"),
        }
    }
}
