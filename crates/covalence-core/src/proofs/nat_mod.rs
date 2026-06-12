//! Theorems about `nat_mod`.
//!
//! `nat_mod n m ≔ n - (n / m) * m`. Since `nat_mod` is now a
//! let-style spec, theorems about it follow by unfolding plus the
//! existing `nat_div` / `nat_mul` / `nat_sub` lemmas.
//!
//! - [`nat_mod_unfold_at`] — `n % m ≡ n - (n / m) * m`
//! - [`nat_mod_self_pos`] — `⋀n. 0 < n ⟹ n % n = 0`

use crate::defs;
use crate::error::Result;
use crate::hol;
use crate::term::{Term, Type};
use crate::thm::Thm;

use super::nat_mul::nat_mul_one_left;
use super::nat_sub::nat_sub_self;
use super::{
    apply_eq, beta_at, instantiate_universal, pure_eq_of_hol_eq, trueprop, trueprop_of_pure_eq,
};

fn trans_then_beta(eq: Thm, beta_lhs: Term) -> Result<Thm> {
    let beta = beta_at(beta_lhs)?;
    eq.trans(beta)
}

/// `⊢ nat_mod n m ≡ nat_sub n (nat_mul (nat_div n m) m)` — unfold +
/// 2× β on the binary lambda body.
pub fn nat_mod_unfold_at(n: Term, m: Term) -> Result<Thm> {
    let nat_mod = defs::nat_mod();
    let unfold = Thm::unfold_term_spec(nat_mod)?;
    let after_n = apply_eq(unfold, n)?;
    let after_n_lhs = after_n.concl_rhs()?.clone();
    let after_n_beta = trans_then_beta(after_n, after_n_lhs)?;
    let after_m = apply_eq(after_n_beta, m)?;
    let after_m_lhs = after_m.concl_rhs()?.clone();
    trans_then_beta(after_m, after_m_lhs)
}

/// `⊢ ⋀n:nat. Trueprop (nat_lt 0 n) ⟹ Trueprop (nat_mod n n = 0)`.
///
/// Proof:
///
/// ```text
///   n % n ≡ n - (n / n) * n       [unfold]
///         ≡ n - 1 * n              [n / n = 1 by nat_div_self_pos]
///         ≡ n - n                  [nat_mul_one_left]
///         ≡ 0                      [nat_sub_self]
/// ```
pub fn nat_mod_self_pos() -> Result<Thm> {
    use super::nat_div::nat_div_self_pos;

    let n = Term::free("n", Type::nat());
    let zero_lt_n = trueprop(Term::app(
        Term::app(defs::nat_lt(), hol::zero()),
        n.clone(),
    ));
    let hyp = Thm::assume(zero_lt_n.clone())?;

    // 1. Unfold: n % n ≡ n - (n / n) * n.
    let unfold = nat_mod_unfold_at(n.clone(), n.clone())?;

    // 2. n / n ≡ 1 (using nat_div_self_pos).
    let div_self = nat_div_self_pos()?;
    let div_self_at_n = div_self.all_elim(n.clone())?;
    let div_self_inst = div_self_at_n.imp_elim(hyp.clone())?;
    let div_self_pure = pure_eq_of_hol_eq(div_self_inst)?;
    // div_self_pure: nat_div n n ≡ succ 0.

    // 3. Lift (n / n ≡ 1) through `_ * n`, then through `n - _`.
    let nat_mul_refl = Thm::refl(defs::nat_mul())?;
    let mul_inner = nat_mul_refl.cong_app(div_self_pure)?;
    let n_refl = Thm::refl(n.clone())?;
    let mul_eq = mul_inner.cong_app(n_refl)?;
    // mul_eq: (n / n) * n ≡ 1 * n.

    let sub_inner = Thm::refl(defs::nat_sub())?.cong_app(Thm::refl(n.clone())?)?;
    let sub_eq = sub_inner.cong_app(mul_eq)?;
    // sub_eq: n - (n / n) * n ≡ n - 1 * n.
    let after_div = unfold.trans(sub_eq)?;
    // after_div: n % n ≡ n - 1 * n.

    // 4. 1 * n ≡ n.
    let one_left = nat_mul_one_left(n.clone())?;
    // one_left: 1 * n ≡ n.

    // Lift through n - _:
    let sub_inner2 = Thm::refl(defs::nat_sub())?.cong_app(Thm::refl(n.clone())?)?;
    let sub_one = sub_inner2.cong_app(one_left)?;
    // sub_one: n - 1 * n ≡ n - n.
    let after_one = after_div.trans(sub_one)?;
    // after_one: n % n ≡ n - n.

    // 5. n - n ≡ 0.
    let sub_self = nat_sub_self()?;
    let sub_self_at_n = instantiate_universal(sub_self, vec![n.clone()])?;
    let sub_self_pure = pure_eq_of_hol_eq(sub_self_at_n)?;
    let pure_eq = after_one.trans(sub_self_pure)?;
    // pure_eq: n % n ≡ 0.

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let imp_form = hol_form.imp_intro(&zero_lt_n)?;
    imp_form.all_intro("n", Type::nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unfold_builds() {
        let n = Term::free("n", Type::nat());
        let m = Term::free("m", Type::nat());
        let _ = nat_mod_unfold_at(n, m).expect("n % m ≡ n - (n/m)*m");
    }

    #[test]
    fn self_pos_builds() {
        let _ = nat_mod_self_pos().expect("⋀n. 0 < n ⟹ n % n = 0");
    }
}
