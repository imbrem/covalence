//! Theorems about `nat_div` (saturating Euclidean division).
//!
//! `nat_div` itself is a declaration-only TermSpec; the kernel pins
//! its behaviour through three axioms ([`Thm::nat_div_zero_right`],
//! [`Thm::nat_div_less`], [`Thm::nat_div_recursion`]). From those:
//!
//! - [`nat_div_self_pos`] — `⋀n. 0 < n ⟹ n / n = 1`
//! - [`nat_div_zero_left_pos`] — `⋀n. 0 < n ⟹ 0 / n = 0`
//!
//! Both are direct chases through the recursion + `nat_sub_self`.

use crate::defs;
use crate::error::Result;
use crate::hol;
use crate::term::{Term, Type};
use crate::thm::Thm;

use super::nat_sub::nat_sub_self;
use super::{
    instantiate_universal, pure_eq_of_hol_eq, trueprop, trueprop_of_pure_eq,
};

/// `succ 0`, the canonical literal 1 as a Term.
fn one() -> Term {
    Term::app(hol::succ_fn(), hol::zero())
}

/// `⊢ ⋀n:nat. Trueprop (nat_lt n n) ⟹ Trueprop (nat_div n n = 1)`.
///
/// Wait — that's wrong; we want `0 < n` as the hypothesis, not `n < n`
/// (which is false). The statement is
/// `⋀n. 0 < n ⟹ n / n = 1`.
///
/// Proof: at any `n` with `0 < n`,
///
/// ```text
///   n / n = succ ((n - n) / n)   [div_recursion: 0 < n and n ≤ n by le_refl]
///         = succ (0 / n)         [n - n = 0 by nat_sub_self]
///         = succ 0 = 1           [0 / n = 0 by div_less: 0 < n]
/// ```
pub fn nat_div_self_pos() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let zero_lt_n = trueprop(Term::app(
        Term::app(defs::nat_lt(), hol::zero()),
        n.clone(),
    ));
    let hyp = Thm::assume(zero_lt_n.clone())?;

    // n ≤ n.
    let le_refl = Thm::nat_le_refl();
    let le_refl_at_n = instantiate_universal(le_refl, vec![n.clone()])?;

    // div_recursion at (n, n): 0 < n ⟹ n ≤ n ⟹ n / n = succ ((n - n) / n)
    let recursion = Thm::nat_div_recursion();
    let recursion_at = recursion.all_elim(n.clone())?.all_elim(n.clone())?;
    let after_lt = recursion_at.imp_elim(hyp.clone())?;
    let recurse_hol = after_lt.imp_elim(le_refl_at_n)?;
    let recurse_pure = pure_eq_of_hol_eq(recurse_hol)?;
    // recurse_pure: nat_div n n ≡ succ (nat_div (n - n) n).

    // n - n ≡ 0.
    let sub_self = nat_sub_self()?;
    let sub_self_at_n = instantiate_universal(sub_self, vec![n.clone()])?;
    let sub_self_pure = pure_eq_of_hol_eq(sub_self_at_n)?;

    // Lift (n - n ≡ 0) inside nat_div (n - n) n.
    let nat_div_refl = Thm::refl(defs::nat_div())?;
    let inner_step = nat_div_refl.cong_app(sub_self_pure)?;
    let n_refl = Thm::refl(n.clone())?;
    let div_arg_eq = inner_step.cong_app(n_refl)?;
    // div_arg_eq: nat_div (n - n) n ≡ nat_div 0 n.

    // Lift through succ.
    let succ_refl = Thm::refl(hol::succ_fn())?;
    let succ_div_arg = succ_refl.cong_app(div_arg_eq)?;
    let recurse_after_sub = recurse_pure.trans(succ_div_arg)?;
    // recurse_after_sub: nat_div n n ≡ succ (nat_div 0 n).

    // 0 / n = 0 by nat_div_less at (0, n) with hypothesis 0 < n.
    let div_less = Thm::nat_div_less();
    let div_less_at = div_less
        .all_elim(hol::zero())?
        .all_elim(n.clone())?;
    let div_zero_hol = div_less_at.imp_elim(hyp)?;
    let div_zero_pure = pure_eq_of_hol_eq(div_zero_hol)?;
    // div_zero_pure: nat_div 0 n ≡ 0.

    let succ_refl2 = Thm::refl(hol::succ_fn())?;
    let succ_div_zero = succ_refl2.cong_app(div_zero_pure)?;
    // succ_div_zero: succ (nat_div 0 n) ≡ succ 0 = 1.

    let pure_eq = recurse_after_sub.trans(succ_div_zero)?;
    // pure_eq: nat_div n n ≡ 1.
    let _ = one();

    // Convert to Trueprop and re-wrap.
    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let imp_form = hol_form.imp_intro(&zero_lt_n)?;
    imp_form.all_intro("n", Type::nat())
}

/// `⊢ ⋀n:nat. Trueprop (nat_lt 0 n) ⟹ Trueprop (nat_div 0 n = 0)`.
///
/// Direct application of [`Thm::nat_div_less`].
pub fn nat_div_zero_left_pos() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let zero_lt_n = trueprop(Term::app(
        Term::app(defs::nat_lt(), hol::zero()),
        n.clone(),
    ));
    let hyp = Thm::assume(zero_lt_n.clone())?;

    let div_less = Thm::nat_div_less();
    let div_less_at = div_less
        .all_elim(hol::zero())?
        .all_elim(n)?;
    let div_zero_hol = div_less_at.imp_elim(hyp)?;
    // div_zero_hol: Trueprop (nat_div 0 n = 0).

    let imp_form = div_zero_hol.imp_intro(&zero_lt_n)?;
    imp_form.all_intro("n", Type::nat())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermKind;

    #[test]
    fn div_self_pos_builds() {
        let thm = nat_div_self_pos().expect("⋀n. 0 < n ⟹ n / n = 1");
        match thm.concl().kind() {
            TermKind::All(_, ty, _) => assert_eq!(ty, &Type::nat()),
            other => panic!("expected ⋀:nat ..., got {other:?}"),
        }
    }

    #[test]
    fn div_zero_left_pos_builds() {
        let _ = nat_div_zero_left_pos().expect("⋀n. 0 < n ⟹ 0 / n = 0");
    }
}
