//! Theorems about `nat_sub` (saturating subtraction).
//!
//! `nat_sub n m ≔ iter m pred n` — recurses on the second argument.
//!
//! - [`nat_sub_zero_right`] — `n - 0 ≡ n` (direct from iter_zero)
//! - [`nat_sub_succ_right_at`] — `n - (S m) ≡ pred (n - m)` (direct)
//! - [`nat_sub_zero_left`] — `⋀n. 0 - n = 0` (induction)
//! - [`nat_sub_self`] — `⋀n. n - n = 0` (induction, via
//!   [`super::iter::iter_succ_corollary_at`])

use crate::defs;
use crate::error::Result;
use crate::hol;
use crate::term::{Term, Type};
use crate::thm::Thm;

use super::iter::{iter_succ_corollary_at, iter_succ_eq_at, iter_zero_eq_at};
use super::{
    apply_eq, beta_at, beta_trueprop, instantiate_universal, pure_eq_of_hol_eq, trueprop,
    trueprop_of_pure_eq, un_beta_trueprop,
};

fn trans_then_beta(eq: Thm, beta_lhs: Term) -> Result<Thm> {
    let beta = beta_at(beta_lhs)?;
    eq.trans(beta)
}

/// `⊢ nat_sub n m ≡ iter[nat] m pred n` — unfold + 2× β.
pub fn nat_sub_unfold_at(n: Term, m: Term) -> Result<Thm> {
    let nat_sub = defs::nat_sub();
    let unfold = Thm::unfold_term_spec(nat_sub)?;
    let after_n = apply_eq(unfold, n)?;
    let after_n_lhs = after_n.concl_rhs()?.clone();
    let after_n_beta = trans_then_beta(after_n, after_n_lhs)?;
    let after_m = apply_eq(after_n_beta, m)?;
    let after_m_lhs = after_m.concl_rhs()?.clone();
    trans_then_beta(after_m, after_m_lhs)
}

/// `⊢ nat_sub n 0 ≡ n` for concrete `n`. No induction.
pub fn nat_sub_zero_right(n: Term) -> Result<Thm> {
    let unfold = nat_sub_unfold_at(n.clone(), hol::zero())?;
    // iter[nat] 0 pred n ≡ n.
    let iter_zero = iter_zero_eq_at(Type::nat(), hol::pred_fn(), n)?;
    unfold.trans(iter_zero)
}

/// `⊢ nat_sub n (succ m) ≡ pred (nat_sub n m)` for concrete `n`, `m`.
pub fn nat_sub_succ_right_at(n: Term, m: Term) -> Result<Thm> {
    let succ_m = Term::app(hol::succ_fn(), m.clone());
    let unfold = nat_sub_unfold_at(n.clone(), succ_m)?;
    let iter_succ = iter_succ_eq_at(Type::nat(), m.clone(), hol::pred_fn(), n.clone())?;
    let chain = unfold.trans(iter_succ)?;
    // chain: nat_sub n (succ m) ≡ pred (iter m pred n).

    // Reverse-unfold iter m pred n ≡ nat_sub n m.
    let m_unfold = nat_sub_unfold_at(n, m)?;
    let pred_refl = Thm::refl(hol::pred_fn())?;
    let fold = pred_refl.cong_app(m_unfold.sym()?)?;
    chain.trans(fold)
}

/// `⊢ ⋀n:nat. Trueprop (nat_sub 0 n = 0)` — `0 - n = 0`. Proved by
/// induction on `n` using the kernel's `nat_pred_zero` axiom.
pub fn nat_sub_zero_left() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(defs::nat_sub(), hol::zero()), n);
    let p_body = hol::hol_eq(lhs, hol::zero());
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base: 0 - 0 ≡ 0.
    let base_pure = nat_sub_zero_right(hol::zero())?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_sub_zero_left_step(&p_lambda)?;

    let after_base = induction_at_p.imp_elim(base)?;
    after_base.imp_elim(step)
}

fn nat_sub_zero_left_step(p_lambda: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?; // 0 - n ≡ 0.

    // Goal: 0 - (S n) ≡ 0.
    // 1. 0 - (S n) ≡ pred (0 - n) by succ_right_at.
    let sr = nat_sub_succ_right_at(hol::zero(), n.clone())?;
    // 2. Lift IH through pred: pred (0 - n) ≡ pred 0.
    let pred_refl = Thm::refl(hol::pred_fn())?;
    let lifted = pred_refl.cong_app(ih_pure)?;
    let chain = sr.trans(lifted)?;
    // chain: 0 - (S n) ≡ pred 0.

    // 3. pred 0 ≡ 0 via the kernel axiom Thm::nat_pred_zero (HOL form
    //    Trueprop (pred 0 = 0)).
    let pred_zero_hol = Thm::nat_pred_zero();
    let pred_zero_pure = pure_eq_of_hol_eq(pred_zero_hol)?;
    let pure_eq = chain.trans(pred_zero_pure)?;

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_n)?;

    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

/// `⊢ ⋀n:nat. Trueprop (nat_sub n n = 0)` — `n - n = 0`. Proved by
/// induction on `n`. The step case uses
/// [`super::iter::iter_succ_corollary_at`] to consume one iteration
/// from the inside, turning `(S n) - (S n) = iter (S n) pred (S n)`
/// into `iter n pred (pred (S n)) = iter n pred n = n - n`.
pub fn nat_sub_self() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(defs::nat_sub(), n.clone()), n);
    let p_body = hol::hol_eq(lhs, hol::zero());
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base: 0 - 0 ≡ 0 (zero_right at 0).
    let base_pure = nat_sub_zero_right(hol::zero())?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_sub_self_step(&p_lambda)?;

    let after_base = induction_at_p.imp_elim(base)?;
    after_base.imp_elim(step)
}

fn nat_sub_self_step(p_lambda: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?; // n - n ≡ 0.

    // Goal: (S n) - (S n) ≡ 0.
    //
    // 1. (S n) - (S n) ≡ iter (S n) pred (S n)              [unfold]
    let unfold = nat_sub_unfold_at(succ_n.clone(), succ_n.clone())?;

    // 2. iter (S n) pred (S n) ≡ iter n pred (pred (S n))   [iter_succ_corollary]
    let corollary = iter_succ_corollary_at(
        Type::nat(),
        n.clone(),
        hol::pred_fn(),
        succ_n.clone(),
    )?;
    let after_corollary = unfold.trans(corollary)?;
    // after_corollary: (S n) - (S n) ≡ iter n pred (pred (S n)).

    // 3. pred (S n) ≡ n via Thm::nat_pred_succ.
    //    Pred_succ_at_n: ⋀n. Trueprop (pred (succ n) = n).
    let pred_succ = Thm::nat_pred_succ();
    let pred_succ_at_n = instantiate_universal(pred_succ, vec![n.clone()])?;
    let pred_succ_pure = pure_eq_of_hol_eq(pred_succ_at_n)?;
    // pred_succ_pure: pred (S n) ≡ n.

    //    Lift through iter n pred _: iter n pred (pred (S n)) ≡ iter n pred n.
    let iter_head_term = Term::app(
        Term::app(defs::iter(Type::nat()), n.clone()),
        hol::pred_fn(),
    );
    let iter_head_refl = Thm::refl(iter_head_term)?;
    let lifted_pred_succ = iter_head_refl.cong_app(pred_succ_pure)?;
    let after_pred = after_corollary.trans(lifted_pred_succ)?;
    // after_pred: (S n) - (S n) ≡ iter n pred n.

    // 4. iter n pred n ≡ nat_sub n n (reverse unfold).
    let n_unfold = nat_sub_unfold_at(n.clone(), n.clone())?; // n - n ≡ iter n pred n.
    let fold = n_unfold.sym()?;
    let after_fold = after_pred.trans(fold)?;
    // after_fold: (S n) - (S n) ≡ n - n.

    // 5. By IH, n - n ≡ 0.
    let pure_eq = after_fold.trans(ih_pure)?;

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_n)?;

    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermKind;

    #[test]
    fn zero_right_builds() {
        let n = Term::free("n", Type::nat());
        let thm = nat_sub_zero_right(n.clone()).expect("n - 0 ≡ n");
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &n),
            other => panic!("expected Eq with n on rhs, got {other:?}"),
        }
    }

    #[test]
    fn succ_right_builds() {
        let n = Term::free("n", Type::nat());
        let m = Term::free("m", Type::nat());
        let _ = nat_sub_succ_right_at(n, m).expect("n - (S m) ≡ pred (n - m)");
    }

    #[test]
    fn zero_left_builds() {
        let _ = nat_sub_zero_left().expect("⋀n. 0 - n = 0");
    }

    #[test]
    fn self_builds() {
        let _ = nat_sub_self().expect("⋀n. n - n = 0");
    }
}
