//! Theorems about `nat_pow` (natural-number exponentiation).
//!
//! `nat_pow n m ≔ iter m (λx. nat_mul n x) 1` — recurse on the
//! exponent. Lemmas:
//!
//! - [`nat_pow_unfold_at`] — `n^m ≡ iter m (λx. n*x) 1`
//! - [`nat_pow_zero`] — `⋀n. n^0 = 1`
//! - [`nat_pow_succ_at`] — `n^(S m) ≡ n * n^m`
//! - [`nat_one_pow`] — `⋀n. 1^n = 1` (induction)
//! - [`nat_pow_zero_pow_succ`] — `⋀n. 0^(S n) = 0` (direct)

use crate::defs;
use crate::error::Result;
use crate::hol;
use crate::term::{Term, Type};
use crate::thm::Thm;

use super::iter::{iter_succ_eq_at, iter_zero_eq_at};
use super::nat_mul::{nat_mul_one_left, nat_mul_zero_left};
use super::{
    apply_eq, beta_at, beta_trueprop, instantiate_universal, pure_eq_of_hol_eq, trueprop,
    trueprop_of_pure_eq, un_beta_trueprop,
};

fn trans_then_beta(eq: Thm, beta_lhs: Term) -> Result<Thm> {
    let beta = beta_at(beta_lhs)?;
    eq.trans(beta)
}

/// `succ 0`, the canonical literal 1 as a Term.
fn one() -> Term {
    Term::app(hol::succ_fn(), hol::zero())
}

/// The step function nat_pow iterates: `λx:nat. nat_mul n x`.
fn pow_step(n: &Term) -> Term {
    let x = Term::free("x", Type::nat());
    let body = Term::app(Term::app(defs::nat_mul(), n.clone()), x);
    hol::pub_abs("x", Type::nat(), body)
}

/// `⊢ nat_pow n m ≡ iter[nat] m (λx. nat_mul n x) 1`.
pub fn nat_pow_unfold_at(n: Term, m: Term) -> Result<Thm> {
    let nat_pow = defs::nat_pow();
    let unfold = Thm::unfold_term_spec(nat_pow)?;
    let after_n = apply_eq(unfold, n)?;
    let after_n_lhs = after_n.concl_rhs()?.clone();
    let after_n_beta = trans_then_beta(after_n, after_n_lhs)?;
    let after_m = apply_eq(after_n_beta, m)?;
    let after_m_lhs = after_m.concl_rhs()?.clone();
    trans_then_beta(after_m, after_m_lhs)
}

/// `⊢ nat_pow n 0 ≡ 1` for concrete `n`. Direct from iter_zero.
pub fn nat_pow_zero_at(n: Term) -> Result<Thm> {
    let unfold = nat_pow_unfold_at(n.clone(), hol::zero())?;
    let step = pow_step(&n);
    let iter_zero = iter_zero_eq_at(Type::nat(), step, one())?;
    unfold.trans(iter_zero)
}

/// `⊢ nat_pow n (succ m) ≡ nat_mul n (nat_pow n m)` for concrete
/// `n`, `m`. Direct from iter_succ + a β-reduction + reverse unfold.
pub fn nat_pow_succ_at(n: Term, m: Term) -> Result<Thm> {
    let succ_m = Term::app(hol::succ_fn(), m.clone());
    let step = pow_step(&n);

    let unfold = nat_pow_unfold_at(n.clone(), succ_m)?;
    let iter_succ = iter_succ_eq_at(Type::nat(), m.clone(), step.clone(), one())?;
    let after_iter = unfold.trans(iter_succ)?;
    // after_iter: nat_pow n (S m) ≡ (λx. n*x) (iter m step 1).

    // β-reduce the step application.
    let inner_arg = match after_iter.concl_rhs()?.kind() {
        crate::term::TermKind::App(_, arg) => (*arg).clone(),
        _ => panic!("nat_pow_succ_at: expected App after iter_succ"),
    };
    let step_app = Term::app(step, inner_arg.clone());
    let beta = beta_at(step_app)?;
    let after_beta = after_iter.trans(beta)?;
    // after_beta: nat_pow n (S m) ≡ n * (iter m pow_step 1).

    // Reverse-unfold iter m step 1 ≡ nat_pow n m.
    let n_unfold = nat_pow_unfold_at(n.clone(), m)?;
    let fold = n_unfold.sym()?;
    let nat_mul_n = Term::app(defs::nat_mul(), n);
    let head_refl = Thm::refl(nat_mul_n)?;
    let lifted = head_refl.cong_app(fold)?;
    // lifted: n * (iter m step 1) ≡ n * (nat_pow n m).

    after_beta.trans(lifted)
}

/// `⊢ ⋀n:nat. Trueprop (nat_pow 1 n = 1)` — `1^n = 1`. Induction
/// on `n`.
pub fn nat_one_pow() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(defs::nat_pow(), one()), n);
    let p_body = hol::hol_eq(lhs, one());
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base: 1^0 ≡ 1.
    let base_pure = nat_pow_zero_at(one())?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_one_pow_step(&p_lambda)?;

    let after_base = induction_at_p.imp_elim(base)?;
    after_base.imp_elim(step)
}

fn nat_one_pow_step(p_lambda: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?; // 1^n ≡ 1.

    // Goal: 1^(S n) ≡ 1.
    //   1^(S n) ≡ 1 * 1^n    [pow_succ]
    //           ≡ 1 * 1       [IH cong]
    //           ≡ 1            [nat_mul_one_left]
    let succ_eq = nat_pow_succ_at(one(), n.clone())?;
    let nat_mul_one = Term::app(defs::nat_mul(), one());
    let head_refl = Thm::refl(nat_mul_one)?;
    let lifted_ih = head_refl.cong_app(ih_pure)?;
    let after_ih = succ_eq.trans(lifted_ih)?;
    // after_ih: 1^(S n) ≡ 1 * 1.

    let one_left = nat_mul_one_left(one())?;
    let pure_eq = after_ih.trans(one_left)?;

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_n)?;

    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

/// `⊢ ⋀n:nat. Trueprop (nat_pow 0 (succ n) = 0)` — `0^(S n) = 0`,
/// direct from the recursion.
///
/// `0^(S n) ≡ 0 * 0^n ≡ 0` by [`nat_pow_succ_at`] and
/// [`nat_mul_zero_left`].
pub fn nat_pow_zero_pow_succ() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let succ_eq = nat_pow_succ_at(hol::zero(), n.clone())?;
    // succ_eq: 0^(S n) ≡ 0 * 0^n.
    let pow_zero_n = Term::app(Term::app(defs::nat_pow(), hol::zero()), n.clone());
    let zero_left = nat_mul_zero_left(pow_zero_n)?;
    // zero_left: 0 * 0^n ≡ 0.
    let pure_eq = succ_eq.trans(zero_left)?;
    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let _ = succ_n;
    hol_form.all_intro("n", Type::nat())
}

/// Specialise [`nat_pow_zero_at`] under `⋀n` for the API surface.
pub fn nat_pow_zero() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let pure_eq = nat_pow_zero_at(n)?;
    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    hol_form.all_intro("n", Type::nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pow_zero_at_builds() {
        let n = Term::free("n", Type::nat());
        let _ = nat_pow_zero_at(n).expect("n^0 ≡ 1");
    }

    #[test]
    fn pow_succ_at_builds() {
        let n = Term::free("n", Type::nat());
        let m = Term::free("m", Type::nat());
        let _ = nat_pow_succ_at(n, m).expect("n^(S m) ≡ n * n^m");
    }

    #[test]
    fn pow_zero_builds() {
        let _ = nat_pow_zero().expect("⋀n. n^0 = 1");
    }

    #[test]
    fn one_pow_builds() {
        let _ = nat_one_pow().expect("⋀n. 1^n = 1");
    }

    #[test]
    fn zero_pow_succ_builds() {
        let _ = nat_pow_zero_pow_succ().expect("⋀n. 0^(S n) = 0");
    }

    #[test]
    fn instantiated_one_pow_unused_imports() {
        // Smoke test that the instantiate_universal import is available
        // for downstream proofs to invoke nat_one_pow at concrete n.
        let two = Term::app(hol::succ_fn(), Term::app(hol::succ_fn(), hol::zero()));
        let one_pow = nat_one_pow().expect("base lemma");
        let _at_two = instantiate_universal(one_pow, vec![two]).expect("instantiable");
    }
}
