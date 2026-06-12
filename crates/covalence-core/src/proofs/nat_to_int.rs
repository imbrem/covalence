//! Theorems about `nat_to_int`.
//!
//! `nat_to_int n ≔ iter[int] n intSucc 0_int` — apply `intSucc` to
//! `0` exactly `n` times. From this definition + the two int
//! axioms ([`Thm::int_add_zero_right`], [`Thm::int_add_succ_right`])
//! the standard ring-homomorphism property follows.
//!
//! Provided:
//! - [`nat_to_int_zero`] — `(int) 0 ≡ 0`
//! - [`nat_to_int_succ_at`] — `(int)(S n) ≡ intSucc ((int) n)`
//! - [`nat_to_int_add_homo`] — `⋀n m. (int)(n + m) = (int) n + (int) m`

use crate::defs;
use crate::error::Result;
use crate::hol;
use crate::term::{Term, Type};
use crate::thm::Thm;

use super::iter::{iter_succ_eq_at, iter_zero_eq_at};
use super::{
    apply_eq, beta_at, beta_trueprop, instantiate_universal, pure_eq_of_hol_eq, trueprop,
    trueprop_of_pure_eq, un_beta_trueprop,
};

fn trans_then_beta(eq: Thm, beta_lhs: Term) -> Result<Thm> {
    let beta = beta_at(beta_lhs)?;
    eq.trans(beta)
}

/// `⊢ nat_to_int n ≡ iter[int] n intSucc 0` — unfold + 1× β.
pub fn nat_to_int_unfold_at(n: Term) -> Result<Thm> {
    let nat_to_int = defs::nat_to_int();
    let unfold = Thm::unfold_term_spec(nat_to_int)?;
    let after_n = apply_eq(unfold, n)?;
    let after_n_lhs = after_n.concl_rhs()?.clone();
    trans_then_beta(after_n, after_n_lhs)
}

/// `⊢ nat_to_int 0 ≡ 0_int`.
pub fn nat_to_int_zero() -> Result<Thm> {
    let unfold = nat_to_int_unfold_at(hol::zero())?;
    let iter_zero = iter_zero_eq_at(Type::int(), defs::int_succ(), defs::int_zero())?;
    unfold.trans(iter_zero)
}

/// `⊢ nat_to_int (S n) ≡ intSucc (nat_to_int n)` for concrete `n`.
pub fn nat_to_int_succ_at(n: Term) -> Result<Thm> {
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let unfold = nat_to_int_unfold_at(succ_n)?;
    // unfold: nat_to_int (S n) ≡ iter (S n) intSucc 0_int.
    let iter_succ = iter_succ_eq_at(Type::int(), n.clone(), defs::int_succ(), defs::int_zero())?;
    // iter_succ: iter (S n) intSucc 0 ≡ intSucc (iter n intSucc 0).
    let chain = unfold.trans(iter_succ)?;

    // Reverse-unfold iter n intSucc 0 ≡ nat_to_int n.
    let n_unfold = nat_to_int_unfold_at(n)?;
    let int_succ_refl = Thm::refl(defs::int_succ())?;
    let lifted = int_succ_refl.cong_app(n_unfold.sym()?)?;
    chain.trans(lifted)
}

/// `⊢ ⋀n m:nat. Trueprop (nat_to_int (nat_add n m) = int_add (nat_to_int n) (nat_to_int m))`
/// — the ring-homomorphism property of `nat_to_int`. Proved by
/// induction on `m` (with `n` held free), then post-quantified.
pub fn nat_to_int_add_homo() -> Result<Thm> {
    let n = Term::free("n", Type::nat());

    let m = Term::free("m", Type::nat());
    let n_plus_m = Term::app(Term::app(defs::nat_add(), n.clone()), m.clone());
    let lhs = Term::app(defs::nat_to_int(), n_plus_m);
    let int_n = Term::app(defs::nat_to_int(), n.clone());
    let int_m = Term::app(defs::nat_to_int(), m);
    let rhs = Term::app(Term::app(defs::int_add(), int_n), int_m);
    let p_body = hol::hol_eq(lhs, rhs);
    let p_lambda = hol::pub_abs("m", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // ---- Base m=0: (int)(n + 0) = (int)n + (int)0 ----
    //   lhs:  (int)(n + 0) ≡ (int) n             [by nat_add_zero_right at n]
    //   rhs:  (int) n + (int) 0
    //        ≡ (int) n + 0_int                    [by nat_to_int_zero cong]
    //        ≡ (int) n                            [by int_add_zero_right at (int) n]
    let base_pure = nat_to_int_add_homo_base_at(&n)?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    // ---- Step ----
    let step = nat_to_int_add_homo_step(&p_lambda, &n)?;

    let after_base = induction_at_p.imp_elim(base)?;
    let universal_m = after_base.imp_elim(step)?;

    universal_m.all_intro("n", Type::nat())
}

/// Base case: `(int)(n + 0) ≡ (int) n + (int) 0`.
fn nat_to_int_add_homo_base_at(n: &Term) -> Result<Thm> {
    use super::nat_add::nat_add_zero_right;

    // lhs: (int)(n + 0) ≡ (int) n   via nat_to_int cong on nat_add_zero_right at n.
    let zr = nat_add_zero_right()?;
    let zr_at_n = instantiate_universal(zr, vec![n.clone()])?;
    let zr_at_n_pure = pure_eq_of_hol_eq(zr_at_n)?;
    // zr_at_n_pure: nat_add n 0 ≡ n.
    let nat_to_int_refl = Thm::refl(defs::nat_to_int())?;
    let lhs_eq = nat_to_int_refl.cong_app(zr_at_n_pure)?;
    // lhs_eq: (int)(n + 0) ≡ (int) n.

    // rhs: (int) n + (int) 0 ≡ (int) n + 0_int   [by nat_to_int_zero cong]
    let nti_zero = nat_to_int_zero()?;
    let int_add_int_n_term = Term::app(
        defs::int_add(),
        Term::app(defs::nat_to_int(), n.clone()),
    );
    let head_refl = Thm::refl(int_add_int_n_term)?;
    let rhs_step1 = head_refl.cong_app(nti_zero)?;
    // rhs_step1: (int)n + (int)0 ≡ (int)n + 0_int.

    //   (int)n + 0_int ≡ (int)n        [int_add_zero_right at (int)n]
    let int_n_term = Term::app(defs::nat_to_int(), n.clone());
    let zr_int = instantiate_universal(Thm::int_add_zero_right(), vec![int_n_term])?;
    let zr_int_pure = pure_eq_of_hol_eq(zr_int)?;
    // zr_int_pure: int_add (int)n 0_int ≡ (int)n.
    let rhs_chain = rhs_step1.trans(zr_int_pure)?;
    // rhs_chain: (int)n + (int)0 ≡ (int)n.

    // Final: lhs and rhs both equal (int)n.
    lhs_eq.trans(rhs_chain.sym()?)
}

/// Inductive step: `(int)(n + S m) ≡ (int)n + (int)(S m)`.
fn nat_to_int_add_homo_step(p_lambda: &Term, n: &Term) -> Result<Thm> {
    use super::nat_add::nat_add_succ_right;

    let m = Term::free("m", Type::nat());
    let succ_m = Term::app(hol::succ_fn(), m.clone());

    let p_m = Term::app(p_lambda.clone(), m.clone());
    let trueprop_p_m = trueprop(p_m.clone());
    let ih_un_beta = Thm::assume(trueprop_p_m.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_m)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?;
    // ih_pure: (int)(n + m) = (int)n + (int)m.

    // Goal: (int)(n + S m) ≡ (int)n + (int)(S m).
    //
    // lhs: (int)(n + S m)
    //   ≡ (int)(S (n + m))             [by nat_add_succ_right at (n, m)]
    //   ≡ intSucc ((int)(n + m))       [by nat_to_int_succ_at (n + m)]
    //   ≡ intSucc ((int)n + (int)m)    [by IH cong]
    //
    // rhs: (int)n + (int)(S m)
    //   ≡ (int)n + intSucc ((int)m)    [by nat_to_int_succ_at m, cong]
    //   ≡ intSucc ((int)n + (int)m)    [by int_add_succ_right at (int)n, (int)m]
    //
    // Both equal intSucc ((int)n + (int)m). ✓

    // --- lhs chain ---
    // nat_add_succ_right's statement (per its proof): ⋀n_old. ⋀m_old.
    //   nat_add m_old (S n_old) = S (nat_add m_old n_old).
    // We want: nat_add n (S m) = S (nat_add n m).
    // So substitute n_old := m, m_old := n  → witnesses [m, n].
    let nasr = nat_add_succ_right()?;
    let nasr_inst = instantiate_universal(nasr, vec![m.clone(), n.clone()])?;
    let nasr_pure = pure_eq_of_hol_eq(nasr_inst)?;
    // nasr_pure: nat_add n (S m) ≡ S (nat_add n m).

    let nat_to_int_refl = Thm::refl(defs::nat_to_int())?;
    let lhs_step1 = nat_to_int_refl.cong_app(nasr_pure)?;
    // lhs_step1: (int)(n + S m) ≡ (int)(S (n + m)).

    let n_plus_m = Term::app(Term::app(defs::nat_add(), n.clone()), m.clone());
    let lhs_step2 = nat_to_int_succ_at(n_plus_m)?;
    // lhs_step2: (int)(S (n + m)) ≡ intSucc ((int)(n + m)).
    let chain1 = lhs_step1.trans(lhs_step2)?;

    let int_succ_refl = Thm::refl(defs::int_succ())?;
    let lhs_step3 = int_succ_refl.cong_app(ih_pure.clone())?;
    // lhs_step3: intSucc ((int)(n + m)) ≡ intSucc ((int)n + (int)m).
    let lhs_chain = chain1.trans(lhs_step3)?;
    // lhs_chain: (int)(n + S m) ≡ intSucc ((int)n + (int)m).

    // --- rhs chain ---
    let nti_succ_m = nat_to_int_succ_at(m.clone())?;
    // nti_succ_m: (int)(S m) ≡ intSucc ((int)m).
    let int_add_int_n_term = Term::app(
        defs::int_add(),
        Term::app(defs::nat_to_int(), n.clone()),
    );
    let int_n_refl_head = Thm::refl(int_add_int_n_term)?;
    let rhs_step1 = int_n_refl_head.cong_app(nti_succ_m)?;
    // rhs_step1: (int)n + (int)(S m) ≡ (int)n + intSucc ((int)m).

    // int_add_succ_right: ⋀a b. int_add a (intSucc b) = intSucc (int_add a b).
    // Instantiate at (a, b) := ((int)n, (int)m).
    let isr = Thm::int_add_succ_right();
    let int_n_term = Term::app(defs::nat_to_int(), n.clone());
    let int_m_term = Term::app(defs::nat_to_int(), m.clone());
    let isr_inst = instantiate_universal(isr, vec![int_n_term, int_m_term])?;
    let isr_pure = pure_eq_of_hol_eq(isr_inst)?;
    // isr_pure: int_add (int)n (intSucc (int)m) ≡ intSucc (int_add (int)n (int)m).
    let rhs_chain = rhs_step1.trans(isr_pure)?;
    // rhs_chain: (int)n + (int)(S m) ≡ intSucc ((int)n + (int)m).

    // Combine.
    let pure_eq = lhs_chain.trans(rhs_chain.sym()?)?;
    // pure_eq: (int)(n + S m) ≡ (int)n + (int)(S m).

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_m = Term::app(p_lambda.clone(), succ_m);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_m)?;

    let imp = un_beta.imp_intro(&trueprop_p_m)?;
    imp.all_intro("m", Type::nat())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermKind;

    #[test]
    fn zero_builds() {
        let thm = nat_to_int_zero().expect("(int) 0 ≡ 0_int");
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &defs::int_zero()),
            other => panic!("expected Eq with 0_int on rhs, got {other:?}"),
        }
    }

    #[test]
    fn succ_at_builds() {
        let n = Term::free("n", Type::nat());
        let _ = nat_to_int_succ_at(n).expect("(int)(S n) ≡ intSucc ((int) n)");
    }

    #[test]
    fn add_homo_builds() {
        let _ = nat_to_int_add_homo().expect("⋀n m. (int)(n+m) = (int)n + (int)m");
    }
}
