//! Theorems about `nat_mul`.
//!
//! `nat_mul n m ≔ iter n (λx. nat_add m x) 0`. The basic equations:
//!
//! - [`nat_mul_zero_left`] — `0 * m ≡ 0`
//! - [`nat_mul_succ_left_at`] — `(S n) * m ≡ m + (n * m)`
//! - [`nat_mul_zero_right`] — `⋀n. n * 0 = 0` (induction)
//! - [`nat_mul_one_left`] — `1 * m ≡ m`
//! - [`nat_mul_one_right`] — `⋀n. n * 1 = n` (induction)
//! - [`nat_mul_succ_right`] — `⋀n m. n * (S m) = n + (n * m)` (induction)
//! - [`nat_mul_comm`] — `⋀n m. n * m = m * n` (induction)

use crate::defs;
use crate::error::Result;
use crate::hol;
use crate::term::{Term, Type};
use crate::thm::Thm;

use super::iter::{iter_succ_eq_at, iter_zero_eq_at};
use super::nat_add::{nat_add_succ_left_at, nat_add_zero_left, nat_add_zero_right};
use super::{
    apply_eq, beta_at, beta_trueprop, instantiate_universal, pure_eq_of_hol_eq, trueprop,
    trueprop_of_pure_eq, un_beta_trueprop,
};

fn trans_then_beta(eq: Thm, beta_lhs: Term) -> Result<Thm> {
    let beta = beta_at(beta_lhs)?;
    eq.trans(beta)
}

/// `succ 0`, i.e. the canonical literal 1 as a Term.
fn one() -> Term {
    Term::app(hol::succ_fn(), hol::zero())
}

/// The step function nat_mul iterates: `λx:nat. nat_add m x` for a
/// concrete `m`. Builds it freshly each call (m differs per use).
fn mul_step(m: &Term) -> Term {
    let x = Term::free("x", Type::nat());
    let body = Term::app(Term::app(defs::nat_add(), m.clone()), x);
    hol::pub_abs("x", Type::nat(), body)
}

/// `⊢ nat_mul n m ≡ iter[nat] n (λx. nat_add m x) 0`. The unfold +
/// 2× β chain on the binary lambda body. Used by every other
/// `nat_mul` lemma to bring the term into iter form.
pub fn nat_mul_unfold_at(n: Term, m: Term) -> Result<Thm> {
    let nat_mul = defs::nat_mul();
    let unfold = Thm::unfold_term_spec(nat_mul)?;
    let after_n = apply_eq(unfold, n)?;
    let after_n_lhs = after_n.concl_rhs()?.clone();
    let after_n_beta = trans_then_beta(after_n, after_n_lhs)?;
    let after_m = apply_eq(after_n_beta, m)?;
    let after_m_lhs = after_m.concl_rhs()?.clone();
    trans_then_beta(after_m, after_m_lhs)
}

/// `⊢ nat_mul 0 m ≡ 0` for concrete `m`.
pub fn nat_mul_zero_left(m: Term) -> Result<Thm> {
    let zero = hol::zero();
    // 1. nat_mul 0 m ≡ iter 0 (λx. m + x) 0
    let unfold = nat_mul_unfold_at(zero.clone(), m.clone())?;
    // 2. iter[nat] 0 (step) 0 ≡ 0.
    let step = mul_step(&m);
    let iter_zero = iter_zero_eq_at(Type::nat(), step, zero)?;
    unfold.trans(iter_zero)
}

/// `⊢ nat_mul (succ n) m ≡ nat_add m (nat_mul n m)` for concrete
/// `n`, `m`. Mirrors [`super::nat_add::nat_add_succ_left_at`] but
/// for multiplication, with the step function `(λx. m + x)`.
pub fn nat_mul_succ_left_at(n: Term, m: Term) -> Result<Thm> {
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let step = mul_step(&m);

    // 1. nat_mul (S n) m ≡ iter (S n) step 0
    let unfold = nat_mul_unfold_at(succ_n, m.clone())?;

    // 2. iter (S n) step 0 ≡ step (iter n step 0)
    let iter_succ = iter_succ_eq_at(Type::nat(), n.clone(), step.clone(), hol::zero())?;
    let after_iter = unfold.trans(iter_succ)?;
    // after_iter: nat_mul (S n) m ≡ (λx. m + x) (iter n step 0)

    // 3. β-reduce the step application: (λx. m + x) (iter n step 0) ≡ m + (iter n step 0)
    let inner_arg = match after_iter.concl_rhs()?.kind() {
        crate::term::TermKind::App(_, arg) => (*arg).clone(),
        _ => panic!("nat_mul_succ_left_at: expected App after iter_succ"),
    };
    let step_app = Term::app(step.clone(), inner_arg.clone());
    let beta = beta_at(step_app)?;
    let after_beta = after_iter.trans(beta)?;
    // after_beta: nat_mul (S n) m ≡ m + (iter n step 0)

    // 4. iter n step 0 ≡ nat_mul n m (reverse unfold).
    let n_unfold = nat_mul_unfold_at(n, m.clone())?; // nat_mul n m ≡ iter n step 0
    let fold = n_unfold.sym()?;
    // 5. Lift via cong (nat_add m _).
    let nat_add_m = Term::app(defs::nat_add(), m);
    let head_refl = Thm::refl(nat_add_m)?;
    let lifted = head_refl.cong_app(fold)?;
    // lifted: nat_add m (iter n step 0) ≡ nat_add m (nat_mul n m)

    after_beta.trans(lifted)
}

/// `⊢ ⋀n:nat. Trueprop (nat_mul n 0 = 0)` — multiplication by zero
/// on the right. Proved by induction on `n`.
pub fn nat_mul_zero_right() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(defs::nat_mul(), n.clone()), hol::zero());
    let p_body = hol::hol_eq(lhs, hol::zero());
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base: nat_mul 0 0 ≡ 0 via nat_mul_zero_left at m = 0.
    let base_pure = nat_mul_zero_left(hol::zero())?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_mul_zero_right_step(&p_lambda)?;

    let after_base = induction_at_p.imp_elim(base)?;
    after_base.imp_elim(step)
}

fn nat_mul_zero_right_step(p_lambda: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?; // nat_mul n 0 ≡ 0.

    // Goal: nat_mul (S n) 0 ≡ 0.
    // 1. nat_mul (S n) 0 ≡ nat_add 0 (nat_mul n 0).
    let succ_left = nat_mul_succ_left_at(n.clone(), hol::zero())?;
    // 2. nat_add 0 (nat_mul n 0) ≡ nat_mul n 0 (zero_left).
    let nm = Term::app(Term::app(defs::nat_mul(), n.clone()), hol::zero());
    let zero_left = nat_add_zero_left(nm)?;
    let chain = succ_left.trans(zero_left)?;
    // chain: nat_mul (S n) 0 ≡ nat_mul n 0.

    // 3. Use IH: nat_mul n 0 ≡ 0.
    let pure_eq = chain.trans(ih_pure)?;

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_n)?;

    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

/// `⊢ nat_mul 1 m ≡ m` for concrete `m`. Direct: `1 * m =
/// succ 0 * m = m + 0 * m = m + 0 = m`.
pub fn nat_mul_one_left(m: Term) -> Result<Thm> {
    // 1. 1 * m ≡ m + (0 * m)  [succ_left]
    let succ_left = nat_mul_succ_left_at(hol::zero(), m.clone())?;
    // 2. 0 * m ≡ 0.
    let zero_left = nat_mul_zero_left(m.clone())?;
    // 3. Lift through (nat_add m _).
    let nat_add_m = Term::app(defs::nat_add(), m.clone());
    let head_refl = Thm::refl(nat_add_m)?;
    let step2 = head_refl.cong_app(zero_left)?;
    // step2: m + (0 * m) ≡ m + 0.
    let chain = succ_left.trans(step2)?;
    // chain: 1 * m ≡ m + 0.

    // 4. m + 0 ≡ m via nat_add_zero_right at m.
    let zr = nat_add_zero_right()?;
    let zr_at_m_un_beta = zr.all_elim(m.clone())?;
    // β to extract: nat_add m 0 = m.
    let p_lambda_zr = {
        let n_free = Term::free("n", Type::nat());
        let body = hol::hol_eq(
            Term::app(Term::app(defs::nat_add(), n_free.clone()), hol::zero()),
            n_free,
        );
        hol::pub_abs("n", Type::nat(), body)
    };
    let zr_at_m_app = Term::app(p_lambda_zr, m);
    let zr_at_m_hol = beta_trueprop(zr_at_m_un_beta, zr_at_m_app)?;
    let zr_at_m_pure = pure_eq_of_hol_eq(zr_at_m_hol)?;

    chain.trans(zr_at_m_pure)
}

/// `⊢ ⋀n:nat. Trueprop (nat_mul n 1 = n)` — right-identity for `1`.
/// Proved by induction on `n`.
pub fn nat_mul_one_right() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(defs::nat_mul(), n.clone()), one());
    let p_body = hol::hol_eq(lhs, n);
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base: nat_mul 0 1 ≡ 0.
    let base_pure = nat_mul_zero_left(one())?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_mul_one_right_step(&p_lambda)?;

    let after_base = induction_at_p.imp_elim(base)?;
    after_base.imp_elim(step)
}

fn nat_mul_one_right_step(p_lambda: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?; // nat_mul n 1 ≡ n.

    // Goal: nat_mul (S n) 1 ≡ S n.
    // 1. (S n) * 1 ≡ 1 + (n * 1) [succ_left].
    let succ_left = nat_mul_succ_left_at(n.clone(), one())?;
    // 2. Lift IH through (nat_add 1 _):  1 + (n * 1) ≡ 1 + n.
    let nat_add_1 = Term::app(defs::nat_add(), one());
    let head_refl = Thm::refl(nat_add_1)?;
    let step2 = head_refl.cong_app(ih_pure)?;
    let chain = succ_left.trans(step2)?;
    // chain: (S n) * 1 ≡ 1 + n.

    // 3. 1 + n ≡ S n.
    //    1 = succ 0; nat_add (succ 0) n ≡ succ (nat_add 0 n) by succ_left, ≡ succ n by zero_left.
    let succ_left_for_add = nat_add_succ_left_at(hol::zero(), n.clone())?;
    // succ_left_for_add: nat_add (succ 0) n ≡ succ (nat_add 0 n)
    let zero_left_for_add = nat_add_zero_left(n.clone())?;
    let succ_refl = Thm::refl(hol::succ_fn())?;
    let lifted_zero_left = succ_refl.cong_app(zero_left_for_add)?;
    // lifted_zero_left: succ (nat_add 0 n) ≡ succ n
    let one_plus_n_eq_succ_n = succ_left_for_add.trans(lifted_zero_left)?;

    let pure_eq = chain.trans(one_plus_n_eq_succ_n)?;
    // pure_eq: nat_mul (S n) 1 ≡ S n.

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_n)?;

    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

/// `⊢ ⋀n m:nat. Trueprop (nat_mul n (succ m) = nat_add n (nat_mul n m))`
/// — succ commutes with `*` on the right (as `+ n`). Proved by
/// induction on `n` with `m` held free, then post-quantified.
pub fn nat_mul_succ_right() -> Result<Thm> {
    let m = Term::free("m", Type::nat());
    let n = Term::free("n", Type::nat());

    let lhs = Term::app(
        Term::app(defs::nat_mul(), n.clone()),
        Term::app(hol::succ_fn(), m.clone()),
    );
    let nm = Term::app(Term::app(defs::nat_mul(), n.clone()), m.clone());
    let rhs = Term::app(Term::app(defs::nat_add(), n.clone()), nm);
    let p_body = hol::hol_eq(lhs, rhs);
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base n=0: nat_mul 0 (succ m) = nat_add 0 (nat_mul 0 m).
    //   lhs: 0 * (S m) ≡ 0 by zero_left.
    //   rhs: 0 + (0 * m) ≡ 0 + 0 ≡ 0.
    let lhs_eq = nat_mul_zero_left(Term::app(hol::succ_fn(), m.clone()))?;
    let nm_at_zero = Term::app(Term::app(defs::nat_mul(), hol::zero()), m.clone());
    let inner = nat_mul_zero_left(m.clone())?; // 0 * m ≡ 0
    let nat_add_zero = Term::app(defs::nat_add(), hol::zero());
    let head_refl = Thm::refl(nat_add_zero)?;
    let rhs_step1 = head_refl.cong_app(inner)?;
    // rhs_step1: 0 + (0 * m) ≡ 0 + 0
    let rhs_step2 = nat_add_zero_left(hol::zero())?; // 0 + 0 ≡ 0
    let rhs_chain_pure = {
        let _ = nm_at_zero;
        rhs_step1.trans(rhs_step2)?
    };
    // rhs_chain_pure: 0 + (0 * m) ≡ 0
    let base_pure = lhs_eq.trans(rhs_chain_pure.sym()?)?;
    // base_pure: 0 * (S m) ≡ 0 + (0 * m)

    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_mul_succ_right_step(&p_lambda, &m)?;

    let after_base = induction_at_p.imp_elim(base)?;
    let universal_n = after_base.imp_elim(step)?;

    universal_n.all_intro("m", Type::nat())
}

fn nat_mul_succ_right_step(p_lambda: &Term, m: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let succ_m = Term::app(hol::succ_fn(), m.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?;
    // ih_pure: nat_mul n (succ m) ≡ nat_add n (nat_mul n m).

    // Goal: nat_mul (S n) (succ m) ≡ nat_add (S n) (nat_mul (S n) m).
    //
    // lhs: (S n) * (S m)
    //   ≡ (S m) + (n * (S m))            [succ_left at n, (S m)]
    //   ≡ (S m) + (n + (n * m))          [IH cong]
    //   = succ m + n + n * m
    let lhs1 = nat_mul_succ_left_at(n.clone(), succ_m.clone())?;
    let nat_add_sm = Term::app(defs::nat_add(), succ_m.clone());
    let head_refl_sm = Thm::refl(nat_add_sm)?;
    let lhs2 = head_refl_sm.cong_app(ih_pure)?;
    let lhs_chain = lhs1.trans(lhs2)?;
    // lhs_chain: (S n) * (S m) ≡ (S m) + (n + (n * m)).

    // rhs: (S n) + ((S n) * m)
    //   ≡ (S n) + (m + (n * m))           [succ_left at n, m → m + (n*m)]
    let nm_at_m = Term::app(Term::app(defs::nat_mul(), n.clone()), m.clone());
    let succ_left_inner = nat_mul_succ_left_at(n.clone(), m.clone())?;
    // succ_left_inner: (S n) * m ≡ m + (n * m).
    let nat_add_sn = Term::app(defs::nat_add(), succ_n.clone());
    let head_refl_sn = Thm::refl(nat_add_sn)?;
    let rhs_step1 = head_refl_sn.cong_app(succ_left_inner)?;
    // rhs_step1: (S n) + ((S n) * m) ≡ (S n) + (m + (n * m)).
    let _ = nm_at_m;

    // We need to show lhs_chain.rhs ≡ rhs_step1.rhs, i.e.
    //   (S m) + (n + (n * m)) ≡ (S n) + (m + (n * m))
    //
    // Strategy: both sides equal S (m + n + n*m) after pushing succ
    // through addition. Specifically:
    //   (S m) + X ≡ S (m + X)  [succ_left at m]
    //   (S n) + Y ≡ S (n + Y)  [succ_left at n]
    // So lhs.rhs ≡ S (m + (n + (n*m))) and rhs.rhs ≡ S (n + (m + (n*m))).
    // Need m + (n + nm) ≡ n + (m + nm). Use assoc + comm.
    let nm = Term::app(Term::app(defs::nat_mul(), n.clone()), m.clone());

    // (S m) + (n + nm) ≡ S (m + (n + nm))
    let n_plus_nm = Term::app(Term::app(defs::nat_add(), n.clone()), nm.clone());
    let lhs_succ_eq = nat_add_succ_left_at(m.clone(), n_plus_nm.clone())?;
    // (S n) + (m + nm) ≡ S (n + (m + nm))
    let m_plus_nm = Term::app(Term::app(defs::nat_add(), m.clone()), nm.clone());
    let rhs_succ_eq = nat_add_succ_left_at(n.clone(), m_plus_nm.clone())?;

    // Show inner: m + (n + nm) ≡ n + (m + nm)
    //   m + (n + nm) ≡ (m + n) + nm    [assoc.sym]
    //   ≡ (n + m) + nm                  [comm cong]
    //   ≡ n + (m + nm)                  [assoc]
    let inner_eq = nat_mul_succ_right_inner(&m.clone(), &n, &nm)?;
    // inner_eq: m + (n + nm) ≡ n + (m + nm).

    // Lift inner_eq through succ.
    let succ_refl = Thm::refl(hol::succ_fn())?;
    let succ_inner = succ_refl.cong_app(inner_eq)?;
    // succ_inner: S (m + (n + nm)) ≡ S (n + (m + nm)).

    let lhs_to_inner = lhs_succ_eq.trans(succ_inner)?;
    // lhs_to_inner: (S m) + (n + nm) ≡ S (n + (m + nm)).
    let lhs_to_rhs = lhs_to_inner.trans(rhs_succ_eq.sym()?)?;
    // lhs_to_rhs: (S m) + (n + nm) ≡ (S n) + (m + nm).

    let final_pure = lhs_chain.trans(lhs_to_rhs)?.trans(rhs_step1.sym()?)?;
    // final_pure: (S n) * (S m) ≡ (S n) + ((S n) * m).

    let hol_form = trueprop_of_pure_eq(final_pure)?;
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_n)?;

    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

/// `⊢ m + (n + nm) ≡ n + (m + nm)` — used in the `nat_mul_succ_right`
/// step. Just assoc + comm chained.
fn nat_mul_succ_right_inner(m: &Term, n: &Term, nm: &Term) -> Result<Thm> {
    use super::nat_add::{nat_add_assoc, nat_add_comm};

    // assoc statement: ⋀m_a p_a n_a. (n_a + m_a) + p_a = n_a + (m_a + p_a)
    // We want m + (n + nm) ≡ (m + n) + nm, i.e. (m + n) + nm = m + (n + nm)
    // with n_a := m, m_a := n, p_a := nm.
    let assoc = nat_add_assoc()?;
    let assoc_inst = instantiate_universal(
        assoc,
        vec![n.clone(), nm.clone(), m.clone()],
    )?;
    let assoc_eq = pure_eq_of_hol_eq(assoc_inst)?;
    // assoc_eq: (m + n) + nm ≡ m + (n + nm). Sym for our direction.
    let assoc_eq = assoc_eq.sym()?;
    // assoc_eq: m + (n + nm) ≡ (m + n) + nm.

    // comm statement: ⋀m_c n_c. n_c + m_c = m_c + n_c.
    // We want m + n ≡ n + m, so instantiate at (m_c := n, n_c := m):
    // gives m + n = n + m.
    let comm = nat_add_comm()?;
    let comm_inst = instantiate_universal(comm, vec![n.clone(), m.clone()])?;
    let comm_eq = pure_eq_of_hol_eq(comm_inst)?;
    // comm_eq: m + n ≡ n + m.

    // Lift through (_ + nm).
    let nat_add_refl = Thm::refl(defs::nat_add())?;
    let step_inner = nat_add_refl.cong_app(comm_eq)?;
    let nm_refl = Thm::refl(nm.clone())?;
    let comm_lifted = step_inner.cong_app(nm_refl)?;
    // comm_lifted: (m + n) + nm ≡ (n + m) + nm.

    // assoc at (m_a := m, p_a := nm, n_a := n): (n + m) + nm = n + (m + nm).
    let assoc2 = nat_add_assoc()?;
    let assoc2_inst = instantiate_universal(
        assoc2,
        vec![m.clone(), nm.clone(), n.clone()],
    )?;
    let assoc2_eq = pure_eq_of_hol_eq(assoc2_inst)?;

    // Chain.
    assoc_eq.trans(comm_lifted)?.trans(assoc2_eq)
}

/// `⊢ ⋀n m:nat. Trueprop (nat_mul n m = nat_mul m n)` — commutativity.
/// Proved by induction on `n`.
pub fn nat_mul_comm() -> Result<Thm> {
    let m = Term::free("m", Type::nat());

    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(defs::nat_mul(), n.clone()), m.clone());
    let rhs = Term::app(Term::app(defs::nat_mul(), m.clone()), n);
    let p_body = hol::hol_eq(lhs, rhs);
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base: 0 * m ≡ m * 0.
    //   0 * m ≡ 0   [zero_left]
    //   m * 0 ≡ 0   [zero_right at m]
    let lhs_eq = nat_mul_zero_left(m.clone())?;
    let zr = nat_mul_zero_right()?;
    let zr_at_m_un_beta = zr.all_elim(m.clone())?;
    let p_lambda_zr = {
        let n_free = Term::free("n", Type::nat());
        let body = hol::hol_eq(
            Term::app(Term::app(defs::nat_mul(), n_free.clone()), hol::zero()),
            hol::zero(),
        );
        let _ = n_free;
        hol::pub_abs("n", Type::nat(), body)
    };
    let zr_at_m_app = Term::app(p_lambda_zr, m.clone());
    let zr_at_m_hol = beta_trueprop(zr_at_m_un_beta, zr_at_m_app)?;
    let zr_at_m_pure = pure_eq_of_hol_eq(zr_at_m_hol)?;
    let base_pure = lhs_eq.trans(zr_at_m_pure.sym()?)?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_mul_comm_step(&p_lambda, &m)?;

    let after_base = induction_at_p.imp_elim(base)?;
    let universal_n = after_base.imp_elim(step)?;

    universal_n.all_intro("m", Type::nat())
}

fn nat_mul_comm_step(p_lambda: &Term, m: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?;
    // ih_pure: n * m ≡ m * n.

    // Goal: (S n) * m ≡ m * (S n).
    // lhs: (S n) * m ≡ m + (n * m)         [succ_left]
    //              ≡ m + (m * n)            [IH cong]
    let lhs_step1 = nat_mul_succ_left_at(n.clone(), m.clone())?;
    let nat_add_m = Term::app(defs::nat_add(), m.clone());
    let head_refl = Thm::refl(nat_add_m)?;
    let lhs_step2 = head_refl.cong_app(ih_pure)?;
    let lhs_chain = lhs_step1.trans(lhs_step2)?;
    // lhs_chain: (S n) * m ≡ m + (m * n).

    // rhs: m * (S n) ≡ m + (m * n) via nat_mul_succ_right.
    //   sr: ⋀m_outer n_outer. Trueprop ((λn. n * (succ m_outer) = ...) n_outer)
    //   We want m * (succ n) — so instantiate at (m_outer := n, n_outer := m).
    let sr = nat_mul_succ_right()?;
    let sr_inst = instantiate_universal(sr, vec![n.clone(), m.clone()])?;
    let sr_inst_pure = pure_eq_of_hol_eq(sr_inst)?;
    // sr_inst_pure: nat_mul m (succ n) ≡ nat_add m (nat_mul m n).
    let pure_eq = lhs_chain.trans(sr_inst_pure.sym()?)?;
    // pure_eq: (S n) * m ≡ m * (S n).

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_n)?;

    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

/// `⊢ ⋀a b c:nat. Trueprop (nat_mul a (nat_add b c) = nat_add (nat_mul a b) (nat_mul a c))`
/// — left-distributivity. Proved by induction on `a` with `(b, c)`
/// held free, then post-quantified.
pub fn nat_mul_distrib_right() -> Result<Thm> {
    let b = Term::free("b", Type::nat());
    let c = Term::free("c", Type::nat());

    let a = Term::free("a", Type::nat());
    let bc = Term::app(Term::app(defs::nat_add(), b.clone()), c.clone());
    let lhs = Term::app(Term::app(defs::nat_mul(), a.clone()), bc);
    let ab = Term::app(Term::app(defs::nat_mul(), a.clone()), b.clone());
    let ac = Term::app(Term::app(defs::nat_mul(), a), c.clone());
    let rhs = Term::app(Term::app(defs::nat_add(), ab), ac);
    let p_body = hol::hol_eq(lhs, rhs);
    let p_lambda = hol::pub_abs("a", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base: 0 * (b + c) = 0 * b + 0 * c.
    //   lhs: 0 * (b+c) ≡ 0       [zero_left]
    //   rhs: 0*b + 0*c ≡ 0 + 0 ≡ 0
    let bc_term = Term::app(Term::app(defs::nat_add(), b.clone()), c.clone());
    let lhs_eq = nat_mul_zero_left(bc_term)?;
    let nb_eq = nat_mul_zero_left(b.clone())?;
    let nc_eq = nat_mul_zero_left(c.clone())?;
    let nat_add_refl = Thm::refl(defs::nat_add())?;
    let rhs_inner = nat_add_refl.cong_app(nb_eq)?;
    let rhs_step = rhs_inner.cong_app(nc_eq)?;
    // rhs_step: 0*b + 0*c ≡ 0 + 0.
    let zero_plus_zero = nat_add_zero_left(hol::zero())?;
    let rhs_chain = rhs_step.trans(zero_plus_zero)?;
    // rhs_chain: 0*b + 0*c ≡ 0.
    let base_pure = lhs_eq.trans(rhs_chain.sym()?)?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_mul_distrib_right_step(&p_lambda, &b, &c)?;

    let after_base = induction_at_p.imp_elim(base)?;
    let universal_a = after_base.imp_elim(step)?;

    universal_a
        .all_intro("c", Type::nat())?
        .all_intro("b", Type::nat())
}

fn nat_mul_distrib_right_step(p_lambda: &Term, b: &Term, c: &Term) -> Result<Thm> {
    use super::nat_add::nat_add_assoc;

    let a = Term::free("a", Type::nat());
    let succ_a = Term::app(hol::succ_fn(), a.clone());

    let p_a = Term::app(p_lambda.clone(), a.clone());
    let trueprop_p_a = trueprop(p_a.clone());
    let ih_un_beta = Thm::assume(trueprop_p_a.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_a)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?;
    // ih_pure: a * (b + c) = a*b + a*c.

    // Goal: (S a) * (b + c) ≡ (S a)*b + (S a)*c.
    // lhs: (S a) * (b + c)
    //   ≡ (b + c) + a * (b + c)        [mul_succ_left at (a, b+c)]
    //   ≡ (b + c) + (a*b + a*c)        [IH cong]
    let bc = Term::app(Term::app(defs::nat_add(), b.clone()), c.clone());
    let lhs_step1 = nat_mul_succ_left_at(a.clone(), bc.clone())?;
    let nat_add_bc_head = Term::app(defs::nat_add(), bc.clone());
    let head_refl = Thm::refl(nat_add_bc_head)?;
    let lhs_step2 = head_refl.cong_app(ih_pure)?;
    let lhs_chain = lhs_step1.trans(lhs_step2)?;
    // lhs_chain: (S a) * (b + c) ≡ (b + c) + (a*b + a*c).

    // rhs: (S a)*b + (S a)*c
    //   ≡ (b + a*b) + (c + a*c)        [mul_succ_left twice + cong]
    let sb_eq = nat_mul_succ_left_at(a.clone(), b.clone())?;
    let sc_eq = nat_mul_succ_left_at(a.clone(), c.clone())?;
    let nat_add_refl = Thm::refl(defs::nat_add())?;
    let rhs_inner = nat_add_refl.cong_app(sb_eq)?;
    let rhs_step1 = rhs_inner.cong_app(sc_eq)?;
    // rhs_step1: (S a)*b + (S a)*c ≡ (b + a*b) + (c + a*c).

    // Final: lhs and rhs both equal (b + c) + (a*b + a*c) vs (b + a*b) + (c + a*c).
    // The shuffle: (b + c) + (a*b + a*c) ≡ (b + a*b) + (c + a*c).
    //   Use assoc + comm: both equal b + c + a*b + a*c without parens,
    //   permuted so that b, a*b together and c, a*c together.
    let ab = Term::app(Term::app(defs::nat_mul(), a.clone()), b.clone());
    let ac = Term::app(Term::app(defs::nat_mul(), a.clone()), c.clone());
    let inner = nat_mul_distrib_right_shuffle(b, c, &ab, &ac)?;
    // inner: (b + c) + (a*b + a*c) ≡ (b + a*b) + (c + a*c).
    let _ = nat_add_assoc;

    let pure_eq = lhs_chain.trans(inner)?.trans(rhs_step1.sym()?)?;
    // pure_eq: (S a) * (b + c) ≡ (S a)*b + (S a)*c.

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_a = Term::app(p_lambda.clone(), succ_a);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_a)?;

    let imp = un_beta.imp_intro(&trueprop_p_a)?;
    imp.all_intro("a", Type::nat())
}

/// Shuffle: `(b + c) + (x + y) ≡ (b + x) + (c + y)`. Pure addition
/// equation; uses assoc and comm in nat_add.
fn nat_mul_distrib_right_shuffle(
    b: &Term,
    c: &Term,
    x: &Term,
    y: &Term,
) -> Result<Thm> {
    use super::nat_add::{nat_add_assoc, nat_add_comm};

    // Strategy:
    // (b + c) + (x + y) = b + (c + (x + y))   [assoc]
    //                   = b + ((c + x) + y)   [assoc inner.sym]
    //                   = b + ((x + c) + y)   [comm inner]
    //                   = b + (x + (c + y))   [assoc inner]
    //                   = (b + x) + (c + y)   [assoc.sym]

    // Step 1: (b + c) + (x + y) ≡ b + (c + (x + y))
    //   assoc: ⋀m_a p_a n_a. (n_a + m_a) + p_a = n_a + (m_a + p_a).
    //   Want: (b + c) + (x + y) = b + (c + (x + y))
    //   So n_a := b, m_a := c, p_a := (x+y).
    let xy = Term::app(Term::app(defs::nat_add(), x.clone()), y.clone());
    let assoc1 = instantiate_universal(
        nat_add_assoc()?,
        vec![c.clone(), xy.clone(), b.clone()],
    )?;
    let assoc1_pure = pure_eq_of_hol_eq(assoc1)?;
    // assoc1_pure: (b + c) + (x + y) ≡ b + (c + (x + y)).

    // Step 2: c + (x + y) ≡ (c + x) + y    [assoc.sym: with our notation
    //   assoc gives (n+m)+p = n+(m+p), sym gives n+(m+p) = (n+m)+p,
    //   so for c + (x + y), set n_a := c, m_a := x, p_a := y.
    let assoc2 = instantiate_universal(
        nat_add_assoc()?,
        vec![x.clone(), y.clone(), c.clone()],
    )?;
    let assoc2_pure = pure_eq_of_hol_eq(assoc2)?;
    // assoc2_pure: (c + x) + y ≡ c + (x + y).
    let assoc2_sym = assoc2_pure.sym()?;
    // assoc2_sym: c + (x + y) ≡ (c + x) + y.

    // Lift assoc2_sym through (b + _).
    let nat_add_b = Term::app(defs::nat_add(), b.clone());
    let head_refl = Thm::refl(nat_add_b.clone())?;
    let step2 = head_refl.cong_app(assoc2_sym)?;
    // step2: b + (c + (x + y)) ≡ b + ((c + x) + y).
    let chain1 = assoc1_pure.trans(step2)?;

    // Step 3: c + x ≡ x + c   [comm at (c, x): set m_c := c, n_c := x gives x + c = c + x; sym]
    let comm_cx = instantiate_universal(nat_add_comm()?, vec![c.clone(), x.clone()])?;
    let comm_cx_pure = pure_eq_of_hol_eq(comm_cx)?;
    // comm_cx_pure: x + c ≡ c + x. Sym to get c + x ≡ x + c.
    let comm_cx_eq = comm_cx_pure.sym()?;
    // comm_cx_eq: c + x ≡ x + c.

    // Lift comm_cx_eq through ((_) + y).
    let nat_add_refl = Thm::refl(defs::nat_add())?;
    let inner_step = nat_add_refl.cong_app(comm_cx_eq)?;
    let y_refl = Thm::refl(y.clone())?;
    let comm_lifted = inner_step.cong_app(y_refl)?;
    // comm_lifted: (c + x) + y ≡ (x + c) + y.

    // Lift through (b + _).
    let head_refl2 = Thm::refl(nat_add_b.clone())?;
    let step3 = head_refl2.cong_app(comm_lifted)?;
    // step3: b + ((c + x) + y) ≡ b + ((x + c) + y).
    let chain2 = chain1.trans(step3)?;

    // Step 4: (x + c) + y ≡ x + (c + y)   [assoc at (x, y, c): n_a := x, m_a := c, p_a := y, gives (x+c)+y = x+(c+y)].
    let assoc4 = instantiate_universal(
        nat_add_assoc()?,
        vec![c.clone(), y.clone(), x.clone()],
    )?;
    let assoc4_pure = pure_eq_of_hol_eq(assoc4)?;
    // assoc4_pure: (x + c) + y ≡ x + (c + y).
    // Lift through (b + _).
    let head_refl3 = Thm::refl(nat_add_b)?;
    let step4 = head_refl3.cong_app(assoc4_pure)?;
    let chain3 = chain2.trans(step4)?;
    // chain3: (b + c) + (x + y) ≡ b + (x + (c + y)).

    // Step 5: b + (x + (c + y)) ≡ (b + x) + (c + y)   [assoc.sym at (b, x, c+y)]
    let cy = Term::app(Term::app(defs::nat_add(), c.clone()), y.clone());
    let assoc5 = instantiate_universal(
        nat_add_assoc()?,
        vec![x.clone(), cy, b.clone()],
    )?;
    let assoc5_pure = pure_eq_of_hol_eq(assoc5)?;
    // assoc5_pure: (b + x) + (c + y) ≡ b + (x + (c + y)). Sym.
    let assoc5_sym = assoc5_pure.sym()?;

    chain3.trans(assoc5_sym)
}

/// `⊢ ⋀b c a:nat. Trueprop (nat_mul (nat_mul a b) c = nat_mul a (nat_mul b c))`
/// — associativity of `*`. Proved by induction on `a` with `(b, c)`
/// held free, then post-quantified.
pub fn nat_mul_assoc() -> Result<Thm> {
    let b = Term::free("b", Type::nat());
    let c = Term::free("c", Type::nat());

    let a = Term::free("a", Type::nat());
    let ab = Term::app(Term::app(defs::nat_mul(), a.clone()), b.clone());
    let lhs = Term::app(Term::app(defs::nat_mul(), ab), c.clone());
    let bc = Term::app(Term::app(defs::nat_mul(), b.clone()), c.clone());
    let rhs = Term::app(Term::app(defs::nat_mul(), a), bc);
    let p_body = hol::hol_eq(lhs, rhs);
    let p_lambda = hol::pub_abs("a", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // Base a=0: (0*b)*c = 0*(b*c).
    //   lhs: (0*b)*c = 0*c = 0 (zero_left twice)
    //   rhs: 0*(b*c) = 0 (zero_left)
    let zero_b_c = Term::app(Term::app(defs::nat_mul(), hol::zero()), b.clone());
    let nat_mul_refl = Thm::refl(defs::nat_mul())?;
    let inner = nat_mul_zero_left(b.clone())?;
    let head = nat_mul_refl.cong_app(inner)?;
    let c_refl = Thm::refl(c.clone())?;
    let lhs_step1 = head.cong_app(c_refl)?;
    // lhs_step1: (0*b)*c ≡ 0*c.
    let lhs_step2 = nat_mul_zero_left(c.clone())?;
    let lhs_chain = lhs_step1.trans(lhs_step2)?;
    // lhs_chain: (0*b)*c ≡ 0.
    let _ = zero_b_c;

    let bc_term = Term::app(Term::app(defs::nat_mul(), b.clone()), c.clone());
    let rhs_eq = nat_mul_zero_left(bc_term)?;
    let base_pure = lhs_chain.trans(rhs_eq.sym()?)?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    let step = nat_mul_assoc_step(&p_lambda, &b, &c)?;

    let after_base = induction_at_p.imp_elim(base)?;
    let universal_a = after_base.imp_elim(step)?;

    universal_a
        .all_intro("c", Type::nat())?
        .all_intro("b", Type::nat())
}

fn nat_mul_assoc_step(p_lambda: &Term, b: &Term, c: &Term) -> Result<Thm> {
    let a = Term::free("a", Type::nat());
    let succ_a = Term::app(hol::succ_fn(), a.clone());

    let p_a = Term::app(p_lambda.clone(), a.clone());
    let trueprop_p_a = trueprop(p_a.clone());
    let ih_un_beta = Thm::assume(trueprop_p_a.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_a)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?;
    // ih_pure: (a*b)*c = a*(b*c).

    // Goal: ((S a)*b)*c ≡ (S a)*(b*c).
    //
    // lhs: ((S a)*b)*c
    //   ≡ (b + a*b)*c              [mul_succ_left at (a, b), cong]
    //   ≡ b*c + (a*b)*c            [distrib_right at (c, b, a*b)]
    //   wait — distrib_right is a * (b+c) = a*b + a*c. We need
    //   (x+y)*c form: that's distrib_LEFT. Use comm to swap.
    //
    // Actually use comm: (b + a*b)*c = c * (b + a*b) = c*b + c*(a*b) = b*c + (a*b)*c [comm].
    //   ≡ b*c + a*(b*c)            [IH cong]
    //
    // rhs: (S a)*(b*c) ≡ (b*c) + a*(b*c)  [mul_succ_left at (a, b*c)]
    //
    // Both equal (b*c) + a*(b*c). ✓

    let ab = Term::app(Term::app(defs::nat_mul(), a.clone()), b.clone());
    let bc = Term::app(Term::app(defs::nat_mul(), b.clone()), c.clone());
    let abc_mid = Term::app(Term::app(defs::nat_mul(), ab.clone()), c.clone());
    let _ = abc_mid;

    // lhs path
    let succ_left_ab = nat_mul_succ_left_at(a.clone(), b.clone())?;
    // succ_left_ab: (S a)*b ≡ b + a*b.
    let nat_mul_refl = Thm::refl(defs::nat_mul())?;
    let head = nat_mul_refl.cong_app(succ_left_ab)?;
    let c_refl = Thm::refl(c.clone())?;
    let lhs_step1 = head.cong_app(c_refl)?;
    // lhs_step1: ((S a)*b)*c ≡ (b + a*b)*c.

    // (b + a*b)*c ≡ b*c + (a*b)*c via distrib_right + comm.
    //   distrib_right: ⋀a' b' c'. a' * (b' + c') = a'*b' + a'*c'.
    //   We want (b + a*b)*c ≡ b*c + (a*b)*c. Use comm to swap:
    //     (b + a*b) * c = c * (b + a*b) [comm]
    //                   = c*b + c*(a*b) [distrib at (c, b, a*b)]
    //                   = b*c + (a*b)*c [comm twice]
    //
    // That's a lot. Let me use a separate distrib_LEFT lemma. We have
    // commutativity, so:
    //   nat_mul_distrib_left: (a + b) * c = a*c + b*c can be derived from
    //   comm + distrib_right but for now I'll inline it.

    let lhs_step2 = nat_mul_distrib_left_inline(b, &ab, c)?;
    // lhs_step2: (b + a*b) * c ≡ b*c + (a*b)*c.
    let lhs_chain_to_distrib = lhs_step1.trans(lhs_step2)?;
    // lhs_chain_to_distrib: ((S a)*b)*c ≡ b*c + (a*b)*c.

    let nat_add_refl = Thm::refl(defs::nat_add())?;
    let nat_add_bc = nat_add_refl.cong_app(Thm::refl(bc.clone())?)?;
    let ih_lifted = nat_add_bc.cong_app(ih_pure)?;
    // ih_lifted: b*c + (a*b)*c ≡ b*c + a*(b*c).
    let lhs_chain = lhs_chain_to_distrib.trans(ih_lifted)?;
    // lhs_chain: ((S a)*b)*c ≡ b*c + a*(b*c).

    // rhs: (S a)*(b*c) ≡ b*c + a*(b*c) [succ_left at (a, b*c)].
    let rhs_chain = nat_mul_succ_left_at(a.clone(), bc)?;

    let pure_eq = lhs_chain.trans(rhs_chain.sym()?)?;
    // pure_eq: ((S a)*b)*c ≡ (S a)*(b*c).

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_a = Term::app(p_lambda.clone(), succ_a);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_a)?;

    let imp = un_beta.imp_intro(&trueprop_p_a)?;
    imp.all_intro("a", Type::nat())
}

/// `⊢ (x + y) * c ≡ x*c + y*c` — right-distributivity, derived
/// inline from comm + distrib_right.
fn nat_mul_distrib_left_inline(x: &Term, y: &Term, c: &Term) -> Result<Thm> {
    // nat_mul_comm statement: ⋀m n. n * m = m * n  (outer m, inner n).
    // Instantiate at (m, n) := (c, xy) → gives Trueprop (xy * c = c * xy);
    // after pure_eq: xy * c ≡ c * xy.

    let xy = Term::app(Term::app(defs::nat_add(), x.clone()), y.clone());
    let comm_xyc = instantiate_universal(nat_mul_comm()?, vec![c.clone(), xy.clone()])?;
    let comm_xyc_pure = pure_eq_of_hol_eq(comm_xyc)?;
    // comm_xyc_pure: (x+y) * c ≡ c * (x+y).

    // distrib_right at (c, x, y): c * (x+y) = c*x + c*y. distrib_right's
    // outer ⋀ is over b, then c, then a (see its proof).
    let distrib = instantiate_universal(
        nat_mul_distrib_right()?,
        vec![x.clone(), y.clone(), c.clone()],
    )?;
    let distrib_pure = pure_eq_of_hol_eq(distrib)?;
    let chain1 = comm_xyc_pure.trans(distrib_pure)?;

    // comm at (m, n) := (x, c) → Trueprop (c * x = x * c); after pure_eq:
    //   c*x ≡ x*c.
    let comm_cx = instantiate_universal(nat_mul_comm()?, vec![x.clone(), c.clone()])?;
    let comm_cx_pure = pure_eq_of_hol_eq(comm_cx)?;
    let comm_cy = instantiate_universal(nat_mul_comm()?, vec![y.clone(), c.clone()])?;
    let comm_cy_pure = pure_eq_of_hol_eq(comm_cy)?;

    let nat_add_refl = Thm::refl(defs::nat_add())?;
    let inner_step = nat_add_refl.cong_app(comm_cx_pure)?;
    let step = inner_step.cong_app(comm_cy_pure)?;

    chain1.trans(step)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermKind;

    #[test]
    fn zero_left_builds() {
        let m = Term::free("m", Type::nat());
        let thm = nat_mul_zero_left(m).expect("0 * m ≡ 0");
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &hol::zero()),
            other => panic!("expected Eq with 0 on rhs, got {other:?}"),
        }
    }

    #[test]
    fn succ_left_builds() {
        let n = Term::free("n", Type::nat());
        let m = Term::free("m", Type::nat());
        let _ = nat_mul_succ_left_at(n, m).expect("(S n) * m ≡ m + (n * m)");
    }

    #[test]
    fn zero_right_builds() {
        let _ = nat_mul_zero_right().expect("⋀n. n * 0 = 0");
    }

    #[test]
    fn one_left_builds() {
        let m = Term::free("m", Type::nat());
        let thm = nat_mul_one_left(m.clone()).expect("1 * m ≡ m");
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &m),
            other => panic!("expected Eq with m on rhs, got {other:?}"),
        }
    }

    #[test]
    fn one_right_builds() {
        let _ = nat_mul_one_right().expect("⋀n. n * 1 = n");
    }

    #[test]
    fn succ_right_builds() {
        let _ = nat_mul_succ_right().expect("⋀n m. n * (S m) = n + n * m");
    }

    #[test]
    fn comm_builds() {
        let _ = nat_mul_comm().expect("⋀n m. n * m = m * n");
    }

    #[test]
    fn distrib_right_builds() {
        let _ = nat_mul_distrib_right().expect("⋀a b c. a * (b + c) = a*b + a*c");
    }

    #[test]
    fn assoc_builds() {
        let _ = nat_mul_assoc().expect("⋀b c a. (a*b)*c = a*(b*c)");
    }
}
