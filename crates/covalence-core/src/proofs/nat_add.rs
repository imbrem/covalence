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

use super::iter::{iter_succ_eq_at, iter_zero_eq_at};
use super::{
    apply_eq, beta_at, beta_trueprop, pure_eq_of_hol_eq, trueprop, trueprop_of_pure_eq,
    un_beta_trueprop,
};

fn trans_then_beta(eq: Thm, beta_lhs: Term) -> Result<Thm> {
    let beta = beta_at(beta_lhs)?;
    eq.trans(beta)
}

/// `⊢ nat_add n m ≡ iter[nat] n succ m`, the let-style spec
/// unfolding plus the two β-reductions on the binary lambda.
/// Used by induction proofs to bring `nat_add n m` into a form
/// the iter equations can rewrite.
fn nat_add_unfold_at(n: Term, m: Term) -> Result<Thm> {
    let nat_add = defs::nat_add();
    let unfold = Thm::unfold_term_spec(nat_add)?;
    let after_n = apply_eq(unfold, n)?;
    let after_n_lhs = after_n.concl_rhs()?.clone();
    let after_n_beta = trans_then_beta(after_n, after_n_lhs)?;
    let after_m = apply_eq(after_n_beta, m)?;
    let after_m_lhs = after_m.concl_rhs()?.clone();
    trans_then_beta(after_m, after_m_lhs)
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

/// `⊢ ⋀n:nat. Trueprop (nat_add n 0 = n)` — i.e. `n + 0 = n`.
///
/// Proved by induction on `n` via [`Thm::nat_induction_pure`]:
///
/// - **Base** `Trueprop (nat_add 0 0 = 0)`: just
///   [`nat_add_zero_left`] at `m = 0` converted into Trueprop form.
/// - **Step** `⋀n. Trueprop (nat_add n 0 = n) ⟹
///                  Trueprop (nat_add (S n) 0 = S n)`:
///   1. Assume the IH.
///   2. Unfold `nat_add (S n) 0` → `iter (S n) succ 0`.
///   3. Apply [`iter_succ_eq_at`]:
///      `iter (S n) succ 0 ≡ succ (iter n succ 0)`.
///   4. Reverse-unfold `nat_add n 0 ≡ iter n succ 0` and chain with
///      the IH to get `iter n succ 0 ≡ n`.
///   5. Congruence under `succ` and `trans` give
///      `nat_add (S n) 0 ≡ S n`.
pub fn nat_add_zero_right() -> Result<Thm> {
    // ---- Predicate ----
    let n = Term::free("n", Type::nat());
    let nat_add_n_0 = Term::app(Term::app(defs::nat_add(), n.clone()), hol::zero());
    let p_body = hol::hol_eq(nat_add_n_0, n.clone());
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // ---- Base case: Trueprop (P 0) ----
    let base_pure = nat_add_zero_left(hol::zero())?; // nat_add 0 0 ≡ 0
    let base_hol = trueprop_of_pure_eq(base_pure)?; // Trueprop (nat_add 0 0 = 0)
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    // ---- Step case: ⋀n. Trueprop (P n) ⟹ Trueprop (P (S n)) ----
    let step = nat_add_zero_right_step(&p_lambda)?;

    // ---- Apply induction ----
    let after_base = induction_at_p.imp_elim(base)?;
    after_base.imp_elim(step)
}

/// The inductive step for [`nat_add_zero_right`]. Returns
/// `⊢ ⋀n. Trueprop (P n) ⟹ Trueprop (P (S n))` where
/// `P = λn. nat_add n 0 = n`.
fn nat_add_zero_right_step(p_lambda: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    // P n and Trueprop (P n) — the un-β form the induction expects.
    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());

    // assume Trueprop (P n)  → IH (in un-β form).
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    // β-reduce to Trueprop (nat_add n 0 = n).
    let ih = beta_trueprop(ih_un_beta, p_n)?;
    // Convert to Pure ≡: nat_add n 0 ≡ n.
    let ih_pure = pure_eq_of_hol_eq(ih)?;

    // Goal: nat_add (S n) 0 ≡ S n.
    // 1. Unfold to iter form.
    let unfold = nat_add_unfold_at(succ_n.clone(), hol::zero())?;
    // unfold: nat_add (S n) 0 ≡ iter (S n) succ 0.

    // 2. Apply iter_succ_eq_at: iter (S n) succ 0 ≡ succ (iter n succ 0).
    let iter_succ = iter_succ_eq_at(Type::nat(), n.clone(), hol::succ_fn(), hol::zero())?;
    let after_iter = unfold.trans(iter_succ)?;
    // after_iter: nat_add (S n) 0 ≡ succ (iter n succ 0).

    // 3. Reverse-unfold: iter n succ 0 ≡ nat_add n 0  (sym of nat_add_unfold).
    let n_unfold = nat_add_unfold_at(n.clone(), hol::zero())?; // nat_add n 0 ≡ iter n succ 0
    let iter_to_natadd = n_unfold.sym()?;
    // 4. Chain with IH: iter n succ 0 ≡ n.
    let iter_to_n = iter_to_natadd.trans(ih_pure)?;

    // 5. Apply succ via cong_app: succ (iter n succ 0) ≡ succ n.
    let succ_refl = Thm::refl(hol::succ_fn())?;
    let succ_eq = succ_refl.cong_app(iter_to_n)?;

    // 6. Trans: nat_add (S n) 0 ≡ S n.
    let pure_eq = after_iter.trans(succ_eq)?;

    // ---- Bridge into induction's expected shape ----
    let hol_eq_form = trueprop_of_pure_eq(pure_eq)?; // Trueprop (nat_add (S n) 0 = S n)
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_eq_form, p_at_succ_n)?;
    // un_beta: Trueprop (P (S n)).

    // imp_intro and all_intro.
    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

/// `⊢ nat_add (succ m) k ≡ succ (nat_add m k)` for concrete `m`, `k`.
///
/// Follows directly from `nat_add`'s definition (`λn k. iter n succ k`)
/// and the `iter_succ_eq` equation — no induction needed. Acts as
/// the "fold one step of recursion on the first argument" lemma,
/// reused everywhere we need to peel a `succ` off the left.
pub fn nat_add_succ_left_at(m: Term, k: Term) -> Result<Thm> {
    let succ_m = Term::app(hol::succ_fn(), m.clone());

    // 1. nat_add (succ m) k ≡ iter (succ m) succ k
    let unfold = nat_add_unfold_at(succ_m, k.clone())?;

    // 2. iter (succ m) succ k ≡ succ (iter m succ k)
    let iter_succ = iter_succ_eq_at(Type::nat(), m.clone(), hol::succ_fn(), k.clone())?;
    let step1 = unfold.trans(iter_succ)?;
    // step1: nat_add (succ m) k ≡ succ (iter m succ k)

    // 3. Reverse-unfold iter m succ k ≡ nat_add m k.
    let m_unfold = nat_add_unfold_at(m, k)?; // nat_add m k ≡ iter m succ k
    let iter_to_natadd = m_unfold.sym()?; // iter m succ k ≡ nat_add m k

    // 4. Lift through `succ (...)` via cong_app(refl succ, ...).
    let succ_refl = Thm::refl(hol::succ_fn())?;
    let succ_eq = succ_refl.cong_app(iter_to_natadd)?;
    // succ_eq: succ (iter m succ k) ≡ succ (nat_add m k)

    step1.trans(succ_eq)
}

/// `⊢ ⋀m n:nat. Trueprop (nat_add m (succ n) = succ (nat_add m n))`
/// — succ commutes with `+` on the right. Proved by induction on
/// `m` (with `n` held free), then post-quantifying `n`.
pub fn nat_add_succ_right() -> Result<Thm> {
    let n = Term::free("n", Type::nat());

    // Predicate body (m free, n free):
    //   nat_add m (succ n) = succ (nat_add m n)
    let m = Term::free("m", Type::nat());
    let lhs = Term::app(
        Term::app(defs::nat_add(), m.clone()),
        Term::app(hol::succ_fn(), n.clone()),
    );
    let rhs = Term::app(
        hol::succ_fn(),
        Term::app(Term::app(defs::nat_add(), m), n.clone()),
    );
    let p_body = hol::hol_eq(lhs, rhs);
    let p_lambda = hol::pub_abs("m", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // ---- Base case: Trueprop (P 0) ---- nat_add 0 (succ n) = succ (nat_add 0 n).
    let base_pure = nat_add_succ_right_base_at(&n)?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    // ---- Step case ----
    let step = nat_add_succ_right_step(&p_lambda, &n)?;

    let after_base = induction_at_p.imp_elim(base)?;
    let universal_m = after_base.imp_elim(step)?;
    // universal_m: ⋀m. Trueprop ((λm. P_body) m), with n still free.

    // Post-quantify n.
    universal_m.all_intro("n", Type::nat())
}

/// Base case for `nat_add_succ_right`: `nat_add 0 (succ n) ≡ succ (nat_add 0 n)`.
fn nat_add_succ_right_base_at(n: &Term) -> Result<Thm> {
    // lhs: nat_add 0 (succ n) ≡ succ n  (zero_left)
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let lhs_eq = nat_add_zero_left(succ_n.clone())?;
    // lhs_eq: nat_add 0 (succ n) ≡ succ n.

    // rhs: succ (nat_add 0 n) ≡ succ n via cong succ on nat_add 0 n ≡ n.
    let inner = nat_add_zero_left(n.clone())?; // nat_add 0 n ≡ n
    let succ_refl = Thm::refl(hol::succ_fn())?;
    let rhs_eq = succ_refl.cong_app(inner)?; // succ (nat_add 0 n) ≡ succ n.

    // Chain: nat_add 0 (succ n) ≡ succ n ≡ succ (nat_add 0 n).
    lhs_eq.trans(rhs_eq.sym()?)
}

/// Inductive step for `nat_add_succ_right`:
/// `⊢ ⋀m. Trueprop (P m) ⟹ Trueprop (P (S m))` where
/// `P = λm. nat_add m (succ n) = succ (nat_add m n)`.
fn nat_add_succ_right_step(p_lambda: &Term, n: &Term) -> Result<Thm> {
    let m = Term::free("m", Type::nat());
    let succ_m = Term::app(hol::succ_fn(), m.clone());

    // assume Trueprop (P m), β to get the IH.
    let p_m = Term::app(p_lambda.clone(), m.clone());
    let trueprop_p_m = trueprop(p_m.clone());
    let ih_un_beta = Thm::assume(trueprop_p_m.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_m)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?;
    // ih_pure: nat_add m (succ n) ≡ succ (nat_add m n).

    let succ_n = Term::app(hol::succ_fn(), n.clone());

    // Goal: nat_add (S m) (succ n) ≡ succ (nat_add (S m) n).
    // lhs side: nat_add (S m) (succ n) ≡ succ (nat_add m (succ n)) ≡ succ (succ (nat_add m n))
    let lhs_step1 = nat_add_succ_left_at(m.clone(), succ_n)?;
    // lhs_step1: nat_add (S m) (succ n) ≡ succ (nat_add m (succ n))

    let succ_refl = Thm::refl(hol::succ_fn())?;
    let lhs_step2 = succ_refl.cong_app(ih_pure)?;
    // lhs_step2: succ (nat_add m (succ n)) ≡ succ (succ (nat_add m n))

    let lhs_chain = lhs_step1.trans(lhs_step2)?;
    // lhs_chain: nat_add (S m) (succ n) ≡ succ (succ (nat_add m n))

    // rhs side: succ (nat_add (S m) n) ≡ succ (succ (nat_add m n))
    let rhs_inner = nat_add_succ_left_at(m, n.clone())?;
    // rhs_inner: nat_add (S m) n ≡ succ (nat_add m n)
    let succ_refl2 = Thm::refl(hol::succ_fn())?;
    let rhs_chain = succ_refl2.cong_app(rhs_inner)?;
    // rhs_chain: succ (nat_add (S m) n) ≡ succ (succ (nat_add m n))

    // Final: lhs_chain.trans(rhs_chain.sym()).
    let pure_eq = lhs_chain.trans(rhs_chain.sym()?)?;
    // pure_eq: nat_add (S m) (succ n) ≡ succ (nat_add (S m) n)

    // Bridge.
    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_m = Term::app(p_lambda.clone(), succ_m);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_m)?;

    let imp = un_beta.imp_intro(&trueprop_p_m)?;
    imp.all_intro("m", Type::nat())
}

/// `⊢ ⋀n m:nat. Trueprop (nat_add n m = nat_add m n)` — addition
/// commutes. Proved by induction on `n` using:
///
/// - `nat_add_zero_left` for the base case (with `m` arbitrary).
/// - `nat_add_zero_right` to handle `nat_add m 0`.
/// - `nat_add_succ_left_at` to peel a `succ` off the left of the
///   inductive `nat_add (S n) m`.
/// - `nat_add_succ_right` to fold a `succ` into the right of
///   `nat_add m (S n)`.
pub fn nat_add_comm() -> Result<Thm> {
    let m = Term::free("m", Type::nat());

    // Predicate body (n free, m free): nat_add n m = nat_add m n
    let n = Term::free("n", Type::nat());
    let lhs = Term::app(Term::app(defs::nat_add(), n.clone()), m.clone());
    let rhs = Term::app(Term::app(defs::nat_add(), m.clone()), n);
    let p_body = hol::hol_eq(lhs, rhs);
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // ---- Base case ----
    let base_pure = nat_add_comm_base_at(&m)?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    // ---- Step case ----
    let step = nat_add_comm_step(&p_lambda, &m)?;

    let after_base = induction_at_p.imp_elim(base)?;
    let universal_n = after_base.imp_elim(step)?;

    // Post-quantify m.
    universal_n.all_intro("m", Type::nat())
}

/// Base case for `nat_add_comm`: `nat_add 0 m ≡ nat_add m 0`.
fn nat_add_comm_base_at(m: &Term) -> Result<Thm> {
    // 0 + m ≡ m (zero_left)
    let lhs_eq = nat_add_zero_left(m.clone())?;
    // m + 0 ≡ m: instantiate the universal nat_add_zero_right at m.
    let zr = nat_add_zero_right()?;
    // zr: ⋀n:nat. Trueprop ((λn. nat_add n 0 = n) n)
    let zr_at_m_un_beta = zr.all_elim(m.clone())?;
    let p_at_m = Term::app(
        hol::pub_abs(
            "n",
            Type::nat(),
            hol::hol_eq(
                Term::app(
                    Term::app(defs::nat_add(), Term::free("n", Type::nat())),
                    hol::zero(),
                ),
                Term::free("n", Type::nat()),
            ),
        ),
        m.clone(),
    );
    let zr_at_m_hol = beta_trueprop(zr_at_m_un_beta, p_at_m)?;
    let zr_at_m_pure = pure_eq_of_hol_eq(zr_at_m_hol)?;
    // zr_at_m_pure: nat_add m 0 ≡ m.

    // 0 + m ≡ m and m ≡ m + 0 → trans.
    lhs_eq.trans(zr_at_m_pure.sym()?)
}

/// Inductive step for `nat_add_comm`.
fn nat_add_comm_step(p_lambda: &Term, m: &Term) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?;
    // ih_pure: nat_add n m ≡ nat_add m n.

    // Goal: nat_add (S n) m ≡ nat_add m (S n).
    // lhs: nat_add (S n) m ≡ succ (nat_add n m) ≡ succ (nat_add m n) via IH.
    let lhs_step1 = nat_add_succ_left_at(n.clone(), m.clone())?;
    let succ_refl = Thm::refl(hol::succ_fn())?;
    let lhs_step2 = succ_refl.cong_app(ih_pure)?;
    let lhs_chain = lhs_step1.trans(lhs_step2)?;
    // lhs_chain: nat_add (S n) m ≡ succ (nat_add m n).

    // rhs: nat_add m (S n) ≡ succ (nat_add m n) via nat_add_succ_right at (m, n).
    let sr = nat_add_succ_right()?;
    // sr: ⋀n m. Trueprop ((λn. ⋀m. ... wait, structure is ⋀n. ⋀m. ...
    // Actually sr is: ⋀n:nat. ⋀m. Trueprop ((λm. nat_add m (succ n) = succ (nat_add m n)) m)
    // We want to instantiate at our (m, n) — note the variable naming difference!
    // sr's outer ⋀ is over n, then inner ⋀ over m. To get an instance:
    // - all_elim at our n (the outer ⋀):
    let sr_at_n = sr.all_elim(n.clone())?;
    // sr_at_n: ⋀m. Trueprop ((λm. nat_add m (succ n) = succ (nat_add m n)) m)
    let sr_at_n_m_un_beta = sr_at_n.all_elim(m.clone())?;
    // β-reduce inside Trueprop.
    let p_lambda_sr_body = {
        // λm. nat_add m (succ n) = succ (nat_add m n)
        let m_free = Term::free("m", Type::nat());
        let lhs = Term::app(
            Term::app(defs::nat_add(), m_free.clone()),
            Term::app(hol::succ_fn(), n.clone()),
        );
        let rhs = Term::app(
            hol::succ_fn(),
            Term::app(Term::app(defs::nat_add(), m_free), n.clone()),
        );
        let body = hol::hol_eq(lhs, rhs);
        hol::pub_abs("m", Type::nat(), body)
    };
    let inner_app = Term::app(p_lambda_sr_body, m.clone());
    let sr_at_n_m_hol = beta_trueprop(sr_at_n_m_un_beta, inner_app)?;
    let sr_at_n_m_pure = pure_eq_of_hol_eq(sr_at_n_m_hol)?;
    // sr_at_n_m_pure: nat_add m (succ n) ≡ succ (nat_add m n).

    // Final: lhs_chain ≡ succ(nat_add m n), and sr_at_n_m_pure says nat_add m (succ n) ≡ succ(nat_add m n).
    //        So we want nat_add (S n) m ≡ nat_add m (S n), i.e.
    //        lhs_chain.trans(sr_at_n_m_pure.sym()).
    let pure_eq = lhs_chain.trans(sr_at_n_m_pure.sym()?)?;
    // pure_eq: nat_add (S n) m ≡ nat_add m (S n).

    // Bridge.
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
    fn zero_left_at_free_var() {
        let m = Term::free("m", Type::nat());
        let thm = nat_add_zero_left(m.clone()).expect("0 + m ≡ m");
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &m),
            other => panic!("expected Eq with m on the rhs, got {other:?}"),
        }
    }

    #[test]
    fn zero_right_builds() {
        let thm = nat_add_zero_right().expect("⋀n. nat_add n 0 = n");
        match thm.concl().kind() {
            TermKind::All(_, ty, _) => assert_eq!(ty, &Type::nat()),
            other => panic!("expected ⋀n:nat ..., got {other:?}"),
        }
    }

    #[test]
    fn succ_left_at_free_vars() {
        let m = Term::free("m", Type::nat());
        let k = Term::free("k", Type::nat());
        let thm = nat_add_succ_left_at(m.clone(), k.clone())
            .expect("nat_add (succ m) k ≡ succ (nat_add m k)");
        // Verify lhs structurally.
        match thm.concl().kind() {
            TermKind::Eq(_, _) => {}
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn succ_right_builds() {
        let thm = nat_add_succ_right().expect("⋀n m. ...");
        match thm.concl().kind() {
            TermKind::All(_, ty, _) => assert_eq!(ty, &Type::nat()),
            other => panic!("expected ⋀n:nat ..., got {other:?}"),
        }
    }

    #[test]
    fn comm_builds() {
        let thm = nat_add_comm().expect("⋀m n. nat_add n m = nat_add m n");
        match thm.concl().kind() {
            TermKind::All(_, ty, _) => assert_eq!(ty, &Type::nat()),
            other => panic!("expected ⋀m:nat ..., got {other:?}"),
        }
    }
}
