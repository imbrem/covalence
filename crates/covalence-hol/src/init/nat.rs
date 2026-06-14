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
//! ## The single postulate, and everything derived from it
//!
//! - **Genuine** (hypothesis-free): [`succ_inj`] / [`zero_ne_succ`]
//!   (kernel freeness primitives generalised with `all_intro`).
//! - **[`rec_holds`]** — `natRec` satisfies its recursion equations.
//!   This is the **one** remaining `nat` postulate (`Thm::assume`,
//!   flagged in `SKELETONS.md`). The plan (option **B**) is to prove it
//!   via the recursion theorem (`∃r. P_rec r` + `spec_ax` + induction).
//! - **Derived from [`rec_holds`] alone**: the four recursion equations
//!   [`add_base`] / [`add_step`] / [`mul_base`] / [`mul_step`], by
//!   δ-unfolding `nat.add` / `nat.mul` / `iter` down to `natRec` and
//!   applying [`rec_holds`]. Each therefore carries exactly *one*
//!   hypothesis — [`rec_holds`]'s conclusion. **The moment `rec_holds`
//!   becomes a hypothesis-free proof, all four become genuine theorems
//!   automatically, with no change here.**

use covalence_core::{Result, Term, Thm, Type, defs, subst};
use covalence_types::Nat;

use crate::init::ext::{TermExt, ThmExt};

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

/// `nat → nat → nat`, the type of a `natRec` step over `nat`.
fn step_ty() -> Type {
    Type::fun(nat(), Type::fun(nat(), nat()))
}

/// `natRec[nat] a b c`.
fn rec3(a: Term, b: Term, c: Term) -> Term {
    Term::app(Term::app(Term::app(nat_rec(nat()), a), b), c)
}

/// The RHS of an equational theorem (panics if not `⊢ _ = _`).
fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::nat: expected an equation")
        .1
        .clone()
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
// The recursion equation — the single postulate (pending the recursion theorem)
// ============================================================================

/// `⊢ ∀z f. (natRec z f 0 = z) ∧ (∀n. natRec z f (S n) = f n (natRec z f n))`
/// at `α = nat` — `natRec` satisfies its recursion equations.
///
/// **Postulated** for now (the only `nat` postulate). Proving it via the
/// recursion theorem discharges everything below automatically — see the
/// [module docs](self).
pub fn rec_holds() -> Thm {
    let z = var("z");
    let f = Term::free("f", step_ty());
    let n = var("n");

    // natRec z f 0 = z
    let base = rec3(z.clone(), f.clone(), zero())
        .equals(z.clone())
        .expect("rec_holds: base eq");
    // ∀n. natRec z f (S n) = f n (natRec z f n)
    let step_lhs = rec3(z.clone(), f.clone(), succ(n.clone()));
    let step_rhs = Term::app(Term::app(f.clone(), n.clone()), rec3(z.clone(), f.clone(), n));
    let step = step_lhs
        .equals(step_rhs)
        .and_then(|e| e.forall("n", nat()))
        .expect("rec_holds: step");
    let body = base.and(step).expect("rec_holds: ∧");
    let all = body
        .forall("f", step_ty())
        .and_then(|t| t.forall("z", nat()))
        .expect("rec_holds: ∀z f");

    Thm::assume(all).expect("rec_holds: assume")
}

/// `⊢ natRec z f 0 = z` — the base equation at a concrete `z`, `f`.
fn rec_zero(z: Term, f: Term) -> Result<Thm> {
    rec_holds().all_elim(z)?.all_elim(f)?.and_elim_l()
}

/// `⊢ natRec z f (S n) = f n (natRec z f n)` — the step equation.
fn rec_succ(z: Term, f: Term, n: Term) -> Result<Thm> {
    rec_holds()
        .all_elim(z)?
        .all_elim(f)?
        .and_elim_r()?
        .all_elim(n)
}

/// `⊢ t = t'`, where `t'` is `t` with the let-style specs `nat.add` /
/// `nat.mul` / `iter` δ-unfolded and β-reduced to weak-normal form
/// (typically a `natRec` application). Reduction is weak, so `natRec`
/// step-functions and folded sub-applications under binders are
/// preserved — exactly what the recursion equations expect.
fn eval(t: Term) -> Result<Thm> {
    let mut acc = Thm::refl(t)?;
    loop {
        let cur = rhs(&acc);
        // δ-unfold the let-specs on the spine, then βι-reduce.
        let mut conv = Thm::refl(cur.clone())?;
        for spec in [defs::nat_add_spec(), defs::nat_mul_spec(), defs::iter_spec()] {
            let d = rhs(&conv).delta_all(spec.symbol())?;
            conv = conv.trans(d)?;
        }
        let red = rhs(&conv).reduce()?;
        conv = conv.trans(red)?;
        let next = rhs(&conv);
        acc = acc.trans(conv)?;
        if next == cur {
            return Ok(acc);
        }
    }
}

// ============================================================================
// Recursion equations for + / * — DERIVED from `rec_holds`
// ============================================================================

/// `⊢ ∀m. 0 + m = m`. Depends only on [`rec_holds`].
pub fn add_base() -> Thm {
    add_base_impl().expect("add_base derivation")
}
fn add_base_impl() -> Result<Thm> {
    let m = var("m");
    let f = Term::abs(nat(), nat_succ()); // λ_:nat. succ
    let conv = eval(add(zero(), m.clone()))?; // ⊢ 0 + m = natRec m (λ_.succ) 0
    let rz = rec_zero(m.clone(), f)?; //          ⊢ natRec m (λ_.succ) 0 = m
    conv.trans(rz)?.all_intro("m", nat())
}

/// `⊢ ∀n m. S n + m = S (n + m)`. Depends only on [`rec_holds`].
pub fn add_step() -> Thm {
    add_step_impl().expect("add_step derivation")
}
fn add_step_impl() -> Result<Thm> {
    let n = var("n");
    let m = var("m");
    let f = Term::abs(nat(), nat_succ()); // λ_:nat. succ

    // S n + m = natRec m (λ_.succ) (S n) = (λ_.succ) n (natRec m (λ_.succ) n)
    let conv1 = eval(add(succ(n.clone()), m.clone()))?;
    let rs = rec_succ(m.clone(), f, n.clone())?;
    let red = rhs(&rs).reduce()?; // = succ (natRec m (λ_.succ) n)
    // natRec m (λ_.succ) n = n + m  (fold), then push under `succ`.
    let fold = eval(add(n.clone(), m.clone()))?.sym()?;
    let cong = fold.cong_arg(nat_succ())?; // ⊢ succ(natRec…) = succ(n + m)

    let eq = conv1.trans(rs)?.trans(red)?.trans(cong)?; // ⊢ S n + m = S (n + m)
    eq.all_intro("m", nat())?.all_intro("n", nat())
}

/// `λ_:nat. λx:nat. m + x` — the `natRec` step function `nat.mul` uses.
fn mul_step_fn(m: Term) -> Term {
    let inner = Term::abs(nat(), subst::close(&add(m, var("x")), "x")); // λx. m + x
    Term::abs(nat(), inner) // λ_. (λx. m + x)
}

/// `⊢ ∀m. 0 * m = 0`. Depends only on [`rec_holds`].
pub fn mul_base() -> Thm {
    mul_base_impl().expect("mul_base derivation")
}
fn mul_base_impl() -> Result<Thm> {
    let m = var("m");
    let f = mul_step_fn(m.clone());
    let conv = eval(mul(zero(), m))?; // ⊢ 0 * m = natRec 0 f 0
    let rz = rec_zero(zero(), f)?; //      ⊢ natRec 0 f 0 = 0
    conv.trans(rz)?.all_intro("m", nat())
}

/// `⊢ ∀n m. S n * m = m + n * m`. Depends only on [`rec_holds`].
pub fn mul_step() -> Thm {
    mul_step_impl().expect("mul_step derivation")
}
fn mul_step_impl() -> Result<Thm> {
    let n = var("n");
    let m = var("m");
    let f = mul_step_fn(m.clone());

    // S n * m = natRec 0 f (S n) = f n (natRec 0 f n)
    let conv1 = eval(mul(succ(n.clone()), m.clone()))?;
    let rs = rec_succ(zero(), f, n.clone())?;
    let red = rhs(&rs).reduce()?; // = m + (natRec 0 f n)
    // natRec 0 f n = n * m  (fold), then push under `(m +)`.
    let fold = eval(mul(n.clone(), m.clone()))?.sym()?;
    let cong = fold.cong_arg(Term::app(nat_add(), m.clone()))?; // ⊢ m + natRec… = m + n*m

    let eq = conv1.trans(rs)?.trans(red)?.trans(cong)?; // ⊢ S n * m = m + n * m
    eq.all_intro("m", nat())?.all_intro("n", nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn freeness_theorems_are_genuine() {
        assert!(succ_inj().hyps().is_empty(), "succ_inj is proved");
        assert!(zero_ne_succ().hyps().is_empty(), "zero_ne_succ is proved");
    }

    /// Every derived recursion equation depends on **exactly** the one
    /// `rec_holds` postulate — nothing else. So discharging `rec_holds`
    /// discharges them all.
    #[test]
    fn arithmetic_facts_depend_only_on_rec_holds() {
        let postulate = rec_holds().concl().clone();
        for fact in [add_base(), add_step(), mul_base(), mul_step()] {
            assert!(fact.concl().type_of().unwrap().is_bool());
            assert_eq!(
                fact.hyps().iter().collect::<Vec<_>>(),
                vec![&postulate],
                "a derived nat fact must rest on rec_holds alone"
            );
        }
    }

    #[test]
    fn add_base_has_the_expected_statement() {
        // ∀m. 0 + m = m  ⟹(spec k)  0 + k = k.
        let inst = add_base().all_elim(var("k")).expect("specialize add_base");
        let expected = add(zero(), var("k")).equals(var("k")).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn add_step_has_the_expected_statement() {
        // ∀n m. S n + m = S (n + m), specialised at n,m := j,k.
        let inst = add_step()
            .all_elim(var("j"))
            .and_then(|t| t.all_elim(var("k")))
            .unwrap();
        let expected = add(succ(var("j")), var("k"))
            .equals(succ(add(var("j"), var("k"))))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn mul_base_and_step_have_expected_statements() {
        let mb = mul_base().all_elim(var("k")).unwrap();
        assert_eq!(
            mb.concl(),
            &mul(zero(), var("k")).equals(zero()).unwrap()
        );

        let ms = mul_step()
            .all_elim(var("j"))
            .and_then(|t| t.all_elim(var("k")))
            .unwrap();
        let expected = mul(succ(var("j")), var("k"))
            .equals(add(var("k"), mul(var("j"), var("k"))))
            .unwrap();
        assert_eq!(ms.concl(), &expected);
    }
}
