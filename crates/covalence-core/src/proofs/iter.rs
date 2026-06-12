//! Equations for the `iter` recursor.
//!
//! `iter` is the let-style polymorphic term-spec from
//! [`crate::defs::iter`]:
//!
//! ```text
//! iter ≔ λn:nat. λf:α→α. λa:α. natRec a (λ_:nat. f) n
//! ```
//!
//! The two "primary" equations follow by unfolding the definition,
//! β-reducing, and then applying the natRec equations:
//!
//! - [`iter_zero_eq_at`] — `iter[α] 0 f a ≡ a`
//! - [`iter_succ_eq_at`] — `iter[α] (S n) f a ≡ f (iter[α] n f a)`
//!
//! Each is parametric in `α`; pass `Type::nat()` (or whatever) for
//! concrete instances.

use crate::defs;
use crate::error::Result;
use crate::hol;
use crate::term::{Term, Type};
use crate::thm::Thm;

use super::{
    apply_eq, beta_at, beta_trueprop, instantiate_universal, nat_rec_succ_at, nat_rec_zero_at,
    pure_eq_of_hol_eq, trueprop, trueprop_of_pure_eq, un_beta_trueprop,
};

/// Internal helper: walk `Thm`'s right-hand side via `beta_at` and
/// chain into the left equation.
fn trans_then_beta(eq: Thm, beta_lhs: Term) -> Result<Thm> {
    let beta = beta_at(beta_lhs)?;
    eq.trans(beta)
}

/// `⊢ iter[α] 0 f a ≡ a`, specialised at concrete `α`, `f`, `a`.
///
/// The proof unfolds `iter`'s spec to its body, β-reduces the three
/// applications, then closes with [`super::nat_rec_zero_at`]:
///
/// ```text
/// iter[α] 0 f a
///   ≡ (λn f a. natRec a (λ_. f) n) 0 f a       -- unfold
///   ≡ natRec[α] a (λ_:nat. f) 0                -- 3× beta
///   ≡ a                                        -- nat_rec_zero
/// ```
pub fn iter_zero_eq_at(alpha: Type, f: Term, a: Term) -> Result<Thm> {
    // Validate inputs at the type-level so failures land here, not
    // deep in the rule chain.
    let f_ty = Type::fun(alpha.clone(), alpha.clone());
    assert_eq!(f.type_of()?, f_ty, "iter_zero_eq_at: f : α → α expected");
    assert_eq!(a.type_of()?, alpha, "iter_zero_eq_at: a : α expected");

    let zero = hol::zero();
    let iter_alpha = defs::iter(alpha.clone());

    // 1. iter[α] ≡ body.
    let unfold = Thm::unfold_term_spec(iter_alpha.clone())?;

    // 2. iter[α] 0 ≡ body 0  (cong_app on refl 0).
    let after_0 = apply_eq(unfold, zero.clone())?;

    // 3. body 0 β-reduces.  body 0 = (λn f a. ...) 0; β gives the
    //    inner λf a. natRec a (λ_. f) 0[0/n], but with n unused.
    let body_at_0 = after_0.concl_rhs()?.clone();
    let after_0_beta = trans_then_beta(after_0, body_at_0)?;

    // 4. ... f
    let after_f = apply_eq(after_0_beta, f.clone())?;
    let after_f_lhs = after_f.concl_rhs()?.clone();
    let after_f_beta = trans_then_beta(after_f, after_f_lhs)?;

    // 5. ... a
    let after_a = apply_eq(after_f_beta, a.clone())?;
    let after_a_lhs = after_a.concl_rhs()?.clone();
    let after_a_beta = trans_then_beta(after_a, after_a_lhs)?;
    // after_a_beta concludes: iter[α] 0 f a ≡ natRec[α] a (λ_:nat. f) 0

    // 6. Build λ_:nat. f and apply nat_rec_zero_at.
    let step_const_f = crate::hol::pub_abs("_", Type::nat(), f.clone());
    let nat_rec_eq = nat_rec_zero_at(alpha, a, step_const_f)?;

    after_a_beta.trans(nat_rec_eq)
}

/// `⊢ iter[α] (succ n) f a ≡ f (iter[α] n f a)`, at concrete
/// `α`, `n`, `f`, `a`.
///
/// Same overall recipe as [`iter_zero_eq_at`] but closing with
/// [`super::nat_rec_succ_at`]:
///
/// ```text
/// iter[α] (succ n) f a
///   ≡ natRec[α] a (λ_:nat. f) (succ n)         -- unfold + 3× beta
///   ≡ (λ_:nat. f) n (natRec[α] a (λ_:nat. f) n) -- nat_rec_succ
///   ≡ f (natRec[α] a (λ_:nat. f) n)            -- beta
///   ≡ f (iter[α] n f a)                        -- fold iter back
/// ```
pub fn iter_succ_eq_at(alpha: Type, n: Term, f: Term, a: Term) -> Result<Thm> {
    let f_ty = Type::fun(alpha.clone(), alpha.clone());
    assert_eq!(f.type_of()?, f_ty, "iter_succ_eq_at: f : α → α expected");
    assert_eq!(a.type_of()?, alpha, "iter_succ_eq_at: a : α expected");
    assert_eq!(n.type_of()?, Type::nat(), "iter_succ_eq_at: n : nat expected");

    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let iter_alpha = defs::iter(alpha.clone());

    // 1. iter[α] (succ n) f a ≡ natRec[α] a (λ_. f) (succ n) via
    //    unfold + 3× beta + cong_app, mirroring `iter_zero_eq_at`.
    let unfold = Thm::unfold_term_spec(iter_alpha.clone())?;
    let after_n = apply_eq(unfold, succ_n.clone())?;
    let after_n_lhs = after_n.concl_rhs()?.clone();
    let after_n_beta = trans_then_beta(after_n, after_n_lhs)?;
    let after_f = apply_eq(after_n_beta, f.clone())?;
    let after_f_lhs = after_f.concl_rhs()?.clone();
    let after_f_beta = trans_then_beta(after_f, after_f_lhs)?;
    let after_a = apply_eq(after_f_beta, a.clone())?;
    let after_a_lhs = after_a.concl_rhs()?.clone();
    let after_a_beta = trans_then_beta(after_a, after_a_lhs)?;
    // after_a_beta: iter[α] (succ n) f a ≡ natRec[α] a (λ_. f) (succ n)

    // 2. nat_rec_succ: natRec[α] a (λ_. f) (succ n) ≡ (λ_. f) n (natRec[α] a (λ_. f) n)
    let step_const_f = crate::hol::pub_abs("_", Type::nat(), f.clone());
    let nat_rec_eq = nat_rec_succ_at(alpha.clone(), a.clone(), step_const_f.clone(), n.clone())?;
    let after_recsucc = after_a_beta.trans(nat_rec_eq)?;

    // 3. β-reduce the `(λ_. f) n` application to `f`.
    //    after_recsucc.rhs = App(App(λ_. f, n), recCall)
    //    Build target = App(λ_. f, n) and β-reduce.
    let rhs = after_recsucc.concl_rhs()?.clone();
    let (outer_lhs, _rec_call) = match rhs.kind() {
        crate::term::TermKind::App(f_app, rec_call) => (f_app.clone(), rec_call.clone()),
        _ => panic!("iter_succ_eq_at: rhs not an application"),
    };
    // outer_lhs = App(λ_. f, n). β-reduce.
    let beta_outer = beta_at(outer_lhs.clone())?;
    // beta_outer: (λ_. f) n ≡ f
    // We need to push that into the larger Eq via cong_app with refl _rec_call.
    let rec_call = match rhs.kind() {
        crate::term::TermKind::App(_, rec_call) => rec_call.clone(),
        _ => unreachable!(),
    };
    let rec_refl = Thm::refl(rec_call)?;
    let beta_full = beta_outer.cong_app(rec_refl)?;
    // beta_full: ((λ_. f) n) rec_call ≡ f rec_call
    let after_beta = after_recsucc.trans(beta_full)?;
    // after_beta: iter[α] (succ n) f a ≡ f (natRec[α] a (λ_. f) n)

    // 4. Finally, fold natRec[α] a (λ_. f) n back into iter[α] n f a.
    //    By reversing the same unfold+β chain at n, we get:
    //      iter[α] n f a ≡ natRec[α] a (λ_. f) n
    //    Sym it and apply via cong_app to fold the rhs.
    let iter_n_eq = iter_n_eq_at_natrec(alpha, n, f, a)?;
    // iter_n_eq:  iter[α] n f a ≡ natRec[α] a (λ_. f) n
    let folded = iter_n_eq.sym()?;
    // folded:     natRec[α] a (λ_. f) n ≡ iter[α] n f a

    // Apply via cong on f's outer application.
    let f_refl = Thm::refl(crate::term::Term::free(
        "__placeholder__",
        Type::fun(crate::term::Type::nat(), crate::term::Type::nat()),
    ))?;
    let _ = f_refl; // silence; we use the explicit lift below.

    // Lift folded inside the `f _` context: build cong_app via
    // refl on the outer `f`.
    let f_unary = extract_outer_f(after_beta.concl_rhs()?)?;
    let f_unary_refl = Thm::refl(f_unary)?;
    let lifted = f_unary_refl.cong_app(folded)?;
    // lifted:     f (natRec[α] a (λ_. f) n) ≡ f (iter[α] n f a)

    after_beta.trans(lifted)
}

/// Sub-proof: `iter[α] n f a ≡ natRec[α] a (λ_:nat. f) n` for a
/// generic `n` (i.e. the unfold + 3× β chain run once at `n`).
fn iter_n_eq_at_natrec(
    alpha: Type,
    n: Term,
    f: Term,
    a: Term,
) -> Result<Thm> {
    let iter_alpha = defs::iter(alpha.clone());
    let unfold = Thm::unfold_term_spec(iter_alpha.clone())?;
    let after_n = apply_eq(unfold, n.clone())?;
    let after_n_lhs = after_n.concl_rhs()?.clone();
    let after_n_beta = trans_then_beta(after_n, after_n_lhs)?;
    let after_f = apply_eq(after_n_beta, f.clone())?;
    let after_f_lhs = after_f.concl_rhs()?.clone();
    let after_f_beta = trans_then_beta(after_f, after_f_lhs)?;
    let after_a = apply_eq(after_f_beta, a.clone())?;
    let after_a_lhs = after_a.concl_rhs()?.clone();
    trans_then_beta(after_a, after_a_lhs)
}

fn extract_outer_f(rhs: &Term) -> Result<Term> {
    match rhs.kind() {
        crate::term::TermKind::App(head, _) => Ok((*head).clone()),
        _ => Err(crate::error::Error::NotASpec),
    }
}

/// `⊢ ⋀n:nat. ⋀f:'a→'a. ⋀a:'a. Trueprop (iter['a] (S n) f a = iter['a] n f (f a))`
/// — the "consume one iteration from the inside" corollary.
///
/// Polymorphic in `'a` (proved at `Type::tfree("a")`). Use
/// [`iter_succ_corollary_at`] to specialise at a concrete type +
/// witnesses.
///
/// Proof: induction on `n`, gluing two applications of
/// [`iter_succ_eq_at`] at the inductive step.
pub fn iter_succ_corollary() -> Result<Thm> {
    let alpha = Type::tfree("a");
    let alpha_to_alpha = Type::fun(alpha.clone(), alpha.clone());

    let f = Term::free("f", alpha_to_alpha.clone());
    let a = Term::free("a", alpha.clone());

    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let lhs = Term::app(
        Term::app(
            Term::app(defs::iter(alpha.clone()), succ_n.clone()),
            f.clone(),
        ),
        a.clone(),
    );
    let f_a = Term::app(f.clone(), a.clone());
    let rhs = Term::app(
        Term::app(Term::app(defs::iter(alpha.clone()), n.clone()), f.clone()),
        f_a,
    );
    let p_body = hol::hol_eq(lhs, rhs);
    let p_lambda = hol::pub_abs("n", Type::nat(), p_body);

    let induction_at_p = Thm::nat_induction_pure().all_elim(p_lambda.clone())?;

    // ---- Base case n=0: iter 1 f a ≡ iter 0 f (f a) ----
    //   lhs: iter (S 0) f a ≡ f (iter 0 f a) ≡ f a
    //   rhs: iter 0 f (f a) ≡ f a
    let lhs_eq = iter_succ_eq_at(alpha.clone(), hol::zero(), f.clone(), a.clone())?;
    let inner = iter_zero_eq_at(alpha.clone(), f.clone(), a.clone())?;
    let f_refl = Thm::refl(f.clone())?;
    let lifted_inner = f_refl.cong_app(inner)?;
    let lhs_chain = lhs_eq.trans(lifted_inner)?; // iter 1 f a ≡ f a.

    let f_a_term = Term::app(f.clone(), a.clone());
    let rhs_eq = iter_zero_eq_at(alpha.clone(), f.clone(), f_a_term)?;
    // rhs_eq: iter 0 f (f a) ≡ f a.

    let base_pure = lhs_chain.trans(rhs_eq.sym()?)?;
    let base_hol = trueprop_of_pure_eq(base_pure)?;
    let p_at_zero = Term::app(p_lambda.clone(), hol::zero());
    let base = un_beta_trueprop(base_hol, p_at_zero)?;

    // ---- Step ----
    let step = iter_succ_corollary_step(&p_lambda, &alpha, &f, &a)?;

    let after_base = induction_at_p.imp_elim(base)?;
    let universal_n = after_base.imp_elim(step)?;

    universal_n
        .all_intro("a", alpha.clone())?
        .all_intro("f", alpha_to_alpha)
}

fn iter_succ_corollary_step(
    p_lambda: &Term,
    alpha: &Type,
    f: &Term,
    a: &Term,
) -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());

    let p_n = Term::app(p_lambda.clone(), n.clone());
    let trueprop_p_n = trueprop(p_n.clone());
    let ih_un_beta = Thm::assume(trueprop_p_n.clone())?;
    let ih_hol = beta_trueprop(ih_un_beta, p_n)?;
    let ih_pure = pure_eq_of_hol_eq(ih_hol)?;
    // ih_pure: iter (S n) f a ≡ iter n f (f a).

    // Goal: iter (S (S n)) f a ≡ iter (S n) f (f a).
    //
    // lhs: iter (S (S n)) f a
    //   ≡ f (iter (S n) f a)            [iter_succ]
    //   ≡ f (iter n f (f a))            [IH cong]
    let lhs_eq = iter_succ_eq_at(alpha.clone(), succ_n.clone(), f.clone(), a.clone())?;
    let f_refl = Thm::refl(f.clone())?;
    let lhs_step2 = f_refl.cong_app(ih_pure)?;
    let lhs_chain = lhs_eq.trans(lhs_step2)?;

    // rhs: iter (S n) f (f a) ≡ f (iter n f (f a)) [iter_succ]
    let f_a = Term::app(f.clone(), a.clone());
    let rhs_eq = iter_succ_eq_at(alpha.clone(), n.clone(), f.clone(), f_a)?;

    let pure_eq = lhs_chain.trans(rhs_eq.sym()?)?;

    let hol_form = trueprop_of_pure_eq(pure_eq)?;
    let p_at_succ_n = Term::app(p_lambda.clone(), succ_n);
    let un_beta = un_beta_trueprop(hol_form, p_at_succ_n)?;

    let imp = un_beta.imp_intro(&trueprop_p_n)?;
    imp.all_intro("n", Type::nat())
}

/// `⊢ iter[α] (S n) f a ≡ iter[α] n f (f a)` specialised at
/// concrete `α`, `n`, `f`, `a`.
pub fn iter_succ_corollary_at(
    alpha: Type,
    n: Term,
    f: Term,
    a: Term,
) -> Result<Thm> {
    let universal = iter_succ_corollary()?;
    let at_alpha = universal.inst_tfree("a", alpha)?;
    let inst = instantiate_universal(at_alpha, vec![f, a, n])?;
    pure_eq_of_hol_eq(inst)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermKind;
    use covalence_types::Nat;

    fn nat_lit(n: u32) -> Term {
        Term::nat_lit(Nat::from_inner(n.into()))
    }

    #[test]
    fn iter_zero_at_nat() {
        let alpha = Type::nat();
        let f = Term::free("f", Type::fun(alpha.clone(), alpha.clone()));
        let a = Term::free("a", alpha.clone());

        let thm = iter_zero_eq_at(alpha, f, a.clone())
            .expect("iter_zero_eq_at builds");
        // Conclusion: iter[nat] 0 f a ≡ a.
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &a),
            other => panic!("expected Eq with a on rhs, got {other:?}"),
        }
    }

    #[test]
    fn iter_zero_at_nat_with_succ_as_f() {
        // Plug in the succ primitive — the same shape used by natAdd.
        let alpha = Type::nat();
        let succ = crate::hol::succ_fn();
        let m = Term::free("m", alpha.clone());

        let thm = iter_zero_eq_at(alpha, succ, m.clone())
            .expect("iter_zero_eq_at(succ) builds");
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &m),
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn iter_succ_corollary_builds() {
        let _ = iter_succ_corollary().expect("⋀f a n. iter (S n) f a = iter n f (f a)");
    }

    #[test]
    fn iter_succ_corollary_at_nat_with_succ() {
        let alpha = Type::nat();
        let n_val = nat_lit(2);
        let succ = crate::hol::succ_fn();
        let a = Term::free("a", alpha.clone());
        let _ = iter_succ_corollary_at(alpha, n_val, succ, a)
            .expect("iter_succ_corollary_at builds");
    }

    #[test]
    fn iter_succ_at_nat_with_succ_as_f() {
        let alpha = Type::nat();
        let n = nat_lit(3);
        let succ = crate::hol::succ_fn();
        let a = Term::free("a", alpha.clone());

        let thm = iter_succ_eq_at(alpha, n.clone(), succ.clone(), a.clone())
            .expect("iter_succ_eq_at builds");
        // Conclusion: iter[nat] (succ n) succ a ≡ succ (iter[nat] n succ a).
        match thm.concl().kind() {
            TermKind::Eq(_, _r) => { /* shape only — full check is brittle */ }
            other => panic!("expected Eq, got {other:?}"),
        }
    }
}
