//! Untrusted proof helpers.
//!
//! This module assembles higher-level theorems from the kernel's
//! primitive rules. Nothing here can build a [`Thm`] directly — every
//! constructor goes through a `Thm::…` rule method. The module's
//! only purpose is **ergonomics**: turn idiomatic proof sketches
//! ("apply both sides to `x`", "β-reduce three times", "rewrite
//! by the iter-zero equation") into concise Rust calls.
//!
//! ## Layout
//!
//! - [`iter`] — equations for the `iter` recursor (`iter 0 f a = a`,
//!   etc.).
//! - [`nat_add`] — `0 + n = n`, `n + 0 = n`, commutativity.
//!
//! ## Helpers
//!
//! - [`apply_eq`] — congruence on application: given `⊢ f ≡ g` and
//!   a term `x`, return `⊢ f x ≡ g x`.
//! - [`beta_at`] — β-reduce a specific application term.
//! - [`pure_eq_of_hol_eq`] — convert `⊢ Trueprop (a = b)` to
//!   `⊢ a ≡ b` via the `eq_reflection` axiom.

use crate::defs;
use crate::error::Result;
use crate::term::{Term, Type};
use crate::thm::Thm;

pub mod iter;
pub mod nat_add;
pub mod nat_div;
pub mod nat_mod;
pub mod nat_mul;
pub mod nat_pow;
pub mod nat_sub;

// ---------------------------------------------------------------------------
// Generic helpers
// ---------------------------------------------------------------------------

/// `⊢ f ≡ g` ⇒ `⊢ f x ≡ g x`. A common idiom: apply both sides of
/// an equation to a fixed argument.
pub fn apply_eq(eq: Thm, arg: Term) -> Result<Thm> {
    let arg_refl = Thm::refl(arg)?;
    eq.cong_app(arg_refl)
}

/// The `Trueprop : bool → prop` constant term.
pub fn trueprop_op() -> Term {
    use crate::term::HolOp;
    Term::hol_op(HolOp::Trueprop, Type::fun(Type::bool(), Type::prop()))
}

/// Wrap a bool term in `Trueprop`.
pub fn trueprop(p: Term) -> Term {
    Term::app(trueprop_op(), p)
}

/// `⊢ Trueprop ((λx:τ. body) arg) ≡ Trueprop body[arg/x]`. Used to
/// bridge between the natural pre-β form (`P 0` where `P` is a
/// lambda, induction-shaped) and the post-β user-facing form.
pub fn beta_under_trueprop(lambda_app: Term) -> Result<Thm> {
    let beta = Thm::beta_conv(lambda_app)?;
    Thm::refl(trueprop_op())?.cong_app(beta)
}

/// Given `⊢ Trueprop body[arg/x]`, return `⊢ Trueprop ((λx. body) arg)`.
/// Inverse of [`beta_trueprop`].
pub fn un_beta_trueprop(reduced_thm: Thm, lambda_app: Term) -> Result<Thm> {
    let bridge = beta_under_trueprop(lambda_app)?;
    bridge.sym()?.eq_mp(reduced_thm)
}

/// Given `⊢ Trueprop ((λx. body) arg)`, return `⊢ Trueprop body[arg/x]`.
/// Inverse of [`un_beta_trueprop`].
pub fn beta_trueprop(un_reduced_thm: Thm, lambda_app: Term) -> Result<Thm> {
    let bridge = beta_under_trueprop(lambda_app)?;
    bridge.eq_mp(un_reduced_thm)
}

/// Extract the bool argument of a `Trueprop X` term.
pub fn extract_trueprop_arg(t: &Term) -> Result<Term> {
    use crate::term::HolOp;
    use crate::term::TermKind;
    match t.kind() {
        TermKind::App(head, arg)
            if matches!(head.kind(), TermKind::HolOp(HolOp::Trueprop, _)) =>
        {
            Ok((*arg).clone())
        }
        _ => Err(crate::error::Error::NotASpec),
    }
}

/// Instantiate a `⋀x1. ⋀x2. … ⋀xk. Trueprop X` theorem at the
/// supplied witnesses (outer-to-inner). When `X` after all the
/// `all_elim`s is `(λy. body) witness` (the shape induction proofs
/// produce), β-reduce inside `Trueprop`; when it's already in
/// natural form (kernel axioms like `nat_pred_succ` built without
/// a predicate-λ), leave it as-is.
pub fn instantiate_universal(thm: Thm, witnesses: Vec<Term>) -> Result<Thm> {
    use crate::term::TermKind;
    let mut current = thm;
    for w in witnesses {
        current = current.all_elim(w)?;
    }
    let inner = extract_trueprop_arg(current.concl())?;
    let needs_beta = matches!(
        inner.kind(),
        TermKind::App(head, _) if matches!(head.kind(), TermKind::Abs(..))
    );
    if needs_beta {
        beta_trueprop(current, inner)
    } else {
        Ok(current)
    }
}

/// Inverse of [`pure_eq_of_hol_eq`]: convert `⊢ a ≡ b` to
/// `⊢ Trueprop (a = b)` via the `eq_reflection` axiom (used
/// backwards).
pub fn trueprop_of_pure_eq(pure_thm: Thm) -> Result<Thm> {
    let (lhs, rhs) = pure_thm.concl_eq_parts()?;
    let ty = lhs.type_of()?;
    let lhs = lhs.clone();
    let rhs = rhs.clone();
    let bridge = Thm::eq_reflection()
        .inst_tfree("a", ty)?
        .all_elim(lhs)?
        .all_elim(rhs)?;
    bridge.sym()?.eq_mp(pure_thm)
}

/// β-reduce the term `app`, returning `⊢ app ≡ app'`. Wraps
/// [`Thm::beta_conv`] for symmetry with the other helpers.
pub fn beta_at(app: Term) -> Result<Thm> {
    Thm::beta_conv(app)
}

/// Convert `⊢ Trueprop (a = b)` (HOL bool equality wrapped to prop)
/// to the Pure meta-equality `⊢ a ≡ b` using the `eq_reflection`
/// axiom.
///
/// The eq_reflection axiom is
/// `⋀x y:'a. Trueprop (x = y) ≡ (x ≡ y)`; we specialise it at the
/// type and witnesses extracted from `hol_eq_thm`'s conclusion, then
/// `eq_mp` the conclusion onto the bridge.
pub fn pure_eq_of_hol_eq(hol_eq_thm: Thm) -> Result<Thm> {
    // Inspect the conclusion to find the HOL eq's type and operands.
    let (lhs, rhs, ty) = extract_trueprop_hol_eq(hol_eq_thm.concl())?;
    let bridge = Thm::eq_reflection()
        .inst_tfree("a", ty)?
        .all_elim(lhs)?
        .all_elim(rhs)?;
    // bridge :   Trueprop (lhs = rhs) ≡ (lhs ≡ rhs)
    // hol_eq_thm: Trueprop (lhs = rhs)
    // eq_mp: bridge is the Pure-eq, hol_eq_thm is the antecedent.
    bridge.eq_mp(hol_eq_thm)
}

fn extract_trueprop_hol_eq(
    t: &Term,
) -> Result<(Term, Term, Type)> {
    use crate::term::{HolOp, TermKind};
    // Expected shape: App(HolOp(Trueprop, _), App(App(HolOp(Eq, ty), lhs), rhs))
    let (head, body) = match t.kind() {
        TermKind::App(f, x) => (f.clone(), x.clone()),
        _ => return Err(eq_extract_err()),
    };
    if !matches!(head.kind(), TermKind::HolOp(HolOp::Trueprop, _)) {
        return Err(eq_extract_err());
    }
    let (eq_lhs_app, rhs) = match body.kind() {
        TermKind::App(f, x) => (f.clone(), x.clone()),
        _ => return Err(eq_extract_err()),
    };
    let (eq_op, lhs) = match eq_lhs_app.kind() {
        TermKind::App(f, x) => (f.clone(), x.clone()),
        _ => return Err(eq_extract_err()),
    };
    let ty = match eq_op.kind() {
        TermKind::HolOp(HolOp::Eq, fun_ty) => {
            // fun_ty : α → α → bool ; recover α
            match fun_ty.kind() {
                crate::term::TypeKind::Fun(a, _) => (*a).clone(),
                _ => return Err(eq_extract_err()),
            }
        }
        _ => return Err(eq_extract_err()),
    };
    Ok((lhs, rhs, ty))
}

fn eq_extract_err() -> crate::error::Error {
    crate::error::Error::NotASpec // placeholder; semantic-shape mismatch
}

// ---------------------------------------------------------------------------
// Re-exports for the standard idiom
// ---------------------------------------------------------------------------

/// `⊢ defs::nat_rec(α) z f 0 ≡ z`, the Pure-meta form of the
/// nat_rec_zero axiom specialised at concrete `α`, `z`, `f`.
pub fn nat_rec_zero_at(alpha: Type, z: Term, f: Term) -> Result<Thm> {
    let hol_form = Thm::nat_rec_zero()
        .inst_tfree("a", alpha)?
        .all_elim(z)?
        .all_elim(f)?;
    pure_eq_of_hol_eq(hol_form)
}

/// `⊢ defs::nat_rec(α) z f (succ n) ≡ f n (defs::nat_rec(α) z f n)`.
pub fn nat_rec_succ_at(alpha: Type, z: Term, f: Term, n: Term) -> Result<Thm> {
    let hol_form = Thm::nat_rec_succ()
        .inst_tfree("a", alpha)?
        .all_elim(z)?
        .all_elim(f)?
        .all_elim(n)?;
    pure_eq_of_hol_eq(hol_form)
}

/// `⊢ defs::nat_add() = (definitional body)` as a Pure-meta
/// equality. Re-exports [`Thm::unfold_term_spec`] for completeness;
/// every let-style spec in `defs::` unfolds via the same method.
pub fn unfold(t: Term) -> Result<Thm> {
    Thm::unfold_term_spec(t)
}

/// Convenience: the iter-applied form `iter[α]`.
pub fn iter_at(alpha: Type) -> Term {
    defs::iter(alpha)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermKind;

    #[test]
    fn unfold_iter_at_nat_round_trips() {
        let t = defs::iter(Type::nat());
        let thm = Thm::unfold_term_spec(t.clone()).expect("iter unfolds");
        // Concl is `t ≡ body` (Pure eq). Check it matches.
        match thm.concl().kind() {
            TermKind::Eq(l, _) => assert_eq!(l, &t),
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn unfold_rejects_natrec_def_style() {
        // natRec is a def-style spec (tm is a `... → bool` predicate);
        // unfolding it via the let-style rule must error cleanly.
        let t = defs::nat_rec(Type::nat());
        assert!(Thm::unfold_term_spec(t).is_err());
    }

    #[test]
    fn nat_rec_zero_at_concrete() {
        let alpha = Type::nat();
        let z = Term::free("z0", alpha.clone());
        let f = Term::free(
            "f0",
            Type::fun(Type::nat(), Type::fun(alpha.clone(), alpha.clone())),
        );
        let thm = nat_rec_zero_at(alpha.clone(), z.clone(), f.clone())
            .expect("nat_rec_zero_at: builds");
        // ⊢ natRec[nat] z f 0 ≡ z
        match thm.concl().kind() {
            TermKind::Eq(_, r) => assert_eq!(r, &z),
            other => panic!("expected Eq with z on the rhs, got {other:?}"),
        }
    }
}
