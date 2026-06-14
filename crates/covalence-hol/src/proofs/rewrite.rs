//! Equational rewriting helpers — pure combinators over the kernel's
//! `refl` / `trans` / `cong_app` / `cong_abs` / `eq_mp` / `sym` rules.
//!
//! None of these grow the TCB. They package common multi-step
//! rewriting patterns so call sites read like proofs rather than
//! plumbing.
//!
//! ## A single equality
//!
//! HOL is folded into the kernel, so there is no `Trueprop` wrapper
//! and no `eq_reflection` bridge: every equality is one HOL `=`.
//! Both `Thm::refl(t)` and `ctx.mk_eq(lhs, rhs)` produce the *same*
//! `TermKind::Eq`-headed term, so the helpers here work uniformly on
//! any equational theorem.

use covalence_core::{Term, Thm};

/// Chain TRANS across a non-empty list of equational theorems:
/// `[A ≡ B, B ≡ C, C ≡ D]` → `A ≡ D`. Panics on an empty list.
pub fn trans_chain(steps: Vec<Thm>) -> Thm {
    let mut iter = steps.into_iter();
    let mut acc = iter
        .next()
        .expect("trans_chain: at least one step required");
    for next in iter {
        acc = acc.trans(next).expect("trans_chain: step mismatch");
    }
    acc
}

/// Given `Γ₁ ⊢ A ≡ B` and `Γ₂ ⊢ B ≡ C`, return `Γ₁ ∪ Γ₂ ⊢ A ≡ C`.
/// Convenience over `Thm::trans` so call sites don't have to thread
/// `.expect(...)` chains.
pub fn trans2(ab: Thm, bc: Thm) -> Thm {
    ab.trans(bc).expect("trans2: middle term mismatch")
}

/// Given `Γ ⊢ A` and `Δ ⊢ A ≡ B`, return `Γ ∪ Δ ⊢ B`. Useful for
/// rewriting a theorem with an equation derived from the kernel
/// (e.g. `Thm::reduce_prim` or a definitional unfolding).
pub fn rewrite_with(thm: Thm, eq: Thm) -> Thm {
    eq.eq_mp(thm).expect("rewrite_with: eq_mp")
}

/// Build `⊢ f a ≡ f a'` from `⊢ a ≡ a'`, given a fixed `f`.
/// (Specialisation of `cong_app` where the function side is
/// reflexive.)
pub fn cong_at_arg(f: Term, arg_eq: Thm) -> Thm {
    Thm::refl(f)
        .expect("cong_at_arg: refl f")
        .cong_app(arg_eq)
        .expect("cong_at_arg: cong_app")
}

/// Build `⊢ f a ≡ g a` from `⊢ f ≡ g`, given a fixed `a`.
/// (Specialisation of `cong_app` where the argument side is
/// reflexive.)
pub fn cong_at_fn(f_eq: Thm, arg: Term) -> Thm {
    f_eq.cong_app(Thm::refl(arg).expect("cong_at_fn: refl arg"))
        .expect("cong_at_fn: cong_app")
}

/// β-reduce `(λx. body) arg` and use the result to rewrite a
/// theorem whose conclusion contains that redex at the head. Given
/// `Γ ⊢ ((λx. body) arg)` (or a Thm whose conclusion is the redex),
/// return `Γ ⊢ body[arg/x]`.
pub fn beta_reduce(thm: Thm) -> Thm {
    let redex = thm.concl().clone();
    let beta = Thm::beta_conv(redex).expect("beta_reduce: beta_conv");
    rewrite_with(thm, beta)
}

/// Given `Γ ⊢ A ≡ B`, return `Γ ⊢ B ≡ A`.
pub fn sym(eq: Thm) -> Thm {
    eq.sym().expect("sym: not an equation")
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::Type;

    #[test]
    fn trans_chain_three_steps() {
        let nat = Type::nat();
        let a = Term::free("a", nat.clone());
        let b = Term::free("b", nat.clone());
        let c = Term::free("c", nat.clone());
        let d = Term::free("d", nat);

        // Three assumed equations a≡b, b≡c, c≡d.
        let ab = Thm::assume(
            crate::HolLightCtx::new().mk_eq(a.clone(), b.clone()).unwrap(),
        )
        .unwrap();
        let bc = Thm::assume(
            crate::HolLightCtx::new().mk_eq(b.clone(), c.clone()).unwrap(),
        )
        .unwrap();
        let cd = Thm::assume(
            crate::HolLightCtx::new().mk_eq(c.clone(), d.clone()).unwrap(),
        )
        .unwrap();
        let ad = trans_chain(vec![ab, bc, cd]);
        let expected = crate::HolLightCtx::new().mk_eq(a, d).unwrap();
        assert_eq!(ad.concl(), &expected);
    }

    #[test]
    fn trans2_two_steps() {
        let nat = Type::nat();
        let a = Term::free("a", nat.clone());
        let b = Term::free("b", nat.clone());
        let c = Term::free("c", nat);

        let ab = Thm::assume(
            crate::HolLightCtx::new().mk_eq(a.clone(), b.clone()).unwrap(),
        )
        .unwrap();
        let bc = Thm::assume(
            crate::HolLightCtx::new().mk_eq(b, c.clone()).unwrap(),
        )
        .unwrap();
        let ac = trans2(ab, bc);
        let expected = crate::HolLightCtx::new().mk_eq(a, c).unwrap();
        assert_eq!(ac.concl(), &expected);
    }

    #[test]
    fn sym_swaps_equation() {
        let nat = Type::nat();
        let a = Term::free("a", nat.clone());
        let b = Term::free("b", nat);
        let ab = Thm::assume(
            crate::HolLightCtx::new().mk_eq(a.clone(), b.clone()).unwrap(),
        )
        .unwrap();
        let ba = sym(ab);
        let expected = crate::HolLightCtx::new().mk_eq(b, a).unwrap();
        assert_eq!(ba.concl(), &expected);
    }
}
