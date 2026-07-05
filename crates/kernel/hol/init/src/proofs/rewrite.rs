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
/// (e.g. `covalence_hol_eval::reduce` or a definitional unfolding).
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

/// Split an equation term `App(App(=, lhs), rhs)` into `(lhs, rhs)`.
/// Returns `None` if `t` is not an `=`-headed application.
pub fn eq_sides(t: &Term) -> Option<(Term, Term)> {
    use covalence_core::TermKind;
    let TermKind::App(f, rhs) = t.kind() else {
        return None;
    };
    let TermKind::App(head, lhs) = f.kind() else {
        return None;
    };
    let TermKind::Eq(_) = head.kind() else {
        return None;
    };
    Some((lhs.clone(), rhs.clone()))
}

/// `⊢ t = nf`, where `nf` is the β-normal form of `t`. A full
/// normalising conversion built from the kernel's `refl` / `cong_app`
/// / `abs` / `beta_conv` / `trans` — descends into both sides of an
/// application and under binders, β-reducing every redex it exposes.
///
/// Terminates because kernel terms are simply typed (hence strongly
/// normalising). Used to evaluate the body of a definition after it
/// has been applied to concrete arguments (see [`unfold_at_1`] /
/// [`unfold_at_2`]).
pub fn beta_nf(t: Term) -> Thm {
    // `beta_nf_opt` returns `None` when `t` is *already* β-normal — no
    // proof spine was built and no terms were allocated for it. In that
    // (very common) case the equation `⊢ t = t` is a single `refl`.
    beta_nf_opt(&t).unwrap_or_else(|| Thm::refl(t).expect("beta_nf: refl on a leaf"))
}

/// The sharing-preserving core of [`beta_nf`]: returns `Some(⊢ t = nf)`
/// when `t` contains a redex (so it *reduces*), and `None` when `t` is
/// already in β-normal form.
///
/// Returning `None` for an unchanged term is the key optimisation: the
/// old `beta_nf` descended into *every* subterm and built a `cong_app`
/// proof at *every* `App` node — even subtrees with no redex — paying an
/// `Arc` allocation plus a `Thm::build` type-check per node, which made
/// normalising an N-node term cost O(N²). Here a redex-free subtree
/// short-circuits to `None` without building any proof; only the spine
/// from the root down to each redex is rebuilt. The whole-term `refl` is
/// built once at the top by [`beta_nf`].
fn beta_nf_opt(t: &Term) -> Option<Thm> {
    use covalence_core::{TermKind, subst};
    match t.kind() {
        TermKind::App(f, x) => {
            let of = beta_nf_opt(f);
            let ox = beta_nf_opt(x);
            // If neither side reduced *and* the function is not a λ, the
            // application `f x` is already normal — nothing to do.
            let f_is_abs = matches!(f.kind(), TermKind::Abs(..));
            if of.is_none() && ox.is_none() && !f_is_abs {
                return None;
            }
            // Build `⊢ f x = f' x'` from the (possibly reflexive) side
            // proofs. Reuse `refl` only for the side that did not reduce.
            let f_nf = of.unwrap_or_else(|| Thm::refl(f.clone()).expect("beta_nf: refl f"));
            let x_nf = ox.unwrap_or_else(|| Thm::refl(x.clone()).expect("beta_nf: refl x"));
            let comb = f_nf.cong_app(x_nf).expect("beta_nf: cong_app");
            let (_, fx_rhs) = eq_sides(comb.concl()).expect("beta_nf: comb is an equation");
            // If the normalised function side is a λ, `f' x'` is a
            // redex — fire it and keep normalising the result.
            if let TermKind::App(f_prime, _) = fx_rhs.kind()
                && matches!(f_prime.kind(), TermKind::Abs(..))
            {
                let beta = Thm::beta_conv(fx_rhs.clone()).expect("beta_nf: beta_conv");
                let (_, body) = eq_sides(beta.concl()).expect("beta_nf: beta is an equation");
                let redex_step = comb.trans(beta).expect("beta_nf: trans redex");
                // Normalise the β-reduct; if it is already normal, skip
                // the trailing `trans` against a reflexive proof.
                return Some(match beta_nf_opt(&body) {
                    Some(body_nf) => redex_step.trans(body_nf).expect("beta_nf: trans body"),
                    None => redex_step,
                });
            }
            Some(comb)
        }
        TermKind::Abs(ty, body) => {
            // Normalise under the binder: open with a fresh free var,
            // normalise, re-abstract. Skip entirely if the body is normal.
            let fresh = fresh_name(body);
            let wit = Term::free(fresh.as_str(), ty.clone());
            let opened = subst::open(body, &wit);
            let opened_nf = beta_nf_opt(&opened)?;
            Some(
                opened_nf
                    .abs(fresh.as_str(), ty.clone())
                    .expect("beta_nf: abs"),
            )
        }
        _ => None,
    }
}

/// A free-variable name that does not occur free in `body`.
fn fresh_name(body: &Term) -> String {
    let mut i = 0usize;
    loop {
        let name = format!("_bnf{i}");
        if !covalence_core::subst::has_free_var(body, &name) {
            return name;
        }
        i += 1;
    }
}

/// Unfold a unary defined constant at an argument:
/// `⊢ op arg = body[arg]`, given `op` is a let-style `Spec` leaf
/// (its definition is `op = λx. body`).
///
/// Uses a *single* top-level β-step ([`Thm::beta_conv`]), **not** full
/// normalisation — so `arg` is substituted in verbatim and any redexes
/// *inside* `arg` are preserved (callers that want them reduced apply
/// [`beta_nf`] themselves).
pub fn unfold_at_1(op: Term, arg: Term) -> Thm {
    let def = crate::init::twins::unfold_spec(&op).expect("unfold_at_1: unfold_spec");
    let applied = cong_at_fn(def, arg); // ⊢ op arg = (λx.body) arg
    let (_, redex) = eq_sides(applied.concl()).expect("unfold_at_1: applied is an equation");
    let beta = Thm::beta_conv(redex).expect("unfold_at_1: beta_conv");
    applied.trans(beta).expect("unfold_at_1: trans")
}

/// Unfold a binary defined constant at two arguments:
/// `⊢ op a b = body[a, b]`, given `op = λx y. body`. One top-level
/// β-step per argument (see [`unfold_at_1`]).
pub fn unfold_at_2(op: Term, a: Term, b: Term) -> Thm {
    let step1 = unfold_at_1(op, a); // ⊢ op a = (λy. body[a])
    let applied = cong_at_fn(step1, b); // ⊢ (op a) b = (λy. body[a]) b
    let (_, redex) = eq_sides(applied.concl()).expect("unfold_at_2: applied is an equation");
    let beta = Thm::beta_conv(redex).expect("unfold_at_2: beta_conv");
    applied.trans(beta).expect("unfold_at_2: trans")
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
            crate::HolLightCtx::new()
                .mk_eq(a.clone(), b.clone())
                .unwrap(),
        )
        .unwrap();
        let bc = Thm::assume(
            crate::HolLightCtx::new()
                .mk_eq(b.clone(), c.clone())
                .unwrap(),
        )
        .unwrap();
        let cd = Thm::assume(
            crate::HolLightCtx::new()
                .mk_eq(c.clone(), d.clone())
                .unwrap(),
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
            crate::HolLightCtx::new()
                .mk_eq(a.clone(), b.clone())
                .unwrap(),
        )
        .unwrap();
        let bc = Thm::assume(crate::HolLightCtx::new().mk_eq(b, c.clone()).unwrap()).unwrap();
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
            crate::HolLightCtx::new()
                .mk_eq(a.clone(), b.clone())
                .unwrap(),
        )
        .unwrap();
        let ba = sym(ab);
        let expected = crate::HolLightCtx::new().mk_eq(b, a).unwrap();
        assert_eq!(ba.concl(), &expected);
    }
}
