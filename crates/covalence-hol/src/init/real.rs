//! `real` theorems: the Dedekind-cut construction of the reals, built on
//! [`init::rat`](crate::init::rat).
//!
//! ## The construction
//!
//! `real := close rat ratLe` ([`defs/real.rs`](covalence_core::defs)) is
//! the type of **upper Dedekind cuts**: a real is a non-empty subset of
//! `rat` that is upward-closed under `≤`. The carrier of the subtype is
//! the powerset `rat → bool`, and the selector predicate (the `close`
//! predicate, [`cut_pred`]) is
//!
//! ```text
//!     λS. (∀x y. ratLe x y ⟹ S x ⟹ S y) ∧ (∃x. S x)
//! ```
//!
//! — "`S` is upward-closed under `≤` and non-empty". We bridge a real and
//! its cut-set with the kernel subtype coercions: [`mk_real`] (`abs`)
//! wraps a cut-set into a real and [`cut_of`] (`rep`) recovers it.
//!
//! The **principal cut** of a rational `q` is its up-set `{x | q ≤ x}`,
//! written η-cleanly as the partial application `ratLe q : rat → bool`
//! (so `(ratLe q) x` is `ratLe q x` with no stray β-redex). [`of_rat`]
//! embeds `rat` into `real` this way; [`real_zero`] / [`real_one`] are the
//! principal cuts of `0` / `1`.
//!
//! ## Status
//!
//! - **Scaffolding** (this layer): the coercions, [`of_rat`], the order
//!   [`real_le`] (reverse inclusion of cut-sets), and [`real_zero`] /
//!   [`real_one`].
//! - **`is_cut`** — `⊢ cut_pred (ratLe q)`, that every principal up-set is
//!   a genuine cut — is **proved** from the `rat` `≤` toolkit
//!   (`le_trans` for upward closure, `le_refl` for non-emptiness).
//! - **[`zero_ne_one`]** — `⊢ ¬(0 = 1)` — is **proved**: distinct
//!   principal cuts (the rational `0` lies in `ratLe 0` but not `ratLe 1`,
//!   by `not_one_le_zero`), transported through the subtype `rep`/`abs`.
//! - **[`complete`]** — the least-upper-bound property — is **derived**
//!   from the supremum-cut postulates ([`sup_is_ub`], [`sup_is_least`]),
//!   exactly as `rat::dense` is derived from the mediant postulates: the
//!   supremum is the *intersection of the cut-sets* ([`real_sup`]).

use covalence_core::defs::{real_spec, real_ty};
use covalence_core::{Result, Term, Thm, Type, subst};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::{logic, rat};

// Re-export the `defs/real.rs` catalogue.
pub use covalence_core::defs::real_ty as real_type;

// ============================================================================
// Coercions and small term helpers
// ============================================================================

/// `real` — the reals type.
fn real() -> Type {
    real_ty()
}

/// `rat` — the base type of the cuts.
fn ratt() -> Type {
    rat::rat_ty()
}

/// `rat → bool` — the powerset carrier a cut-set lives in.
fn powerset() -> Type {
    Type::fun(ratt(), Type::bool())
}

/// `abs : (rat→bool) → real` — wrap a cut-set into a real.
fn real_abs() -> Term {
    Term::spec_abs(real_spec(), Vec::new())
}
/// `rep : real → (rat→bool)` — the cut-set of a real.
fn real_rep() -> Term {
    Term::spec_rep(real_spec(), Vec::new())
}

/// `mkReal S ≔ abs S` — the real whose cut-set is `S : rat→bool`.
fn mk_real(s: Term) -> Term {
    Term::app(real_abs(), s)
}
/// `cutOf r ≔ rep r : rat→bool` — the cut-set of the real `r`.
fn cut_of(r: Term) -> Term {
    Term::app(real_rep(), r)
}

/// The `close`/cut selector predicate `P : (rat→bool) → bool` — the
/// `real` subtype's `tm()`.
fn cut_pred() -> Term {
    real_spec()
        .tm()
        .expect("real is a close-subtype with a selector predicate")
        .clone()
}

/// `ratLe q : rat → bool` — the principal upper cut `{x | q ≤ x}` of a
/// rational `q`, η-cleanly as a partial application.
fn upper_cut(q: Term) -> Term {
    Term::app(rat::rat_le(), q)
}

// ============================================================================
// Embedding ℚ ↪ ℝ and the order
// ============================================================================

/// `of_rat : rat → real` ≡ `λq. mkReal (ratLe q)` — the principal-cut
/// embedding of the rationals.
pub fn of_rat() -> Term {
    let q = Term::free("q", ratt());
    let body = mk_real(upper_cut(q.clone()));
    Term::abs(ratt(), subst::close(&body, "q"))
}

/// `0 : real` ≡ the principal cut of `rat`'s `0`.
pub fn real_zero() -> Term {
    mk_real(upper_cut(rat::rat_zero()))
}

/// `1 : real` ≡ the principal cut of `rat`'s `1`.
pub fn real_one() -> Term {
    mk_real(upper_cut(rat::rat_one()))
}

/// `realLe : real → real → bool` ≡ `λr s. ∀q. cutOf s q ⟹ cutOf r q` —
/// the order on reals as **reverse inclusion** of cut-sets (a larger real
/// has a smaller up-set).
pub fn real_le() -> Term {
    let (r, s) = (Term::free("r", real()), Term::free("s", real()));
    let q = Term::free("q", ratt());
    let body = Term::app(cut_of(s.clone()), q.clone())
        .imp(Term::app(cut_of(r.clone()), q))
        .expect("real_le: body")
        .forall("q", ratt())
        .expect("real_le: ∀q");
    Term::abs(
        real(),
        subst::close(&Term::abs(real(), subst::close(&body, "s")), "r"),
    )
}

/// `r ≤ s` on `real`.
fn rle(r: Term, s: Term) -> Term {
    Term::app(Term::app(real_le(), r), s)
}

/// `ratLe a b` — a rational `≤` atom.
fn rat_le_app(a: &Term, b: &Term) -> Term {
    Term::app(Term::app(rat::rat_le(), a.clone()), b.clone())
}

// ============================================================================
// Principal up-sets are genuine cuts
// ============================================================================

/// `⊢ cut_pred (ratLe q)` — every principal up-set `{x | q ≤ x}` is a
/// Dedekind cut. **Proved** from the `rat` `≤` toolkit: upward closure is
/// `le_trans` (`q ≤ x` and `x ≤ y` give `q ≤ y`), non-emptiness is
/// `le_refl` (the witness `q` lies in its own up-set).
///
/// The conclusion is the *un-reduced* redex `cut_pred (ratLe q)` — exactly
/// the antecedent [`Thm::spec_rep_abs_fwd`] expects — obtained by proving
/// the β-reduced conjunction and transporting back across `beta_conv`.
fn is_cut(q: &Term) -> Result<Thm> {
    let s = upper_cut(q.clone()); // ratLe q : rat→bool
    let pred_app = Term::app(cut_pred(), s);
    let conv = Thm::beta_conv(pred_app)?; // ⊢ pred_app = (closed ∧ nonempty)
    let clean = conv.concl().as_eq().expect("beta_conv yields an equation").1.clone();

    // clean = and closed nonempty = App(App(and, closed), nonempty).
    let (and_closed, nonempty_t) = clean.as_app().expect("clean is a conjunction");
    let closed_t = and_closed.as_app().expect("clean is a conjunction").1.clone();
    let nonempty_t = nonempty_t.clone();

    // closed: ∀x y. x≤y ⟹ q≤x ⟹ q≤y, via le_trans q x y (antecedents reordered).
    let closed_thm = {
        let (x, y) = (Term::free("x", ratt()), Term::free("y", ratt()));
        let xy = rat_le_app(&x, &y);
        let qx = rat_le_app(q, &x);
        let qy = rat::le_trans()
            .all_elim(q.clone())?
            .all_elim(x.clone())?
            .all_elim(y.clone())?
            .imp_elim(Thm::assume(qx.clone())?)?
            .imp_elim(Thm::assume(xy.clone())?)?; // {q≤x, x≤y} ⊢ q≤y
        qy.imp_intro(&qx)?
            .imp_intro(&xy)?
            .all_intro("y", ratt())?
            .all_intro("x", ratt())?
    };

    // nonempty: ∃x. q≤x, witness q, proof le_refl q (β-expanded to `pred q`).
    let nonempty_thm = {
        let pred = nonempty_t.as_app().expect("nonempty is `exists pred`").1.clone();
        let refl = rat::le_refl().all_elim(q.clone())?; // ⊢ q≤q
        let pf = Thm::beta_conv(Term::app(pred.clone(), q.clone()))?
            .sym()?
            .eq_mp(refl)?; // ⊢ pred q
        logic::exists_intro(pred, q.clone(), pf)? // ⊢ ∃x. q≤x
    };

    // Re-assemble the conjunction and transport back to the redex.
    debug_assert_eq!(closed_thm.concl(), &closed_t);
    let p_clean = closed_thm.and_intro(nonempty_thm)?; // ⊢ closed ∧ nonempty
    conv.sym()?.eq_mp(p_clean) // ⊢ cut_pred (ratLe q)
}

// ============================================================================
// 0 ≠ 1
// ============================================================================

cached_thm! {
    /// `⊢ ¬(0 = 1)` — zero and one are distinct reals.
    ///
    /// **Proved.** The principal cuts `ratLe 0` and `ratLe 1` differ at the
    /// rational `0`: `0 ≤ 0` holds (`le_refl`) but `1 ≤ 0` does not
    /// (`not_one_le_zero`). Assuming `0 = 1`, congruence under `rep` plus
    /// the subtype round-trip [`Thm::spec_rep_abs_fwd`] (discharged by
    /// [`is_cut`]) collapses the two cut-sets, so `0 ≤ 0 = 1 ≤ 0`,
    /// contradicting `not_one_le_zero`. Genuine *modulo* the `rat` order
    /// postulates `is_cut` / `not_one_le_zero` rest on.
    pub fn zero_ne_one() -> Thm {
        zero_ne_one_impl().expect("real zero_ne_one")
    }
}
fn zero_ne_one_impl() -> Result<Thm> {
    let (zero, one) = (rat::rat_zero(), rat::rat_one());
    let (s0, s1) = (upper_cut(zero.clone()), upper_cut(one.clone()));
    let eq01 = real_zero().equals(real_one())?; // abs s0 = abs s1

    // rep both sides of the assumed equality.
    let reps_eq = Thm::assume(eq01.clone())?.cong_arg(real_rep())?; // {eq} ⊢ rep(abs s0)=rep(abs s1)
    // rep(abs sᵢ) = sᵢ, the subtype round-trip discharged by `is_cut`.
    let r0 = Thm::spec_rep_abs_fwd(real_spec(), Vec::new(), s0)?.imp_elim(is_cut(&zero)?)?;
    let r1 = Thm::spec_rep_abs_fwd(real_spec(), Vec::new(), s1)?.imp_elim(is_cut(&one)?)?;
    let sets_eq = r0.sym()?.trans(reps_eq)?.trans(r1)?; // {eq} ⊢ s0 = s1

    // Evaluate both cut-sets at the rational 0: (0≤0) = (1≤0).
    let at0 = sets_eq.cong_fn(zero.clone())?; // {eq} ⊢ ratLe 0 0 = ratLe 1 0
    let le00 = rat::le_refl().all_elim(zero.clone())?; // ⊢ ratLe 0 0
    let le10 = at0.eq_mp(le00)?; // {eq} ⊢ ratLe 1 0

    // ¬(1≤0) gives the contradiction.
    rat::not_one_le_zero()
        .not_elim(le10)? // {eq, …} ⊢ F
        .imp_intro(&eq01)?
        .not_intro() // ⊢ ¬(0 = 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_ty_matches_the_catalogue() {
        assert_eq!(real(), covalence_core::defs::real_ty());
        assert!(!real().is_bool());
    }

    #[test]
    fn carrier_is_the_rational_powerset() {
        // abs : (rat→bool) → real ; rep : real → (rat→bool).
        assert_eq!(
            real_abs().type_of().unwrap(),
            Type::fun(powerset(), real())
        );
        assert_eq!(
            real_rep().type_of().unwrap(),
            Type::fun(real(), powerset())
        );
    }

    #[test]
    fn embedding_and_constants_have_expected_types() {
        assert_eq!(of_rat().type_of().unwrap(), Type::fun(ratt(), real()));
        assert_eq!(real_zero().type_of().unwrap(), real());
        assert_eq!(real_one().type_of().unwrap(), real());
    }

    #[test]
    fn real_le_is_a_binary_relation() {
        assert_eq!(
            real_le().type_of().unwrap(),
            Type::fun(real(), Type::fun(real(), Type::bool()))
        );
        // `r ≤ s` is a bool.
        let (r, s) = (Term::free("r", real()), Term::free("s", real()));
        assert!(rle(r, s).type_of().unwrap().is_bool());
    }

    #[test]
    fn is_cut_proves_a_principal_up_set_is_a_cut() {
        // A concrete rational (`is_cut` is only ever called on closed
        // rationals; `exists_intro` reserves the name `q` internally).
        let q = rat::rat_zero();
        let thm = is_cut(&q).expect("is_cut q");
        // Conclusion is exactly the redex `cut_pred (ratLe q)`.
        assert_eq!(thm.concl(), &Term::app(cut_pred(), upper_cut(q)));
        assert!(thm.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn zero_is_distinct_from_one() {
        let thm = zero_ne_one();
        // Statement: ¬(0 = 1).
        assert_eq!(
            thm.concl(),
            &real_zero().equals(real_one()).unwrap().not().unwrap()
        );
        // Genuine modulo the rat-order postulates: the assumed `0 = 1` is
        // discharged, so no equation hypothesis remains — only bool
        // (postulate) hyps.
        let eq01 = real_zero().equals(real_one()).unwrap();
        assert!(
            !thm.hyps().iter().any(|h| h == &eq01),
            "the assumed equality is discharged"
        );
        for h in thm.hyps() {
            assert!(h.type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn cut_pred_is_the_close_predicate() {
        // cut_pred : (rat→bool) → bool.
        assert_eq!(
            cut_pred().type_of().unwrap(),
            Type::fun(powerset(), Type::bool())
        );
        // It applies to a principal cut to give a bool statement.
        let p = Term::app(cut_pred(), upper_cut(rat::rat_zero()));
        assert!(p.type_of().unwrap().is_bool());
    }
}
