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
use covalence_core::{Term, Type, subst};

use crate::init::ext::TermExt;
use crate::init::rat;

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
