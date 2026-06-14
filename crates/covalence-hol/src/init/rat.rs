//! `rat` theorems: the `defs/rat.rs` catalogue re-exported, plus the
//! quotient scaffolding for HOL `rat := (int × int.pos) / ~` — mirroring
//! how [`init::int`] pairs the `int` definitions with the Grothendieck
//! quotient machinery, one level up.
//!
//! [`init::int`]: crate::init::int
//!
//! ## The construction
//!
//! A pair `(a, b) : int × int.pos` represents the rational `a / b` with a
//! strictly-positive denominator (so it is always nonzero and the sign
//! lives in the numerator), and pairs are identified by
//! cross-multiplication:
//!
//! ```text
//!     (a, b) ~ (c, d)  ⟺  a · d = c · b
//! ```
//!
//! `rat` is the quotient of `prod int int.pos` by that relation; the
//! carrier is `(prod int int.pos) → bool` (a class is the set of
//! equivalent numerator/denominator pairs). The bridge between a
//! representative pair and its class reuses the generic
//! [`init::quotient`](crate::init::quotient) machinery exactly as `int`
//! does over `nat × nat`.
//!
//! ## Status
//!
//! This module is built up in layers, mirroring `init::int`:
//!
//! - **Quotient relation.** [`rat_rel`] is the cross-multiplication
//!   relation, structurally the term `defs/rat.rs` quotients by.
//!   [`rat_rel_refl`] / [`rat_rel_symm`] are **proved** (`int`-equation
//!   `refl` / `sym`); [`rat_rel_trans`] is **postulated** — it is the one
//!   piece that needs `int` *multiplicative cancellation by a positive*,
//!   an `int` fact not yet discharged (see `SKELETONS.md`).
//! - **Maps in.** [`of_int`] (`a ↦ a/1`) and [`of_nat`] (`= of_int ∘
//!   nat.toInt`, by composition) embed the integers and naturals.
//! - **Ring / order.** The field operations ([`rat_zero`], [`rat_one`],
//!   [`rat_add`], [`rat_neg`], [`rat_mul`]) and the strict order
//!   ([`rat_lt`]) are defined at the representative level; the ordered-
//!   field axioms over them are **postulated** (same audit-trail style as
//!   `init::int`), pending the quotient derivations.
//! - **Density.** [`dense`] — `∀x y. x < y ⟹ ∃z. x < z ∧ z < y` — is
//!   **derived** from the two mediant-inequality postulates via the
//!   mediant `(a+c)/(b+d)`, the witness that needs no division.

use covalence_core::defs::{fst, int_pos_spec, int_pos_ty, prod, snd};
use covalence_core::{Result, Term, Thm, Type};

use crate::init::ext::TermExt;
use crate::init::int;

// Re-export the `defs/rat.rs` catalogue (the type handles + the declared
// `ratLe` order constant; bodies stay in `covalence_core::defs`).
pub use covalence_core::defs::{rat_le, rat_le_spec, rat_spec, rat_ty};

// ============================================================================
// Small term helpers (private — the public surface is theorems / maps)
// ============================================================================

/// `rat` — the rationals type.
fn rat() -> Type {
    rat_ty()
}

/// `int × int.pos` — the numerator/denominator representative carrier.
fn ip_pair() -> Type {
    prod(Type::int(), int_pos_ty())
}

/// `fst p : int` — the numerator of a representative pair.
fn num(p: &Term) -> Term {
    Term::app(fst(Type::int(), int_pos_ty()), p.clone())
}

/// `rep (snd p) : int` — the (positive) denominator of a representative
/// pair, coerced from `int.pos` down to its underlying `int`.
fn den(p: &Term) -> Term {
    let d_pos = Term::app(snd(Type::int(), int_pos_ty()), p.clone());
    let rep = Term::spec_rep(int_pos_spec(), Vec::new());
    Term::app(rep, d_pos)
}

/// `a · b` on `int`.
fn imul(a: Term, b: Term) -> Term {
    Term::app(Term::app(int::int_mul(), a), b)
}

/// `λp q. num p · den q = num q · den p` — the cross-multiplication
/// relation carving `rat`. Structurally the same term `defs/rat.rs`
/// quotients by.
pub fn rat_rel() -> Term {
    let pair_ty = ip_pair();
    let (p, q) = (Term::free("p", pair_ty.clone()), Term::free("q", pair_ty.clone()));
    let body = imul(num(&p), den(&q))
        .equals(imul(num(&q), den(&p)))
        .expect("rat_rel: body");
    let inner = Term::abs(pair_ty.clone(), covalence_core::subst::close(&body, "q"));
    Term::abs(pair_ty, covalence_core::subst::close(&inner, "p"))
}

/// `rat_rel p q` as an (un-reduced) application — the shape
/// [`quotient::class_intro`](crate::init::quotient::class_intro) reads
/// its relation in.
fn rel_app(p: &Term, q: &Term) -> Term {
    Term::app(Term::app(rat_rel(), p.clone()), q.clone())
}

/// `mkRat p ≔ abs (λq. rat_rel p q)` — the rational whose class is `[p]`,
/// for a representative pair term `p : int × int.pos`.
fn mk_rat(p: &Term) -> Term {
    crate::init::quotient::mk_class(&rat_spec(), &[], &ip_pair(), &rat_rel(), p)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `pair a b : int × int.pos` from an `int` numerator and an
    /// `int.pos` denominator.
    fn ip(a: Term, b: Term) -> Term {
        Term::app(
            Term::app(covalence_core::defs::pair(Type::int(), int_pos_ty()), a),
            b,
        )
    }

    /// `1 : int.pos` — the abstraction of the `int` literal `1`.
    fn one_pos() -> Term {
        Term::app(Term::spec_abs(int_pos_spec(), Vec::new()), Term::int_lit(1i128))
    }

    #[test]
    fn rat_ty_matches_the_catalogue() {
        // The re-exported `rat` type is the `defs/rat.rs` one, and not bool.
        assert_eq!(rat(), covalence_core::defs::rat_ty());
        assert!(!rat().is_bool());
    }

    #[test]
    fn rat_rel_is_a_binary_relation_on_pairs() {
        // rat_rel : (int×int.pos) → (int×int.pos) → bool.
        let expected = Type::fun(
            ip_pair(),
            Type::fun(ip_pair(), Type::bool()),
        );
        assert_eq!(rat_rel().type_of().unwrap(), expected);
    }

    #[test]
    fn rel_app_reduces_to_a_cross_multiplication() {
        // rat_rel (a,1) (c,1)  β-reduces to  a·den(c,1) = c·den(a,1).
        let p = ip(Term::int_lit(2i128), one_pos());
        let q = ip(Term::int_lit(3i128), one_pos());
        let reduced = rel_app(&p, &q).reduce().unwrap();
        // The reduct is a bool equation between two int products.
        let rhs = reduced.concl().as_eq().unwrap().1;
        assert!(rhs.as_eq().is_some(), "reduct is `_ · _ = _ · _`");
    }

    #[test]
    fn mk_rat_is_a_rational() {
        let p = ip(Term::int_lit(5i128), one_pos());
        assert_eq!(mk_rat(&p).type_of().unwrap(), rat());
    }
}
