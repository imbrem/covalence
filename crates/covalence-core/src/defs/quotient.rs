//! `close` and `quot` type constructors — both subtypes of the
//! powerset `base → bool`.
//!
//! - [`TypeSpec::close`] `base rel` is the type of **non-empty,
//!   `rel`-upward-closed subsets** of `base`. Dedekind cuts use it
//!   directly (`real := close rat (≤)`).
//! - [`TypeSpec::quot`] `base rel` is the **quotient** `base / rel`:
//!   its equivalence classes are exactly the `close`-sets of the
//!   *symmetric closure* of `rel`. So `quot = close ∘ symmetric-closure`.
//!
//! Both bottom out in [`TypeSpec::subtype`] of `base → bool`.

use crate::hol;
use crate::term::{Term, Type};

use super::spec::TypeSpec;
use super::symbol::Symbol;

/// `λS:base→bool. (∀x y. rel x y ⟹ S x ⟹ S y) ∧ (∃x. S x)` — selects
/// the non-empty subsets of `base` upward-closed under `rel`.
fn close_predicate(base: Type, rel: Term) -> Term {
    let powerset = Type::fun(base.clone(), Type::bool());
    let s = Term::free("S", powerset.clone());

    let x = Term::free("x", base.clone());
    let y = Term::free("y", base.clone());
    let s_x = Term::app(s.clone(), x.clone());
    let s_y = Term::app(s.clone(), y.clone());
    let rel_xy = Term::app(Term::app(rel, x.clone()), y.clone());
    let closed_imp = hol::hol_imp(rel_xy, hol::hol_imp(s_x, s_y));
    let inner = hol::hol_forall("y", base.clone(), closed_imp);
    let closed_part = hol::hol_forall("x", base.clone(), inner);

    let x2 = Term::free("x", base.clone());
    let nonempty_part = hol::hol_exists("x", base.clone(), Term::app(s.clone(), x2));

    hol::pub_abs("S", powerset, hol::hol_and(closed_part, nonempty_part))
}

impl TypeSpec {
    /// `close base rel` — the type of non-empty subsets of `base`
    /// upward-closed under `rel : base → base → bool`; a subtype of
    /// the powerset `base → bool`.
    pub fn close<S: Symbol>(symbol: S, base: Type, rel: Term) -> Self {
        let powerset = Type::fun(base.clone(), Type::bool());
        TypeSpec::subtype(symbol, powerset, close_predicate(base, rel))
    }

    /// `quot base rel` — the quotient of `base` by the relation
    /// `rel : base → base → bool`. Defined as [`TypeSpec::close`] of
    /// the symmetric closure `λx y. rel x y ∨ rel y x`, so a plain
    /// pre-order or partial relation still yields the right classes.
    pub fn quot<S: Symbol>(symbol: S, base: Type, rel: Term) -> Self {
        let x = Term::free("x", base.clone());
        let y = Term::free("y", base.clone());
        let rxy = Term::app(Term::app(rel.clone(), x.clone()), y.clone());
        let ryx = Term::app(Term::app(rel, y.clone()), x.clone());
        let sym_rel = hol::pub_abs(
            "x",
            base.clone(),
            hol::pub_abs("y", base.clone(), hol::hol_or(rxy, ryx)),
        );
        TypeSpec::close(symbol, base, sym_rel)
    }
}
