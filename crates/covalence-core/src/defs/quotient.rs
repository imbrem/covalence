//! `close` and `quot` type constructors — both subtypes of the
//! powerset `base → bool`.
//!
//! - [`TypeSpec::close`] `base rel` is the type of **non-empty,
//!   `rel`-upward-closed subsets** of `base`. Dedekind cuts use it
//!   directly (`real := close rat (≤)`).
//! - [`TypeSpec::quot`] `base rel` is the **quotient** `base / rel`:
//!   its elements are exactly the `rel`-equivalence classes, each
//!   represented as the set of its members. The carving predicate is
//!   `λS. ∃z. S = (λy. rel z y)` — `S` is *exactly* one class
//!   (`classOf z`), nothing more. When `rel` is an equivalence relation
//!   those sets are precisely its equivalence classes, with no junk.
//!
//! Both bottom out in [`TypeSpec::subtype`] of `base → bool`.
//!
//! ## Why `quot` is not `close`
//!
//! An earlier version defined `quot = close ∘ symmetric-closure`, i.e.
//! the non-empty subsets upward-closed under `rel`. That is **wrong**:
//! for an equivalence `rel`, every *union* of classes (including the
//! whole carrier) is non-empty and upward-closed, so the type was full
//! of junk that is not a single class. Picking representatives off such
//! junk breaks quotient induction and makes identities like `a + 0 = a`
//! fail. The image predicate below admits a set iff it is `classOf z`
//! for some `z`, so there is exactly one inhabitant per class.

use crate::hol;
use crate::term::{Term, Type};

use super::spec::TypeSpec;
use super::symbol::TrustedSymbol;

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

/// `λy:base. rel z y` — the `rel`-class of `z` as a subset of `base`.
/// `z` must be a free/closed term; the result is the carrier value a
/// quotient element abstracts.
fn class_of(base: &Type, rel: &Term, z: &Term) -> Term {
    let body = Term::app(
        Term::app(rel.clone(), z.clone()),
        Term::free("y", base.clone()),
    );
    hol::pub_abs("y", base.clone(), body)
}

/// `λS:base→bool. ∃z. S = (λy. rel z y)` — selects exactly the sets
/// that are the `rel`-class `classOf z` of some representative `z`.
/// When `rel` is an equivalence relation these are precisely its
/// equivalence classes — no junk (contrast [`close_predicate`], which
/// also admits every *union* of classes).
fn quot_predicate(base: Type, rel: Term) -> Term {
    let powerset = Type::fun(base.clone(), Type::bool());
    let s = Term::free("S", powerset.clone());
    let z = Term::free("z", base.clone());
    // `S = classOf z`, with `z` free (bound by the ∃ below).
    let eq = hol::hol_eq(s, class_of(&base, &rel, &z));
    let exists_z = hol::hol_exists("z", base.clone(), eq);
    hol::pub_abs("S", powerset, exists_z)
}

impl TypeSpec {
    /// `close base rel` — the type of non-empty subsets of `base`
    /// upward-closed under `rel : base → base → bool`; a subtype of
    /// the powerset `base → bool`.
    pub fn close<S: TrustedSymbol>(symbol: S, base: Type, rel: Term) -> Self {
        let powerset = Type::fun(base.clone(), Type::bool());
        TypeSpec::subtype(symbol, powerset, close_predicate(base, rel))
    }

    /// `quot base rel` — the quotient of `base` by the relation
    /// `rel : base → base → bool`. A subtype of the powerset
    /// `base → bool` carved by [`quot_predicate`]: an element is an
    /// equivalence class `classOf z = λy. rel z y` for some
    /// representative `z`. `rel` is expected to be an equivalence
    /// relation (reflexive / symmetric / transitive); only then do the
    /// inhabitants partition `base`.
    pub fn quot<S: TrustedSymbol>(symbol: S, base: Type, rel: Term) -> Self {
        let powerset = Type::fun(base.clone(), Type::bool());
        TypeSpec::subtype(symbol, powerset, quot_predicate(base, rel))
    }
}
