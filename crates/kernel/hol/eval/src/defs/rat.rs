//! `rat := (int × int.pos) / ~` and the `ratLe` order constant.
//!
//! A pair `(a, b) : int × int.pos` represents the rational `a / b`,
//! with the denominator drawn from [`int.pos`](super::int::int_pos_ty)
//! — the strictly-positive integers — so it is **always nonzero**
//! (no `x/0` to collapse, no base to carve) and canonically positive,
//! which also fixes sign handling for the order. Pairs are identified
//! by cross-multiplication:
//!
//! ```text
//!     (a, b) ~ (c, d)  ⟺  a · d = c · b
//! ```
//!
//! built from `fst`/`snd` on `prod int int.pos`, the `int.pos → int`
//! representation coercion (`rep`), and `int.mul`. The carrier of the
//! quotient is `(prod int int.pos) → bool` (a class is the set of
//! equivalent numerator/denominator pairs).
//!
//! `ratLe : rat → rat → bool` is the order on rationals, declaration-
//! only at the kernel level: a representative-based body
//! (`a · d ≤ c · b`, valid because denominators are positive) is a
//! straightforward follow-up, but the order axioms are proved
//! downstream. It lives here because it is needed to define
//! `real := close rat ratLe` (Dedekind cuts).

use std::sync::LazyLock;

use covalence_core::hol;
use covalence_core::term::{Term, Type};

use crate::defs::Canonical;
use crate::defs::{TermSpec, TypeSpec};
use crate::defs::{fst, prod, snd};
use crate::defs::{int_mul, int_pos_spec, int_pos_ty};

/// `int × int.pos` — the numerator/denominator carrier.
fn ip_pair() -> Type {
    prod(Type::int(), int_pos_ty())
}

/// `fst p : int` — the numerator of a representative pair.
fn num(p: Term) -> Term {
    Term::app(fst(Type::int(), int_pos_ty()), p)
}

/// `rep (snd p) : int` — the (positive) denominator of a representative
/// pair, coerced from `int.pos` down to its underlying `int`.
fn den(p: Term) -> Term {
    let d_pos = Term::app(snd(Type::int(), int_pos_ty()), p);
    let rep = Term::spec_rep(int_pos_spec(), Vec::new());
    Term::app(rep, d_pos)
}

/// `λp q. num p · den q = num q · den p` — cross-multiplication
/// `(a, b) ~ (c, d) ⟺ a·d = c·b`.
fn rat_rel() -> Term {
    let pair_ty = ip_pair();
    let p = Term::free("p", pair_ty.clone());
    let q = Term::free("q", pair_ty.clone());
    let lhs = Term::app(Term::app(int_mul(), num(p.clone())), den(q.clone()));
    let rhs = Term::app(Term::app(int_mul(), num(q)), den(p));
    let eq = hol::hol_eq(lhs, rhs);
    hol::pub_abs("p", pair_ty.clone(), hol::pub_abs("q", pair_ty, eq))
}

/// `rat := (int × int.pos) / ~` — the rationals as numerator/denominator
/// pairs (positive denominator) modulo cross-multiplication.
pub fn rat_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| TypeSpec::quot(Canonical::Rat, ip_pair(), rat_rel()));
    LAZY.clone()
}
pub fn rat_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(rat_spec(), vec![]));
    LAZY.clone()
}

/// `ratLe : rat → rat → bool` — the order on `rat`. Declaration-only
/// (see module docs); used as the cutting relation in
/// `real := { rat } close ratLe`.
pub fn rat_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let ty = Type::fun(rat_ty(), Type::fun(rat_ty(), Type::bool()));
        TermSpec::new(Canonical::RatLe, Some(ty), None)
    });
    LAZY.clone()
}
/// `ratLe : rat → rat → bool`.
pub fn rat_le() -> Term {
    Term::term_spec(rat_le_spec(), vec![])
}
