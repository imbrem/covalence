//! `rat := (int × int) / ~` and the `ratLe` order constant.
//!
//! A pair `(a, b) : int × int` represents the rational `a / b`, and
//! two pairs are identified by cross-multiplication:
//!
//! ```text
//!     (a, b) ~ (c, d)  ⟺  a · d = c · b
//! ```
//!
//! built with `fst`/`snd` on `prod int int` and `intMul`. The carrier
//! of the quotient is `(prod int int) → bool` (a class is the set of
//! equivalent numerator/denominator pairs).
//!
//! ⚠️ Remaining refinement (TODO — `docs/roadmap.md`): the
//! **denominator should be nonzero**. With `b = 0` admitted, `a·0 =
//! c·0` makes every `(a, 0)` equivalent, collapsing all "`x/0`" into a
//! single spurious class. The faithful construction carves the base to
//! `{ (a, b) | b ≠ 0 }` before quotienting (the cross-multiplication
//! relation is then exactly rational equality). The *cross-multiplication
//! relation itself* — the headline correctness fix over the previous
//! placeholder `=` — is in place here; the nonzero-denominator carve is
//! the open item.
//!
//! `ratLe : rat → rat → bool` is the order on rationals. It is
//! declaration-only at the kernel level: a representative-based body
//! (`a·d ≤ c·b`) needs sign-aware denominator normalization (the
//! inequality flips for negative denominators), so the order axioms
//! are proved downstream once `rat` has its nonzero-positive
//! canonical form. It lives here because it is needed to define
//! `real := close rat ratLe` (Dedekind cuts).

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::int::int_mul;
use super::prod::{fst, prod, snd};
use super::spec::{TermSpec, TypeSpec};

/// `int × int` — the numerator/denominator carrier.
fn ii_pair() -> Type {
    prod(Type::int(), Type::int())
}

/// `λp q. fst p * snd q = fst q * snd p` — cross-multiplication
/// `(a, b) ~ (c, d) ⟺ a·d = c·b`.
fn rat_rel() -> Term {
    let pair_ty = ii_pair();
    let p = Term::free("p", pair_ty.clone());
    let q = Term::free("q", pair_ty.clone());
    let fp = Term::app(fst(Type::int(), Type::int()), p.clone());
    let sp = Term::app(snd(Type::int(), Type::int()), p);
    let fq = Term::app(fst(Type::int(), Type::int()), q.clone());
    let sq = Term::app(snd(Type::int(), Type::int()), q);
    // a·d = c·b
    let lhs = Term::app(Term::app(int_mul(), fp), sq);
    let rhs = Term::app(Term::app(int_mul(), fq), sp);
    let eq = hol::hol_eq(lhs, rhs);
    hol::pub_abs("p", pair_ty.clone(), hol::pub_abs("q", pair_ty, eq))
}

/// `rat := (int × int) / ~` — the rationals as numerator/denominator
/// pairs modulo cross-multiplication. (TODO: carve the base to
/// nonzero denominators — see module docs.)
pub fn rat_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| TypeSpec::quot(Canonical::Rat, ii_pair(), rat_rel()));
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
