//! `rat := (int × int⁺) / ~` and the `ratLe` order constant.
//!
//! `rat` is the quotient of numerator/denominator pairs by
//! cross-multiplication: `(a, b)` represents `a / b` and
//! `(a, b) ~ (c, d) ⟺ a*d = c*b`.
//!
//! ⚠️ TODO (broadly-correct shape, not finalized). Two things the real
//! construction must get right, neither captured by the placeholder
//! below:
//!   1. **The denominator must be nonzero.** With zero denominators,
//!      `a*0 = 0*0` makes every `(a, 0)` equivalent, collapsing all
//!      "`x/0`" into one spurious class. Restrict the second component
//!      to `int⁺` (positive ints, which also fixes sign canonicality),
//!      or carve out `b ≠ 0`. `(0, a)` with `a ≠ 0` is fine (it's `0`).
//!   2. The `~` relation here is a placeholder (`=` on pairs); the real
//!      cross-multiplication `a*d = c*b` needs pair projections.
//! The *shape* — a quotient of numerator/denominator pairs — is what
//! matters for now. See the `defs` module docs / `docs/roadmap.md`.
//!
//! `ratLe : rat → rat → bool` is the order on rationals,
//! declaration-only at the kernel level (order axioms are proved
//! downstream). It lives here because it's needed to define
//! `real := close rat ratLe` (Dedekind cuts).

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::prod::prod;
use super::spec::{TermSpec, TypeSpec};

/// `rat := (int × int⁺) / ~` — the rationals as numerator/denominator
/// pairs modulo cross-multiplication. (TODO: the carrier here is
/// `prod int int` and the relation is a placeholder `=`; the real
/// construction restricts the denominator to nonzero — see module docs.)
pub fn rat_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let pair = prod(Type::int(), Type::int());
        let p = Term::free("p", pair.clone());
        let q = Term::free("q", pair.clone());
        let rel = hol::pub_abs(
            "p",
            pair.clone(),
            hol::pub_abs("q", pair.clone(), hol::hol_eq(p, q)),
        );
        TypeSpec::quot(Canonical::Rat, pair, rel)
    });
    LAZY.clone()
}
pub fn rat_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(rat_spec(), vec![]));
    LAZY.clone()
}

/// `ratLe : rat → rat → bool` — the order on `rat`. Declaration-only.
/// Used as the cutting relation in `real := { rat } close ratLe`.
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
