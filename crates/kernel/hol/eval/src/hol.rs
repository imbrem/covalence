//! HOL term-builder helpers — the **untrusted** public home (stage A3).
//!
//! The primitive-atom builders (`hol_eq` / `hol_eq_at` / `pub_abs` /
//! `zero`) still live in `covalence_core::hol` (the kernel rules state
//! their equation conclusions with them) and are re-exported here; the
//! **defined-connective** builders below moved OUT of core: they apply
//! the `defs::logic` catalogue specs (`⟹` / `∧` / `∨` / `¬` / `∃` /
//! `∀`), so their public home is the eval catalogue, next to the
//! definitions downstream code unfolds. (Core keeps `pub(crate)` copies
//! in `covalence-core::defs::logic` for the D3 residue bodies and the
//! two staying connective-built rules — that residue dies with the
//! literal leaves.)
//!
//! Building terms mints nothing; there is no trust here.

use covalence_core::{Term, Type};

use crate::defs;

pub use covalence_core::hol::{hol_eq, hol_eq_at, pub_abs, zero};

/// HOL `p ⟹ q : bool` — `imp` applied to `p` and `q`.
pub fn hol_imp(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::imp(), p), q)
}

/// HOL `p ∧ q : bool`.
pub fn hol_and(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::and(), p), q)
}

/// HOL `p ∨ q : bool`.
pub fn hol_or(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::or(), p), q)
}

/// HOL `¬ p : bool` — `not` applied to `p`.
pub fn hol_not(p: Term) -> Term {
    Term::app(defs::not(), p)
}

/// HOL `∃x:α. body[x]` — `exists[α] (λx:α. body[Bound 0])`.
pub fn hol_exists(hint: &str, alpha: Type, body: Term) -> Term {
    Term::app(defs::exists(alpha.clone()), pub_abs(hint, alpha, body))
}

/// HOL `∀` at `(α → bool) → bool` — the `forall` spec at `α`.
pub fn forall_at(alpha: Type) -> Term {
    defs::forall(alpha)
}

/// HOL `∀x:α. body[x]` — `forall[α] (λx:α. body[Bound 0])`. The free
/// variable `Free(hint, α)` in `body` is closed into `Bound(0)`.
pub fn hol_forall(hint: &str, alpha: Type, body: Term) -> Term {
    Term::app(forall_at(alpha.clone()), pub_abs(hint, alpha, body))
}
