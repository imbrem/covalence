//! `fail : 'a` — the unspecified / "don't care" value of any type,
//! defined `fail ≔ ε(λx. T)`.
//!
//! `ε(λx:α. T)` is Hilbert choice over the always-true predicate: for
//! an inhabited `α` it denotes *some* element, with no commitment to
//! which one. It is the canonical result for partial operations on the
//! branch where there is no meaningful answer — e.g. `option.unwrap`
//! of `none`. Naming it `fail` gives those definitions a readable form
//! instead of an inline `ε`.

use crate::term::{Term, Type};

use super::canonical::Canonical;

/// `ε(λx:'a. T)` — an arbitrary inhabitant of `'a`.
fn fail_body() -> Term {
    let alpha = Type::tfree("a");
    let pred = Term::abs(alpha.clone(), Term::bool_lit(true));
    Term::app(Term::select_op(alpha), pred)
}

poly_let_term! {
    /// `fail : 'a` ≡ `ε(λx. T)` — the unspecified value of `'a`. Used
    /// as the "no meaningful answer" result of partial operations
    /// (e.g. `option.unwrap none`).
    fail_spec, fail(alpha), Canonical::Fail, fail_body()
}
