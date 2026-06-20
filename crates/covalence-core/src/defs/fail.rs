//! `fail : 'a` — the unspecified / "don't care" value of any type,
//! defined `fail ≔ ε(λx. T)`.
//!
//! **Source of truth: [`core.cov`](super::cov).** The body is the
//! `(#def fail (#sel (x 'a) T))` directive; the accessors below are thin
//! lookups into [`super::cov::core_env`].
//!
//! `ε(λx:α. T)` is Hilbert choice over the always-true predicate: for
//! an inhabited `α` it denotes *some* element, with no commitment to
//! which one. It is the canonical result for partial operations on the
//! branch where there is no meaningful answer — e.g. `option.unwrap`
//! of `none`. Naming it `fail` gives those definitions a readable form
//! instead of an inline `ε`.

use crate::term::{Term, Type};

use super::cov::core_env;
use super::spec::TermSpec;

/// `fail : 'a` ≡ `ε(λx. T)` — the unspecified value of `'a`. Used as
/// the "no meaningful answer" result of partial operations (e.g.
/// `option.unwrap none`).
pub fn fail_spec() -> TermSpec {
    core_env()
        .term_spec("fail")
        .expect("core.cov must define `fail`")
        .clone()
}

/// `fail α : α` — an arbitrary inhabitant of `α`.
pub fn fail(alpha: Type) -> Term {
    Term::term_spec(fail_spec(), vec![alpha])
}
