//! `cond : bool → 'a → 'a → 'a` — the Boolean conditional
//! (`if b then x else y`).
//!
//! Declaration-only. The kernel commits to the standard
//! semantics:
//!
//! ```text
//!     cond T x y  =  x
//!     cond F x y  =  y
//! ```
//!
//! These reduction equations are postulated downstream in
//! `covalence-hol` (or proved from Hilbert ε once a
//! derivation lands). At the kernel level `cond` is a
//! declaration-only TermSpec: it has a type but no body.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::TermSpec;

/// `cond : bool → 'a → 'a → 'a` — Boolean conditional, declared
/// only (no kernel reduction rule; postulated downstream).
pub fn cond_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        TermSpec::new(
            Canonical::Cond,
            Some(Type::fun(
                Type::bool(),
                Type::fun(alpha.clone(), Type::fun(alpha.clone(), alpha)),
            )),
            None,
        )
    });
    LAZY.clone()
}

/// `cond α : bool → α → α → α`.
pub fn cond(alpha: Type) -> Term {
    Term::term_spec(cond_spec(), vec![alpha])
}
