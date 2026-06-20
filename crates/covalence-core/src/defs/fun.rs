//! Point-free ("pointless") programming utilities — the basic
//! function combinators `id`, `const`, `compose`, `flip`.
//!
//! **Source of truth: [`core.cov`](super::cov).** These are ordinary
//! let-style definitions (`λ`-bodies over the kernel atoms), polymorphic
//! in the obvious type variables; their bodies live as `(#def fun.xxx
//! …)` directives in `defs/core.cov` and the accessors below are thin
//! lookups into [`super::cov::core_env`]. They give call sites and other
//! definitions a combinator vocabulary instead of spelling out the
//! lambdas each time — e.g. `mk (const F)` for the empty set,
//! `compose g f` for `g ∘ f`.
//!
//! (The term accessor for `fun.const` is spelled [`konst`] because
//! `const` is a Rust keyword; the catalogue label is still
//! `"fun.const"`.)

use crate::term::{Term, Type};

use super::cov::core_env;
use super::spec::TermSpec;

/// Fetch a migrated combinator's `TermSpec` from `core.cov` by label.
fn spec(label: &str) -> TermSpec {
    core_env()
        .term_spec(label)
        .unwrap_or_else(|| panic!("core.cov must define `{label}`"))
        .clone()
}

/// `fun.id : 'a → 'a` ≡ `λx. x` — the identity function.
pub fn id_spec() -> TermSpec {
    spec("fun.id")
}
/// `fun.id α : α → α`.
pub fn id(alpha: Type) -> Term {
    Term::term_spec(id_spec(), vec![alpha])
}

/// `fun.const : 'a → 'b → 'a` ≡ `λx _. x` — the constant function
/// (ignores its second argument).
pub fn konst_spec() -> TermSpec {
    spec("fun.const")
}
/// `fun.const α β : α → β → α`.
pub fn konst(alpha: Type, beta: Type) -> Term {
    Term::term_spec(konst_spec(), vec![alpha, beta])
}

/// `fun.compose : ('b → 'c) → ('a → 'b) → 'a → 'c` ≡
/// `λg f x. g (f x)` — function composition `g ∘ f`.
pub fn compose_spec() -> TermSpec {
    spec("fun.compose")
}
/// `fun.compose α β γ : (β → γ) → (α → β) → α → γ`.
pub fn compose(alpha: Type, beta: Type, gamma: Type) -> Term {
    Term::term_spec(compose_spec(), vec![alpha, beta, gamma])
}

/// `fun.flip : ('a → 'b → 'c) → 'b → 'a → 'c` ≡ `λf y x. f x y` —
/// swap the first two arguments of a binary function.
pub fn flip_spec() -> TermSpec {
    spec("fun.flip")
}
/// `fun.flip α β γ : (α → β → γ) → β → α → γ`.
pub fn flip(alpha: Type, beta: Type, gamma: Type) -> Term {
    Term::term_spec(flip_spec(), vec![alpha, beta, gamma])
}
