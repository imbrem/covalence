//! A trait for reasoning in a **commutative ring** — a
//! [`Semiring`](crate::semiring::Semiring) with additive inverses.
//!
//! [`Ring`] extends [`Semiring`](crate::semiring::Semiring): a ring is a
//! semiring whose additive monoid is a *group*, so it adds negation `-a`
//! ([`neg`](Ring::neg)), subtraction `a - b` ([`sub`](Ring::sub)), and the
//! two extra axioms that pin them down:
//!
//! - **Additive inverse** — [`add_neg`](Ring::add_neg): `a + (-a) = 0`.
//! - **Subtraction** — [`sub_def`](Ring::sub_def): `a - b = a + (-b)`.
//!
//! Everything else — the additive/multiplicative commutative monoids,
//! distributivity, annihilation — comes from the [`Semiring`] supertrait, so
//! a `Ring` proof object *is* a semiring proof object and the carrier's term
//! theory is shared.
//!
//! ## Embedding
//!
//! [`crate::semiring::Int`] implements [`Ring`] over HOL `int` (the
//! additive-inverse axioms forward to [`crate::init::int`], postulated for
//! now; see `SKELETONS.md`). `nat` is deliberately *not* a `Ring` — it has
//! no additive inverses — so it implements only [`Semiring`]. The future
//! `rat` / `real` carriers will implement `Ring` (and, eventually, `Field`).

pub mod normalize;
pub mod shallow;

pub use normalize::{RingNormalizer, RingOps};

use crate::semiring::Semiring;

/// Reasoning in a commutative ring — a [`Semiring`] with additive inverses.
/// See the [module docs](self).
pub trait Ring: Semiring {
    /// Additive inverse `-a`.
    fn neg(&self, a: Self::Term) -> Self::Term;
    /// Subtraction `a - b`.
    fn sub(&self, a: Self::Term, b: Self::Term) -> Self::Term;

    /// `⊢ ∀a. a + (-a) = 0` — additive inverse.
    fn add_neg(&self) -> Self::Proof;
    /// `⊢ ∀a b. a - b = a + (-b)` — subtraction by negation.
    fn sub_def(&self) -> Self::Proof;
}
