//! The trusted [`Union`] / [`TryUnion`] traits — merging two trust-contexts,
//! infallibly or fallibly — and the `∧`-introductions they power ([`MThm::zip`] /
//! [`MThm::try_zip`]).

use super::{MThm, Stmt};

/// Combine two trust-contexts into `Self` (the context of a [`MThm::zip`]).
///
/// Infallible: implementing `Union<K1, K2>` asserts `K1` and `K2` are
/// unconditionally mergeable into `Self`. If a merge can fail, use [`TryUnion`].
pub trait Union<K1, K2>: Sized {
    fn union(lhs: K1, rhs: K2) -> Self;
}

/// Fallibly combine two trust-contexts (the context of a [`MThm::try_zip`]).
///
/// For contexts that merge only conditionally — notably type-erased contexts
/// (`Arc`/`Rc`/`&` of `dyn Any`), whose default merge is the
/// pointer-equality-or-error impl in the `erased` module.
pub trait TryUnion<K1, K2>: Sized {
    type Err;

    fn try_union(lhs: K1, rhs: K2) -> Result<Self, Self::Err>;
}

impl<K, P> MThm<K, P> {
    /// `∧`-introduction across contexts: [`Union`] the contexts, pair the props.
    pub fn zip<K2, P2, U>(self, other: MThm<K2, P2>) -> MThm<U, (P, P2)>
    where
        U: Union<K, K2>,
    {
        MThm::new(Stmt {
            ctx: U::union(self.0.ctx, other.0.ctx),
            prop: (self.0.prop, other.0.prop),
        })
    }

    /// Fallible [`MThm::zip`]: `∧`-intro across contexts that merge fallibly
    /// ([`TryUnion`]). On failure both theorems are consumed and the error is
    /// returned.
    pub fn try_zip<K2, P2, U>(self, other: MThm<K2, P2>) -> Result<MThm<U, (P, P2)>, U::Err>
    where
        U: TryUnion<K, K2>,
    {
        let Stmt { ctx: c1, prop: p1 } = self.0;
        let Stmt { ctx: c2, prop: p2 } = other.0;
        Ok(MThm::new(Stmt {
            ctx: U::try_union(c1, c2)?,
            prop: (p1, p2),
        }))
    }
}
