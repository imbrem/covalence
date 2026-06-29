//! The trusted [`Rule`] trait — how a context mints theorems — together with
//! `MThm`'s [`Derive`] impl (the public minting API) and the canonical [`Id`] rule.

use std::convert::Infallible;

use super::{MThm, Stmt};
use crate::Derive;

/// A `covalence-pure` inference rule. `Self` is the **output context** — the
/// orphan rule reserves the impl to `Self`'s crate, so a context controls every
/// theorem minted in it.
///
/// Premises ride inside `R` as real [`MThm`]s (unforgeable, hence genuine); the
/// rule opens them (deref to [`Stmt`], or [`MThm::into_stmt`]) and produces a
/// fresh `(context, prop)`. Untrusted on its own: invoked directly it yields a
/// raw pair — only [`Derive::derive`] (on `MThm`) blesses it into a `MThm`.
pub trait Rule<R, P, E>: Sized {
    fn derive(rule: R) -> Result<(Self, P), E>;
}

/// `MThm`'s minting API: for every rule `R` with `K: Rule<R, P, E>`, run it and
/// bless the result. This impl *is* the public rule surface of `MThm` — there is
/// no separate inherent constructor.
impl<R, K, P, E> Derive<R, K, P, E> for MThm<K, P>
where
    K: Rule<R, P, E>,
{
    fn derive(rule: R) -> Result<Self, E> {
        <K as Rule<R, P, E>>::derive(rule).map(|(ctx, prop)| MThm::new(Stmt { ctx, prop }))
    }
}

/// The identity rule: re-derive a theorem unchanged — the canonical minimal
/// [`Rule`], showing how a rule carries its premise.
/// `<MThm<_, _> as Derive<_, _, _, _>>::derive(Id(t))` ≡ `t`.
pub struct Id<K, P>(pub MThm<K, P>);

impl<K, P> Rule<Id<K, P>, P, Infallible> for K {
    fn derive(Id(thm): Id<K, P>) -> Result<(K, P), Infallible> {
        Ok(thm.into_parts())
    }
}
