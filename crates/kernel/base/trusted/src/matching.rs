//! Static "view as an application" ([`MatchApp`]) and the generic-method rewrite
//! rule ([`Rewrite`] / [`apply_rewrite`]).
//!
//! [`MatchApp`] is a **sealed** (via its `Expr` supertrait), **untrusted** companion
//! trait: `as_app` returns `Ok` *only* for a real [`App`], and is `Err(self)` for
//! every other shape. It never mints — it is a zero-alloc pattern-match facility a
//! rule uses to decide whether to fire. Coverage is **total** over every `Sized`
//! `Expr` shape (each a blanket, so there is no orphan gap and a downstream type
//! cannot sneak in a lying `AsApp`); the unsized `dyn Expr<Ty=T>` cannot impl it
//! (`Sized` unsatisfiable) and a bare `dyn` value never exists, so no gap there.
//!
//! [`apply_rewrite`] is a **minting site**: after gating on the rewrite rule's own
//! `TypeId` it calls the untrusted `Rewrite::rewrite` (which only *proposes* a
//! right-hand side) and blesses the result through the single `Eqn::new` choke
//! point. One `TypeId` (the rule's) gates the rule at *all* expression shapes.

use core::convert::Infallible;
use std::any::TypeId;
use std::rc::Rc;
use std::sync::Arc;

use crate::eqn::{Eqn, Error, Thm};
use crate::expr::{App, Dyn, Expr, False, Ref, True, TrustedDeref, Val};
use crate::lang::Language;
use crate::op::Op;

/// Static "view as an application `App<F, A>`" — the zero-alloc happy path for a
/// structural rule. `AsApp` is `App<F, A>` for an application and [`Infallible`]
/// otherwise; `as_app` returns `Ok` **only** for a real application.
pub trait MatchApp: Expr + Sized {
    /// The application shape recovered on a hit (`App<F, A>`), or [`Infallible`].
    type AsApp;
    /// Consume and view as an application: `Ok` only for a real [`App`], else the
    /// value is handed back unchanged as `Err(self)`. (Takes `self` by value on
    /// purpose — a miss returns ownership via `Err(self)`, no clone.)
    #[allow(clippy::wrong_self_convention)]
    fn as_app(self) -> Result<Self::AsApp, Self>;
}

// The one hit: a real application views as itself.
impl<F: Op, A: Expr<Ty = F::In>> MatchApp for App<F, A> {
    type AsApp = App<F, A>;
    fn as_app(self) -> Result<Self, Self> {
        Ok(self)
    }
}

// ---- Total coverage of the remaining Sized shapes (all misses) ----

/// A miss impl for a monomorphic shape.
macro_rules! no_app {
    ($ty:ty) => {
        impl MatchApp for $ty {
            type AsApp = Infallible;
            fn as_app(self) -> Result<Infallible, Self> {
                Err(self)
            }
        }
    };
}
no_app!(True);
no_app!(False);

impl<C> MatchApp for Val<C> {
    type AsApp = Infallible;
    fn as_app(self) -> Result<Infallible, Self> {
        Err(self)
    }
}
impl<P: TrustedDeref> MatchApp for Ref<P>
where
    P::Target: Sized,
{
    type AsApp = Infallible;
    fn as_app(self) -> Result<Infallible, Self> {
        Err(self)
    }
}
impl<A: Expr + ?Sized> MatchApp for &A {
    type AsApp = Infallible;
    fn as_app(self) -> Result<Infallible, Self> {
        Err(self)
    }
}
// The equality proposition `Eqn<A, B>` is a bool expression, never a top-level App.
impl<A: Expr, B: Expr<Ty = A::Ty>> MatchApp for Eqn<A, B> {
    type AsApp = Infallible;
    fn as_app(self) -> Result<Infallible, Self> {
        Err(self)
    }
}

// Pointers to any expr (`Box`/`Rc`/`Arc<A>`, concrete or `dyn`) — misses (a
// pointer to an application is not itself a top-level `App`).
macro_rules! no_app_ptr {
    ($p:ident) => {
        impl<A: Expr + ?Sized> MatchApp for $p<A> {
            type AsApp = Infallible;
            fn as_app(self) -> Result<Infallible, Self> {
                Err(self)
            }
        }
    };
}
no_app_ptr!(Box);
no_app_ptr!(Rc);
no_app_ptr!(Arc);

// The pointer-equal dynamic operand — a miss.
impl<T> MatchApp for Dyn<T> {
    type AsApp = Infallible;
    fn as_app(self) -> Result<Infallible, Self> {
        Err(self)
    }
}

// Tuples 2..=12 — product expressions, all misses.
macro_rules! no_app_tuple {
    ($($T:ident),+) => {
        impl<$($T: Expr),+> MatchApp for ($($T,)+) {
            type AsApp = Infallible;
            fn as_app(self) -> Result<Infallible, Self> {
                Err(self)
            }
        }
    };
}
no_app_tuple!(A, B);
no_app_tuple!(A, B, C);
no_app_tuple!(A, B, C, D);
no_app_tuple!(A, B, C, D, E);
no_app_tuple!(A, B, C, D, E, F);
no_app_tuple!(A, B, C, D, E, F, G);
no_app_tuple!(A, B, C, D, E, F, G, H);
no_app_tuple!(A, B, C, D, E, F, G, H, I);
no_app_tuple!(A, B, C, D, E, F, G, H, I, J);
no_app_tuple!(A, B, C, D, E, F, G, H, I, J, K);
no_app_tuple!(A, B, C, D, E, F, G, H, I, J, K, L);

/// A generic-method rewrite rule: one rule that inspects *any* `E: MatchApp` and
/// proposes a (shape-erased) right-hand side. UNTRUSTED — it only proposes; the
/// single gated mint is in [`apply_rewrite`].
///
/// The right-hand side is `Box<dyn Expr<Ty = E::Ty>>` because a generic method
/// cannot name a *shaped* right-hand side. `E: Clone + 'static` (a minimal, sound
/// tightening of the blueprint's `E: MatchApp`) lets an implementation keep the
/// original expression as the left-hand side while boxing an owned right-hand side
/// — both are needed for an `a = b` conclusion, and neither is expressible without
/// owning/duplicating `e`. It only restricts *which* expressions a rewrite accepts;
/// the mint stays gated, so soundness is unaffected.
pub trait Rewrite<L>: 'static {
    /// Inspect `e` and the read-only language, proposing `(lhs, rhs)`.
    fn rewrite<E: MatchApp + Clone + 'static>(
        &self,
        e: E,
        lang: &L,
    ) -> Result<(E, Box<dyn Expr<Ty = E::Ty>>), Error>;
}

/// Apply a [`Rewrite`] rule to an expression, gated on the rule's **own `TypeId`**
/// (one identity for *all* `E`). Sound: the untrusted `rewrite` only proposes; the
/// result is blessed through the single `Eqn::new` choke point exactly when the
/// rule is admitted.
pub fn apply_rewrite<L: Language, R: Rewrite<L>, E: MatchApp + Clone + 'static>(
    lang: L,
    r: R,
    e: E,
) -> Result<Thm<L, Eqn<E, Box<dyn Expr<Ty = E::Ty>>>>, Error> {
    let id = TypeId::of::<R>();
    if !lang.admits(id) {
        return Err(Error::NotAdmitted(id));
    }
    let (lhs, rhs) = r.rewrite(e, &lang)?;
    Ok(Thm::new(lang, Eqn(lhs, rhs)))
}
