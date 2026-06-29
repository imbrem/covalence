//! Statements and their (optional) views.
//!
//! Statement-ness itself is the marker [`IsStmt<S, P>`], implemented by the
//! **context** `K`: it says "context `K` admits the statement representation `S`
//! (asserting prop `P`)", and it is what gates construction of `MThm<K, P, S>`.
//! Only `K` decides which representations it can form. Right now the sole one is
//! the canonical [`Stmt`] struct (blanket below); later a context may admit
//! richer `S` — content-addressed, arena-indexed, Nat-literal, *erasing*, … —
//! and mint / cast them.
//!
//! Whether a statement *exposes* its context or proposition is a separate,
//! **optional** matter: [`GetCtx<K>`], [`GetProp<P>`], [`IntoParts<K, P>`] are
//! capabilities a representation may or may not provide. The canonical `Stmt`
//! provides all three; a statement that *erases* its context would omit
//! [`GetCtx`]. `GetProp` is parameterized by `P` (not associated) on purpose: one
//! carrier may expose several prop views, which is how `P ⟺ Q` arises.

use std::{ops::Deref, rc::Rc, sync::Arc};

use super::{MThm, Stmt};

/// Marker: context `K` admits the statement representation `S` (asserting prop
/// `P`). Gates construction of `MThm<K, P, S>` — only `K` decides what it forms.
pub trait IsStmt<S: ?Sized, P> {}

/// Every context admits the canonical [`Stmt`] statement.
impl<K, P> IsStmt<Stmt<K, P>, P> for K {}

// If a context admits a statement `S`, it also admits `S` behind a faithful
// pointer — the representation is the same, just shared / borrowed / boxed.
impl<K, S: ?Sized, P> IsStmt<Box<S>, P> for K where K: IsStmt<S, P> {}
impl<K, S: ?Sized, P> IsStmt<Rc<S>, P> for K where K: IsStmt<S, P> {}
impl<K, S: ?Sized, P> IsStmt<Arc<S>, P> for K where K: IsStmt<S, P> {}
impl<'a, K, S: ?Sized, P> IsStmt<&'a S, P> for K where K: IsStmt<S, P> {}

/// *Optional* capability: borrow the context of a statement. A statement that
/// erases its context simply does not implement this.
pub trait GetCtx<K: ?Sized> {
    fn get_ctx(&self) -> &K;
}

/// *Optional* capability: borrow a proposition view of a statement. A carrier
/// may implement it for several `P` — each a view of the same statement, which
/// is how `P ⟺ Q` is realized.
pub trait GetProp<P: ?Sized> {
    fn get_prop(&self) -> &P;
}

/// *Optional* capability: take ownership of the canonical `(K, P)` form. Owning
/// carriers move; borrowed / shared ones clone.
pub trait IntoParts<K, P> {
    fn into_parts(self) -> (K, P);
}

// === Canonical implementor: the `Stmt` struct provides every capability ===

impl<K, P> GetCtx<K> for Stmt<K, P> {
    fn get_ctx(&self) -> &K {
        &self.ctx
    }
}

impl<K, P> GetProp<P> for Stmt<K, P> {
    fn get_prop(&self) -> &P {
        &self.prop
    }
}

impl<K, P> IntoParts<K, P> for Stmt<K, P> {
    fn into_parts(self) -> (K, P) {
        (self.ctx, self.prop)
    }
}

// === Forward the read capabilities through references and shared pointers ===

macro_rules! forward_views {
    ($($ty:ty),* $(,)?) => {$(
        impl<'a, K: ?Sized, S: GetCtx<K> + ?Sized> GetCtx<K> for $ty {
            fn get_ctx(&self) -> &K {
                (**self).get_ctx()
            }
        }
        impl<'a, P: ?Sized, S: GetProp<P> + ?Sized> GetProp<P> for $ty {
            fn get_prop(&self) -> &P {
                (**self).get_prop()
            }
        }
    )*};
}

forward_views!(&'a S, &'a mut S);

macro_rules! forward_views_owned {
    ($($ptr:ident),* $(,)?) => {$(
        impl<K: ?Sized, S: GetCtx<K> + ?Sized> GetCtx<K> for $ptr<S> {
            fn get_ctx(&self) -> &K {
                (**self).get_ctx()
            }
        }
        impl<P: ?Sized, S: GetProp<P> + ?Sized> GetProp<P> for $ptr<S> {
            fn get_prop(&self) -> &P {
                (**self).get_prop()
            }
        }
    )*};
}

forward_views_owned!(Box, Rc, Arc);

// === Owned `(K, P)`: move through `Box`, clone through borrowed / shared ===

impl<K, P, S: IntoParts<K, P>> IntoParts<K, P> for Box<S> {
    fn into_parts(self) -> (K, P) {
        (*self).into_parts()
    }
}

impl<K: Clone, P: Clone, S: GetCtx<K> + GetProp<P> + ?Sized> IntoParts<K, P> for &S {
    fn into_parts(self) -> (K, P) {
        (self.get_ctx().clone(), self.get_prop().clone())
    }
}

impl<K: Clone, P: Clone, S: GetCtx<K> + GetProp<P> + ?Sized> IntoParts<K, P> for Arc<S> {
    fn into_parts(self) -> (K, P) {
        (self.get_ctx().clone(), self.get_prop().clone())
    }
}

impl<K: Clone, P: Clone, S: GetCtx<K> + GetProp<P> + ?Sized> IntoParts<K, P> for Rc<S> {
    fn into_parts(self) -> (K, P) {
        (self.get_ctx().clone(), self.get_prop().clone())
    }
}

// === Move a theorem's statement between representations (the gate is still
// `MThm::new`, so every result is admitted by the context) ===

impl<K, P, S> MThm<K, P, S> {
    /// Box the statement representation: `MThm<K, P, S>` → `MThm<K, P, Box<S>>`.
    pub fn box_stmt(self) -> MThm<K, P, Box<S>>
    where
        K: IsStmt<S, P>,
    {
        MThm::new(Box::new(self.0))
    }

    /// Share the statement representation: `MThm<K, P, S>` → `MThm<K, P, Arc<S>>`.
    pub fn arc_stmt(self) -> MThm<K, P, Arc<S>>
    where
        K: IsStmt<S, P>,
    {
        MThm::new(Arc::new(self.0))
    }

    /// Share the statement representation: `MThm<K, P, S>` → `MThm<K, P, Rc<S>>`.
    pub fn rc_stmt(self) -> MThm<K, P, Rc<S>>
    where
        K: IsStmt<S, P>,
    {
        MThm::new(Rc::new(self.0))
    }

    /// Borrow the inner statement behind a pointer representation as a `&S`
    /// theorem (no copy). Works for `Box`/`Arc`/`Rc`/`&` statements.
    pub fn deref_stmt<S2: ?Sized>(&self) -> MThm<K, P, &S2>
    where
        S: Deref<Target = S2>,
        K: IsStmt<S2, P>,
    {
        MThm::new(&*self.0)
    }
}

impl<K, P, S> MThm<K, P, Box<S>> {
    /// Unbox the statement (moves it out): `MThm<K, P, Box<S>>` → `MThm<K, P, S>`.
    pub fn unbox_stmt(self) -> MThm<K, P, S>
    where
        K: IsStmt<S, P>,
    {
        MThm::new(*self.0)
    }
}

impl<K, P, S: Clone> MThm<K, P, Arc<S>> {
    /// Extract the statement from the `Arc` (moves if uniquely held, else clones).
    pub fn unarc_stmt(self) -> MThm<K, P, S>
    where
        K: IsStmt<S, P>,
    {
        MThm::new(Arc::unwrap_or_clone(self.0))
    }
}

impl<K, P, S: Clone> MThm<K, P, Rc<S>> {
    /// Extract the statement from the `Rc` (moves if uniquely held, else clones).
    pub fn unrc_stmt(self) -> MThm<K, P, S>
    where
        K: IsStmt<S, P>,
    {
        MThm::new(Rc::unwrap_or_clone(self.0))
    }
}
