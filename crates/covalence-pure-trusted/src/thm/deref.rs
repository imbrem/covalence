//! Pointer support: faithful-deref wrapping/unwrapping and pointer-equality
//! transport for [`MThm`].

use std::{ops::Deref, rc::Rc, sync::Arc};

use super::{MThm, Stmt};

/// Read-only access to the underlying statement `S`. There is no `DerefMut`: a
/// `&mut Stmt` would expose `&mut prop` and let a live theorem be overwritten.
impl<K, P, S> Deref for MThm<K, P, S> {
    type Target = S;
    fn deref(&self) -> &S {
        &self.0
    }
}

/// A pointer whose [`Deref`] **faithfully** represents its target: the target is
/// the pointer's *entire* semantic content. So wrapping/unwrapping preserves
/// truth, and pointer-equality implies value-equality.
///
/// Implemented for `Box`/`Arc`/`Rc`/`&`/`Vec` (`Vec<T>` derefs to its `[T]`). A
/// user pointer may opt in **iff** it adds no truth-relevant state beyond its
/// target (implementing it is a TCB assertion, like writing a [`crate::Rule`]).
/// This is the one exception to "a different context type is a different trust
/// domain": `Arc<K>` and `K` are the *same* domain, because the wrap is faithful.
pub trait TrustedDeref: Deref {}

impl<T: ?Sized> TrustedDeref for Box<T> {}
impl<T: ?Sized> TrustedDeref for Arc<T> {}
impl<T: ?Sized> TrustedDeref for Rc<T> {}
impl<T: ?Sized> TrustedDeref for &T {}
// `Vec<T>: Deref<Target = [T]>` — a `TrustedDeref` (so `ptr_subst` compares the
// backing slice), but *not* `TrustedTake`, since `[T]` is unsized and cannot be
// taken by value.
impl<T> TrustedDeref for Vec<T> {}

/// A [`TrustedDeref`] pointer that yields its **owned** target — by *move* where
/// possible (`Box`, or a uniquely-owned `Arc`/`Rc`), else by clone. This is what
/// makes each pointer first-class on unwrap: a `Box<P>` needs no `Clone` bound,
/// and `Arc`/`Rc` avoid the copy when their refcount is 1.
pub trait TrustedTake: TrustedDeref {
    fn take(self) -> Self::Target
    where
        Self: Sized;
}

impl<T> TrustedTake for Box<T> {
    fn take(self) -> T {
        *self
    }
}

impl<T: Clone> TrustedTake for Arc<T> {
    fn take(self) -> T {
        Arc::unwrap_or_clone(self)
    }
}

impl<T: Clone> TrustedTake for Rc<T> {
    fn take(self) -> T {
        Rc::unwrap_or_clone(self)
    }
}

impl<T: Clone> TrustedTake for &T {
    fn take(self) -> T {
        (*self).clone()
    }
}

impl<K, P> MThm<K, P> {
    /// Wrap the prop in a faithful owning pointer (`Arc<P>` / `Rc<P>` / `Box<P>`).
    pub fn wrap_prop<W>(self) -> MThm<K, W>
    where
        W: From<P> + TrustedDeref<Target = P>,
    {
        MThm::new(Stmt {
            ctx: self.0.ctx,
            prop: W::from(self.0.prop),
        })
    }

    /// Wrap the context in a faithful owning pointer — `Arc<K>` is the *same*
    /// trust domain as `K`.
    pub fn wrap_ctx<W>(self) -> MThm<W, P>
    where
        W: From<K> + TrustedDeref<Target = K>,
    {
        MThm::new(Stmt {
            ctx: W::from(self.0.ctx),
            prop: self.0.prop,
        })
    }

    /// Pointer-equality transport (positive): if this prop and `target` deref to
    /// the **same allocation**, they are the same value, so re-stamp `target`.
    /// A pointer mismatch returns `self` unchanged — it proves nothing (they may
    /// still be value-equal, just not identical).
    pub fn ptr_subst<Q>(self, target: Q) -> Result<MThm<K, Q>, Self>
    where
        P: TrustedDeref,
        Q: TrustedDeref<Target = P::Target>,
    {
        if std::ptr::eq::<P::Target>(&*self.0.prop, &*target) {
            Ok(MThm::new(Stmt {
                ctx: self.0.ctx,
                prop: target,
            }))
        } else {
            Err(self)
        }
    }
}

impl<K, W: TrustedTake> MThm<K, W>
where
    W::Target: Sized,
{
    /// Unwrap a faithful-pointer prop to its owned target (moves where possible;
    /// see [`TrustedTake`] — a `Box<P>` needs no `Clone`).
    pub fn unwrap_prop(self) -> MThm<K, W::Target> {
        MThm::new(Stmt {
            ctx: self.0.ctx,
            prop: self.0.prop.take(),
        })
    }
}

impl<W: TrustedTake, P> MThm<W, P>
where
    W::Target: Sized,
{
    /// Unwrap a faithful-pointer context to its owned target (moves where
    /// possible; see [`TrustedTake`]).
    pub fn unwrap_ctx(self) -> MThm<W::Target, P> {
        MThm::new(Stmt {
            ctx: self.0.ctx.take(),
            prop: self.0.prop,
        })
    }
}
