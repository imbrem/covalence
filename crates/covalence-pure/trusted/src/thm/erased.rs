//! Type erasure via `dyn Any` pointers, and the pointer-equality fallible union.
//!
//! Erase a context or prop by putting it behind a `dyn Any` pointer; the
//! convenience [`MThm::erase_ctx`] / [`MThm::erase_prop`] target `Arc<dyn Any>`
//! (shared + threadable), but the union below works for `Rc` and `&` too — use
//! whichever you like. Recover the concrete type with the `downcast_*` methods.
//!
//! Erasure is **faithful**: the concrete type id lives in the value, so a `MThm`
//! erased from domain `A` only downcasts back to `A` — type erasure is an
//! existential over domains, never a launder from one into another.
//!
//! Two erased contexts merge ([`TryUnion`]) only when they are the **same
//! allocation** (pointer equality) — the safe default for opaque contexts, since
//! distinct ones can't be soundly merged. Provided for `Arc`/`Rc`/`&`, but *not*
//! `Box`: a `Box` is unique-owned, so two erased contexts are never
//! pointer-equal and the merge would always fail.

use std::{any::Any, rc::Rc, sync::Arc};

use super::{MThm, Stmt, TryUnion};

/// Two contexts could not be merged: they are distinct allocations.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CtxMismatch;

/// Shared (`Arc`) contexts merge iff they are the same allocation.
impl<K: ?Sized> TryUnion<Arc<K>, Arc<K>> for Arc<K> {
    type Err = CtxMismatch;

    fn try_union(lhs: Arc<K>, rhs: Arc<K>) -> Result<Arc<K>, CtxMismatch> {
        if Arc::ptr_eq(&lhs, &rhs) {
            Ok(lhs)
        } else {
            Err(CtxMismatch)
        }
    }
}

/// Shared (`Rc`) contexts merge iff they are the same allocation.
impl<K: ?Sized> TryUnion<Rc<K>, Rc<K>> for Rc<K> {
    type Err = CtxMismatch;

    fn try_union(lhs: Rc<K>, rhs: Rc<K>) -> Result<Rc<K>, CtxMismatch> {
        if Rc::ptr_eq(&lhs, &rhs) {
            Ok(lhs)
        } else {
            Err(CtxMismatch)
        }
    }
}

/// Borrowed contexts merge iff they are the **same reference** — same address
/// *and* metadata (`std::ptr::eq`, not `addr_eq`): two different sub-slices that
/// share a data pointer (`&v[0..3]` vs `&v[0..5]`) are distinct contexts and
/// must not merge.
impl<'a, T: ?Sized> TryUnion<&'a T, &'a T> for &'a T {
    type Err = CtxMismatch;

    fn try_union(lhs: &'a T, rhs: &'a T) -> Result<&'a T, CtxMismatch> {
        if std::ptr::eq(lhs, rhs) {
            Ok(lhs)
        } else {
            Err(CtxMismatch)
        }
    }
}

impl<K: Any, P> MThm<K, P> {
    /// Type-erase the context: `MThm<K, P>` → `MThm<Arc<dyn Any>, P>`.
    pub fn erase_ctx(self) -> MThm<Arc<dyn Any>, P> {
        let Stmt { ctx, prop } = self.0;
        MThm::new(Stmt {
            ctx: Arc::new(ctx),
            prop,
        })
    }
}

impl<K, P: Any> MThm<K, P> {
    /// Type-erase the prop: `MThm<K, P>` → `MThm<K, Arc<dyn Any>>`.
    pub fn erase_prop(self) -> MThm<K, Arc<dyn Any>> {
        let Stmt { ctx, prop } = self.0;
        MThm::new(Stmt {
            ctx,
            prop: Arc::new(prop),
        })
    }
}

impl<K: Any, P: Any> MThm<K, P> {
    /// Type-erase **both** context and prop:
    /// `MThm<K, P>` → `MThm<Arc<dyn Any>, Arc<dyn Any>>`. Recover each independently
    /// (in either order) with [`MThm::downcast_ctx`] / [`MThm::downcast_prop`].
    pub fn erase_both(self) -> MThm<Arc<dyn Any>, Arc<dyn Any>> {
        let Stmt { ctx, prop } = self.0;
        MThm::new(Stmt {
            ctx: Arc::new(ctx),
            prop: Arc::new(prop),
        })
    }
}

impl<P> MThm<Arc<dyn Any>, P> {
    /// Recover the concrete context if it has type `K` (clones out of the `Arc`),
    /// else returns `self`.
    pub fn downcast_ctx<K: Any + Clone>(self) -> Result<MThm<K, P>, Self> {
        let Stmt { ctx, prop } = self.0;
        let recovered = (*ctx).downcast_ref::<K>().cloned();
        match recovered {
            Some(ctx) => Ok(MThm::new(Stmt { ctx, prop })),
            None => Err(MThm::new(Stmt { ctx, prop })),
        }
    }
}

impl<K> MThm<K, Arc<dyn Any>> {
    /// Recover the concrete prop if it has type `P` (clones out of the `Arc`),
    /// else returns `self`.
    pub fn downcast_prop<P: Any + Clone>(self) -> Result<MThm<K, P>, Self> {
        let Stmt { ctx, prop } = self.0;
        let recovered = (*prop).downcast_ref::<P>().cloned();
        match recovered {
            Some(prop) => Ok(MThm::new(Stmt { ctx, prop })),
            None => Err(MThm::new(Stmt { ctx, prop })),
        }
    }
}
