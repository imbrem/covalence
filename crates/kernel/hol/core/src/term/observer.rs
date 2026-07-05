//! Observer infrastructure: traits and the type-erased `Object` handle.
//!
//! `TermKind::Obs { observer: Object, ty: Type }` is the only term
//! leaf that carries oracle-supplied data. The kernel never sees the
//! observer's concrete type: it holds a type-erased [`Object`] and
//! compares Obs leaves by **`Arc` pointer identity** — never by
//! calling user-supplied `Eq`/`Hash`/`Ord` impls. This means a
//! misbehaving observer cannot corrupt the kernel's `BTreeSet<Term>`
//! invariants or otherwise compromise soundness.
//!
//! The observer *rules* (`obs_eq`/`obs_true`/`obs_imp`) and their
//! policy traits were deleted in the toHOL purge. `Obs` leaves remain
//! solely as `new_type_definition`'s freshness/unforgeability tokens
//! (allocated inside `NewTypeDefRule::decide`).

use std::any::{Any, TypeId};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Marker trait for types that may be wrapped in [`Object`].
///
/// The bounds are exactly what's needed for a [`Object`] to round-trip
/// safely across threads (`Send + Sync`), survive past stack frames
/// (`'static` via [`Any`]), and be printed in error messages
/// (`Debug`). Any qualifying type automatically becomes an `Observer`
/// via the blanket impl below.
///
/// Crucially, the kernel never calls user-supplied `Eq`/`Ord`/`Hash`
/// methods on an `Observer` — `Object` uses `Arc` pointer identity for
/// all comparisons. So a misbehaving observer impl cannot break the
/// kernel.
pub trait Observer: Any + Send + Sync + fmt::Debug {}
impl<T: Any + Send + Sync + fmt::Debug> Observer for T {}

/// Type-erased observer leaf. Wraps any `O: Observer` inside an `Arc`,
/// and compares / hashes / orders by the `Arc`'s data-pointer
/// identity. Use [`Object::new`] to wrap, [`Object::downcast`] to
/// recover a typed reference.
///
/// Pointer-identity semantics: two distinct `Object::new(o)` calls
/// produce distinct values *even if `o` is identical between calls*.
/// To share an observation across multiple terms, construct it once
/// via `Term::obs` and clone the resulting `Term` (the clone shares
/// the `Arc` and so shares the observation identity).
pub struct Object {
    /// The underlying observer, type-erased through `Any`. We store
    /// `Arc<dyn Any + Send + Sync>` directly (rather than wrapping in
    /// a custom trait) so that `Arc::downcast` works directly and
    /// `Any::downcast_ref` has the right vtable.
    inner: Arc<dyn Any + Send + Sync>,
    /// Hand-rolled vtable for `Debug` — `dyn Any` doesn't carry it.
    debug_fn: fn(&dyn Any, &mut fmt::Formatter<'_>) -> fmt::Result,
}

impl Object {
    /// Wrap any [`Observer`] in a `Object`. Allocates a new `Arc`;
    /// two calls with identical inputs produce distinct `Object`
    /// values.
    pub fn new<O: Observer>(o: O) -> Self {
        Object {
            inner: Arc::new(o),
            debug_fn: |any, f| {
                let o = any
                    .downcast_ref::<O>()
                    .expect("Object debug_fn: type id matches at construction");
                fmt::Debug::fmt(o, f)
            },
        }
    }

    /// Try to recover the underlying `O` by reference. Returns
    /// `None` if the dynamic type does not match.
    pub fn downcast<O: Observer>(&self) -> Option<&O> {
        self.inner.downcast_ref::<O>()
    }

    /// The runtime type identity of the wrapped observer.
    pub fn type_id(&self) -> TypeId {
        (*self.inner).type_id()
    }

    /// Stable pointer identity of the underlying `Arc`. Useful as a
    /// disambiguator in display output and as a cache key for
    /// outside-the-TCB walkers.
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.inner) as *const () as usize
    }
}

impl Clone for Object {
    fn clone(&self) -> Self {
        Object {
            inner: Arc::clone(&self.inner),
            debug_fn: self.debug_fn,
        }
    }
}

/// **`Arc` pointer identity** — never the user's `Eq`.
impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}
impl Eq for Object {}

/// **`Arc` pointer ordering** — never the user's `Ord`. Two distinct
/// `Object` instances may compare in any order, but the ordering is
/// stable for the lifetime of the `Arc`s.
impl Ord for Object {
    fn cmp(&self, other: &Self) -> Ordering {
        let a = Arc::as_ptr(&self.inner) as *const () as usize;
        let b = Arc::as_ptr(&other.inner) as *const () as usize;
        a.cmp(&b)
    }
}
impl PartialOrd for Object {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// **`Arc` pointer hash** — never the user's `Hash`.
impl Hash for Object {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.inner) as *const () as usize).hash(state);
    }
}

impl fmt::Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Object(")?;
        (self.debug_fn)(&*self.inner, f)?;
        write!(f, ")")
    }
}
