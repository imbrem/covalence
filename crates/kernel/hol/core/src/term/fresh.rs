//! `FreshId` — the kernel's private fresh-identity token.
//!
//! `new_type_definition` needs *unforgeable freshness*: each call must
//! mint a subtype τ and `abs`/`rep` constants that can never collide
//! with those of any other call (otherwise two typedefs' bijection
//! theorems could be glued into a non-conservative fact). The token is
//! a type-erased `Arc` compared by **pointer identity** — never by any
//! user-supplied `Eq`/`Hash`/`Ord` — so the allocator itself is the
//! freshness oracle, exactly like [`super::term::Def`]'s per-`define`
//! `Arc`.
//!
//! `FreshId` values are allocated **only** inside
//! `crate::thm::rules::NewTypeDefRule::decide` ([`FreshId::new`] is
//! `pub(crate)`), and appear in terms/types only inside the opaque
//! [`FreshLeaf`] / [`FreshTyLeaf`] pairings built by the `pub(crate)`
//! constructors [`crate::Term::fresh_const`] /
//! [`crate::Type::fresh_tycon`]. The **token↔type pairing is a
//! structural invariant**: the leaf structs have private fields and no
//! public constructor, so downstream code can *read* the token and its
//! type/args (via the accessors) and *clone* a whole leaf out of a
//! matched `TermKind::FreshConst` / `TypeKind::FreshTyCon`, but can
//! never re-pair a cloned `FreshId` with a *different* type — it can
//! only reconstruct constants the kernel already minted, never a
//! fresh (or forged) one.

use std::any::Any;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::ty::{Type, TypeList};

/// Type-erased fresh-identity token. Wraps a private marker value in
/// an `Arc` and compares / hashes / orders by the `Arc`'s data-pointer
/// identity. Two `FreshId::new` calls — even with identical marker
/// values — produce **distinct** tokens; cloning shares the identity.
pub struct FreshId {
    /// The underlying marker, type-erased through `Any`. Never
    /// inspected by the kernel beyond its pointer identity.
    inner: Arc<dyn Any + Send + Sync>,
    /// Hand-rolled vtable for `Debug` — `dyn Any` doesn't carry it.
    /// Display-only (the typedef `abs`/`rep` name hints).
    debug_fn: fn(&dyn Any, &mut fmt::Formatter<'_>) -> fmt::Result,
}

impl FreshId {
    /// Allocate a fresh token around `marker`. Crate-private: only the
    /// generative kernel rules (`NewTypeDefRule`) may mint identity.
    pub(crate) fn new<M: Any + Send + Sync + fmt::Debug>(marker: M) -> Self {
        FreshId {
            inner: Arc::new(marker),
            debug_fn: |any, f| {
                let m = any
                    .downcast_ref::<M>()
                    .expect("FreshId debug_fn: type id matches at construction");
                fmt::Debug::fmt(m, f)
            },
        }
    }

    /// Stable pointer identity of the underlying `Arc`. Useful as a
    /// disambiguator in display output and as a cache key for
    /// outside-the-TCB walkers.
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.inner) as *const () as usize
    }
}

impl Clone for FreshId {
    fn clone(&self) -> Self {
        FreshId {
            inner: Arc::clone(&self.inner),
            debug_fn: self.debug_fn,
        }
    }
}

/// **`Arc` pointer identity** — never a user `Eq`.
impl PartialEq for FreshId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}
impl Eq for FreshId {}

/// **`Arc` pointer ordering** — never a user `Ord`. Two distinct
/// `FreshId`s may compare in any order, but the ordering is stable for
/// the lifetime of the `Arc`s.
impl Ord for FreshId {
    fn cmp(&self, other: &Self) -> Ordering {
        self.ptr_id().cmp(&other.ptr_id())
    }
}
impl PartialOrd for FreshId {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// **`Arc` pointer hash** — never a user `Hash`.
impl Hash for FreshId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ptr_id().hash(state);
    }
}

impl fmt::Debug for FreshId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.debug_fn)(&*self.inner, f)
    }
}

/// Opaque `(FreshId, Type)` pairing — the payload of
/// `TermKind::FreshConst`. Fields are **private** and the only
/// constructor is `pub(crate)`, so the kernel's token↔type pairing is
/// a structural invariant: downstream code can read (and clone) a leaf
/// out of a matched kind, but can never re-pair a cloned [`FreshId`]
/// with a different [`Type`].
///
/// ```compile_fail
/// use covalence_core::{FreshId, FreshLeaf, Type};
/// fn forge(id: FreshId, ty: Type) -> FreshLeaf {
///     FreshLeaf { id, ty } // ERROR: fields are private
/// }
/// ```
///
/// Equality / ordering / hashing are the derived field-order
/// (`id`, then `ty`) semantics — identical to the former
/// `FreshConst(FreshId, Type)` tuple payload: the token by `Arc`
/// pointer identity, then the type structurally.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FreshLeaf {
    id: FreshId,
    ty: Type,
}

impl FreshLeaf {
    /// Pair a kernel-minted token with its type. Crate-private: only
    /// the kernel (and its type-substitution walkers, which preserve
    /// identity) may build the pairing.
    pub(crate) fn new(id: FreshId, ty: Type) -> Self {
        FreshLeaf { id, ty }
    }

    /// The fresh-identity token (compared by `Arc` pointer identity).
    pub fn id(&self) -> &FreshId {
        &self.id
    }

    /// The type the kernel minted this constant at.
    pub fn ty(&self) -> &Type {
        &self.ty
    }
}

/// Opaque `(FreshId, TypeList)` pairing — the payload of
/// `TypeKind::FreshTyCon`. The type-side mirror of [`FreshLeaf`]:
/// private fields, `pub(crate)` constructor, read-only accessors —
/// so a cloned token can never be re-paired with different args.
///
/// ```compile_fail
/// use covalence_core::{FreshId, FreshTyLeaf, TypeList};
/// fn forge(id: FreshId, args: TypeList) -> FreshTyLeaf {
///     FreshTyLeaf { id, args } // ERROR: fields are private
/// }
/// ```
///
/// Equality / ordering / hashing are the derived field-order
/// (`id`, then `args`) semantics — identical to the former
/// `FreshTyCon(FreshId, TypeList)` tuple payload.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FreshTyLeaf {
    id: FreshId,
    args: TypeList,
}

impl FreshTyLeaf {
    /// Pair a kernel-minted token with its type arguments.
    /// Crate-private — see [`FreshLeaf::new`].
    pub(crate) fn new(id: FreshId, args: TypeList) -> Self {
        FreshTyLeaf { id, args }
    }

    /// The fresh-identity token (compared by `Arc` pointer identity).
    pub fn id(&self) -> &FreshId {
        &self.id
    }

    /// The type arguments the constructor is applied to.
    pub fn args(&self) -> &TypeList {
        &self.args
    }
}
