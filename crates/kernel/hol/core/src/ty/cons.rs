//! Optional **hash-consing of types** — the type-level analogue of
//! [`crate::term::cons`].
//!
//! Types have no bound variables and are always well-formed, so (unlike
//! terms) there is no typedness/closedness to track — type interning is
//! pure structural sharing. The design otherwise mirrors the term side: a
//! sealed [`TrustedTypeCons`] (the kernel trusts the result to be
//! structurally equal to the requested kind) and a public, untrusted
//! [`TypeCons`] that becomes trusted via [`crate::term::Checked`] (the same
//! verifying wrapper works for both terms and types).
//!
//! The default term interner [`crate::term::HashCons`] is *also* a
//! `TrustedTypeCons` (it carries a type interner as a template, default
//! [`TypeHashCons`]), so one constructor threaded through a proof shares
//! both terms and types.

use std::ops::Deref;

use indexmap::IndexSet;

use super::ty::{Type, TypeKind};

pub(crate) mod sealed {
    /// Seals [`super::TrustedTypeCons`] to kernel-blessed implementors.
    pub trait Sealed {}
}

/// **Untrusted** type constructor (public). Mirror of
/// [`crate::term::TermCons`]: offer a `Type` for `kind`, or `None` to defer
/// allocation to the caller. Becomes trusted via [`crate::term::Checked`].
pub trait TypeCons {
    /// Offer a `Type` for `kind`, or `None` to defer. A returned `Some(t)`
    /// *should* be structurally equal to `kind` ([`crate::term::Checked`]
    /// enforces this when used trusted).
    fn cons(&mut self, kind: &TypeKind) -> Option<Type>;
}

impl<C: TypeCons + ?Sized> TypeCons for &mut C {
    fn cons(&mut self, kind: &TypeKind) -> Option<Type> {
        (**self).cons(kind)
    }
}

impl<C: TypeCons + ?Sized> TypeCons for Box<C> {
    fn cons(&mut self, kind: &TypeKind) -> Option<Type> {
        (**self).cons(kind)
    }
}

/// **Trusted, sealed** type constructor.
///
/// `Soundness:` any `Some(t)` returned must be structurally equal to the
/// requested `kind`; `None` is always sound — the caller allocates a fresh
/// `Arc` from `kind`, which is `kind` by construction.
pub trait TrustedTypeCons: sealed::Sealed {
    /// Offer a `Type` for `kind`, or `None` to defer allocation.
    fn cons(&mut self, kind: &TypeKind) -> Option<Type>;

    /// Build a `Type` for `kind`, allocating ourselves when
    /// [`cons`](Self::cons) defers. The entry point the type-building APIs
    /// call.
    fn make(&mut self, kind: TypeKind) -> Type {
        match self.cons(&kind) {
            Some(t) => t,
            None => Type::alloc(kind),
        }
    }
}

// ---- `()` — the no-op (always allocate fresh) ----

impl sealed::Sealed for () {}

impl TrustedTypeCons for () {
    #[inline]
    fn cons(&mut self, _kind: &TypeKind) -> Option<Type> {
        None
    }
}

// ---- `Checked<C>` — make any untrusted `TypeCons` trusted ----
//
// The same `crate::term::Checked` wrapper serves terms and types; here we
// give it the type-side trusted impl (verify-then-keep, else defer).

impl<C: TypeCons + ?Sized> sealed::Sealed for crate::term::Checked<C> {}

impl<C: TypeCons + ?Sized> TrustedTypeCons for crate::term::Checked<C> {
    fn cons(&mut self, kind: &TypeKind) -> Option<Type> {
        self.0.cons(kind).filter(|t| t.kind() == kind)
    }
}

// ---- `TypeHashCons` — the default type interner ----

/// An [`IndexSet`]-backed type interner: returns a shared canonical `Type`
/// for each structurally-distinct kind. Deref exposes the set read-only.
#[derive(Clone, Default)]
pub struct TypeHashCons {
    set: IndexSet<Type>,
}

impl TypeHashCons {
    /// An empty type interner.
    pub fn new() -> Self {
        Self::default()
    }

    /// Consume the interner, returning the underlying set.
    pub fn into_set(self) -> IndexSet<Type> {
        self.set
    }
}

impl Deref for TypeHashCons {
    type Target = IndexSet<Type>;

    fn deref(&self) -> &IndexSet<Type> {
        &self.set
    }
}

impl sealed::Sealed for TypeHashCons {}

impl TrustedTypeCons for TypeHashCons {
    fn cons(&mut self, kind: &TypeKind) -> Option<Type> {
        let t = Type::alloc(kind.clone());
        if let Some(existing) = self.set.get(&t) {
            return Some(existing.clone());
        }
        self.set.insert(t.clone());
        Some(t)
    }
}

// ---- the unified term+type interner: `HashCons` is also a type cons ----

impl<D, T: TrustedTypeCons> sealed::Sealed for crate::term::HashCons<D, T> {}

impl<D, T: TrustedTypeCons> TrustedTypeCons for crate::term::HashCons<D, T> {
    fn cons(&mut self, kind: &TypeKind) -> Option<Type> {
        self.types_mut().cons(kind)
    }
}

// ---- deep interning of a whole type ----

impl Type {
    /// Rebuild this type bottom-up through `cons`, returning a
    /// structurally-equal type. With a [`TypeHashCons`] this **interns**
    /// the whole tree, so equal subtypes — within this type and across
    /// every other type routed through the same interner — come back
    /// `Arc`-shared. Mirror of [`crate::Term::cons_with`].
    pub fn cons_with<C: TrustedTypeCons + ?Sized>(&self, cons: &mut C) -> Type {
        let kind = match self.kind() {
            TypeKind::Fun(a, b) => TypeKind::Fun(a.cons_with(cons), b.cons_with(cons)),
            TypeKind::Tycon(n, args) => TypeKind::Tycon(n.clone(), cons_args(args, cons)),
            TypeKind::FreshTyCon(id, args) => {
                TypeKind::FreshTyCon(id.clone(), cons_args(args, cons))
            }
            TypeKind::Spec(s, args) => TypeKind::Spec(s.clone(), cons_args(args, cons)),
            // TFree / Nat / Bool are leaves.
            other => other.clone(),
        };
        cons.make(kind)
    }
}

/// Deep-intern each argument in a [`crate::TypeList`].
fn cons_args<C: TrustedTypeCons + ?Sized>(
    args: &crate::ty::TypeList,
    cons: &mut C,
) -> crate::ty::TypeList {
    args.iter()
        .map(|a| a.cons_with(cons))
        .collect::<Vec<_>>()
        .into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Checked;

    fn k(name: &str) -> TypeKind {
        TypeKind::TFree(name.into())
    }

    struct Forward;
    impl TypeCons for Forward {
        fn cons(&mut self, kind: &TypeKind) -> Option<Type> {
            Some(Type::alloc(kind.clone()))
        }
    }
    struct Evil;
    impl TypeCons for Evil {
        fn cons(&mut self, _kind: &TypeKind) -> Option<Type> {
            Some(Type::nat())
        }
    }

    #[test]
    fn unit_defers_make_allocates() {
        assert!(().cons(&k("a")).is_none());
        let a = ().make(k("a"));
        let b = ().make(k("a"));
        assert_eq!(a, b);
        assert_ne!(a.ptr_id(), b.ptr_id());
    }

    #[test]
    fn hashcons_dedups() {
        let mut hc = TypeHashCons::new();
        let a = hc.make(k("a"));
        let b = hc.make(k("a"));
        assert_eq!(a.ptr_id(), b.ptr_id());
        assert_eq!(hc.len(), 1);
        let _c = hc.make(k("b"));
        assert_eq!(hc.len(), 2);
        assert!(hc.contains(&a));
    }

    #[test]
    fn checked_keeps_correct_rejects_wrong() {
        let mut good = Checked::new(Forward);
        assert_eq!(*TrustedTypeCons::make(&mut good, k("a")).kind(), k("a"));
        let mut evil = Checked::new(Evil);
        // Evil offers `nat` for everything; Checked rejects → make allocates.
        let got = TrustedTypeCons::make(&mut evil, k("a"));
        assert_eq!(*got.kind(), k("a"));
    }

    #[test]
    fn cons_with_interns_shared_subtypes() {
        // (a -> a) built from two distinct-Arc `a`s; interning shares them.
        let a1 = Type::tfree("a");
        let a2 = Type::tfree("a");
        assert_ne!(a1.ptr_id(), a2.ptr_id());
        let t = Type::fun(a1, a2);
        let mut hc = TypeHashCons::new();
        let interned = t.cons_with(&mut hc);
        assert_eq!(interned, t);
        if let TypeKind::Fun(d, c) = interned.kind() {
            assert_eq!(d.ptr_id(), c.ptr_id());
        } else {
            panic!("expected Fun");
        }
    }

    #[test]
    fn dyn_trusted_type_cons() {
        let mut hc = TypeHashCons::new();
        let dynref: &mut dyn TrustedTypeCons = &mut hc;
        let t = Type::fun(Type::tfree("a"), Type::tfree("a"));
        let interned = t.cons_with(dynref);
        if let TypeKind::Fun(d, c) = interned.kind() {
            assert_eq!(d.ptr_id(), c.ptr_id());
        } else {
            panic!("expected Fun");
        }
    }
}
