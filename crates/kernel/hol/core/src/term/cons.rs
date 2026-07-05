//! Optional **hash-consing** of terms.
//!
//! Every `Term` is an `Arc<TermKind>`, and `Term` equality is *structural*
//! (with an `Arc::ptr_eq` fast path — see [`Term`]'s `Eq`/`Ord` impls). So
//! whether two structurally-equal terms share one allocation or not is
//! purely a **performance** concern: sharing makes the `ptr_eq` fast path
//! fire more often (cheap equality, cheap hashing of already-interned
//! children) and saves memory. It can never change a proof.
//!
//! That observation is exactly what lets hash-consing be *pluggable* and
//! *optional*. A term constructor is modelled by the [`TrustedCons`]
//! trait: given a [`TermKind`], hand back *some* `Term` structurally equal
//! to it. The trivial implementor is `()` — it just allocates a fresh
//! `Arc` every time (no interning at all). A real interner
//! ([`HashCons`]) keeps an [`IndexSet`] of canonical representatives and
//! returns the shared one. Both are equally correct; they differ only in
//! how much sharing you get.
//!
//! ## Trusted vs. untrusted
//!
//! [`TrustedCons`] is **sealed**: only kernel-blessed implementors exist
//! (`()`, [`HashCons`], and [`Checked`]). Its contract — *the returned
//! term is structurally equal to the requested kind* — is relied on by
//! the kernel, so it must not be implementable by downstream code.
//!
//! [`TermCons`] is the **public, untrusted** mirror: anyone can implement
//! it (e.g. a custom interning policy, a content-addressed store, a WASM
//! bridge). It carries *no* guarantee. To use one where a `TrustedCons`
//! is required, wrap it in [`Checked`]: that adapter clones the requested
//! kind, lets the untrusted cons produce a term, then **re-checks** the
//! result structurally and falls back to a fresh allocation if the
//! untrusted code returned anything else. So an arbitrary `TermCons`
//! becomes a `TrustedCons` with the guarantee restored by verification,
//! not by trust.
//!
//! ## The `_with` convention
//!
//! Term-building APIs come in pairs: `foo_with(…, &mut cons)` threads a
//! caller-supplied constructor, and `foo(…)` delegates to
//! `foo_with(…, &mut ())`. Passing `&mut ()` opts out of interning;
//! passing `&mut HashCons` opts in. Because `()` is a perfectly valid
//! `TrustedCons` that does no interning, "doesn't hash-cons" is just a
//! special case of "hash-cons with this policy".
//!
//! ## Object-safe (`dyn`) use
//!
//! Both traits are object-safe. The `_with` methods accept
//! `C: TrustedCons + ?Sized`, so `&mut dyn TrustedCons` works directly —
//! useful for the WASM boundary and for swapping policies at runtime.

use std::hash::{Hash, Hasher};
use std::ops::Deref;

use indexmap::{Equivalent, IndexSet};

use super::term::{Term, TermKind};

/// Borrow a [`TermKind`] as a probe key into the interner's `IndexSet<Term>`,
/// so [`HashCons::cons`] can look up an existing representative **without
/// materialising a candidate `Term`** (which would allocate, compute its
/// `TermInfo` — including a `type_of_in` walk for a closing `Abs` — and then be
/// dropped on a hit). Hashes and compares exactly as [`Term`] does (on `kind`),
/// so it locates the same representative. Private: this is an internal
/// fast-path, not public API.
///
/// FUTURE (see `crates/kernel/hol/traits/PERF.md`): to probe an *ordered*
/// interner (`BTreeSet<Term>`) alloc-free — which reuses the O(1) fingerprint
/// `cmp` and needs no cached wide hash — make this `#[repr(transparent)]` over
/// `TermKind` and obtain `&KindRef` from `&TermKind` via a safe reference-cast
/// crate (e.g. `ref-cast`), then `impl Borrow<KindRef> for Term`. The `Ord`
/// below is already shaped for it (fingerprint-then-structural, matching
/// `Term::cmp`). That avoids the O(size) `Hash for Term` that currently makes
/// replay interning ~20–30× slower.
struct KindRef<'a>(&'a TermKind);

impl Hash for KindRef<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Must match `impl Hash for Term`, which hashes `self.0.kind`.
        self.0.hash(state);
    }
}

impl Equivalent<Term> for KindRef<'_> {
    fn equivalent(&self, term: &Term) -> bool {
        // Must match `impl PartialEq for Term`, which compares `kind`.
        *self.0 == *term.kind()
    }
}

// Full self-consistent comparison surface, matching `Term`'s semantics
// (`Eq`/`Ord` on the kind, ordered by the cached structural fingerprint then
// the exact kind). This lets a `KindRef` serve as a probe key for an *ordered*
// interner (`BTreeMap`/`BTreeSet`) as well as the hashed one — comparisons use
// the O(1) fingerprint fast-path, the same accelerator `Term::cmp` relies on.
impl PartialEq for KindRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        *self.0 == *other.0
    }
}
impl Eq for KindRef<'_> {}
impl Ord for KindRef<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Mirror `Term::cmp`: fingerprint first (O(1) reject), then structure.
        self.0
            .compute_fp()
            .cmp(&other.0.compute_fp())
            .then_with(|| self.0.cmp(other.0))
    }
}
impl PartialOrd for KindRef<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

mod sealed {
    /// Seals [`super::TrustedCons`] so only this crate can vouch for the
    /// structural-equality contract.
    pub trait Sealed {}
}

/// **Untrusted** term constructor. Public — downstream code may
/// implement it freely.
///
/// The intended contract is the same as [`TrustedCons`]: `cons(kind)`
/// returns a `Term` structurally equal to `kind`. But because anyone can
/// implement `TermCons`, the kernel does **not** take that on faith — to
/// use one in a trusted position, wrap it in [`Checked`], which verifies
/// the result. A `TermCons` need not actually intern (returning a fresh
/// `Arc` each call is fine), and it need not preserve `Arc` identity
/// across calls.
pub trait TermCons {
    /// Offer a `Term` for `kind`, or `None` to let the caller allocate a
    /// fresh `Arc` itself. A returned `Some(t)` *should* be structurally
    /// equal to `kind` ([`Checked`] enforces this when used trusted).
    ///
    /// Taking `kind` by reference and returning `Option` is what makes
    /// constructors **composable**: a layered policy tries one source
    /// then the next with `a.cons(kind).or_else(|| b.cons(kind))`, and
    /// the no-op (`None`) costs nothing.
    fn cons(&mut self, kind: &TermKind) -> Option<Term>;
}

// Forwarding impls so `&mut dyn TermCons` / `Box<dyn TermCons>` can be
// dropped straight into [`Checked`] (and other `TermCons` positions).
impl<C: TermCons + ?Sized> TermCons for &mut C {
    fn cons(&mut self, kind: &TermKind) -> Option<Term> {
        (**self).cons(kind)
    }
}

impl<C: TermCons + ?Sized> TermCons for Box<C> {
    fn cons(&mut self, kind: &TermKind) -> Option<Term> {
        (**self).cons(kind)
    }
}

/// **Trusted, sealed** term constructor.
///
/// `Soundness:` every implementor guarantees that `cons(kind)` returns a
/// `Term` *structurally equal* to `Term` freshly allocated from `kind`
/// (`*result.kind() == kind`). The kernel routes its term construction
/// through `TrustedCons`, so this guarantee is what lets it stay sound
/// regardless of which interning policy a caller plugs in. The trait is
/// sealed precisely so that only the three vetted implementors below —
/// `()`, [`HashCons`], and [`Checked`] (which restores the guarantee by
/// re-checking) — can exist.
pub trait TrustedCons: sealed::Sealed {
    /// Offer a `Term` for `kind`, or `None` to defer allocation to the
    /// caller.
    ///
    /// `Soundness:` any `Some(t)` returned must satisfy `*t.kind() ==
    /// *kind` (structural equality). `None` is always sound — the caller
    /// allocates a fresh `Arc` from `kind`, which is `kind` by
    /// construction. So a constructor that does no interning simply
    /// returns `None` (see `()`).
    fn cons(&mut self, kind: &TermKind) -> Option<Term>;

    /// Build a `Term` for `kind`, allocating a fresh `Arc` ourselves
    /// when [`cons`](Self::cons) defers (`None`). This is the entry point
    /// the term-building APIs call; it always returns a term structurally
    /// equal to `kind`.
    fn make(&mut self, kind: TermKind) -> Term {
        match self.cons(&kind) {
            Some(t) => t,
            None => Term::alloc(kind),
        }
    }

    /// True iff [`Term::cons_with`] may short-circuit a rebuild to an identity
    /// `self.clone()` (one `Arc` bump) instead of a deep structural copy —
    /// because routing the existing tree through this constructor would produce
    /// something `Arc`-equal anyway. This holds exactly for constructors that
    /// never intern (the no-op `()`), where a rebuild would deep-copy an
    /// already-equal term; callers thread `&mut ()` through a shared "intern if
    /// asked" path (e.g. the plain Metamath import) and must not pay a per-term
    /// deep copy. Conservatively defaults to `false` (force the rebuild).
    fn allow_clone(&self) -> bool {
        false
    }
}

// ---------------------------------------------------------------------------
// `()` — the no-op constructor (always allocate fresh)
// ---------------------------------------------------------------------------

impl sealed::Sealed for () {}

impl TrustedCons for () {
    /// `Soundness:` always defers (`None`), so [`make`](TrustedCons::make)
    /// allocates a fresh `Arc` from `kind` — `kind` by construction. The
    /// canonical witness that a `TrustedCons` need not intern at all.
    #[inline]
    fn cons(&mut self, _kind: &TermKind) -> Option<Term> {
        None
    }

    #[inline]
    fn allow_clone(&self) -> bool {
        true
    }
}

// ---------------------------------------------------------------------------
// `Checked<C>` — make any `TermCons` trusted by verification
// ---------------------------------------------------------------------------

/// Adapts an untrusted [`TermCons`] into a [`TrustedCons`] by verifying
/// every result.
///
/// `Soundness:` `cons(kind)` clones `kind`, asks the wrapped untrusted
/// constructor for a term, then compares the produced term's kind against
/// the clone. If they match it returns the produced (possibly shared)
/// term; otherwise it discards it and allocates a fresh `Arc` from the
/// clone. Either branch yields a term structurally equal to `kind`, so
/// the `TrustedCons` contract holds no matter what the wrapped code does.
pub struct Checked<C: ?Sized>(pub C);

impl<C> Checked<C> {
    /// Wrap an untrusted constructor.
    pub fn new(cons: C) -> Self {
        Checked(cons)
    }

    /// Recover the wrapped constructor.
    pub fn into_inner(self) -> C {
        self.0
    }
}

impl<C: TermCons + ?Sized> sealed::Sealed for Checked<C> {}

impl<C: TermCons + ?Sized> TrustedCons for Checked<C> {
    /// `Soundness:` keeps the wrapped constructor's offer only when it is
    /// structurally equal to `kind`; any other result (or `None`) becomes
    /// `None`, so [`make`](TrustedCons::make) allocates the requested term
    /// itself. Either way the contract holds regardless of what the
    /// untrusted code does.
    fn cons(&mut self, kind: &TermKind) -> Option<Term> {
        self.0.cons(kind).filter(|t| t.kind() == kind)
    }
}

// ---------------------------------------------------------------------------
// `HashCons<D>` — the default interner
// ---------------------------------------------------------------------------

/// The default hash-consing constructor: an [`IndexSet`] of canonical
/// `Term` representatives, optionally bundled with user data `D`.
///
/// `Soundness:` `cons(kind)` allocates the requested term, then either
/// returns the structurally-equal representative already in the set or
/// inserts and returns the fresh one. The representative is found by
/// `Term`'s structural `Eq`/`Hash`, so it is always structurally equal to
/// `kind` — the `TrustedCons` contract holds. Interning additionally
/// gives `Arc`-sharing: a second `cons` of an equal kind returns a term
/// that is `Arc::ptr_eq` to the first.
///
/// Deref exposes the underlying [`IndexSet`] read-only (so callers can
/// inspect `len`, `contains`, iterate, …); there is intentionally no
/// `DerefMut`, since mutating the set out from under the interner could
/// drop a representative that live terms still alias. Bundle auxiliary
/// state with [`HashCons::with_data`] and reach it via [`HashCons::data`]
/// / [`HashCons::data_mut`].
/// The interner carries a **type-cons template** `T` (default
/// [`TypeHashCons`](crate::ty::TypeHashCons)) alongside its term set, and is itself a
/// [`crate::ty::TrustedTypeCons`] (delegating to `T`) — so one `HashCons`
/// threaded through a proof shares both terms and types. The type params
/// are ordered `<D, T>` (data first) so `HashCons<MyData>` keeps the
/// default type interner.
#[derive(Clone)]
pub struct HashCons<D = (), T = crate::ty::TypeHashCons> {
    set: IndexSet<Term>,
    types: T,
    data: D,
}

impl HashCons {
    /// An empty interner with no bundled data and the default type
    /// interner.
    pub fn new() -> Self {
        Self {
            set: IndexSet::new(),
            types: crate::ty::TypeHashCons::new(),
            data: (),
        }
    }
}

impl Default for HashCons {
    fn default() -> Self {
        Self::new()
    }
}

impl<D> HashCons<D> {
    /// An empty interner carrying the given bundled `data` and the default
    /// type interner.
    pub fn with_data(data: D) -> Self {
        Self {
            set: IndexSet::new(),
            types: crate::ty::TypeHashCons::new(),
            data,
        }
    }
}

impl<D, T> HashCons<D, T> {
    /// An empty interner with bundled `data` and a caller-supplied type
    /// interner template.
    pub fn with_data_and_types(data: D, types: T) -> Self {
        Self {
            set: IndexSet::new(),
            types,
            data,
        }
    }

    /// Shared access to the bundled data.
    pub fn data(&self) -> &D {
        &self.data
    }

    /// Mutable access to the bundled data. (Distinct from the interner's
    /// term set, which stays read-only via [`Deref`].)
    pub fn data_mut(&mut self) -> &mut D {
        &mut self.data
    }

    /// Shared access to the type-cons template.
    pub fn types(&self) -> &T {
        &self.types
    }

    /// Mutable access to the type-cons template (used by the
    /// [`crate::ty::TrustedTypeCons`] impl).
    pub fn types_mut(&mut self) -> &mut T {
        &mut self.types
    }

    /// Consume the interner, returning the bundled data.
    pub fn into_data(self) -> D {
        self.data
    }

    /// Consume the interner, returning the term set and the bundled data.
    pub fn into_parts(self) -> (IndexSet<Term>, D) {
        (self.set, self.data)
    }
}

impl<D, T> Deref for HashCons<D, T> {
    type Target = IndexSet<Term>;

    fn deref(&self) -> &IndexSet<Term> {
        &self.set
    }
}

impl<D, T> sealed::Sealed for HashCons<D, T> {}

impl<D, T> TrustedCons for HashCons<D, T> {
    fn cons(&mut self, kind: &TermKind) -> Option<Term> {
        // Probe by borrowed kind — no candidate allocation on a hit (the common
        // case when a proof rebuilds shared structure). Only a miss allocates.
        if let Some(existing) = self.set.get(&KindRef(kind)) {
            return Some(existing.clone());
        }
        let t = Term::alloc(kind.clone());
        self.set.insert(t.clone());
        Some(t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::subst;
    use crate::term::{Type, Var};

    fn bvar(name: &str) -> Term {
        Term::free(name, Type::bool())
    }

    /// A `TermCons` that faithfully offers a fresh equal term, so
    /// `Checked` should always accept its output.
    struct Forward;
    impl TermCons for Forward {
        fn cons(&mut self, kind: &TermKind) -> Option<Term> {
            Some(Term::alloc(kind.clone()))
        }
    }

    /// A malicious `TermCons` that ignores the request and always offers
    /// the same wrong term. `Checked` must reject every result.
    struct Evil;
    impl TermCons for Evil {
        fn cons(&mut self, _kind: &TermKind) -> Option<Term> {
            Some(Term::bound(999))
        }
    }

    #[test]
    fn unit_cons_defers_and_make_allocates_distinct_arcs() {
        let k = || TermKind::Free(Var::new("a", Type::bool()));
        assert!(().cons(&k()).is_none()); // () always defers
        let a = ().make(k());
        let b = ().make(k());
        assert_eq!(a, b); // structurally equal
        assert_ne!(a.ptr_id(), b.ptr_id()); // but not interned
    }

    #[test]
    fn hashcons_dedups_equal_kinds() {
        let mut hc = HashCons::new();
        let k = || TermKind::Free(Var::new("a", Type::bool()));
        let a = hc.make(k());
        let b = hc.make(k());
        assert_eq!(a, b);
        assert_eq!(a.ptr_id(), b.ptr_id()); // shared Arc
        assert_eq!(hc.len(), 1); // Deref to IndexSet
        // A direct `cons` hit returns the same representative.
        assert_eq!(hc.cons(&k()).unwrap().ptr_id(), a.ptr_id());

        let c = hc.make(TermKind::Free(Var::new("b", Type::bool())));
        assert_ne!(a.ptr_id(), c.ptr_id());
        assert_eq!(hc.len(), 2);
    }

    #[test]
    fn hashcons_deref_to_indexset() {
        let mut hc = HashCons::new();
        let a = hc.make(TermKind::Free(Var::new("a", Type::bool())));
        assert!(hc.contains(&a));
        assert!(!hc.is_empty());
        assert_eq!(hc.iter().count(), 1);
    }

    #[test]
    fn hashcons_custom_data() {
        let mut hc: HashCons<u32> = HashCons::with_data(0);
        *hc.data_mut() += 7;
        hc.make(TermKind::Bool(true));
        assert_eq!(*hc.data(), 7);
        assert_eq!(hc.len(), 1);
        let (set, data) = hc.into_parts();
        assert_eq!(set.len(), 1);
        assert_eq!(data, 7);
    }

    #[test]
    fn cons_with_intern_shares_structurally_equal_subterms() {
        // Two *distinct-Arc* but structurally-equal leaves.
        let a1 = bvar("a");
        let a2 = bvar("a");
        assert_eq!(a1, a2);
        assert_ne!(a1.ptr_id(), a2.ptr_id());

        let t = Term::app(a1, a2);
        let mut hc = HashCons::new();
        let interned = t.cons_with(&mut hc);

        assert_eq!(interned, t); // structural copy
        let (f, x) = interned.as_app().unwrap();
        assert_eq!(f.ptr_id(), x.ptr_id()); // now the two leaves share
    }

    #[test]
    fn cons_with_unit_is_structural_copy() {
        let t = Term::app(bvar("f"), bvar("x"));
        let copy = t.cons_with(&mut ());
        assert_eq!(t, copy);
    }

    #[test]
    fn checked_passes_through_correct_cons() {
        let mut checked = Checked::new(Forward);
        let want = TermKind::App(bvar("f"), bvar("x"));
        // Forward's offer is structurally equal, so Checked keeps it.
        assert_eq!(*checked.cons(&want).unwrap().kind(), want);
        assert_eq!(*checked.make(want.clone()).kind(), want);
    }

    #[test]
    fn checked_rejects_malicious_cons() {
        let mut checked = Checked::new(Evil);
        let want = TermKind::Free(Var::new("a", Type::bool()));
        // Evil's wrong offer is filtered to None...
        assert!(checked.cons(&want).is_none());
        // ...so `make` allocates the requested term itself.
        let got = checked.make(want.clone());
        assert_eq!(*got.kind(), want);
        assert_ne!(*got.kind(), TermKind::Bound(999));
    }

    #[test]
    fn dyn_trusted_cons_is_usable() {
        let mut hc = HashCons::new();
        let t = Term::app(bvar("a"), bvar("a"));
        let dynref: &mut dyn TrustedCons = &mut hc;
        let interned = t.cons_with(dynref);
        let (f, x) = interned.as_app().unwrap();
        assert_eq!(f.ptr_id(), x.ptr_id());
    }

    #[test]
    fn dyn_term_cons_through_checked() {
        // `&mut dyn TermCons` is object-safe and forwards into `Checked`.
        let mut fwd = Forward;
        let tc: &mut dyn TermCons = &mut fwd;
        let mut checked = Checked::new(tc);
        let want = TermKind::Bool(false);
        assert_eq!(*checked.make(want.clone()).kind(), want);

        // Same via `Box<dyn TermCons>`.
        let boxed: Box<dyn TermCons> = Box::new(Evil);
        let mut checked = Checked::new(boxed);
        let want = TermKind::Free(Var::new("z", Type::bool()));
        assert_eq!(*checked.make(want.clone()).kind(), want); // allocated
    }

    #[test]
    fn subst_open_with_interns() {
        // body = (#0 #0) under a binder; open with u = free "u".
        let body = Term::app(Term::bound(0), Term::bound(0));
        let u = bvar("u");

        let plain = subst::open(&body, &u);
        let mut hc = HashCons::new();
        let interned = subst::open_with(&body, &u, &mut hc);

        assert_eq!(plain, interned); // same result, with/without interning
        let (f, x) = interned.as_app().unwrap();
        assert_eq!(f.ptr_id(), x.ptr_id()); // both copies of u shared
    }

    #[test]
    fn subst_free_with_interns_across_calls() {
        // Interning persists across separate substitutions sharing one
        // HashCons: equal results come back Arc-shared.
        let t = Term::app(bvar("p"), bvar("q"));
        let r = bvar("r");
        let mut hc = HashCons::new();
        let p = Var::new("p", Type::bool());
        let one = subst::subst_free_with(&t, &p, &r, &mut hc);
        let two = subst::subst_free_with(&t, &p, &r, &mut hc);
        assert_eq!(one, two);
        assert_eq!(one.ptr_id(), two.ptr_id());
    }
}
