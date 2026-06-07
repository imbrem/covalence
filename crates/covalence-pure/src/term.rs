//! Pure's term and type language.
//!
//! Locally-nameless: bound variables use de Bruijn indices, free
//! variables and constants carry their declared type. Meta-implication,
//! meta-universal, and meta-equality are first-class variants — not
//! built-in `Const` applications — so inference rules pattern-match
//! them directly.
//!
//! ## α-equivalence is structural equality
//!
//! Each `Abs` and `All` carries a [`Hint`] — a display label for the
//! binder. The `Hint` type is *transparent* to `PartialEq`, `Hash`, and
//! `Ord`: two `Hint`s always compare equal and hash the same. So
//! structural equality on `TermKind` is α-equivalence; rules can use
//! `==` freely without worrying about display labels.
//!
//! ## Observations
//!
//! `TermKind::Obs { observer: DynObs, ty: Type }` is the only leaf
//! that carries oracle-supplied data. The kernel never sees the
//! observer's concrete type: it holds a type-erased [`DynObs`] and
//! compares Obs leaves by **`Arc` pointer identity** — never by
//! calling user-supplied `Eq`/`Hash`/`Ord` impls. This means a
//! misbehaving observer cannot corrupt the kernel's `BTreeSet<Term>`
//! invariants or otherwise compromise soundness.
//!
//! Construct an observation with `Term::obs(o, ty)`. Two
//! `Term::obs(o, ty)` calls — even with identical `o` values —
//! produce **distinct** leaves; clone the constructed `Term` to
//! share an observation across multiple call sites.
//!
//! The **only** kernel rule that operates on observations is
//! [`crate::Thm::obs_eq`], which equates two applications whose heads
//! are observations of the same Rust type at the same Pure type.
//! There is no kernel rule for "this observation is true / equal to
//! some non-observation term" — that kind of fact is added via
//! [`crate::Thm::assume`] as an explicit meaning axiom, visible in
//! every dependent theorem's hypotheses.

use std::any::{Any, TypeId};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, LazyLock};

use bytes::Bytes;
use smol_str::SmolStr;

use crate::error::{Error, Result};

// ============================================================================
// Observer trait + DynObs
// ============================================================================

/// Marker trait for types that may be wrapped in [`DynObs`].
///
/// The bounds are exactly what's needed for a [`DynObs`] to round-trip
/// safely across threads (`Send + Sync`), survive past stack frames
/// (`'static` via [`Any`]), and be printed in error messages
/// (`Debug`). Any qualifying type automatically becomes an `Observer`
/// via the blanket impl below.
///
/// Crucially, the kernel never calls user-supplied `Eq`/`Ord`/`Hash`
/// methods on an `Observer` — `DynObs` uses `Arc` pointer identity for
/// all comparisons. So a misbehaving observer impl cannot break the
/// kernel.
pub trait Observer: Any + Send + Sync + fmt::Debug {}
impl<T: Any + Send + Sync + fmt::Debug> Observer for T {}

/// Per-observer-Rust-type policy for the kernel's
/// [`crate::Thm::obs_eq`] rule.
///
/// **Implementations are NOT part of the TCB.** Soundness is
/// guaranteed by the kernel under the parametric ε-model regardless
/// of what an `obs_eq` implementation returns. The trait exists only
/// so each Rust observer type `O` can pick its own equality policy
/// without affecting any other observer type's behaviour.
///
/// ## Why no trust is required
///
/// The model interprets every `Obs` whose underlying Rust type is `O`
/// at Pure type τ as `ε_O(τ)` — the per-`O`, per-τ canonical
/// inhabitant. With `ε_O(τ → σ) = λ_. ε_O(σ)` and `ε_O(bool) = ⊤`,
/// any two `(obs o)(args…)` and `(obs o')(args'…)` with both heads
/// of Rust type `O` and the same final Pure type τ interpret to the
/// same `ε_O(τ)`. So:
///
/// - Returning `true` from `obs_eq` is sound: the model already
///   satisfies the equation.
/// - Returning `false` is sound: the kernel simply doesn't derive
///   the equation.
///
/// ## Type-locality
///
/// Different Rust observer types `O`, `O'` get **independent**
/// ε-families in the model, so a policy choice — or a bug — in
/// `WasmObs::obs_eq` cannot affect equations involving `SatObs`.
/// The kernel's downcast check ensures `obs_eq` is only invoked when
/// both heads are of the requested type `O`.
pub trait ObsEq: Observer {
    /// Per-`O` policy: decide whether `(obs self)(my_args…)` and
    /// `(obs other)(other_args…)` should be emitted as an equation
    /// by the kernel. Returning either answer is sound; this is
    /// purely a policy choice for the observer type.
    ///
    /// `my_args` and `other_args` are in left-to-right application
    /// order (outermost binder applied first).
    fn obs_eq(
        &self,
        other: &Self,
        my_args: &[Term],
        other_args: &[Term],
    ) -> bool;
}

/// Type-erased observer leaf. Wraps any `O: Observer` inside an `Arc`,
/// and compares / hashes / orders by the `Arc`'s data-pointer
/// identity. Use [`DynObs::new`] to wrap, [`DynObs::downcast`] to
/// recover a typed reference.
///
/// Pointer-identity semantics: two distinct `DynObs::new(o)` calls
/// produce distinct values *even if `o` is identical between calls*.
/// To share an observation across multiple terms, construct it once
/// via `Term::obs` and clone the resulting `Term` (the clone shares
/// the `Arc` and so shares the observation identity).
pub struct DynObs {
    /// The underlying observer, type-erased through `Any`. We store
    /// `Arc<dyn Any + Send + Sync>` directly (rather than wrapping in
    /// a custom trait) so that `Arc::downcast` works directly and
    /// `Any::downcast_ref` has the right vtable.
    inner: Arc<dyn Any + Send + Sync>,
    /// Hand-rolled vtable for `Debug` — `dyn Any` doesn't carry it.
    debug_fn: fn(&dyn Any, &mut fmt::Formatter<'_>) -> fmt::Result,
}

impl DynObs {
    /// Wrap any [`Observer`] in a `DynObs`. Allocates a new `Arc`;
    /// two calls with identical inputs produce distinct `DynObs`
    /// values.
    pub fn new<O: Observer>(o: O) -> Self {
        DynObs {
            inner: Arc::new(o),
            debug_fn: |any, f| {
                let o = any.downcast_ref::<O>()
                    .expect("DynObs debug_fn: type id matches at construction");
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
}

impl Clone for DynObs {
    fn clone(&self) -> Self {
        DynObs {
            inner: Arc::clone(&self.inner),
            debug_fn: self.debug_fn,
        }
    }
}

/// **`Arc` pointer identity** — never the user's `Eq`.
impl PartialEq for DynObs {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}
impl Eq for DynObs {}

/// **`Arc` pointer ordering** — never the user's `Ord`. Two distinct
/// `DynObs` instances may compare in any order, but the ordering is
/// stable for the lifetime of the `Arc`s.
impl Ord for DynObs {
    fn cmp(&self, other: &Self) -> Ordering {
        let a = Arc::as_ptr(&self.inner) as *const () as usize;
        let b = Arc::as_ptr(&other.inner) as *const () as usize;
        a.cmp(&b)
    }
}
impl PartialOrd for DynObs {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

/// **`Arc` pointer hash** — never the user's `Hash`.
impl Hash for DynObs {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.inner) as *const () as usize).hash(state);
    }
}

impl fmt::Debug for DynObs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DynObs(")?;
        (self.debug_fn)(&*self.inner, f)?;
        write!(f, ")")
    }
}

// ============================================================================
// Hint
// ============================================================================

/// A display label for an `Abs`/`All` binder. Transparent to equality
/// and ordering — `Hint("x") == Hint("y")` is `true`. Only `Display`
/// and `Debug` distinguish them.
#[derive(Clone, Default)]
pub struct Hint(pub SmolStr);

impl Hint {
    pub fn new(s: impl Into<SmolStr>) -> Self { Hint(s.into()) }
    pub fn as_str(&self) -> &str { self.0.as_str() }
    pub fn is_empty(&self) -> bool { self.0.is_empty() }
}

impl<S: Into<SmolStr>> From<S> for Hint {
    fn from(s: S) -> Self { Hint(s.into()) }
}

impl PartialEq for Hint { fn eq(&self, _: &Self) -> bool { true } }
impl Eq for Hint {}
impl Hash for Hint { fn hash<H: Hasher>(&self, _: &mut H) {} }
impl Ord for Hint { fn cmp(&self, _: &Self) -> Ordering { Ordering::Equal } }
impl PartialOrd for Hint { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }

impl fmt::Debug for Hint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Display for Hint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// ============================================================================
// Type
// ============================================================================

#[derive(Clone)]
pub struct Type(Arc<TypeKind>);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeKind {
    /// Type variable, e.g. `'a` in Isabelle notation.
    TFree(SmolStr),
    /// Kind of meta-propositions. Built in.
    Prop,
    /// Type of `Blob(_)` term values. Built in.
    Bytes,
    /// Function type τ ⇒ σ.
    Fun(Type, Type),
    /// User-declared type constructor applied to arguments.
    Tycon(SmolStr, Vec<Type>),
}

// Cached canonical instances of the common `Type`s, so the methods
// below are O(1) `Arc::clone` instead of a fresh allocation per call.
static PROP: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Prop)));
static BYTES: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Bytes)));
static BOOL: LazyLock<Type> =
    LazyLock::new(|| Type(Arc::new(TypeKind::Tycon(SmolStr::new("bool"), Vec::new()))));

impl Type {
    pub fn kind(&self) -> &TypeKind { &self.0 }

    /// Pointer identity of the underlying `Arc`. Useful as a cache key
    /// for outside-the-TCB walkers (hashers, pretty-printers).
    pub fn ptr_id(&self) -> usize { Arc::as_ptr(&self.0) as usize }

    fn alloc(kind: TypeKind) -> Self { Type(Arc::new(kind)) }

    pub fn tfree(name: impl Into<SmolStr>) -> Self { Self::alloc(TypeKind::TFree(name.into())) }

    /// The kind of meta-propositions — `prop`. Returns a shared
    /// instance; calls are O(1) `Arc` bumps.
    pub fn prop() -> Self { PROP.clone() }

    /// The native byte-string type — `bytes`. Returns a shared
    /// instance; calls are O(1) `Arc` bumps.
    pub fn bytes() -> Self { BYTES.clone() }

    /// The HOL `bool` type (a 0-ary `tycon`). Pure does not bake bool
    /// in semantically — it's just a named constructor — but this
    /// canonical instance is cached because user code references it
    /// often. Returns a shared instance; calls are O(1) `Arc` bumps.
    pub fn bool() -> Self { BOOL.clone() }

    pub fn fun(dom: Type, cod: Type) -> Self { Self::alloc(TypeKind::Fun(dom, cod)) }

    pub fn tycon(name: impl Into<SmolStr>, args: Vec<Type>) -> Self {
        Self::alloc(TypeKind::Tycon(name.into(), args))
    }

    pub fn is_prop(&self) -> bool { matches!(self.kind(), TypeKind::Prop) }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}
impl Eq for Type {}
impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) { self.0.hash(state); }
}
impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl Ord for Type {
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0, &other.0) { return Ordering::Equal; }
        self.0.cmp(&other.0)
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TypeKind::TFree(n) => write!(f, "'{}", n),
            TypeKind::Prop => write!(f, "prop"),
            TypeKind::Bytes => write!(f, "bytes"),
            TypeKind::Fun(a, b) => write!(f, "({} ⇒ {})", a, b),
            TypeKind::Tycon(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "({}", name)?;
                    for a in args { write!(f, " {}", a)?; }
                    write!(f, ")")
                }
            }
        }
    }
}

// ============================================================================
// Def — kernel-managed defined constant
// ============================================================================

/// A defined constant. Carries a display [`Hint`] (the name, for
/// pretty-printing) and the definition body behind an `Arc`. Each
/// [`crate::Thm::define`] call allocates a *fresh* `Arc`, so two
/// distinct definitions — even with the same name and the same body
/// — produce distinct `Def`s. Identity is `Arc::ptr_eq`; the name is
/// display-only (transparent to `Eq`/`Hash`/`Ord`, like [`Hint`]).
///
/// This is how we get freshness without a stateful kernel signature:
/// the allocator gives us a unique pointer per call.
#[derive(Clone)]
pub struct Def {
    name: Hint,
    body: Arc<Term>,
}

impl Def {
    pub fn name(&self) -> &Hint { &self.name }
    pub fn body(&self) -> &Term { &self.body }

    /// Pointer identity of the body Arc — useful as a cache key.
    pub fn ptr_id(&self) -> usize { Arc::as_ptr(&self.body) as usize }

    pub(crate) fn new_internal(name: Hint, body: Term) -> Self {
        Def { name, body: Arc::new(body) }
    }
}

impl PartialEq for Def {
    fn eq(&self, other: &Self) -> bool { Arc::ptr_eq(&self.body, &other.body) }
}
impl Eq for Def {}

impl Hash for Def {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.body) as usize).hash(state)
    }
}

impl Ord for Def {
    fn cmp(&self, other: &Self) -> Ordering {
        (Arc::as_ptr(&self.body) as usize).cmp(&(Arc::as_ptr(&other.body) as usize))
    }
}
impl PartialOrd for Def {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

impl fmt::Debug for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Def({})", self.name)
    }
}

impl fmt::Display for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

// ============================================================================
// Term
// ============================================================================

#[derive(Clone)]
pub struct Term(Arc<TermKind>);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TermKind {
    /// de Bruijn–indexed bound variable. Index 0 refers to the
    /// innermost surrounding binder (`Abs` or `All`).
    Bound(u32),
    /// Free variable: name + declared type.
    Free(SmolStr, Type),
    /// Declared/defined constant: name + instance type.
    Const(SmolStr, Type),
    /// Application `f x`.
    App(Term, Term),
    /// Abstraction `λ(hint:ty). body`. `body` uses Bound(0) for the
    /// binder; `hint` is a display label (α-transparent).
    Abs(Hint, Type, Term),
    /// Meta-implication `φ ⟹ ψ`.
    Imp(Term, Term),
    /// Meta-universal `⋀(hint:ty). body`. Same layout as `Abs`.
    All(Hint, Type, Term),
    /// Meta-equality `t ≡ u`.
    Eq(Term, Term),
    /// Builtin: opaque byte literal of kernel type `bytes`.
    Blob(Bytes),
    /// Typed observation leaf: observer + Pure type. The kernel
    /// compares these by `Arc` pointer identity (via [`DynObs`]'s
    /// impls), never by the user's `Eq` on the underlying observer.
    Obs(DynObs, Type),
    /// A defined constant. Each [`crate::Thm::define`] call produces
    /// a fresh `Def` (a fresh `Arc<Term>` allocation); the
    /// unfolding equation `Def ≡ body` is emitted by the same rule
    /// application. Two distinct `define` calls — even with the
    /// same name and same body — yield distinct `Def`s.
    Def(Def),
}

impl Term {
    pub fn kind(&self) -> &TermKind { &self.0 }

    /// Pointer identity of the underlying `Arc`. Useful as a cache key
    /// for outside-the-TCB walkers (hashers, pretty-printers).
    pub fn ptr_id(&self) -> usize { Arc::as_ptr(&self.0) as usize }

    fn alloc(kind: TermKind) -> Self {
        Term(Arc::new(kind))
    }

    // ---- smart constructors ----
    pub fn bound(idx: u32) -> Self { Self::alloc(TermKind::Bound(idx)) }
    pub fn free(name: impl Into<SmolStr>, ty: Type) -> Self {
        Self::alloc(TermKind::Free(name.into(), ty))
    }
    pub fn const_(name: impl Into<SmolStr>, ty: Type) -> Self {
        Self::alloc(TermKind::Const(name.into(), ty))
    }
    pub fn app(fun: Term, arg: Term) -> Self { Self::alloc(TermKind::App(fun, arg)) }
    pub fn abs(hint: impl Into<Hint>, ty: Type, body: Term) -> Self {
        Self::alloc(TermKind::Abs(hint.into(), ty, body))
    }
    pub fn imp(lhs: Term, rhs: Term) -> Self { Self::alloc(TermKind::Imp(lhs, rhs)) }
    pub fn all(hint: impl Into<Hint>, ty: Type, body: Term) -> Self {
        Self::alloc(TermKind::All(hint.into(), ty, body))
    }
    pub fn eq(lhs: Term, rhs: Term) -> Self { Self::alloc(TermKind::Eq(lhs, rhs)) }
    pub fn blob(bytes: impl Into<Bytes>) -> Self { Self::alloc(TermKind::Blob(bytes.into())) }

    /// Wrap an observer as a typed leaf. The kernel treats the
    /// underlying value opaquely; only the user code constructing
    /// `o` controls what observations exist.
    pub fn obs<O: Observer>(o: O, ty: Type) -> Self {
        Self::alloc(TermKind::Obs(DynObs::new(o), ty))
    }

    /// Like [`Term::obs`] but reuses an existing [`DynObs`] handle
    /// (preserving its `Arc` identity). Used by deserialisers and
    /// other shells that have already constructed a `DynObs`.
    pub fn obs_from_dyn(observer: DynObs, ty: Type) -> Self {
        Self::alloc(TermKind::Obs(observer, ty))
    }

    /// Wrap an existing [`Def`] as a `Term` leaf. Sharing the same
    /// `Def` via `clone` preserves kernel identity; constructing two
    /// distinct `Def`s with the same name produces two distinct
    /// `Term`s here.
    pub fn def(d: Def) -> Self { Self::alloc(TermKind::Def(d)) }

    /// Compute the type of `self` in an empty env. Walks the whole
    /// term, checking that every Free / Const occurrence uses a
    /// consistent type, every App is well-typed, every Imp / All body
    /// has type `prop`, every Eq has matching argument types, and no
    /// Bound variable escapes its binder.
    ///
    /// Each Thm-construction shares a single env across all hypotheses
    /// and the conclusion, so Thm validity is *stronger* than every
    /// individual term being well-typed: it also enforces that Free
    /// names are consistent *across* hyps and concl.
    pub fn type_of(&self) -> Result<Type> {
        let mut env = TypeEnv::default();
        type_of_in(self, &mut env)
    }

    /// Returns `true` iff no `Obs` leaf appears anywhere in this
    /// term (including transitively through any `Def` bodies). Used
    /// at theorem level via [`crate::Thm::has_no_obs`].
    pub fn has_no_obs(&self) -> bool {
        match self.kind() {
            TermKind::Obs(..) => false,
            TermKind::Bound(_)
            | TermKind::Free(..)
            | TermKind::Const(..)
            | TermKind::Blob(_) => true,
            TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
                a.has_no_obs() && b.has_no_obs()
            }
            TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => body.has_no_obs(),
            TermKind::Def(d) => d.body().has_no_obs(),
        }
    }

    /// Returns `true` iff every `Obs` leaf carries an observer
    /// whose dynamic type is `O`. Trivially `true` for a term with
    /// no `Obs` leaves.
    pub fn all_obs_match<O: Observer>(&self) -> bool {
        match self.kind() {
            TermKind::Obs(observer, _) => observer.downcast::<O>().is_some(),
            TermKind::Bound(_)
            | TermKind::Free(..)
            | TermKind::Const(..)
            | TermKind::Blob(_) => true,
            TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
                a.all_obs_match::<O>() && b.all_obs_match::<O>()
            }
            TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => body.all_obs_match::<O>(),
            TermKind::Def(d) => d.body().all_obs_match::<O>(),
        }
    }

    /// Walk the term and call `f` on every `Obs` leaf's observer
    /// downcast to `O`. Returns `Err(ObsDowncastTypeMismatch)` at
    /// the first leaf whose dynamic type does not match `O`.
    pub fn for_each_obs<O: Observer, F: FnMut(&O)>(&self, f: &mut F) -> Result<()> {
        match self.kind() {
            TermKind::Obs(observer, _) => {
                let o = observer.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
                f(o);
                Ok(())
            }
            TermKind::Bound(_)
            | TermKind::Free(..)
            | TermKind::Const(..)
            | TermKind::Blob(_) => Ok(()),
            TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
                a.for_each_obs::<O, F>(f)?;
                b.for_each_obs::<O, F>(f)
            }
            TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => body.for_each_obs::<O, F>(f),
            TermKind::Def(d) => d.body().for_each_obs::<O, F>(f),
        }
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}
impl Eq for Term {}
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) { self.0.hash(state); }
}
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl Ord for Term {
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0, &other.0) { return Ordering::Equal; }
        self.0.cmp(&other.0)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TermKind::Bound(i) => write!(f, "@{}", i),
            TermKind::Free(name, _) | TermKind::Const(name, _) => write!(f, "{}", name),
            TermKind::App(g, x) => write!(f, "({} {})", g, x),
            TermKind::Abs(hint, ty, body) if hint.is_empty() => write!(f, "(λ:{}. {})", ty, body),
            TermKind::Abs(hint, ty, body) => write!(f, "(λ{}:{}. {})", hint, ty, body),
            TermKind::Imp(a, b) => write!(f, "({} ⟹ {})", a, b),
            TermKind::All(hint, ty, body) if hint.is_empty() => write!(f, "(⋀:{}. {})", ty, body),
            TermKind::All(hint, ty, body) => write!(f, "(⋀{}:{}. {})", hint, ty, body),
            TermKind::Eq(a, b) => write!(f, "({} ≡ {})", a, b),
            TermKind::Blob(b) => write!(f, "blob[{}]", b.len()),
            TermKind::Obs(observer, ty) => write!(f, "obs[{:?}:{}]", observer, ty),
            TermKind::Def(d) => write!(f, "{}", d),
        }
    }
}

// ============================================================================
// Type-of
// ============================================================================

/// Carries the binder context plus the first-seen type of every free
/// variable referenced so far. Pass the same env across every term in
/// a theorem to enforce HOL Light–style cross-term consistency for
/// free variables.
#[derive(Default)]
pub(crate) struct TypeEnv {
    /// Stack of binder types; the innermost binder is at the top.
    ctx: Vec<Type>,
    /// First-seen type for each Free name; subsequent occurrences must
    /// match. Scope is whatever set of terms share this env.
    frees: BTreeMap<SmolStr, Type>,
}

/// Type-check `t` in `env`. The env carries the binder context plus
/// every Free name we have already seen, with its declared type.
/// Subsequent occurrences (in `t` or in later calls sharing the env)
/// must use the same type.
pub(crate) fn type_of_in(t: &Term, env: &mut TypeEnv) -> Result<Type> {
    match t.kind() {
        TermKind::Bound(i) => {
            let i = *i as usize;
            if i >= env.ctx.len() { return Err(Error::NotClosed); }
            Ok(env.ctx[env.ctx.len() - 1 - i].clone())
        }
        TermKind::Free(name, ty) => {
            if let Some(prev) = env.frees.get(name) {
                if prev != ty {
                    return Err(Error::FreeVarReuse {
                        name: name.clone(),
                        first: prev.clone(),
                        second: ty.clone(),
                    });
                }
            } else {
                env.frees.insert(name.clone(), ty.clone());
            }
            Ok(ty.clone())
        }
        // Const instance types are NOT required to be consistent
        // across occurrences within a theorem — polymorphic constants
        // (`=` at `'a → 'a → bool`, etc.) are used at many instance
        // types in a single proof. The signature check that ties each
        // Const's instance type to a declared principal type lands
        // when `define` lands.
        TermKind::Const(_, ty) => Ok(ty.clone()),
        TermKind::App(fun, arg) => {
            let fun_ty = type_of_in(fun, env)?;
            let arg_ty = type_of_in(arg, env)?;
            let TypeKind::Fun(dom, cod) = fun_ty.kind() else {
                return Err(Error::NotFunction(fun_ty));
            };
            if *dom != arg_ty {
                return Err(Error::TypeMismatch { expected: dom.clone(), got: arg_ty });
            }
            Ok(cod.clone())
        }
        TermKind::Abs(_, ty, body) => {
            env.ctx.push(ty.clone());
            let body_ty = type_of_in(body, env);
            env.ctx.pop();
            Ok(Type::fun(ty.clone(), body_ty?))
        }
        TermKind::All(_, ty, body) => {
            env.ctx.push(ty.clone());
            let body_ty = type_of_in(body, env);
            env.ctx.pop();
            let body_ty = body_ty?;
            if !body_ty.is_prop() { return Err(Error::NotProp(body_ty)); }
            Ok(Type::prop())
        }
        TermKind::Imp(a, b) => {
            let ta = type_of_in(a, env)?;
            if !ta.is_prop() { return Err(Error::NotProp(ta)); }
            let tb = type_of_in(b, env)?;
            if !tb.is_prop() { return Err(Error::NotProp(tb)); }
            Ok(Type::prop())
        }
        TermKind::Eq(a, b) => {
            let ta = type_of_in(a, env)?;
            let tb = type_of_in(b, env)?;
            if ta != tb { return Err(Error::TypeMismatch { expected: ta, got: tb }); }
            Ok(Type::prop())
        }
        TermKind::Blob(_) => Ok(Type::bytes()),
        TermKind::Obs(_, ty) => Ok(ty.clone()),
        // A `Def` denotes its body, so it shares the body's type.
        // Body validation happens once at `Thm::define` time; we
        // recompute here so the env's Free-var tracking is consistent
        // across the rest of the Thm.
        TermKind::Def(d) => type_of_in(d.body(), env),
    }
}
