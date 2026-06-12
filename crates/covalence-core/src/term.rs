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
//! Each `Abs` and `All` carries a [`BinderHint`] — a display label for the
//! binder. The `BinderHint` type is *transparent* to `PartialEq`, `Hash`, and
//! `Ord`: two `BinderHint`s always compare equal and hash the same. So
//! structural equality on `TermKind` is α-equivalence; rules can use
//! `==` freely without worrying about display labels.
//!
//! ## Observations
//!
//! `TermKind::Obs { observer: Object, ty: Type }` is the only leaf
//! that carries oracle-supplied data. The kernel never sees the
//! observer's concrete type: it holds a type-erased [`Object`] and
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
use covalence_types::{Int, Nat};
use smol_str::SmolStr;

use crate::error::{Error, Result};

// ============================================================================
// Observer trait + Object
// ============================================================================

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

/// Caller-supplied policy hint — an opaque, refcounted, type-erased
/// witness passed to observer policies (`ObsEq`, `ObsTrue`, `ObsImp`).
///
/// Implementations get the same auto-impl as `Observer`: any
/// `Any + Send + Sync + Debug` type qualifies. Policies recover the
/// concrete type via `hint.as_any().downcast_ref::<T>()`.
///
/// Stored as `Arc<dyn BinderHint>` so the same hint instance can be passed
/// across thread / kernel boundaries (notably for WASM-component
/// resources — a hint can be allocated on the host, handed across the
/// component-model ABI as an opaque resource handle, then passed in to
/// the observer policy on the other side).
pub trait Hint: Any + Send + Sync + fmt::Debug {
    /// Downcast helper. The default impl returns `self` typed as
    /// `&dyn Any`, enabling `hint.as_any().downcast_ref::<MyType>()`.
    fn as_any(&self) -> &dyn Any;
}

impl<T: Any + Send + Sync + fmt::Debug> Hint for T {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

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
/// Per-observer-Rust-type policy for the kernel's
/// [`crate::Thm::obs_true`] rule: a way to mint `⊢ (obs O) args…` for
/// a prop-typed observation directly, gated by the observer's policy.
///
/// **Implementations are NOT part of the TCB.** Soundness is
/// guaranteed by Pure's parametric-ε model: for any observer whose
/// final Pure type is `prop`, the standard ε-interpretation maps it
/// to `⊤` (truth). Returning `true` from `obs_true` is sound — the
/// model already satisfies the proposition. Returning `false` is
/// sound — the kernel simply doesn't derive it.
///
/// `hint` is the same opaque caller-supplied witness as [`ObsEq`]'s.
/// Observer theories use it for external evidence (e.g., HOL trans
/// needs the middle term and the two source theorems).
pub trait ObsTrue: Observer {
    fn obs_true(&self, args: &[Term], hint: Option<&dyn Hint>) -> bool;
}

/// Per-observer-Rust-type policy for the kernel's
/// [`crate::Thm::obs_imp`] rule: a way to mint a **lazy theorem**
/// `⊢ h₀ ⟹ h₁ ⟹ … ⟹ hₙ ⟹ (obs O) args`
/// where each `hᵢ` is a Pure proposition and the consequent is a
/// prop-typed obs application. The policy decides whether the
/// implication chain is HOL-derivable (or whatever-derivable for
/// other observer theories) given the supplied hyps.
///
/// **Soundness.** Strictly weaker than [`ObsTrue`]: if it's sound
/// to assert `⊢ (obs O) args` unconditionally (which it is, under
/// the parametric-ε model at result type prop), then it's *also*
/// sound to assert any implication chain that ends in it — the
/// chain is `⊤` whenever the consequent is `⊤`. Returning `true`
/// from any policy is sound; returning `false` just refuses.
///
/// `hint` is the same opaque pass-through as on [`ObsEq`] / [`ObsTrue`].
pub trait ObsImp: Observer {
    /// Decide whether the lazy theorem
    /// `⊢ hyps[0] ⟹ … ⟹ hyps[n] ⟹ (obs self) args` should be minted.
    fn obs_imp(
        &self,
        args: &[Term],
        hyps: &[Term],
        hint: Option<&dyn Hint>,
    ) -> bool;
}

pub trait ObsEq: Observer {
    /// Per-`O` policy: decide whether `(obs self)(my_args…)` and
    /// `(obs other)(other_args…)` should be emitted as an equation
    /// by the kernel. Returning either answer is sound; this is
    /// purely a policy choice for the observer type.
    ///
    /// `my_args` and `other_args` are in left-to-right application
    /// order (outermost binder applied first).
    ///
    /// `hint` is an opaque caller-supplied witness — typically `None`,
    /// but observer theories that need external evidence (e.g., HOL
    /// trans needs the middle term, observers backed by SAT/SMT need
    /// a model) can downcast it to their expected type via
    /// `<dyn Any>::downcast_ref::<T>()`. Sound under the same ε-model:
    /// soundness doesn't depend on what the hint is or whether it's
    /// provided.
    fn obs_eq(
        &self,
        other: &Self,
        my_args: &[Term],
        other_args: &[Term],
        hint: Option<&dyn Hint>,
    ) -> bool;
}

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

// ============================================================================
// BinderHint
// ============================================================================

/// A display label for an `Abs`/`All` binder. Transparent to equality
/// and ordering — `BinderHint("x") == BinderHint("y")` is `true`. Only `Display`
/// and `Debug` distinguish them.
#[derive(Clone, Default)]
pub struct BinderHint(pub SmolStr);

impl BinderHint {
    pub fn new(s: impl Into<SmolStr>) -> Self {
        BinderHint(s.into())
    }
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<S: Into<SmolStr>> From<S> for BinderHint {
    fn from(s: S) -> Self {
        BinderHint(s.into())
    }
}

impl PartialEq for BinderHint {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for BinderHint {}
impl Hash for BinderHint {
    fn hash<H: Hasher>(&self, _: &mut H) {}
}
impl Ord for BinderHint {
    fn cmp(&self, _: &Self) -> Ordering {
        Ordering::Equal
    }
}
impl PartialOrd for BinderHint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for BinderHint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Display for BinderHint {
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
    /// Type of `TermKind::Nat(_)` term values. Built in. The natural
    /// numbers (non-negative integers, arbitrary precision).
    Nat,
    /// Type of `TermKind::Int(_)` term values. Built in. The integers
    /// (arbitrary precision, possibly negative).
    Int,
    /// Singleton type — exactly one inhabitant (kernel "trivial"
    /// representative `ε(λ_. T)`). Built in alongside the other
    /// primitive types so the derived `defs::*` catalogue can spec
    /// `prod` (the empty product) and `option α` (= `coprod α unit`)
    /// without bottoming out into a typedef.
    Unit,
    /// Function type τ ⇒ σ.
    Fun(Type, Type),
    /// User-declared type constructor applied to arguments.
    /// **Structural identity** by name + args — cross-process stable.
    /// Best for "named uninterpreted" cases (HOL `bool`, `num`, `list`, …).
    Tycon(SmolStr, Vec<Type>),
    /// Type constructor whose identity is the wrapped observer's `Arc`
    /// pointer. **Process-local** — two `Type::tycon_obs` calls with
    /// independently constructed observers compare unequal even if they
    /// share the same `BinderHint` and args. Mirrors `TermKind::Obs` on the
    /// type side: the same Rust observer type is the unifying ε-family
    /// across term- and type-level uses (one theory → one identity).
    ///
    /// The [`BinderHint`] is α-transparent (display only). Identity is the
    /// `Object` plus the args; the args participate in equality so
    /// that `list α` and `list β` are distinct even though they share
    /// the same constructor.
    TyConObs(Object, BinderHint, Vec<Type>),
    /// Application of a derived-type [`crate::defs::TypeSpec`]
    /// factory to type arguments. The spec is process-shared
    /// (`LazyLock`-backed) and `args` is the positional
    /// substitution for the spec's type variables (in
    /// `spec.ty.free_tvars()` order — canonical alphabetical).
    ///
    /// Used by `crate::defs::*` to embed the semi-trusted derived-
    /// type catalogue (`set α`, `rel α β`, `option α`, …) into the
    /// kernel's type system without committing each one to its own
    /// `TypeKind` variant.
    Spec(crate::defs::TypeSpec, Vec<Type>),
}

// Cached canonical instances of the common `Type`s, so the methods
// below are O(1) `Arc::clone` instead of a fresh allocation per call.
static PROP: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Prop)));
static BYTES: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Bytes)));
static NAT: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Nat)));
static INT: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Int)));
static UNIT: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Unit)));
static BOOL: LazyLock<Type> =
    LazyLock::new(|| Type(Arc::new(TypeKind::Tycon(SmolStr::new("bool"), Vec::new()))));

impl Type {
    pub fn kind(&self) -> &TypeKind {
        &self.0
    }

    /// Pointer identity of the underlying `Arc`. Useful as a cache key
    /// for outside-the-TCB walkers (hashers, pretty-printers).
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }

    fn alloc(kind: TypeKind) -> Self {
        Type(Arc::new(kind))
    }

    pub fn tfree(name: impl Into<SmolStr>) -> Self {
        Self::alloc(TypeKind::TFree(name.into()))
    }

    /// The kind of meta-propositions — `prop`. Returns a shared
    /// instance; calls are O(1) `Arc` bumps.
    pub fn prop() -> Self {
        PROP.clone()
    }

    /// The native byte-string type — `bytes`. Returns a shared
    /// instance; calls are O(1) `Arc` bumps.
    pub fn bytes() -> Self {
        BYTES.clone()
    }

    /// The native unbounded-naturals type — `nat`. Returns a
    /// shared instance; calls are O(1) `Arc` bumps. Literal terms
    /// of this type are constructed via [`Term::nat_lit`] and
    /// reduced through [`crate::Thm::reduce_nat`].
    pub fn nat() -> Self {
        NAT.clone()
    }

    /// The native unbounded-integers type — `int`. Returns a
    /// shared instance; calls are O(1) `Arc` bumps. Literal terms
    /// of this type are constructed via [`Term::int_lit`] and
    /// reduced through [`crate::Thm::reduce_int`].
    pub fn int() -> Self {
        INT.clone()
    }

    /// The singleton type — `unit`. Has exactly one inhabitant.
    pub fn unit() -> Self {
        UNIT.clone()
    }

    /// The HOL `bool` type (a 0-ary `tycon`). Pure does not bake bool
    /// in semantically — it's just a named constructor — but this
    /// canonical instance is cached because user code references it
    /// often. Returns a shared instance; calls are O(1) `Arc` bumps.
    pub fn bool() -> Self {
        BOOL.clone()
    }

    pub fn fun(dom: Type, cod: Type) -> Self {
        Self::alloc(TypeKind::Fun(dom, cod))
    }

    pub fn tycon(name: impl Into<SmolStr>, args: Vec<Type>) -> Self {
        Self::alloc(TypeKind::Tycon(name.into(), args))
    }

    /// Apply a derived-type [`crate::defs::TypeSpec`] to type
    /// arguments. The spec's type variables (in `ty.free_tvars()`
    /// order) are substituted positionally by `args`. The handle is
    /// process-shared (`LazyLock`-backed in `crate::defs`), so two
    /// `Type::spec(defs::set_spec(), …)` calls land at the same
    /// kind of leaf and pointer-equal at the spec component.
    pub fn spec(spec: crate::defs::TypeSpec, args: Vec<Type>) -> Self {
        Self::alloc(TypeKind::Spec(spec, args))
    }

    /// Construct a fresh-identity type constructor wrapping an
    /// observer. The Arc-pointer identity of `observer` is the
    /// distinguishing identity; `hint` is display-only (α-transparent).
    /// Distinct calls with independently-constructed observers produce
    /// distinct types — that's the freshness primitive
    /// [`crate::Thm::new_type_definition`] uses.
    pub fn tycon_obs<O: Observer>(observer: O, hint: impl Into<BinderHint>, args: Vec<Type>) -> Self {
        Self::alloc(TypeKind::TyConObs(Object::new(observer), hint.into(), args))
    }

    /// Like [`Type::tycon_obs`] but reuses an existing [`Object`]
    /// handle (preserving its `Arc` identity). Used internally by
    /// kernel rules and by deserialisers that already have a `Object`.
    pub fn tycon_obs_from_dyn(observer: Object, hint: impl Into<BinderHint>, args: Vec<Type>) -> Self {
        Self::alloc(TypeKind::TyConObs(observer, hint.into(), args))
    }

    pub fn is_prop(&self) -> bool {
        matches!(self.kind(), TypeKind::Prop)
    }

    /// Free type variables of `self`, in sorted order with duplicates
    /// removed. Used by [`crate::Thm::new_type_definition`] to decide
    /// the arity of a freshly-introduced type constructor.
    pub fn free_tvars(&self) -> Vec<SmolStr> {
        let mut out = std::collections::BTreeSet::new();
        free_tvars_into(self, &mut out);
        out.into_iter().collect()
    }
}

fn free_tvars_into(ty: &Type, out: &mut std::collections::BTreeSet<SmolStr>) {
    match ty.kind() {
        TypeKind::TFree(name) => {
            out.insert(name.clone());
        }
        TypeKind::Prop
        | TypeKind::Bytes
        | TypeKind::Nat
        | TypeKind::Int
        | TypeKind::Unit => {}
        TypeKind::Fun(a, b) => {
            free_tvars_into(a, out);
            free_tvars_into(b, out);
        }
        TypeKind::Tycon(_, args) | TypeKind::TyConObs(_, _, args) | TypeKind::Spec(_, args) => {
            for a in args {
                free_tvars_into(a, out);
            }
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}
impl Eq for Type {}
impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Type {
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return Ordering::Equal;
        }
        self.0.cmp(&other.0)
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TypeKind::TFree(n) => write!(f, "'{}", n),
            TypeKind::Prop => write!(f, "prop"),
            TypeKind::Bytes => write!(f, "bytes"),
            TypeKind::Nat => write!(f, "nat"),
            TypeKind::Int => write!(f, "int"),
            TypeKind::Unit => write!(f, "unit"),
            TypeKind::Fun(a, b) => write!(f, "({} ⇒ {})", a, b),
            TypeKind::Tycon(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "({}", name)?;
                    for a in args {
                        write!(f, " {}", a)?;
                    }
                    write!(f, ")")
                }
            }
            TypeKind::Spec(spec, args) => {
                if args.is_empty() {
                    write!(f, "{}", spec.symbol().label())
                } else {
                    write!(f, "({}", spec.symbol().label())?;
                    for a in args {
                        write!(f, " {}", a)?;
                    }
                    write!(f, ")")
                }
            }
            TypeKind::TyConObs(observer, hint, args) => {
                // `<hint#ptr>` for the constructor head, then args.
                // `hint` is the user-visible label; the pointer suffix
                // disambiguates fresh allocations sharing a name.
                let ptr = observer.ptr_id();
                let label = if hint.is_empty() {
                    format!("tycon#{ptr:x}")
                } else {
                    format!("{hint}#{ptr:x}")
                };
                if args.is_empty() {
                    write!(f, "{label}")
                } else {
                    write!(f, "({label}")?;
                    for a in args { write!(f, " {a}")?; }
                    write!(f, ")")
                }
            }
        }
    }
}

// ============================================================================
// Def — kernel-managed defined constant
// ============================================================================

/// A defined constant. Carries a display [`BinderHint`] (the name, for
/// pretty-printing) and the definition body behind an `Arc`. Each
/// [`crate::Thm::define`] call allocates a *fresh* `Arc`, so two
/// distinct definitions — even with the same name and the same body
/// — produce distinct `Def`s. Identity is `Arc::ptr_eq`; the name is
/// display-only (transparent to `Eq`/`Hash`/`Ord`, like [`BinderHint`]).
///
/// This is how we get freshness without a stateful kernel signature:
/// the allocator gives us a unique pointer per call.
/// A fresh defined constant, optionally instantiated at a specific
/// type. Two `Def`s are equal iff they share the same `original`
/// identity (same `Thm::define` call) AND are at the same instance
/// type. This mirrors Isabelle/Pure's signature-based naming
/// (`Const(name, instance_type)`) but uses Arc identity for the
/// "which entry in the signature" lookup, so no global signature
/// is needed.
///
/// `subst_tfree_in_term` on a `Term::def` updates `instance_type`
/// without rebuilding `original` — preserving Arc identity across
/// type-variable instantiation. This is what makes a HOL constant
/// usable at multiple type instances while still comparing equal
/// to other uses at the same instance.
#[derive(Clone)]
pub struct Def {
    original: Arc<DefOriginal>,
    instance_type: Type,
}

#[derive(Debug)]
struct DefOriginal {
    name: BinderHint,
    body: Term,
    /// Cached `body.type_of()` — the most-general (polymorphic)
    /// type of this constant. `instance_type` always equals this
    /// for un-substituted `Def`s, and a one-way `match_types`
    /// against this recovers the substitution applied to the body
    /// when `body()` is called.
    body_type: Type,
}

impl Def {
    pub fn name(&self) -> &BinderHint {
        &self.original.name
    }

    /// The type at which this `Def` is currently used. For the
    /// `Def` returned by `Thm::define` this equals the body's
    /// type; `subst_tfree_in_term` updates this without recomputing
    /// the body.
    pub fn instance_type(&self) -> &Type {
        &self.instance_type
    }

    /// The body of this `Def` with type variables instantiated to
    /// match `instance_type`. For an un-substituted `Def` this is
    /// just the original body; otherwise we recover the substitution
    /// by one-way matching the original body type against
    /// `instance_type`, then apply it to the body.
    pub fn body(&self) -> Term {
        if self.instance_type == self.original.body_type {
            return self.original.body.clone();
        }
        let mut sub: std::collections::BTreeMap<SmolStr, Type> =
            std::collections::BTreeMap::new();
        crate::subst::match_types(&self.original.body_type, &self.instance_type, &mut sub)
            .expect("Def: instance_type unreachable from body_type — kernel bug");
        let mut result = self.original.body.clone();
        for (tv, replacement) in sub {
            result = crate::subst::subst_tfree_in_term(&result, tv.as_str(), &replacement);
        }
        result
    }

    /// Identity of the original definition (stable across
    /// substitutions). Useful as a cache key.
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.original) as usize
    }

    pub(crate) fn new_internal(name: BinderHint, body: Term, body_type: Type) -> Self {
        let original = Arc::new(DefOriginal {
            name,
            body,
            body_type: body_type.clone(),
        });
        Def {
            original,
            instance_type: body_type,
        }
    }

    /// Build a `Def` reusing this one's `original` identity but at a
    /// different instance type. Crate-private: used by
    /// `subst_tfree_in_term`.
    pub(crate) fn with_instance_type(&self, instance_type: Type) -> Self {
        Def {
            original: self.original.clone(),
            instance_type,
        }
    }
}

impl PartialEq for Def {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.original, &other.original) && self.instance_type == other.instance_type
    }
}
impl Eq for Def {}

impl Hash for Def {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.original) as usize).hash(state);
        self.instance_type.hash(state);
    }
}

impl Ord for Def {
    fn cmp(&self, other: &Self) -> Ordering {
        (Arc::as_ptr(&self.original) as usize)
            .cmp(&(Arc::as_ptr(&other.original) as usize))
            .then_with(|| self.instance_type.cmp(&other.instance_type))
    }
}
impl PartialOrd for Def {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Def({})", self.original.name)
    }
}

impl fmt::Display for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.original.name)
    }
}

// ============================================================================
// Term
// ============================================================================

// Arith and Prim enums removed — arithmetic and bytes operations
// now live entirely as TermSpec constants under `crate::defs`, and
// `builtins::reduce_spec` matches on them by `ptr_eq` for
// closed-form reduction.

/// HOL Light's primitive operators, folded into the kernel.
///
/// Every variant denotes a *single* HOL constant. The
/// [`TermKind::HolOp`] variant pairs it with the instance type at the
/// point of use:
///
/// - Non-polymorphic ops (`Imp`, `Not`, `And`, `Or`, `Iff`,
///   `Trueprop`) take a fixed type (e.g., `bool → bool → bool`).
/// - Polymorphic ops (`Eq`, `Forall`, `Exists`, `Select`) carry the
///   instance type at α (e.g., `Eq` at α has full type
///   `α → α → bool`).
///
/// Soundness for the type field is enforced by `type_of_in`, which
/// matches the stored type against the operator's expected shape.
/// True / False are *not* HOL ops — they are kernel literals
/// [`TermKind::Bool`].
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum HolOp {
    /// HOL `=` at type `α → α → bool` for the α stored alongside.
    Eq,
    /// HOL `==>` at type `bool → bool → bool`.
    Imp,
    /// HOL `~` at type `bool → bool`.
    Not,
    /// HOL `/\` at type `bool → bool → bool`.
    And,
    /// HOL `\/` at type `bool → bool → bool`.
    Or,
    /// HOL `<=>` at type `bool → bool → bool`.
    Iff,
    /// HOL `∀` at type `(α → bool) → bool`.
    Forall,
    /// HOL `∃` at type `(α → bool) → bool`.
    Exists,
    /// HOL `ε` (Hilbert's choice) at type `(α → bool) → α`.
    Select,
    /// `Trueprop : bool → prop` — explicit coercion from HOL `bool` to
    /// the kernel's meta-prop, mirroring Isabelle/HOL's `Trueprop`.
    Trueprop,
}

impl HolOp {
    /// Printable label, matching HOL Light's surface syntax.
    pub fn label(&self) -> &'static str {
        match self {
            HolOp::Eq => "=",
            HolOp::Imp => "==>",
            HolOp::Not => "~",
            HolOp::And => "/\\",
            HolOp::Or => "\\/",
            HolOp::Iff => "<=>",
            HolOp::Forall => "!",
            HolOp::Exists => "?",
            HolOp::Select => "@",
            HolOp::Trueprop => "Trueprop",
        }
    }
}

impl fmt::Display for HolOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}


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
    Abs(BinderHint, Type, Term),
    /// Meta-implication `φ ⟹ ψ`.
    Imp(Term, Term),
    /// Meta-universal `⋀(hint:ty). body`. Same layout as `Abs`.
    All(BinderHint, Type, Term),
    /// Meta-equality `t ≡ u`.
    Eq(Term, Term),
    /// Builtin: opaque byte literal of kernel type `bytes`.
    Blob(Bytes),
    /// Builtin: natural-number literal. Kernel type `nat`. See
    /// [`crate::Thm::reduce_prim`] for the single-step computation
    /// rule that decides closed-form arithmetic by reflexivity.
    Nat(Nat),
    /// Builtin: integer literal. Kernel type `int`.
    Int(Int),
    /// Builtin: HOL `bool` literal (`T` / `F`). Kernel type
    /// `Tycon("bool", [])`. Folded into the kernel so HOL truth
    /// values aren't a separate observer system.
    Bool(bool),
    /// Folded-in HOL primitive operator at its instance type. See
    /// [`HolOp`] for the catalogue. Applications are formed by the
    /// usual `App` chain.
    HolOp(HolOp, Type),
    /// Application of a derived-term [`crate::defs::TermSpec`]
    /// factory to type arguments. The spec is process-shared
    /// (`LazyLock`-backed) and `args` is the positional substitution
    /// for the spec's type variables.
    ///
    /// Used by `crate::defs::*` to embed semi-trusted term constants
    /// (`natAdd`, `listMap`, …) as catalogue entries instead of
    /// dedicated kernel variants. `Thm::reduce_prim` recognises a
    /// `Spec(h, args)` leaf by `h.ptr_eq(&catalogue_handle)`.
    Spec(crate::defs::TermSpec, Vec<Type>),
    /// Typed observation leaf: observer + Pure type. The kernel
    /// compares these by `Arc` pointer identity (via [`Object`]'s
    /// impls), never by the user's `Eq` on the underlying observer.
    Obs(Object, Type),
    /// A defined constant. Each [`crate::Thm::define`] call produces
    /// a fresh `Def` (a fresh `Arc<Term>` allocation); the
    /// unfolding equation `Def ≡ body` is emitted by the same rule
    /// application. Two distinct `define` calls — even with the
    /// same name and same body — yield distinct `Def`s.
    Def(Def),
}

impl Term {
    pub fn kind(&self) -> &TermKind {
        &self.0
    }

    /// Pointer identity of the underlying `Arc`. Useful as a cache key
    /// for outside-the-TCB walkers (hashers, pretty-printers).
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }

    fn alloc(kind: TermKind) -> Self {
        Term(Arc::new(kind))
    }

    // ---- smart constructors ----
    pub fn bound(idx: u32) -> Self {
        Self::alloc(TermKind::Bound(idx))
    }
    pub fn free(name: impl Into<SmolStr>, ty: Type) -> Self {
        Self::alloc(TermKind::Free(name.into(), ty))
    }
    pub fn const_(name: impl Into<SmolStr>, ty: Type) -> Self {
        Self::alloc(TermKind::Const(name.into(), ty))
    }
    pub fn app(fun: Term, arg: Term) -> Self {
        Self::alloc(TermKind::App(fun, arg))
    }
    pub fn abs(hint: impl Into<BinderHint>, ty: Type, body: Term) -> Self {
        Self::alloc(TermKind::Abs(hint.into(), ty, body))
    }
    pub fn imp(lhs: Term, rhs: Term) -> Self {
        Self::alloc(TermKind::Imp(lhs, rhs))
    }
    pub fn all(hint: impl Into<BinderHint>, ty: Type, body: Term) -> Self {
        Self::alloc(TermKind::All(hint.into(), ty, body))
    }
    pub fn eq(lhs: Term, rhs: Term) -> Self {
        Self::alloc(TermKind::Eq(lhs, rhs))
    }
    pub fn blob(bytes: impl Into<Bytes>) -> Self {
        Self::alloc(TermKind::Blob(bytes.into()))
    }

    // ---- builtin value constructors ----
    /// `nat` literal.
    pub fn nat_lit(n: impl Into<Nat>) -> Self {
        Self::alloc(TermKind::Nat(n.into()))
    }
    /// `int` literal.
    pub fn int_lit(n: impl Into<Int>) -> Self {
        Self::alloc(TermKind::Int(n.into()))
    }

    /// HOL `bool` literal — `Bool(true)` is `T`, `Bool(false)` is
    /// `F`. Kernel type `bool`.
    pub fn bool_lit(b: bool) -> Self {
        Self::alloc(TermKind::Bool(b))
    }

    /// HOL operator constant at the supplied instance type. Used by
    /// `covalence-hol`'s `HolLightCtx::mk_*` builders.
    pub fn hol_op(op: HolOp, ty: Type) -> Self {
        Self::alloc(TermKind::HolOp(op, ty))
    }

    /// Apply a derived-term [`crate::defs::TermSpec`] to type
    /// arguments. The spec is process-shared (`LazyLock`-backed in
    /// `crate::defs`); two calls with handles from the same lazy
    /// static pointer-equal at the spec component.
    pub fn term_spec(spec: crate::defs::TermSpec, args: Vec<Type>) -> Self {
        Self::alloc(TermKind::Spec(spec, args))
    }

    /// Wrap an observer as a typed leaf. The kernel treats the
    /// underlying value opaquely; only the user code constructing
    /// `o` controls what observations exist.
    pub fn obs<O: Observer>(o: O, ty: Type) -> Self {
        Self::alloc(TermKind::Obs(Object::new(o), ty))
    }

    /// Like [`Term::obs`] but reuses an existing [`Object`] handle
    /// (preserving its `Arc` identity). Used by deserialisers and
    /// other shells that have already constructed a `Object`.
    pub fn obs_from_dyn(observer: Object, ty: Type) -> Self {
        Self::alloc(TermKind::Obs(observer, ty))
    }

    /// Wrap an existing [`Def`] as a `Term` leaf. Sharing the same
    /// `Def` via `clone` preserves kernel identity; constructing two
    /// distinct `Def`s with the same name produces two distinct
    /// `Term`s here.
    pub fn def(d: Def) -> Self {
        Self::alloc(TermKind::Def(d))
    }

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
            | TermKind::Blob(_)
            | TermKind::Nat(_)
            | TermKind::Int(_)
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::HolOp(_, _) => true,
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
            | TermKind::Blob(_)
            | TermKind::Nat(_)
            | TermKind::Int(_)
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::HolOp(_, _) => true,
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
                let o = observer
                    .downcast::<O>()
                    .ok_or(Error::ObsDowncastTypeMismatch)?;
                f(o);
                Ok(())
            }
            TermKind::Bound(_)
            | TermKind::Free(..)
            | TermKind::Const(..)
            | TermKind::Blob(_)
            | TermKind::Nat(_)
            | TermKind::Int(_)
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::HolOp(_, _) => Ok(()),
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
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Term {
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return Ordering::Equal;
        }
        self.0.cmp(&other.0)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
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
            TermKind::Nat(n) => write!(f, "{}n", n.as_inner()),
            TermKind::Int(n) => write!(f, "{}i", n.as_inner()),
            TermKind::Bool(b) => write!(f, "{}", if *b { "T" } else { "F" }),
            TermKind::HolOp(op, ty) => write!(f, "{op}:{ty}"),
            TermKind::Spec(spec, args) => {
                if args.is_empty() {
                    write!(f, "{}", spec.symbol().label())
                } else {
                    write!(f, "({}", spec.symbol().label())?;
                    for a in args {
                        write!(f, " {}", a)?;
                    }
                    write!(f, ")")
                }
            }
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
            if i >= env.ctx.len() {
                return Err(Error::NotClosed);
            }
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
                return Err(Error::TypeMismatch {
                    expected: dom.clone(),
                    got: arg_ty,
                });
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
            if !body_ty.is_prop() {
                return Err(Error::NotProp(body_ty));
            }
            Ok(Type::prop())
        }
        TermKind::Imp(a, b) => {
            let ta = type_of_in(a, env)?;
            if !ta.is_prop() {
                return Err(Error::NotProp(ta));
            }
            let tb = type_of_in(b, env)?;
            if !tb.is_prop() {
                return Err(Error::NotProp(tb));
            }
            Ok(Type::prop())
        }
        TermKind::Eq(a, b) => {
            let ta = type_of_in(a, env)?;
            let tb = type_of_in(b, env)?;
            if ta != tb {
                return Err(Error::TypeMismatch {
                    expected: ta,
                    got: tb,
                });
            }
            Ok(Type::prop())
        }
        TermKind::Blob(_) => Ok(Type::bytes()),
        TermKind::Nat(_) => Ok(Type::nat()),
        TermKind::Int(_) => Ok(Type::int()),
        TermKind::Bool(_) => Ok(Type::bool()),
        // A `Spec` leaf's type is the spec's own `ty` field (the
        // factory's carrier) with positional type-arg substitution
        // applied. The spec is held by handle; deref is cheap.
        TermKind::Spec(spec, args) => {
            let mut result = spec
                .ty()
                .cloned()
                .ok_or_else(|| Error::NotProp(Type::prop()))?;
            // free_tvars on the carrier gives the spec's tvar names
            // in canonical alphabetical order. Substitute positionally.
            let tvars = result.free_tvars();
            for (tvar_name, arg) in tvars.iter().zip(args.iter()) {
                result = crate::subst::subst_tfree_in_type(&result, tvar_name, arg);
            }
            Ok(result)
        }
        TermKind::HolOp(_, ty) => Ok(ty.clone()),
        TermKind::Obs(_, ty) => Ok(ty.clone()),
        // A `Def` denotes its body at the current instance type.
        // The body was validated once at `Thm::define` time, and
        // `subst_tfree_in_term` updates `instance_type` consistently
        // — so we can just read `instance_type` here without walking
        // through to the body. The body's Free-var tracking only
        // matters for the body itself; since this Term is just a
        // Def reference, there are no Free leaves to track at this
        // node.
        TermKind::Def(d) => Ok(d.instance_type().clone()),
    }
}
