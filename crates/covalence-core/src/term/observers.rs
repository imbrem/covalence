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
//! The **only** kernel rule that operates on observations is
//! [`crate::Thm::obs_eq`], which equates two applications whose heads
//! are observations of the same Rust type at the same Pure type. There
//! is no kernel rule for "this observation is true / equal to some
//! non-observation term" — that kind of fact is added via
//! [`crate::Thm::assume`] as an explicit meaning axiom, visible in
//! every dependent theorem's hypotheses.

use std::any::{Any, TypeId};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use super::terms::Term;

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
/// Stored as `Arc<dyn Hint>` so the same hint instance can be passed
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
