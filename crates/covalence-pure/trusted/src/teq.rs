//! Trusted equality on leaf values — the seam by which native Rust computation
//! enters the kernel.

use std::any::Any;

/// Trusted, **sound-but-partial** equality at a sort `C`: `teq(a, b) == true`
/// ⟹ `a` and `b` are *genuinely* equal (so an [`crate::Eqn`] between
/// `Val(a)`/`Val(b)` holds in **any** language). It MAY return `false` for equal
/// values — incompleteness is fine.
///
/// **DISTINCT from [`PartialEq`].** `PartialEq` is untrusted (a buggy or
/// deliberately-wrong impl is allowed by the type system); implementing
/// `TrustedEq` is a deliberate **TCB claim**: you are asserting that `true` means
/// real semantic equality. This is the audited boundary at which Rust (and later
/// WASM) computation is admitted into proofs.
pub trait TrustedEq {
    /// Sound, possibly-incomplete equality decision.
    fn teq(&self, other: &Self) -> bool;
}

impl TrustedEq for bool {
    fn teq(&self, other: &Self) -> bool {
        self == other
    }
}

/// The unit context (`()` = the base language value) — all values are equal.
impl TrustedEq for () {
    fn teq(&self, _other: &Self) -> bool {
        true
    }
}

impl<A: TrustedEq, B: TrustedEq> TrustedEq for (A, B) {
    fn teq(&self, other: &Self) -> bool {
        self.0.teq(&other.0) && self.1.teq(&other.1)
    }
}

mod sealed {
    /// Sealed marker: [`LeafEq`](super::LeafEq) can be obtained **only** through the
    /// blanket over [`TrustedEq`](super::TrustedEq) below. A downstream type cannot
    /// name this trait, so it cannot hand-write a `LeafEq` (which would let it lie
    /// in `dyn_teq`); the only route to being a leaf is a real `TrustedEq` impl.
    pub trait Sealed {}
    impl<T: super::TrustedEq + 'static> Sealed for T {}
}

/// Object-safe erased view of a `'static` [`TrustedEq`] leaf, used by the trusted
/// structural equality on expressions (see [`crate::struct_eq`]) to compare leaf
/// payloads behind `dyn`. **Framework TCB.**
///
/// **Sealed** (`: sealed::Sealed`): the *only* implementor is the blanket over
/// `TrustedEq + 'static`, so a sort's equality is declared in exactly one place —
/// [`TrustedEq`] — which is the single, greppable leaf-equality audit surface.
/// (This is *audit-surface unification*, not anti-forgery: a leaf equality is the
/// sort's *definition* of equality — it may legitimately be a quotient identifying
/// distinct representations, and is sound on its own. Unsoundness arises only from
/// *also* admitting a distinguishing op inconsistent with it — and that op's
/// reduction must itself be in the TCB, so it is an enumerated, self-inflicted
/// inconsistency, not a forgery.)
///
/// A hand-written `LeafEq` is rejected — leaf equality goes through `TrustedEq`:
///
/// ```compile_fail
/// use covalence_pure_trusted::LeafEq;
/// use std::any::Any;
/// struct Evil;
/// // Evil does NOT implement TrustedEq, so it cannot satisfy LeafEq's sealed
/// // supertrait — this fails to compile (no lying `dyn_teq` is reachable):
/// impl LeafEq for Evil {
///     fn as_any(&self) -> &dyn Any { self }
///     fn dyn_teq(&self, _o: &dyn LeafEq) -> bool { true }
/// }
/// ```
pub trait LeafEq: sealed::Sealed + 'static {
    /// Upcast for type-directed downcasting in [`LeafEq::dyn_teq`].
    fn as_any(&self) -> &dyn Any;
    /// Sound erased equality: downcast `other` to `Self`'s concrete type, then
    /// `teq`. Different concrete types ⇒ `false` (sound: not the same leaf).
    fn dyn_teq(&self, other: &dyn LeafEq) -> bool;
}

impl<T: TrustedEq + 'static> LeafEq for T {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn dyn_teq(&self, other: &dyn LeafEq) -> bool {
        match other.as_any().downcast_ref::<T>() {
            Some(o) => self.teq(o),
            None => false,
        }
    }
}
