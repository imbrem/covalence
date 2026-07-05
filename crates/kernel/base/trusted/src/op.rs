//! Operation symbols — a first-class, extensible vocabulary with pointer + `dyn`
//! support (this subsumes the old `DynApp`/`DynOp`).

use std::any::Any;
use std::rc::Rc;
use std::sync::Arc;

/// An operation symbol `In → Out`. May carry data (the impl type's fields).
/// `In`/`Out` are plain types — **sorts need no trait**; any Rust type becomes a
/// sort the moment it is wrapped in [`crate::Val`]. Relations are ops with
/// `Out = bool`.
///
/// `Op` says nothing about *evaluation*: writing `App<F, _>` is always sound
/// (uninterpreted ⇒ inert). Evaluation arrives separately via
/// [`crate::CanonRule`], and is gated by a language's manifest.
///
/// **`Any` supertrait** (⇒ `Op: 'static`): a `dyn Op` operator can be downcast to
/// its real concrete type through [`App::as_op`](crate::App::as_op), whose soundness rests on the
/// compiler-built vtable's genuine `TypeId`. Ops are already `'static` (they are
/// symbols), so this costs nothing. This is the **open vocabulary** — extend it by
/// declaring new `Op`s, never with a `newtype Op(F)` wrapper.
pub trait Op: Any {
    /// The argument sort.
    type In;
    /// The result sort.
    type Out;
}

// ---- Pointer forwarding: a pointer to an op is an op with the same signature ----
//
// Distinct self types ⇒ no coherence clash with each other or with concrete ops.
// `F: Op ⟹ F: 'static` (via the `Any` supertrait), so `Box<F>`/`Rc<F>`/`Arc<F>`
// are `'static` and satisfy `Op: Any`. `Arc<dyn Op<In=I, Out=O>>` is then itself an
// `Op`, so `App<Arc<dyn Op<..>>, A>` IS a dynamic application — no separate type.

macro_rules! ptr_op {
    ($p:ident) => {
        impl<F: Op + ?Sized> Op for $p<F> {
            type In = F::In;
            type Out = F::Out;
        }
    };
}
ptr_op!(Box);
ptr_op!(Rc);
ptr_op!(Arc);

// A shared reference is an op too. It must be `&'static F` (not a generic `&'a F`):
// the `Any` supertrait requires `Self: 'static`, which `&'a F` satisfies only for
// `'a = 'static`. (Deviation from the blueprint's `&F` — the sound specialization.)
impl<F: Op + ?Sized> Op for &'static F {
    type In = F::In;
    type Out = F::Out;
}
