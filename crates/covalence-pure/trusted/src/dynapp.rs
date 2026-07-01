//! Dynamic application: an operator held behind `Arc<dyn DynOp>` applied to a
//! statically-sorted [`Dyn`] argument.
//!
//! [`DynApp`] is another **sealed** [`Expr`] shape (a grammar extension, ZERO new
//! mint): building one derives nothing — it is inert until an admitted rule
//! interprets it. It is *not* `Eq`, so it can never be a `trans` middle term.
//!
//! The escape hatch for when the **operator** is not known statically. When the
//! operator *is* static (only the operands vary), prefer a fixed-`Input`
//! [`Rule`](crate::Rule) over `App<StaticOp, (Dyn, Dyn)>` — one rule `TypeId` then
//! gates every operand shape at a sort (see the `Comm` pattern in the tests).

use std::any::{Any, TypeId};
use std::sync::Arc;

use crate::expr::{Dyn, Expr};
use crate::sealed;

/// An object-safe operator with a runtime identity. `op_id` is an **UNTRUSTED**
/// hint (a lying op may return any `TypeId`); the *sound* identity check is
/// [`DynApp::as_op`], which downcasts the operator **trait object itself** through
/// its `Any` supertrait — the compiler-built vtable carries the real concrete
/// `TypeId`, which downstream code cannot forge. Requiring `Any` (⇒ `'static`) is
/// what enables that upcast+downcast.
///
/// **There is deliberately no `as_any` method:** an `as_any` hook is implemented by
/// (untrusted) downstream code and could return a reference to a *different* value
/// of the target type, spoofing the downcast. Upcasting the real `&dyn DynOp` to
/// `&dyn Any` avoids trusting any downstream-supplied hook.
pub trait DynOp: Any {
    /// The argument sort.
    type In;
    /// The result sort.
    type Out;
    /// Untrusted identity hint — a filter only; never the soundness gate.
    fn op_id(&self) -> TypeId;
}

/// A runtime-shaped application: a dynamic operator applied to a statically-sorted
/// argument. Sealed [`Expr`] of sort `Out`; inert until an admitted rule interprets
/// it. Not `Eq` ⇒ never a `trans` middle.
pub struct DynApp<In, Out> {
    /// The dynamic operator.
    pub op: Arc<dyn DynOp<In = In, Out = Out>>,
    /// The (dynamic) argument, of sort `In`.
    pub arg: Dyn<In>,
}

impl<In, Out> sealed::Sealed for DynApp<In, Out> {}
impl<In, Out> Expr for DynApp<In, Out> {
    type Ty = Out;
}

impl<In: 'static, Out: 'static> DynApp<In, Out> {
    /// View this as an application of the concrete operator `F`. Identity is checked
    /// by upcasting the **real** operator trait object to `&dyn Any` (via the `Any`
    /// supertrait, stable trait-upcasting) and downcasting — the vtable's `TypeId`
    /// is the genuine concrete type, so **no downstream hook is trusted** and a
    /// lying op cannot spoof it. Returns `(&F, &arg)` iff the operator really is an
    /// `F`, else `None`.
    pub fn as_op<F: DynOp + 'static>(&self) -> Option<(&F, &Dyn<In>)> {
        let op: &dyn Any = &*self.op;
        op.downcast_ref::<F>().map(|f| (f, &self.arg))
    }
}
