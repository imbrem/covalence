//! Expressions: a typed, **sealed** first-order term language whose sort is the
//! associated type [`Expr::Ty`].
//!
//! Each expression *shape* is a distinct Rust type carrying its leaf values; the
//! sort is the associated type, so an expression has *exactly one* interpretation
//! (you cannot read it two ways). The trait is **sealed** — extend the vocabulary
//! by declaring new [`Op`](crate::Op)s and using [`App`], never by implementing
//! [`Expr`].
//!
//! Expressions are compared by **stdlib [`Eq`]** — `derive(Eq)` on each shape *is*
//! the structural equality [`Eqn::trans`](crate::Eqn::trans) uses to match middle
//! terms (and [`of_eq`](crate::of_eq) to introduce a leaf equation). "No `Eq`, no
//! comparison": a shape whose leaves aren't `Eq` simply can't be a `trans` middle.

use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

use crate::op::Op;
use crate::sealed;

/// A **faithful** pointer whose [`Deref::Target`] *is* the value it stands for —
/// `&T`, `Box<T>`, `Rc<T>`, `Arc<T>`. Marks "deref gives the actual value" (an
/// arbitrary `Deref` might project to something unrelated). Open: a custom faithful
/// smart pointer may add an impl — its `Target` is then the sort and its `Eq` the
/// comparison, both that pointer's own trust (like any leaf's `Eq`).
pub trait TrustedDeref: Deref {}
impl<T: ?Sized> TrustedDeref for &T {}
impl<T: ?Sized> TrustedDeref for Box<T> {}
impl<T: ?Sized> TrustedDeref for Rc<T> {}
impl<T: ?Sized> TrustedDeref for Arc<T> {}

/// A well-typed expression; [`Expr::Ty`] is its (unique) sort. **SEALED** — every
/// implementor is in this crate, so the shapes below are the whole grammar.
pub trait Expr: sealed::Sealed {
    /// The (unique) sort of this expression.
    type Ty;
}

/// A Rust value as a leaf expression — the type *is* the sort. The seam by which a
/// concrete native value enters the expression language.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Val<C>(pub C);

impl<C> sealed::Sealed for Val<C> {}
impl<C> Expr for Val<C> {
    type Ty = C;
}

/// A leaf expression behind a [`TrustedDeref`] pointer `P` — `Ref(&v)`,
/// `Ref(Rc::new(v))`, `Ref(Arc::new(v))`, `Ref(Box::new(v))`. The sort is the
/// pointee `P::Target`; compared by `P`'s `Eq` (which, for the std pointers,
/// compares pointees). The seam for sharing a sub-value without cloning it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ref<P>(pub P);

impl<P: TrustedDeref> sealed::Sealed for Ref<P> where P::Target: Sized {}
impl<P: TrustedDeref> Expr for Ref<P>
where
    P::Target: Sized,
{
    type Ty = P::Target;
}

/// Apply op `F: In → Out` to an argument expression of sort `In`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct App<F: Op, A>(pub F, pub A);

impl<F: Op, A: Expr<Ty = F::In>> sealed::Sealed for App<F, A> {}
impl<F: Op, A: Expr<Ty = F::In>> Expr for App<F, A> {
    type Ty = F::Out;
}

/// The canonical boolean constant `⊤`. Propositions reduce to `True`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct True;
impl sealed::Sealed for True {}
impl Expr for True {
    type Ty = bool;
}

/// The canonical boolean constant `⊥`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct False;
impl sealed::Sealed for False {}
impl Expr for False {
    type Ty = bool;
}

// A borrowed *expression* is the same expression (no move / clone). `&A` is `Eq`
// (via std) whenever `A` is.
impl<A: Expr + ?Sized> sealed::Sealed for &A {}
impl<A: Expr + ?Sized> Expr for &A {
    type Ty = A::Ty;
}

// The unsized principal `dyn Expr<Ty=T>` is *already* an `Expr` (and `Sealed`): a
// trait object automatically implements its own trait and its supertrait, so no
// explicit impl is written (nor allowed). Consequently the existing
// `impl Expr for &A` blanket covers `&dyn Expr<Ty=T>` for free. (Not `Eq`, so no
// `dyn` value can be a `trans` middle term — "no Eq, no comparison".)

// A pointer to an expression is itself an expression of the same sort, for ANY
// expr `A` — concrete OR `dyn` (the `?Sized` bound covers `Box<dyn Expr<Ty=T>>`).
// Each pointer needs its own impl (no `impl<A> Expr for Box<A>` in std to lean on),
// so a macro keeps the three in lockstep. Distinct self types ⇒ no coherence clash.
macro_rules! ptr_expr {
    ($p:ident) => {
        impl<A: Expr + ?Sized> sealed::Sealed for $p<A> {}
        impl<A: Expr + ?Sized> Expr for $p<A> {
            type Ty = A::Ty;
        }
    };
}
ptr_expr!(Box);
ptr_expr!(Rc);
ptr_expr!(Arc);

/// A dynamic, runtime-shaped operand of sort `T` (`Arc<dyn Expr<Ty=T>>`) with
/// **pointer equality**: two `Dyn`s are equal iff they share the same allocation.
/// That makes `Dyn` a valid `trans` middle through the *ordinary* [`Eqn::trans`]
/// (it is `Eq`), giving pointer-equality transitivity with NO `Eq` on the
/// underlying dynamic expression. Sealed ⇒ ZERO new TCB.
pub struct Dyn<T>(pub Arc<dyn Expr<Ty = T>>);

impl<T> sealed::Sealed for Dyn<T> {}
impl<T> Expr for Dyn<T> {
    type Ty = T;
}
impl<T> Clone for Dyn<T> {
    fn clone(&self) -> Self {
        Dyn(Arc::clone(&self.0))
    }
}
impl<T> Dyn<T> {
    /// Wrap any expression of sort `T` as a shared dynamic operand.
    pub fn new(e: impl Expr<Ty = T> + 'static) -> Self {
        Dyn(Arc::new(e))
    }
}
// Pointer equality: same allocation ⇒ same expression (sound, incomplete).
impl<T> PartialEq for Dyn<T> {
    fn eq(&self, o: &Self) -> bool {
        Arc::ptr_eq(&self.0, &o.0)
    }
}
impl<T> Eq for Dyn<T> {}
impl<T> std::fmt::Debug for Dyn<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Dyn(@{:p})", Arc::as_ptr(&self.0))
    }
}

// Products: tuples of expressions are expressions of the product sort (up to
// 12-ary). `(A, …)` is `Eq` (via std) whenever its components are.
macro_rules! tuple_expr {
    ($($T:ident),+) => {
        impl<$($T: Expr),+> sealed::Sealed for ($($T,)+) {}
        impl<$($T: Expr),+> Expr for ($($T,)+) {
            type Ty = ($($T::Ty,)+);
        }
    };
}
tuple_expr!(A, B);
tuple_expr!(A, B, C);
tuple_expr!(A, B, C, D);
tuple_expr!(A, B, C, D, E);
tuple_expr!(A, B, C, D, E, F);
tuple_expr!(A, B, C, D, E, F, G);
tuple_expr!(A, B, C, D, E, F, G, H);
tuple_expr!(A, B, C, D, E, F, G, H, I);
tuple_expr!(A, B, C, D, E, F, G, H, I, J);
tuple_expr!(A, B, C, D, E, F, G, H, I, J, K);
tuple_expr!(A, B, C, D, E, F, G, H, I, J, K, L);
