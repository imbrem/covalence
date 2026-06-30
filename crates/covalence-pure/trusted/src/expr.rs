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

use crate::op::Op;

mod sealed {
    pub trait Sealed {}
}

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

/// A borrowed *raw value* leaf — no clone. Compared by value (deref) under `Eq`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ref<'a, C>(pub &'a C);

impl<C> sealed::Sealed for Ref<'_, C> {}
impl<C> Expr for Ref<'_, C> {
    type Ty = C;
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

// A dynamic, runtime-shaped expression — sealed ⇒ genuine, ZERO new TCB. (It is
// not `Eq`, so it cannot be a `trans` middle term — "no Eq, no comparison".)
impl<T> sealed::Sealed for Box<dyn Expr<Ty = T>> {}
impl<T> Expr for Box<dyn Expr<Ty = T>> {
    type Ty = T;
}

// Products: 2-tuples of expressions are expressions of the product sort. `(A, B)`
// is `Eq` (via std) whenever `A` and `B` are.
impl<A: Expr, B: Expr> sealed::Sealed for (A, B) {}
impl<A: Expr, B: Expr> Expr for (A, B) {
    type Ty = (A::Ty, B::Ty);
}
