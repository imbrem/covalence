//! Expressions: a typed, **sealed** first-order term language whose sort is the
//! associated type [`Expr::Ty`].
//!
//! Each expression *shape* is a distinct Rust type carrying its leaf values; the
//! sort is the associated type, so an expression has *exactly one* interpretation
//! (you cannot read it two ways). The trait is **sealed** — extend the vocabulary
//! by declaring new [`Op`](crate::Op)s and using [`App`], never by implementing
//! [`Expr`].

use crate::op::Op;
use crate::teq::LeafEq;

mod sealed {
    pub trait Sealed {}
}

/// A well-typed expression; [`Expr::Ty`] is its (unique) sort. **SEALED** — every
/// implementor is in this crate, so the closed set of shapes below is the whole
/// expression grammar, and the trusted [`StructEq`] below is exhaustive.
///
/// `Expr` carries exactly one operation — the object-safe, framework-TCB trusted
/// structural equality (via the [`StructEq`] supertrait) — which is what makes
/// `dyn Expr` usable and what [`Eqn::trans`](crate::Eqn::trans) uses to check
/// that two middle terms really match.
pub trait Expr: sealed::Sealed + StructEq {
    /// The (unique) sort of this expression.
    type Ty;
}

/// A structural view of an expression's top level, used by [`struct_eq`]. The
/// closed set of cases mirrors the sealed [`Expr`] grammar.
pub enum View<'a> {
    /// The canonical `⊤`.
    True,
    /// The canonical `⊥`.
    False,
    /// A leaf value ([`Val`]/[`Ref`]), compared via its [`LeafEq`].
    Leaf(&'a dyn LeafEq),
    /// `App(op, arg)`: an operator (compared as a leaf — type + carried data) and
    /// its argument sub-expression.
    App(&'a dyn LeafEq, &'a dyn StructEq),
    /// A 2-tuple product, compared componentwise.
    Pair(&'a dyn StructEq, &'a dyn StructEq),
}

/// Object-safe trusted **structural equality** on expressions. Audited once here;
/// `struct_eq(a, b) == true` ⟹ `a` and `b` denote the same expression in every
/// language. Sound and (for `'static` leaves) complete.
pub trait StructEq {
    /// Expose this expression's top-level structure.
    fn view(&self) -> View<'_>;
}

/// The trusted structural equality decision. Recurses over [`View`]: leaves via
/// [`LeafEq::dyn_teq`], applications by operator-identity + argument, pairs
/// componentwise. Distinct shapes ⇒ `false`.
pub fn struct_eq(a: &dyn StructEq, b: &dyn StructEq) -> bool {
    match (a.view(), b.view()) {
        (View::True, View::True) => true,
        (View::False, View::False) => true,
        (View::Leaf(x), View::Leaf(y)) => x.dyn_teq(y),
        (View::App(o1, a1), View::App(o2, a2)) => o1.dyn_teq(o2) && struct_eq(a1, a2),
        (View::Pair(l1, r1), View::Pair(l2, r2)) => struct_eq(l1, l2) && struct_eq(r1, r2),
        _ => false,
    }
}

/// A Rust value as a leaf expression — the type *is* the sort. The seam by which
/// a concrete native value enters the expression language.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Val<C>(pub C);

impl<C: LeafEq> sealed::Sealed for Val<C> {}
impl<C: LeafEq> StructEq for Val<C> {
    fn view(&self) -> View<'_> {
        View::Leaf(&self.0)
    }
}
impl<C: LeafEq> Expr for Val<C> {
    type Ty = C;
}

/// A borrowed *raw value* leaf — no clone; the home of pointer/borrow leaves.
/// `C` is `'static` (so the leaf can be compared), but the borrow `'a` is free.
#[derive(Clone, Copy, Debug)]
pub struct Ref<'a, C>(pub &'a C);

impl<C: LeafEq> sealed::Sealed for Ref<'_, C> {}
impl<C: LeafEq> StructEq for Ref<'_, C> {
    fn view(&self) -> View<'_> {
        View::Leaf(self.0)
    }
}
impl<C: LeafEq> Expr for Ref<'_, C> {
    type Ty = C;
}

/// Apply op `F: In → Out` to an argument expression of sort `In`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct App<F: Op, A>(pub F, pub A);

impl<F: Op + LeafEq, A: Expr<Ty = F::In>> sealed::Sealed for App<F, A> {}
impl<F: Op + LeafEq, A: Expr<Ty = F::In>> StructEq for App<F, A> {
    fn view(&self) -> View<'_> {
        View::App(&self.0, &self.1)
    }
}
impl<F: Op + LeafEq, A: Expr<Ty = F::In>> Expr for App<F, A> {
    type Ty = F::Out;
}

/// The canonical boolean constant `⊤`. Propositions reduce to `True`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct True;
impl sealed::Sealed for True {}
impl StructEq for True {
    fn view(&self) -> View<'_> {
        View::True
    }
}
impl Expr for True {
    type Ty = bool;
}

/// The canonical boolean constant `⊥`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct False;
impl sealed::Sealed for False {}
impl StructEq for False {
    fn view(&self) -> View<'_> {
        View::False
    }
}
impl Expr for False {
    type Ty = bool;
}

// A borrowed *expression* is the same expression (no move / clone).
impl<A: Expr + ?Sized> sealed::Sealed for &A {}
impl<A: Expr + ?Sized> StructEq for &A {
    fn view(&self) -> View<'_> {
        (**self).view()
    }
}
impl<A: Expr + ?Sized> Expr for &A {
    type Ty = A::Ty;
}

// A dynamic, runtime-shaped expression — sealed ⇒ genuine, ZERO new TCB.
impl<T> sealed::Sealed for Box<dyn Expr<Ty = T>> {}
impl<T> StructEq for Box<dyn Expr<Ty = T>> {
    fn view(&self) -> View<'_> {
        (**self).view()
    }
}
impl<T> Expr for Box<dyn Expr<Ty = T>> {
    type Ty = T;
}

// Products: 2-tuples of expressions are expressions of the product sort.
impl<A: Expr, B: Expr> sealed::Sealed for (A, B) {}
impl<A: Expr, B: Expr> StructEq for (A, B) {
    fn view(&self) -> View<'_> {
        View::Pair(&self.0, &self.1)
    }
}
impl<A: Expr, B: Expr> Expr for (A, B) {
    type Ty = (A::Ty, B::Ty);
}
