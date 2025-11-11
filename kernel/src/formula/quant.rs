use crate::{
    data::term::{Close1, Fv},
    formula::{IntoPred1, Is, Rw, stable::StableFormula},
    store::{Ctx, LocalTerm},
};

/// A quantified formula, of the form `Q . F`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Quantified<Q, S> {
    /// The quantifier for this formula
    pub binder: Q,
    /// The body of this formula
    pub body: S,
}

/// A universal quantifier
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Forall<T>(pub T);

pub trait CloseChildren<C, D>: StableFormula<C, D> {
    type Close1Children: StableFormula<C, D>;

    fn close1_children(self, var: Fv<C>) -> Self::Close1Children;
}

impl<D, C, P, T> CloseChildren<C, D> for Is<P, T>
where
    P: IntoPred1,
    C: Ctx<D>,
    T: LocalTerm<C, D>,
{
    type Close1Children = Is<P, Close1<C, T>>;

    fn close1_children(self, var: Fv<C>) -> Self::Close1Children {
        Is(self.0, Close1::new(var, self.1))
    }
}

impl<D, C, L, R> CloseChildren<C, D> for Rw<L, R>
where
    C: Ctx<D> + Copy,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
    type Close1Children = Rw<Close1<C, L>, Close1<C, R>>;

    fn close1_children(self, var: Fv<C>) -> Self::Close1Children {
        Rw(Close1::new(var, self.0), Close1::new(var, self.1))
    }
}
