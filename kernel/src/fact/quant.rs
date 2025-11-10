use crate::{
    data::term::{Close1, Fv},
    fact::stable::StableFactIn,
};

use super::*;

/// A quantified statement, of the form `Q . S`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Quantified<Q, S> {
    /// The quantifier for this statement
    pub binder: Q,
    /// The body of this statement
    pub body: S,
}

/// A universal quantifier
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Forall<T>(pub T);

pub trait CloseChildren<C, D> {
    type Close1Children: StableFactIn<C, D>;

    fn close1_children(self, var: Fv<C>) -> Self::Close1Children;

    //TODO: segment close
}

impl<D, C, T> CloseChildren<C, D> for Holds<T>
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
{
    type Close1Children = Holds<Close1<C, T>>;

    fn close1_children(self, var: Fv<C>) -> Self::Close1Children {
        Holds(self.0, Close1::new(var, self.1))
    }
}

impl<D, C, L, R> CloseChildren<C, D> for HasTy<L, R>
where
    C: Ctx<D> + Copy,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
    type Close1Children = HasTy<Close1<C, L>, Close1<C, R>>;

    fn close1_children(self, var: Fv<C>) -> Self::Close1Children {
        HasTy {
            tm: Close1::new(var, self.tm),
            ty: Close1::new(var, self.ty),
        }
    }
}

impl<D, C, L, R> CloseChildren<C, D> for Eqn<L, R>
where
    C: Ctx<D> + Copy,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
    type Close1Children = Eqn<Close1<C, L>, Close1<C, R>>;

    fn close1_children(self, var: Fv<C>) -> Self::Close1Children {
        Eqn(Close1::new(var, self.0), Close1::new(var, self.1))
    }
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
