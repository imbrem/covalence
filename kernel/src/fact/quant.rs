use crate::data::term::{Close, Fv};

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
pub struct Forall<T>(T);

mod close_children_sealed {
    pub trait CloseChildrenSealed<C> {}
}

pub(crate) use close_children_sealed::CloseChildrenSealed;

pub trait CloseChildren<C>: CloseChildrenSealed<C> {
    type ClosedChildren;

    fn close_children(self, var: Fv<C>) -> Self::ClosedChildren;
}

impl<C, T> CloseChildrenSealed<C> for Holds<T> {}

impl<C, T> CloseChildren<C> for Holds<T> {
    type ClosedChildren = Holds<Close<C, T>>;

    fn close_children(self, var: Fv<C>) -> Self::ClosedChildren {
        Holds(self.0, Close::new(var, self.1))
    }
}

impl<C, T> CloseChildrenSealed<C> for HasTy<T> {}

impl<C, T> CloseChildren<C> for HasTy<T>
where
    C: Copy,
{
    type ClosedChildren = HasTy<Close<C, T>>;

    fn close_children(self, var: Fv<C>) -> Self::ClosedChildren {
        HasTy {
            tm: Close::new(var, self.tm),
            ty: Close::new(var, self.ty),
        }
    }
}

impl<C, T> CloseChildrenSealed<C> for Eqn<T> {}

impl<C, T> CloseChildren<C> for Eqn<T>
where
    C: Copy,
{
    type ClosedChildren = Eqn<Close<C, T>>;

    fn close_children(self, var: Fv<C>) -> Self::ClosedChildren {
        Eqn(Close::new(var, self.0), Close::new(var, self.1))
    }
}

impl<C, P, T> CloseChildrenSealed<C> for Is<P, T> where P: IntoPred1 {}

impl<C, P, T> CloseChildren<C> for Is<P, T>
where
    P: IntoPred1,
{
    type ClosedChildren = Is<P, Close<C, T>>;

    fn close_children(self, var: Fv<C>) -> Self::ClosedChildren {
        Is(self.0, Close::new(var, self.1))
    }
}
