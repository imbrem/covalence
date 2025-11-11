use std::convert::Infallible;

pub use crate::univ::ULvl;

pub mod bv;
pub mod mltt;
pub mod node;

pub use bv::*;
pub use mltt::*;
pub use node::*;

/// A term localized in a given context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct TmIn<C, T> {
    /// The context being imported from
    pub ctx: C,
    /// The term being imported (in `ctx`)
    pub ix: T,
}

impl<C, T> TmIn<C, T> {
    /// Borrow this import
    pub const fn as_ref(&self) -> TmIn<&C, &T> {
        TmIn {
            ctx: &self.ctx,
            ix: &self.ix,
        }
    }

    /// Borrow this import mutably
    pub const fn as_mut(&mut self) -> TmIn<&mut C, &mut T> {
        TmIn {
            ctx: &mut self.ctx,
            ix: &mut self.ix,
        }
    }
}

/// A variable closure under `k` binders
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Close1<C, T> {
    /// The number of binders being closed under
    pub under: Bv,
    /// The variable being closed over
    pub var: Fv<C>,
    /// The term being closed over (in `this`, _not_ necessarily `ctx`)
    pub tm: T,
}

impl<C, T> Close1<C, T> {
    /// Construct a new closure, under no variables
    pub fn new(var: Fv<C>, tm: T) -> Close1<C, T> {
        Close1 {
            under: Bv(0),
            var,
            tm,
        }
    }

    /// Borrow this closure
    pub fn as_ref(&self) -> Close1<&C, &T> {
        Close1 {
            under: self.under,
            var: self.var.as_ref(),
            tm: &self.tm,
        }
    }

    /// Borrow this closure mutably
    pub fn as_mut(&mut self) -> Close1<&mut C, &mut T> {
        Close1 {
            under: self.under,
            var: self.var.as_mut(),
            tm: &mut self.tm,
        }
    }

    /// Lift this close under `n` binders
    pub fn lift(self, n: Bv) -> Close1<C, T> {
        Close1 {
            under: self.under + n,
            var: self.var,
            tm: self.tm,
        }
    }

    /// Get this closure as an operation
    pub fn op(self) -> Close1<C, ()> {
        Close1 {
            under: self.under,
            var: self.var,
            tm: (),
        }
    }
}

impl<C> Close1<C, Bv> {
    /// Get an upper bound on the bound variables in this closure
    pub fn bvi(&self) -> Bv {
        self.under.succ().max(self.tm.succ())
    }
}

impl<C, LT, RT> Close1<C, (LT, RT)>
where
    C: Copy,
{
    /// Convert a close of pairs into a pair of closes
    pub fn into_pair(self) -> (Close1<C, LT>, Close1<C, RT>) {
        (
            Close1 {
                under: self.under,
                var: self.var,
                tm: self.tm.0,
            },
            Close1 {
                under: self.under,
                var: self.var,
                tm: self.tm.1,
            },
        )
    }
}

impl<C, T> From<TmIn<C, T>> for Node<C, T> {
    fn from(copy: TmIn<C, T>) -> Self {
        Node::Quote(copy)
    }
}

impl<C, T, I> From<Close1<C, T>> for Node<C, T, I> {
    fn from(close: Close1<C, T>) -> Self {
        Node::Close1(close)
    }
}

impl<C, T, I> PartialEq<Close1<C, T>> for Node<C, T, I>
where
    C: PartialEq,
    T: PartialEq,
{
    fn eq(&self, other: &Close1<C, T>) -> bool {
        match self {
            Node::Close1(this) => this == other,
            _ => false,
        }
    }
}

impl<C, T, I> PartialEq<Node<C, T, I>> for Close1<C, T>
where
    C: PartialEq,
    T: PartialEq,
{
    fn eq(&self, other: &Node<C, T, I>) -> bool {
        other.eq(self)
    }
}

/// A single substitution
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Subst1<L, R = L> {
    /// How many binders to substitute under
    pub under: Bv,
    /// The term to substitute in
    pub bound: L,
    /// The term to substitute into
    pub body: R,
}

impl<C, T, I> From<Subst1<T>> for Node<C, T, I> {
    fn from(subst: Subst1<T>) -> Self {
        Node::Subst1(subst.under, [subst.bound, subst.body])
    }
}

impl<C, T, I> TryFrom<Node<C, T, I>> for Subst1<T> {
    type Error = Node<C, T, I>;

    fn try_from(value: Node<C, T, I>) -> Result<Self, Self::Error> {
        match value {
            Node::Subst1(k, [a, b]) => Ok(Subst1 {
                under: k,
                bound: a,
                body: b,
            }),
            other => Err(other),
        }
    }
}

impl<C, T, I> PartialEq<Subst1<T>> for Node<C, T, I>
where
    T: PartialEq,
{
    fn eq(&self, other: &Subst1<T>) -> bool {
        match self {
            Node::Subst1(k, [a, b]) => k == &other.under && a == &other.bound && b == &other.body,
            _ => false,
        }
    }
}

impl<C, T, I> PartialEq<Node<C, T, I>> for Subst1<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Node<C, T, I>) -> bool {
        other.eq(self)
    }
}
