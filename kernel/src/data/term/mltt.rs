use super::*;

/// A variable index in `covalence`'s core calculus
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Fv<C> {
    pub ctx: C,
    pub ix: u32,
}

impl<C> Fv<C> {
    pub fn as_ref(&self) -> Fv<&C> {
        Fv {
            ctx: &self.ctx,
            ix: self.ix,
        }
    }

    pub fn as_mut(&mut self) -> Fv<&mut C> {
        Fv {
            ctx: &mut self.ctx,
            ix: self.ix,
        }
    }
}

impl<C, T, I, S> From<Fv<C>> for Node<C, T, I, S> {
    fn from(x: Fv<C>) -> Self {
        Node::Fv(x)
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for Fv<C> {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Fv(x) => Ok(x),
            _ => Err(value),
        }
    }
}

impl<C: PartialEq, T, I, S> PartialEq<Fv<C>> for Node<C, T, I, S> {
    fn eq(&self, other: &Fv<C>) -> bool {
        match self {
            Node::Fv(this) => this == other,
            _ => false,
        }
    }
}

impl<C: PartialEq, T, I, S> PartialEq<Node<C, T, I, S>> for Fv<C> {
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

impl<C, T, I, S> From<Bv> for Node<C, T, I, S> {
    fn from(bv: Bv) -> Self {
        Node::Bv(bv)
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for Bv {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Bv(bv) => Ok(bv),
            _ => Err(value),
        }
    }
}

impl<C, T, I, S> PartialEq<Bv> for Node<C, T, I, S> {
    fn eq(&self, other: &Bv) -> bool {
        match self {
            Node::Bv(this) => this == other,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for Bv {
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

impl<C, T, I, S> From<ULvl> for Node<C, T, I, S> {
    fn from(level: ULvl) -> Self {
        Node::U(level)
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for ULvl {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::U(level) => Ok(level),
            _ => Err(value),
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for ULvl {
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        match other {
            Node::U(this) => this == self,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<ULvl> for Node<C, T, I, S> {
    fn eq(&self, other: &ULvl) -> bool {
        other.eq(self)
    }
}

impl<C, T, I, S> From<()> for Node<C, T, I, S> {
    fn from(_value: ()) -> Self {
        Node::Unit
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for () {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Unit => Ok(()),
            _ => Err(value),
        }
    }
}

impl<C, T, I, S> PartialEq<()> for Node<C, T, I, S> {
    fn eq(&self, _other: &()) -> bool {
        match self {
            Node::Unit => true,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for () {
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Null;

impl<C, T, I, S> From<Null> for Node<C, T, I, S> {
    fn from(_value: Null) -> Self {
        Node::Null
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for Null {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Null => Ok(Null),
            _ => Err(value),
        }
    }
}

impl<C, T, I, S> PartialEq<Null> for Node<C, T, I, S> {
    fn eq(&self, _other: &Null) -> bool {
        match self {
            Node::Null => true,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for Null {
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Empty;

impl<C, T, I, S> From<Empty> for Node<C, T, I, S> {
    fn from(_value: Empty) -> Self {
        Node::Empty
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for Empty {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Empty => Ok(Empty),
            _ => Err(value),
        }
    }
}

impl<C, T, I, S> PartialEq<Empty> for Node<C, T, I, S> {
    fn eq(&self, _other: &Empty) -> bool {
        match self {
            Node::Empty => true,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for Empty {
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

impl<C, T, I, S> From<bool> for Node<C, T, I, S> {
    fn from(value: bool) -> Self {
        if value { Node::Unit } else { Node::Empty }
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for bool {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Unit => Ok(true),
            Node::Empty => Ok(false),
            _ => Err(value),
        }
    }
}

impl<C, T, I, S> PartialEq<bool> for Node<C, T, I, S> {
    fn eq(&self, other: &bool) -> bool {
        match self {
            Node::Unit => *other,
            Node::Empty => !*other,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for bool {
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

/// An equation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Eqn<L, R = L>(L, R);

impl<C, T, I, S> From<Eqn<T>> for Node<C, T, I, S> {
    fn from(eqn: Eqn<T>) -> Self {
        Node::Eqn([eqn.0, eqn.1])
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for Eqn<T> {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Eqn([a, b]) => Ok(Eqn(a, b)),
            other => Err(other),
        }
    }
}

impl<C, T, I, S> PartialEq<Eqn<T>> for Node<C, T, I, S>
where
    T: PartialEq,
{
    fn eq(&self, other: &Eqn<T>) -> bool {
        match self {
            Node::Eqn([a, b]) => a == &other.0 && b == &other.1,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for Eqn<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

/// A pi type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Pi<L, R = L> {
    /// The type of the argument
    pub ty: L,
    /// The body of the pi type
    pub body: R,
}

impl<C, T, I, S> From<Pi<T>> for Node<C, T, I, S> {
    fn from(pi: Pi<T>) -> Self {
        Node::Pi([pi.ty, pi.body])
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for Pi<T> {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Pi([a, b]) => Ok(Pi { ty: a, body: b }),
            other => Err(other),
        }
    }
}

impl<C, T, I, S> PartialEq<Pi<T>> for Node<C, T, I, S>
where
    T: PartialEq,
{
    fn eq(&self, other: &Pi<T>) -> bool {
        match self {
            Node::Pi([a, b]) => a == &other.ty && b == &other.body,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for Pi<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

/// A sigma type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Sigma<L, R = L> {
    /// The type of the first component
    pub fst: L,
    /// The type of the second component
    pub snd: R,
}

impl<C, T, I, S> From<Sigma<T>> for Node<C, T, I, S>
where
    T: Clone,
{
    fn from(sigma: Sigma<T>) -> Self {
        Node::Sigma([sigma.fst, sigma.snd])
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for Sigma<T>
where
    T: Clone,
{
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Sigma([a, b]) => Ok(Sigma { fst: a, snd: b }),
            other => Err(other),
        }
    }
}

impl<C, T, I, S> PartialEq<Sigma<T>> for Node<C, T, I, S>
where
    T: PartialEq,
{
    fn eq(&self, other: &Sigma<T>) -> bool {
        match self {
            Node::Sigma([a, b]) => a == &other.fst && b == &other.snd,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for Sigma<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

/// An abstraction
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Abs<L, R = L> {
    /// The type of the argument
    pub ty: L,
    /// The body of the abstraction
    pub body: R,
}

impl<C, T, I, S> From<Abs<T>> for Node<C, T, I, S> {
    fn from(abs: Abs<T>) -> Self {
        Node::Abs([abs.ty, abs.body])
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for Abs<T> {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::Abs([a, b]) => Ok(Abs { ty: a, body: b }),
            other => Err(other),
        }
    }
}

impl<C, T, I, S> PartialEq<Abs<T>> for Node<C, T, I, S>
where
    T: PartialEq,
{
    fn eq(&self, other: &Abs<T>) -> bool {
        match self {
            Node::Abs([a, b]) => a == &other.ty && b == &other.body,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for Abs<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct HasTy<L, R = L> {
    pub tm: L,
    pub ty: R,
}

impl<C, T, I, S> From<HasTy<T>> for Node<C, T, I, S> {
    fn from(has_ty: HasTy<T>) -> Self {
        Node::HasTy([has_ty.tm, has_ty.ty])
    }
}

impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for HasTy<T> {
    type Error = Node<C, T, I, S>;

    fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
        match value {
            Node::HasTy([a, b]) => Ok(HasTy { tm: a, ty: b }),
            other => Err(other),
        }
    }
}

impl<C, T, I, S> PartialEq<HasTy<T>> for Node<C, T, I, S>
where
    T: PartialEq,
{
    fn eq(&self, other: &HasTy<T>) -> bool {
        match self {
            Node::HasTy([a, b]) => a == &other.tm && b == &other.ty,
            _ => false,
        }
    }
}

impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for HasTy<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Node<C, T, I, S>) -> bool {
        other.eq(self)
    }
}
