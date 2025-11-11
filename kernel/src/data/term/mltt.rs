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

mod kind_sealed {
    pub trait KindSealed {}
}

use kind_sealed::KindSealed;

/// A kind of term
pub trait Kind<const N: usize>: KindSealed {
    /// Get this term's binders
    fn binders(&self) -> [Bv; N] {
        [Bv::new(0); N]
    }
}

/// A unary term
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Tm1<K, T>(pub K, pub T);

impl<K: Copy, T> Tm1<K, T> {
    /// Get this term as a reference
    pub fn as_ref<'a>(&'a self) -> Tm1<K, &'a T> {
        Tm1(self.0, &self.1)
    }

    /// Get this term as a mutable reference
    pub fn as_mut<'a>(&'a mut self) -> Tm1<K, &'a mut T> {
        Tm1(self.0, &mut self.1)
    }
}

impl<K: Kind<1>> Tm1<K, Bv> {
    /// Get the bvi of this term
    pub fn max_bvi(&self) -> Bv {
        self.1 - self.0.binders()[0]
    }
}

/// A binary term
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Tm2<K, L, R = L>(pub K, pub L, pub R);

impl<K: Copy, L, R> Tm2<K, L, R> {
    /// Get this term as a reference
    pub fn as_ref<'a>(&'a self) -> Tm2<K, &'a L, &'a R> {
        Tm2(self.0, &self.1, &self.2)
    }

    /// Get this term as a mutable reference
    pub fn as_mut<'a>(&'a mut self) -> Tm2<K, &'a mut L, &'a mut R> {
        Tm2(self.0, &mut self.1, &mut self.2)
    }
}

impl<K: Kind<2>> Tm2<K, Bv, Bv> {
    /// Get the maximum bvi of this term
    pub fn max_bvi(&self) -> Bv {
        let binders = self.0.binders();
        (self.1 - binders[0]).max(self.2 - binders[1])
    }
}

/// A ternary term
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Tm3<K, L, M = L, R = L>(pub K, pub L, pub M, pub R);

impl<K: Copy, L, M, R> Tm3<K, L, M, R> {
    /// Get this term as a reference
    pub fn as_ref<'a>(&'a self) -> Tm3<K, &'a L, &'a M, &'a R> {
        Tm3(self.0, &self.1, &self.2, &self.3)
    }

    /// Get this term as a mutable reference
    pub fn as_mut<'a>(&'a mut self) -> Tm3<K, &'a mut L, &'a mut M, &'a mut R> {
        Tm3(self.0, &mut self.1, &mut self.2, &mut self.3)
    }
}

impl<K: Kind<3>> Tm3<K, Bv, Bv, Bv> {
    /// Get the maximum bvi of this term
    pub fn max_bvi(&self) -> Bv {
        let binders = self.0.binders();
        (self.1 - binders[0])
            .max(self.2 - binders[1])
            .max(self.3 - binders[2])
    }
}

macro_rules! impl_kind0 {
    ($ty:tt, $node:path) => {
        impl KindSealed for $ty {}

        impl Kind<0> for $ty {}

        impl<C, T, I, S> From<$ty> for Node<C, T, I, S> {
            fn from(_value: $ty) -> Self {
                $node
            }
        }

        impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for $ty {
            type Error = Node<C, T, I, S>;

            fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
                match value {
                    $node => Ok($ty),
                    _ => Err(value),
                }
            }
        }

        impl<C, T, I, S> PartialEq<$ty> for Node<C, T, I, S> {
            fn eq(&self, _other: &$ty) -> bool {
                match self {
                    $node => true,
                    _ => false,
                }
            }
        }

        impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for $ty {
            fn eq(&self, other: &Node<C, T, I, S>) -> bool {
                match other {
                    $node => true,
                    _ => false,
                }
            }
        }
    };
}

macro_rules! mk_kind0 {
    ($ty:tt, $node:path) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
        pub struct $ty;

        impl_kind0!($ty, $node);
    };
}

macro_rules! mk_kind1 {
    ($name:ident, $kname:ident, $node:path, $binders:expr) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
        pub struct $kname;

        impl KindSealed for $kname {}

        impl Kind<1> for $kname {
            fn binders(&self) -> [Bv; 1] {
                $binders
            }
        }

        pub type $name<T> = Tm1<$kname, T>;

        impl<T> $name<T> {
            pub const fn new(tm: T) -> Self {
                Tm1($kname, tm)
            }
        }

        impl<C, T, I, S> From<$name<T>> for Node<C, T, I, S> {
            fn from(value: $name<T>) -> Self {
                $node([value.1])
            }
        }

        impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for $name<T> {
            type Error = Node<C, T, I, S>;

            fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
                match value {
                    $node([a]) => Ok(Tm1($kname, a)),
                    other => Err(other),
                }
            }
        }

        impl<C, T, I, S> PartialEq<$name<T>> for Node<C, T, I, S>
        where
            T: PartialEq,
        {
            fn eq(&self, other: &$name<T>) -> bool {
                match self {
                    $node([a]) => a == &other.1,
                    _ => false,
                }
            }
        }

        impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for $name<T>
        where
            T: PartialEq,
        {
            fn eq(&self, other: &Node<C, T, I, S>) -> bool {
                match other {
                    $node([a]) => a == &self.1,
                    _ => false,
                }
            }
        }
    };
}

macro_rules! mk_kind2 {
    ($name:ident, $kname:ident, $node:path, $binders:expr) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
        pub struct $kname;

        impl KindSealed for $kname {}

        impl Kind<2> for $kname {
            fn binders(&self) -> [Bv; 2] {
                $binders
            }
        }

        pub type $name<L, R = L> = Tm2<$kname, L, R>;

        impl<L, R> $name<L, R> {
            pub const fn new(lhs: L, rhs: R) -> Self {
                Tm2($kname, lhs, rhs)
            }
        }

        impl<C, T, I, S> From<$name<T>> for Node<C, T, I, S> {
            fn from(value: $name<T>) -> Self {
                $node([value.1, value.2])
            }
        }

        impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for $name<T> {
            type Error = Node<C, T, I, S>;

            fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
                match value {
                    $node([a, b]) => Ok(Tm2($kname, a, b)),
                    other => Err(other),
                }
            }
        }

        impl<C, T, I, S> PartialEq<$name<T>> for Node<C, T, I, S>
        where
            T: PartialEq,
        {
            fn eq(&self, other: &$name<T>) -> bool {
                match self {
                    $node([a, b]) => a == &other.1 && b == &other.2,
                    _ => false,
                }
            }
        }

        impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for $name<T>
        where
            T: PartialEq,
        {
            fn eq(&self, other: &Node<C, T, I, S>) -> bool {
                match other {
                    $node([a, b]) => a == &self.1 && b == &self.2,
                    _ => false,
                }
            }
        }
    };
}

macro_rules! mk_kind3 {
    ($name:ident, $kname:ident, $node:path, $binders:expr) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
        pub struct $kname;

        impl KindSealed for $kname {}

        impl Kind<3> for $kname {
            fn binders(&self) -> [Bv; 3] {
                $binders
            }
        }

        pub type $name<L, M = L, R = L> = Tm3<$kname, L, M, R>;

        impl<L, M, R> $name<L, M, R> {
            pub const fn new(lhs: L, mid: M, rhs: R) -> Self {
                Tm3($kname, lhs, mid, rhs)
            }
        }

        impl<C, T, I, S> From<$name<T>> for Node<C, T, I, S> {
            fn from(value: $name<T>) -> Self {
                $node([value.1, value.2, value.3])
            }
        }

        impl<C, T, I, S> TryFrom<Node<C, T, I, S>> for $name<T> {
            type Error = Node<C, T, I, S>;

            fn try_from(value: Node<C, T, I, S>) -> Result<Self, Self::Error> {
                match value {
                    $node([a, b, c]) => Ok(Tm3($kname, a, b, c)),
                    other => Err(other),
                }
            }
        }

        impl<C, T, I, S> PartialEq<$name<T>> for Node<C, T, I, S>
        where
            T: PartialEq,
        {
            fn eq(&self, other: &$name<T>) -> bool {
                match self {
                    $node([a, b, c]) => a == &other.1 && b == &other.2 && c == &other.3,
                    _ => false,
                }
            }
        }

        impl<C, T, I, S> PartialEq<Node<C, T, I, S>> for $name<T>
        where
            T: PartialEq,
        {
            fn eq(&self, other: &Node<C, T, I, S>) -> bool {
                match other {
                    $node([a, b, c]) => a == &self.1 && b == &self.2 && c == &self.3,
                    _ => false,
                }
            }
        }
    };
}

impl_kind0!((), Node::Unit);
mk_kind0!(Null, Node::Null);
mk_kind0!(Empty, Node::Empty);
mk_kind2!(Eqn, EqnK, Node::Eqn, [Bv(0), Bv(0)]);
mk_kind2!(Pi, PiK, Node::Pi, [Bv(0), Bv(1)]);
mk_kind2!(Sigma, SigmaK, Node::Sigma, [Bv(0), Bv(1)]);
mk_kind2!(Abs, AbsK, Node::Abs, [Bv(0), Bv(1)]);
mk_kind2!(Pair, PairK, Node::Pair, [Bv(0), Bv(0)]);
mk_kind1!(Fst, FstK, Node::Fst, [Bv(0)]);
mk_kind1!(Snd, SndK, Node::Snd, [Bv(0)]);
mk_kind3!(Ite, IteK, Node::Ite, [Bv(0), Bv(1), Bv(1)]);
mk_kind1!(Trunc, TruncK, Node::Trunc, [Bv(0)]);
mk_kind2!(Choose, ChooseK, Node::Choose, [Bv(0), Bv(1)]);
mk_kind1!(Succ, SuccK, Node::Succ, [Bv(0)]);
mk_kind3!(Natrec, NatrecK, Node::Natrec, [Bv(1), Bv(1), Bv(0)]);
mk_kind2!(HasTy, HasTyK, Node::HasTy, [Bv(0), Bv(0)]);

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
