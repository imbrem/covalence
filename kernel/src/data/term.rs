use std::{
    fmt::{self, Debug},
    ops::{Add, Sub},
};

/// A term in `covalence`'s core calculus
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub enum NodeT<C, T, I = Val<C, T>> {
    // == Term formers, corresponding to Tm from `gt3-lean` ==
    /// A free variable
    Fv(Fv<C>),
    /// A bound variable
    Bv(Bv),
    /// A universe level
    U(ULvl),
    /// The empty type
    Empty,
    /// The unit type
    Unit,
    /// The unique value of the unit type
    Null,
    /// An equation between terms at a given type
    Eqn([T; 2]),
    /// A pi type
    Pi([T; 2]),
    /// A sigma type
    Sigma([T; 2]),
    /// An abstraction
    Abs([T; 2]),
    /// An application
    App([T; 2]),
    /// A pair
    Pair([T; 2]),
    /// The first projection of a pair
    Fst([T; 1]),
    /// The second projection of a pair
    Snd([T; 1]),
    /// A dependent if-then-else
    Ite([T; 3]),
    /// A propositional truncation
    Trunc([T; 1]),
    /// Hilbert choice
    Choose([T; 2]),
    /// The type of natural numbers
    Nats,
    /// A small natural number
    N64(u64),
    /// The successor of a natural number
    Succ([T; 1]),
    /// Recursion on natural numbers
    Natrec([T; 3]),
    /// An assertion that a term has the given type
    HasTy([T; 2]),
    /// A known-invalid term
    #[default]
    Invalid,

    // == Meta-syntax ==
    /// A substitution under `k` binders
    Subst1(Bv, [T; 2]),
    /// A weakening by a shift
    BWk(Shift, [T; 1]),
    /// A variable closure under `k` binders
    Close(Close<C, T>),

    // == Imports from other contexts ==
    /// A direct import from another context
    Import(I),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum GDisc<C, T, I = Val<C, T>> {
    Fv(Fv<C>),
    Bv(Bv),
    U(ULvl),
    Empty,
    Unit,
    Null,
    Eqn,
    Pi,
    Sigma,
    Abs,
    App,
    Pair,
    Fst,
    Snd,
    Ite,
    Trunc,
    Choose,
    Nats,
    N64(u64),
    Succ,
    Natrec,
    HasTy,
    Invalid,
    Let(Bv),
    BWk(Shift),
    Close(Close<C, T>),
    Import(I),
}

impl<C, T, I> NodeT<C, T, I> {
    /// Get this node's discriminant
    pub fn disc(self) -> GDisc<C, T, I> {
        match self {
            NodeT::Fv(x) => GDisc::Fv(x),
            NodeT::Bv(i) => GDisc::Bv(i),
            NodeT::U(level) => GDisc::U(level),
            NodeT::Empty => GDisc::Empty,
            NodeT::Unit => GDisc::Unit,
            NodeT::Null => GDisc::Null,
            NodeT::Eqn(_) => GDisc::Eqn,
            NodeT::Pi(_) => GDisc::Pi,
            NodeT::Sigma(_) => GDisc::Sigma,
            NodeT::Abs(_) => GDisc::Abs,
            NodeT::App(_) => GDisc::App,
            NodeT::Pair(_) => GDisc::Pair,
            NodeT::Fst(_) => GDisc::Fst,
            NodeT::Snd(_) => GDisc::Snd,
            NodeT::Ite(_) => GDisc::Ite,
            NodeT::Trunc(_) => GDisc::Trunc,
            NodeT::Choose(_) => GDisc::Choose,
            NodeT::Nats => GDisc::Nats,
            NodeT::N64(n) => GDisc::N64(n),
            NodeT::Succ(_) => GDisc::Succ,
            NodeT::Natrec(_) => GDisc::Natrec,
            NodeT::HasTy(_) => GDisc::HasTy,
            NodeT::Invalid => GDisc::Invalid,
            NodeT::Subst1(k, _) => GDisc::Let(k),
            NodeT::BWk(s, _) => GDisc::BWk(s),
            NodeT::Close(close) => GDisc::Close(close),
            NodeT::Import(import) => GDisc::Import(import),
        }
    }

    /// Map this node's subterms and imports
    pub fn map<U, J>(self, mut f: impl FnMut(T) -> U, g: impl FnOnce(I) -> J) -> NodeT<C, U, J> {
        match self {
            NodeT::Fv(x) => NodeT::Fv(x),
            NodeT::Bv(i) => NodeT::Bv(i),
            NodeT::U(level) => NodeT::U(level),
            NodeT::Empty => NodeT::Empty,
            NodeT::Unit => NodeT::Unit,
            NodeT::Null => NodeT::Null,
            NodeT::Eqn([a, b]) => NodeT::Eqn([f(a), f(b)]),
            NodeT::Pi([a, b]) => NodeT::Pi([f(a), f(b)]),
            NodeT::Sigma([a, b]) => NodeT::Sigma([f(a), f(b)]),
            NodeT::Abs([a, b]) => NodeT::Abs([f(a), f(b)]),
            NodeT::App([a, b]) => NodeT::App([f(a), f(b)]),
            NodeT::Pair([a, b]) => NodeT::Pair([f(a), f(b)]),
            NodeT::Fst([a]) => NodeT::Fst([f(a)]),
            NodeT::Snd([a]) => NodeT::Snd([f(a)]),
            NodeT::Ite([a, b, c]) => NodeT::Ite([f(a), f(b), f(c)]),
            NodeT::Trunc([a]) => NodeT::Trunc([f(a)]),
            NodeT::Choose([a, b]) => NodeT::Choose([f(a), f(b)]),
            NodeT::Nats => NodeT::Nats,
            NodeT::N64(n) => NodeT::N64(n),
            NodeT::Succ([a]) => NodeT::Succ([f(a)]),
            NodeT::Natrec([a, b, c]) => NodeT::Natrec([f(a), f(b), f(c)]),
            NodeT::HasTy([a, b]) => NodeT::HasTy([f(a), f(b)]),
            NodeT::Invalid => NodeT::Invalid,
            NodeT::Subst1(k, [a, b]) => NodeT::Subst1(k, [f(a), f(b)]),
            NodeT::BWk(k, [a]) => NodeT::BWk(k, [f(a)]),
            NodeT::Close(close) => NodeT::Close(Close {
                under: close.under,
                var: close.var,
                tm: f(close.tm),
            }),
            NodeT::Import(import) => NodeT::Import(g(import)),
        }
    }

    /// Map this node's subterms
    pub fn map_subterms<U>(self, f: impl FnMut(T) -> U) -> NodeT<C, U, I> {
        self.map(f, |x| x)
    }

    /// Map this node's imports
    pub fn map_import<J>(self, g: impl FnOnce(I) -> J) -> NodeT<C, T, J> {
        self.map(|x| x, g)
    }

    /// Map this node's subterms and imports, potentially returning an error
    pub fn try_map<U, J, E>(
        self,
        mut f: impl FnMut(T) -> Result<U, E>,
        g: impl FnOnce(I) -> Result<J, E>,
    ) -> Result<NodeT<C, U, J>, E> {
        match self {
            NodeT::Fv(x) => Ok(NodeT::Fv(x)),
            NodeT::Bv(i) => Ok(NodeT::Bv(i)),
            NodeT::U(level) => Ok(NodeT::U(level)),
            NodeT::Empty => Ok(NodeT::Empty),
            NodeT::Unit => Ok(NodeT::Unit),
            NodeT::Null => Ok(NodeT::Null),
            NodeT::Eqn([a, b]) => Ok(NodeT::Eqn([f(a)?, f(b)?])),
            NodeT::Pi([a, b]) => Ok(NodeT::Pi([f(a)?, f(b)?])),
            NodeT::Sigma([a, b]) => Ok(NodeT::Sigma([f(a)?, f(b)?])),
            NodeT::Abs([a, b]) => Ok(NodeT::Abs([f(a)?, f(b)?])),
            NodeT::App([a, b]) => Ok(NodeT::App([f(a)?, f(b)?])),
            NodeT::Pair([a, b]) => Ok(NodeT::Pair([f(a)?, f(b)?])),
            NodeT::Fst([a]) => Ok(NodeT::Fst([f(a)?])),
            NodeT::Snd([a]) => Ok(NodeT::Snd([f(a)?])),
            NodeT::Ite([a, b, c]) => Ok(NodeT::Ite([f(a)?, f(b)?, f(c)?])),
            NodeT::Trunc([a]) => Ok(NodeT::Trunc([f(a)?])),
            NodeT::Choose([a, b]) => Ok(NodeT::Choose([f(a)?, f(b)?])),
            NodeT::Nats => Ok(NodeT::Nats),
            NodeT::N64(n) => Ok(NodeT::N64(n)),
            NodeT::Succ([a]) => Ok(NodeT::Succ([f(a)?])),
            NodeT::Natrec([a, b, c]) => Ok(NodeT::Natrec([f(a)?, f(b)?, f(c)?])),
            NodeT::HasTy([a, b]) => Ok(NodeT::HasTy([f(a)?, f(b)?])),
            NodeT::Invalid => Ok(NodeT::Invalid),
            NodeT::Subst1(k, [a, b]) => Ok(NodeT::Subst1(k, [f(a)?, f(b)?])),
            NodeT::BWk(k, [a]) => Ok(NodeT::BWk(k, [f(a)?])),
            NodeT::Close(close) => Ok(NodeT::Close(Close {
                under: close.under,
                var: close.var,
                tm: f(close.tm)?,
            })),
            NodeT::Import(import) => Ok(NodeT::Import(g(import)?)),
        }
    }

    /// Map this node's children, potentially returning an error
    pub fn try_map_subterms<U, E>(
        self,
        f: impl FnMut(T) -> Result<U, E>,
    ) -> Result<NodeT<C, U, I>, E> {
        self.try_map(f, Ok)
    }

    /// Map this node's imports, potentially returning an error
    pub fn try_map_import<J, E>(
        self,
        g: impl FnOnce(I) -> Result<J, E>,
    ) -> Result<NodeT<C, T, J>, E> {
        self.try_map(Ok, g)
    }

    /// Annotate this node's subterms with binders
    pub fn with_binders(self) -> NodeT<C, (Bv, T), I> {
        match self {
            NodeT::Fv(x) => NodeT::Fv(x),
            NodeT::Bv(i) => NodeT::Bv(i),
            NodeT::U(level) => NodeT::U(level),
            NodeT::Empty => NodeT::Empty,
            NodeT::Unit => NodeT::Unit,
            NodeT::Null => NodeT::Null,
            NodeT::Eqn([a, b]) => NodeT::Eqn([(Bv(0), a), (Bv(0), b)]),
            NodeT::Pi([a, b]) => NodeT::Pi([(Bv(0), a), (Bv(1), b)]),
            NodeT::Sigma([a, b]) => NodeT::Sigma([(Bv(0), a), (Bv(1), b)]),
            NodeT::Abs([a, b]) => NodeT::Abs([(Bv(0), a), (Bv(1), b)]),
            NodeT::App([a, b]) => NodeT::App([(Bv(0), a), (Bv(0), b)]),
            NodeT::Pair([a, b]) => NodeT::Pair([(Bv(0), a), (Bv(0), b)]),
            NodeT::Fst([a]) => NodeT::Fst([(Bv(0), a)]),
            NodeT::Snd([a]) => NodeT::Snd([(Bv(0), a)]),
            NodeT::Ite([a, b, c]) => NodeT::Ite([(Bv(0), a), (Bv(0), b), (Bv(0), c)]),
            NodeT::Trunc([a]) => NodeT::Trunc([(Bv(0), a)]),
            NodeT::Choose([a, b]) => NodeT::Choose([(Bv(0), a), (Bv(1), b)]),
            NodeT::Nats => NodeT::Nats,
            NodeT::N64(n) => NodeT::N64(n),
            NodeT::Succ([a]) => NodeT::Succ([(Bv(0), a)]),
            NodeT::Natrec([a, b, c]) => NodeT::Natrec([(Bv(0), a), (Bv(0), b), (Bv(0), c)]),
            NodeT::HasTy([a, b]) => NodeT::HasTy([(Bv(0), a), (Bv(0), b)]),
            NodeT::Invalid => NodeT::Invalid,
            NodeT::Subst1(k, [a, b]) => NodeT::Subst1(k, [(Bv(0), a), (Bv(1), b)]),
            NodeT::BWk(k, [a]) => NodeT::BWk(k, [(Bv(0), a)]),
            NodeT::Close(close) => NodeT::Close(Close {
                under: close.under,
                var: close.var,
                tm: (Bv(0), close.tm),
            }),
            NodeT::Import(import) => NodeT::Import(import),
        }
    }

    /// Borrow this node
    pub fn as_ref(&self) -> NodeT<&C, &T, &I> {
        match self {
            NodeT::Fv(x) => NodeT::Fv(x.as_ref()),
            NodeT::Bv(i) => NodeT::Bv(*i),
            NodeT::U(level) => NodeT::U(*level),
            NodeT::Empty => NodeT::Empty,
            NodeT::Unit => NodeT::Unit,
            NodeT::Null => NodeT::Null,
            NodeT::Eqn([a, b]) => NodeT::Eqn([a, b]),
            NodeT::Pi([a, b]) => NodeT::Pi([a, b]),
            NodeT::Sigma([a, b]) => NodeT::Sigma([a, b]),
            NodeT::Abs([a, b]) => NodeT::Abs([a, b]),
            NodeT::App([a, b]) => NodeT::App([a, b]),
            NodeT::Pair([a, b]) => NodeT::Pair([a, b]),
            NodeT::Fst([a]) => NodeT::Fst([a]),
            NodeT::Snd([a]) => NodeT::Snd([a]),
            NodeT::Ite([a, b, c]) => NodeT::Ite([a, b, c]),
            NodeT::Trunc([a]) => NodeT::Trunc([a]),
            NodeT::Choose([a, b]) => NodeT::Choose([a, b]),
            NodeT::Nats => NodeT::Nats,
            NodeT::N64(n) => NodeT::N64(*n),
            NodeT::Succ([a]) => NodeT::Succ([a]),
            NodeT::Natrec([a, b, c]) => NodeT::Natrec([a, b, c]),
            NodeT::HasTy([a, b]) => NodeT::HasTy([a, b]),
            NodeT::Invalid => NodeT::Invalid,
            NodeT::Subst1(k, [a, b]) => NodeT::Subst1(*k, [a, b]),
            NodeT::BWk(k, [a]) => NodeT::BWk(*k, [a]),
            NodeT::Close(close) => NodeT::Close(close.as_ref()),
            NodeT::Import(import) => NodeT::Import(import),
        }
    }

    /// Borrow this node mutably
    pub fn as_mut(&mut self) -> NodeT<&mut C, &mut T, &mut I> {
        match self {
            NodeT::Fv(x) => NodeT::Fv(x.as_mut()),
            NodeT::Bv(i) => NodeT::Bv(*i),
            NodeT::U(level) => NodeT::U(*level),
            NodeT::Empty => NodeT::Empty,
            NodeT::Unit => NodeT::Unit,
            NodeT::Null => NodeT::Null,
            NodeT::Eqn([a, b]) => NodeT::Eqn([a, b]),
            NodeT::Pi([a, b]) => NodeT::Pi([a, b]),
            NodeT::Sigma([a, b]) => NodeT::Sigma([a, b]),
            NodeT::Abs([a, b]) => NodeT::Abs([a, b]),
            NodeT::App([a, b]) => NodeT::App([a, b]),
            NodeT::Pair([a, b]) => NodeT::Pair([a, b]),
            NodeT::Fst([a]) => NodeT::Fst([a]),
            NodeT::Snd([a]) => NodeT::Snd([a]),
            NodeT::Ite([a, b, c]) => NodeT::Ite([a, b, c]),
            NodeT::Trunc([a]) => NodeT::Trunc([a]),
            NodeT::Choose([a, b]) => NodeT::Choose([a, b]),
            NodeT::Nats => NodeT::Nats,
            NodeT::N64(n) => NodeT::N64(*n),
            NodeT::Succ([a]) => NodeT::Succ([a]),
            NodeT::Natrec([a, b, c]) => NodeT::Natrec([a, b, c]),
            NodeT::HasTy([a, b]) => NodeT::HasTy([a, b]),
            NodeT::Invalid => NodeT::Invalid,
            NodeT::Subst1(k, [a, b]) => NodeT::Subst1(*k, [a, b]),
            NodeT::BWk(k, [a]) => NodeT::BWk(*k, [a]),
            NodeT::Close(close) => NodeT::Close(close.as_mut()),
            NodeT::Import(import) => NodeT::Import(import),
        }
    }

    /// Get the children of this term
    ///
    /// Note that the argument of a closure does _not_ count as a child of the closure, since
    /// closure does _not_ respect congruence!
    pub fn children(&self) -> &[T] {
        match self {
            NodeT::Fv(_) => &[],
            NodeT::Bv(_) => &[],
            NodeT::U(_) => &[],
            NodeT::Empty => &[],
            NodeT::Unit => &[],
            NodeT::Null => &[],
            NodeT::Eqn(xs) => &xs[..],
            NodeT::Pi(xs) => &xs[..],
            NodeT::Sigma(xs) => &xs[..],
            NodeT::Abs(xs) => &xs[..],
            NodeT::App(xs) => &xs[..],
            NodeT::Pair(xs) => &xs[..],
            NodeT::Fst(xs) => &xs[..],
            NodeT::Snd(xs) => &xs[..],
            NodeT::Ite(xs) => &xs[..],
            NodeT::Trunc(xs) => &xs[..],
            NodeT::Choose(xs) => &xs[..],
            NodeT::Nats => &[],
            NodeT::N64(_) => &[],
            NodeT::Succ(xs) => &xs[..],
            NodeT::Natrec(xs) => &xs[..],
            NodeT::HasTy(xs) => &xs[..],
            NodeT::Invalid => &[],
            NodeT::Subst1(_, xs) => &xs[..],
            NodeT::BWk(_, xs) => &xs[..],
            NodeT::Close(_) => &[],
            NodeT::Import(_) => &[],
        }
    }

    /// Get the children of this term
    ///
    /// Note this only returns children _in the same context_ as this term; in particular, imports
    /// and closures will return an empty slice.
    pub fn children_mut(&mut self) -> &mut [T] {
        match self {
            NodeT::Fv(_) => &mut [],
            NodeT::Bv(_) => &mut [],
            NodeT::U(_) => &mut [],
            NodeT::Empty => &mut [],
            NodeT::Unit => &mut [],
            NodeT::Null => &mut [],
            NodeT::Eqn(xs) => &mut xs[..],
            NodeT::Pi(xs) => &mut xs[..],
            NodeT::Sigma(xs) => &mut xs[..],
            NodeT::Abs(xs) => &mut xs[..],
            NodeT::App(xs) => &mut xs[..],
            NodeT::Pair(xs) => &mut xs[..],
            NodeT::Fst(xs) => &mut xs[..],
            NodeT::Snd(xs) => &mut xs[..],
            NodeT::Ite(xs) => &mut xs[..],
            NodeT::Trunc(xs) => &mut xs[..],
            NodeT::Choose(xs) => &mut xs[..],
            NodeT::Nats => &mut [],
            NodeT::N64(_) => &mut [],
            NodeT::Succ(xs) => &mut xs[..],
            NodeT::Natrec(xs) => &mut xs[..],
            NodeT::HasTy(xs) => &mut xs[..],
            NodeT::Invalid => &mut [],
            NodeT::Subst1(_, xs) => &mut xs[..],
            NodeT::BWk(_, xs) => &mut xs[..],
            NodeT::Close(_) => &mut [],
            NodeT::Import(_) => &mut [],
        }
    }

    /// Check whether this term is relocatable
    pub fn is_relocatable(&self) -> bool {
        matches!(
            self,
            NodeT::Fv(_)
                | NodeT::Bv(_)
                | NodeT::U(_)
                | NodeT::Empty
                | NodeT::Unit
                | NodeT::Null
                | NodeT::Nats
                | NodeT::N64(_)
                | NodeT::Invalid
                | NodeT::Import(_)
        )
    }

    /// If this term has no dependencies, return it
    pub fn relocate(self) -> Option<NodeT<C, T, I>> {
        if self.is_relocatable() {
            Some(self)
        } else {
            None
        }
    }

    /// Compute a bound on this term's unbound variables
    pub fn bvi_with(&self, mut tm: impl FnMut(&T) -> Bv) -> Bv {
        match self {
            NodeT::Bv(i) => i.succ(),
            NodeT::Import(_) => Bv::INVALID,
            NodeT::Close(Close {
                under: k,
                tm: a,
                var,
            }) => tm(a).bvi_add_under(Bv(var.ix).succ(), *k),
            NodeT::BWk(s, [a]) => s.bvi(tm(a)),
            n => n
                .as_ref()
                .with_binders()
                .children()
                .iter()
                .map(move |(b, t)| tm(*t) - *b)
                .max()
                .unwrap_or(Bv(0)),
        }
    }

    /// Get this node as an import
    pub fn as_import(&self) -> Option<&I> {
        match self {
            NodeT::Import(import) => Some(import),
            _ => None,
        }
    }

    /// Get this node as a universe level
    pub fn as_level(&self) -> Option<ULvl> {
        match self {
            NodeT::U(level) => Some(*level),
            _ => None,
        }
    }

    /// Get whether this node can be unfolded
    pub fn is_unfoldable(&self) -> bool {
        matches!(
            self,
            NodeT::Subst1(_, _) | NodeT::BWk(_, _) | NodeT::Close(_) | NodeT::Import(_)
        )
    }
}

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

/// A bound variable
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Bv(pub u32);

impl Bv {
    /// An invalid bound variable
    ///
    /// Compares greater-than all other bound variables
    pub const INVALID: Bv = Bv(u32::MAX);

    /// Construct a bound variable from a `u32`
    pub const fn new(ix: u32) -> Bv {
        assert!(
            ix != u32::MAX,
            "cannot use new to construct an invalid bound variable"
        );
        Bv(ix)
    }

    /// Get the successor of this bound variable
    ///
    /// Panics if this would overflow
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::data::term::Bv;
    /// for x in 0..100 {
    ///     assert_eq!(Bv(x).succ(), Bv(x + 1));
    /// }
    /// assert_eq!(Bv::INVALID.succ(), Bv::INVALID);
    /// ```
    pub fn succ(self) -> Bv {
        if self.0 == u32::MAX - 1 {
            panic!("bound variable overflow");
        }
        Bv(self.0.saturating_add(1))
    }

    /// Get whether this bound variable is valid
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::data::term::Bv;
    /// for x in 0..100 {
    ///    assert!(Bv(x).is_valid());
    /// }
    /// assert!(!Bv::INVALID.is_valid());
    /// ```
    pub fn is_valid(self) -> bool {
        self.0 != u32::MAX
    }

    /// Get the `bvi` of this bound variable after inserting a bound variable under `k` binders
    pub fn bvi_under(self, k: Bv) -> Bv {
        if self < k { self } else { self.succ() }
    }

    /// Get the `bvi` of this bound variable after inserting `n` bound variables under `k` binders
    pub fn bvi_add_under(self, shift: Bv, k: Bv) -> Bv {
        if self < k { self } else { self + shift }
    }
}

impl Add for Bv {
    type Output = Bv;

    fn add(self, rhs: Bv) -> Bv {
        let add = self.0.saturating_add(rhs.0);
        if add != u32::MAX {
            Bv(add)
        } else if self.is_valid() && rhs.is_valid() {
            panic!("bound variable overflow");
        } else {
            Bv::INVALID
        }
    }
}

impl Sub for Bv {
    type Output = Bv;

    fn sub(self, rhs: Bv) -> Bv {
        Bv(self.0.saturating_sub(rhs.0))
    }
}

impl Debug for Bv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == Bv::INVALID {
            return write!(f, "#invalid");
        }
        write!(f, "#{}", self.0)
    }
}

/// A substitution which shifts up `shift` binders under `under` binders
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Shift {
    /// The level at which to shift
    under: Bv,
    /// The number of binders to shift by
    shift: Bv,
}

impl Shift {
    /// Construct a new shift from a level and shift
    ///
    /// Panics if either is invalid
    pub fn new(level: Bv, shift: Bv) -> Shift {
        debug_assert!(
            level.is_valid(),
            "cannot construct a shift at an invalid level"
        );
        debug_assert!(
            shift.is_valid(),
            "cannot construct a shift by an invalid amount"
        );
        Shift {
            under: if shift == Bv(0) { Bv(0) } else { level },
            shift,
        }
    }

    /// Construct a new shift from the number of binders to shift by
    ///
    /// Panics if the shift is invalid
    pub fn from_shift(shift: Bv) -> Shift {
        Self::new(Bv(0), shift)
    }

    /// Shift upwards by one at the given level
    ///
    /// Panics if the level is invalid
    pub fn up(level: Bv) -> Shift {
        Self::new(level, Bv(1))
    }

    /// Lift this shift under a binder
    pub fn lift(self) -> Shift {
        if self.shift == Bv(0) {
            debug_assert_eq!(self.under, Bv(0), "the identity shift must have zero level");
            return self;
        }
        Shift {
            under: self.under.succ(),
            shift: self.shift,
        }
    }

    /// Lift this shift under `n` binders
    pub fn lift_under(self, n: Bv) -> Shift {
        if self.shift == Bv(0) {
            debug_assert_eq!(self.under, Bv(0), "the identity shift must have zero level");
            return self;
        }
        Shift {
            under: self.under + n,
            shift: self.shift,
        }
    }

    /// Get the successor of this shift
    pub fn succ(self) -> Shift {
        Shift {
            under: self.under,
            shift: self.shift.succ(),
        }
    }

    /// Apply this shift
    pub fn apply(self, bv: Bv) -> Bv {
        if bv < self.under { bv } else { bv + self.shift }
    }

    /// Get an upper bound on the bound variable index after applying this shift
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::data::term::*;
    /// # for level in (0..10).map(Bv) { for shift in (0..10).map(Bv) {
    /// let shift = Shift::new(level, shift);
    /// assert_eq!(shift.bvi(Bv(0)), Bv(0));
    /// # for bv in (0..10).map(Bv) {
    /// assert_eq!(shift.bvi(bv.succ()), shift.apply(bv).succ());
    /// # } } }
    /// ```
    pub fn bvi(self, bvi: Bv) -> Bv {
        if bvi <= self.under {
            bvi
        } else {
            bvi + self.shift
        }
    }

    /// Get this shift's level
    pub fn under(self) -> Bv {
        self.under
    }

    /// Get this shift's shift
    pub fn shift(self) -> Bv {
        self.shift
    }

    /// Check whether this shift is the identity
    pub fn is_id(self) -> bool {
        if self.shift == Bv(0) {
            debug_assert_eq!(self.under, Bv(0), "the identity shift must have zero level");
            true
        } else {
            false
        }
    }
}

/// A universe level
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ULvl {
    pub(crate) level: i32,
}

impl ULvl {
    /// The universe of propositions
    pub const PROP: Self = ULvl { level: 0 };
    // The universe of sets
    pub const SET: Self = ULvl { level: 1 };

    /// Construct a constant universe level
    pub fn of_nat(level: u32) -> ULvl {
        assert!(level <= i32::MAX as u32, "universe level out of bounds");
        ULvl {
            level: level as i32,
        }
    }

    /// Get this universe level as a constant
    pub fn as_const(self) -> Option<u32> {
        if self.level >= 0 {
            Some(self.level as u32)
        } else {
            None
        }
    }
}

impl Debug for ULvl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.level >= 0 {
            write!(f, "#u{}", self.level)
        } else {
            write!(f, "#uv{}", -self.level)
        }
    }
}

/// A variable closure under `k` binders
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Close<C, T> {
    /// The number of binders being closed under
    pub under: Bv,
    /// The variable being closed over
    pub var: Fv<C>,
    /// The term being closed over (in `this`, _not_ necessarily `ctx`)
    pub tm: T,
}

impl<C, T> Close<C, T> {
    /// Borrow this closure
    pub fn as_ref(&self) -> Close<&C, &T> {
        Close {
            under: self.under,
            var: self.var.as_ref(),
            tm: &self.tm,
        }
    }

    /// Borrow this closure mutably
    pub fn as_mut(&mut self) -> Close<&mut C, &mut T> {
        Close {
            under: self.under,
            var: self.var.as_mut(),
            tm: &mut self.tm,
        }
    }

    /// Lift this close under `n` binders
    pub fn lift(self, n: Bv) -> Close<C, T> {
        Close {
            under: self.under + n,
            var: self.var,
            tm: self.tm,
        }
    }
}

/// An import from another context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Val<C, T> {
    /// The context being imported from
    pub ctx: C,
    /// The term being imported (in `ctx`)
    pub tm: T,
}

impl<C, T> Val<C, T> {
    /// Replace this value's term
    pub fn val<U>(self, tm: U) -> Val<C, U> {
        Val { ctx: self.ctx, tm }
    }

    /// Borrow this import
    pub fn as_ref(&self) -> Val<&C, &T> {
        Val {
            ctx: &self.ctx,
            tm: &self.tm,
        }
    }

    /// Borrow this import mutably
    pub fn as_mut(&mut self) -> Val<&mut C, &mut T> {
        Val {
            ctx: &mut self.ctx,
            tm: &mut self.tm,
        }
    }
}

pub type NodeVT<C, T> = NodeT<C, Val<C, T>, Val<C, T>>;

pub type NodeT2<C, T> = NodeT<C, NodeT<C, T>, Val<C, T>>;

pub type NodeVT2<C, T> = NodeT<C, NodeVT<C, T>, Val<C, T>>;

pub type VNodeT<C, T> = Val<C, NodeT<C, T>>;

pub type VNodeT2<C, T> = Val<C, NodeT2<C, T>>;

impl<C, T> From<Bv> for NodeT<C, T> {
    fn from(bv: Bv) -> Self {
        NodeT::Bv(bv)
    }
}

impl<C, T> From<ULvl> for NodeT<C, T> {
    fn from(level: ULvl) -> Self {
        NodeT::U(level)
    }
}

impl<C, T> From<bool> for NodeT<C, T> {
    fn from(value: bool) -> Self {
        if value { NodeT::Unit } else { NodeT::Empty }
    }
}

impl<C, T> From<Val<C, T>> for NodeT<C, T> {
    fn from(copy: Val<C, T>) -> Self {
        NodeT::Import(copy)
    }
}

impl<C, T> From<Close<C, T>> for NodeT<C, T> {
    fn from(close: Close<C, T>) -> Self {
        NodeT::Close(close)
    }
}
