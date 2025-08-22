use std::{
    fmt::{self, Debug},
    ops::{Add, Sub},
};

/// A term in `covalence`'s core calculus
pub enum GNode<C, T, I = T> {
    // == MLTT term formers ==
    /// A context's parameter
    Var(C),
    /// A bound variable
    Bv(Bv),
    /// A universe level
    U(ULevel),
    /// The unit type at a given universe level
    Unit(ULevel),
    /// The unique value of the unit type at a given universe level
    Null(ULevel),
    /// The empty type at a given universe level
    Empty(ULevel),
    /// An equation between terms at a given type
    Eqn([T; 2]),
    /// A pi type
    Pi(ULevel, [T; 2]),
    /// An abstraction
    Abs(ULevel, [T; 3]),
    /// An application
    App([T; 4]),
    /// A sigma type
    Sigma(ULevel, [T; 2]),
    /// A pair
    Pair(ULevel, [T; 4]),
    /// The first projection of a pair
    Fst([T; 3]),
    /// The second projection of a pair
    Snd([T; 3]),
    /// An if-then-else
    Ite([T; 4]),
    /// A propositional truncation
    Trunc([T; 1]),
    /// Hilbert choice
    Choose([T; 2]),
    /// The type of natural numbers
    Nats,
    /// Zero
    Zero,
    /// The successor function
    Succ,
    /// Recursion on natural numbers
    Natrec([T; 4]),

    // == Syntax extensions ==
    /// A substitution
    Let([T; 2]),
    /// A known-invalid term
    Invalid,

    // == Predicates ==
    /// An assertion that a term has the given type
    HasTy([T; 2]),

    // == Imports and closures ==
    /// A direct import from another context
    Import(Import<C, I>),
    /// An import from another context, closing over that context's parameter
    Close(Close<C, I>),
}

impl<C, T, I> GNode<C, T, I> {
    /// Map this node's children
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> GNode<C, U, I> {
        match self {
            GNode::Var(x) => GNode::Var(x),
            GNode::Bv(i) => GNode::Bv(i),
            GNode::U(level) => GNode::U(level),
            GNode::Unit(level) => GNode::Unit(level),
            GNode::Null(level) => GNode::Null(level),
            GNode::Empty(level) => GNode::Empty(level),
            GNode::Eqn([a, b]) => GNode::Eqn([f(a), f(b)]),
            GNode::Pi(level, [a, b]) => GNode::Pi(level, [f(a), f(b)]),
            GNode::Abs(level, [a, b, c]) => GNode::Abs(level, [f(a), f(b), f(c)]),
            GNode::App([a, b, c, d]) => GNode::App([f(a), f(b), f(c), f(d)]),
            GNode::Sigma(level, [a, b]) => GNode::Sigma(level, [f(a), f(b)]),
            GNode::Pair(level, [a, b, c, d]) => GNode::Pair(level, [f(a), f(b), f(c), f(d)]),
            GNode::Fst([a, b, c]) => GNode::Fst([f(a), f(b), f(c)]),
            GNode::Snd([a, b, c]) => GNode::Snd([f(a), f(b), f(c)]),
            GNode::Ite([a, b, c, d]) => GNode::Ite([f(a), f(b), f(c), f(d)]),
            GNode::Trunc([a]) => GNode::Trunc([f(a)]),
            GNode::Choose([a, b]) => GNode::Choose([f(a), f(b)]),
            GNode::Nats => GNode::Nats,
            GNode::Zero => GNode::Zero,
            GNode::Succ => GNode::Succ,
            GNode::Natrec([a, b, c, d]) => GNode::Natrec([f(a), f(b), f(c), f(d)]),
            GNode::Let([a, b]) => GNode::Let([f(a), f(b)]),
            GNode::Invalid => GNode::Invalid,
            GNode::HasTy([a, b]) => GNode::HasTy([f(a), f(b)]),
            GNode::Import(import) => GNode::Import(import),
            GNode::Close(close) => GNode::Close(close),
        }
    }

    /// Map this node's children, potentially returning an error
    pub fn try_map<U, E>(self, mut f: impl FnMut(T) -> Result<U, E>) -> Result<GNode<C, U, I>, E> {
        match self {
            GNode::Var(x) => Ok(GNode::Var(x)),
            GNode::Bv(i) => Ok(GNode::Bv(i)),
            GNode::U(level) => Ok(GNode::U(level)),
            GNode::Unit(level) => Ok(GNode::Unit(level)),
            GNode::Null(level) => Ok(GNode::Null(level)),
            GNode::Empty(level) => Ok(GNode::Empty(level)),
            GNode::Eqn([a, b]) => Ok(GNode::Eqn([f(a)?, f(b)?])),
            GNode::Pi(level, [a, b]) => Ok(GNode::Pi(level, [f(a)?, f(b)?])),
            GNode::Abs(level, [a, b, c]) => Ok(GNode::Abs(level, [f(a)?, f(b)?, f(c)?])),
            GNode::App([a, b, c, d]) => Ok(GNode::App([f(a)?, f(b)?, f(c)?, f(d)?])),
            GNode::Sigma(level, [a, b]) => Ok(GNode::Sigma(level, [f(a)?, f(b)?])),
            GNode::Pair(level, [a, b, c, d]) => {
                Ok(GNode::Pair(level, [f(a)?, f(b)?, f(c)?, f(d)?]))
            }
            GNode::Fst([a, b, c]) => Ok(GNode::Fst([f(a)?, f(b)?, f(c)?])),
            GNode::Snd([a, b, c]) => Ok(GNode::Snd([f(a)?, f(b)?, f(c)?])),
            GNode::Ite([a, b, c, d]) => Ok(GNode::Ite([f(a)?, f(b)?, f(c)?, f(d)?])),
            GNode::Trunc([a]) => Ok(GNode::Trunc([f(a)?])),
            GNode::Choose([a, b]) => Ok(GNode::Choose([f(a)?, f(b)?])),
            GNode::Nats => Ok(GNode::Nats),
            GNode::Zero => Ok(GNode::Zero),
            GNode::Succ => Ok(GNode::Succ),
            GNode::Natrec([a, b, c, d]) => Ok(GNode::Natrec([f(a)?, f(b)?, f(c)?, f(d)?])),
            GNode::Let([a, b]) => Ok(GNode::Let([f(a)?, f(b)?])),
            GNode::Invalid => Ok(GNode::Invalid),
            GNode::HasTy([a, b]) => Ok(GNode::HasTy([f(a)?, f(b)?])),
            GNode::Import(import) => Ok(GNode::Import(import)),
            GNode::Close(close) => Ok(GNode::Close(close)),
        }
    }

    /// Annotate this node's children with binders
    pub fn with_binders(self) -> GNode<C, (Bv, T), I> {
        match self {
            GNode::Var(x) => GNode::Var(x),
            GNode::Bv(i) => GNode::Bv(i),
            GNode::U(level) => GNode::U(level),
            GNode::Unit(level) => GNode::Unit(level),
            GNode::Null(level) => GNode::Null(level),
            GNode::Empty(level) => GNode::Empty(level),
            GNode::Eqn([a, b]) => GNode::Eqn([(Bv(0), a), (Bv(1), b)]),
            GNode::Pi(level, [a, b]) => GNode::Pi(level, [(Bv(0), a), (Bv(1), b)]),
            GNode::Abs(level, [a, b, c]) => GNode::Abs(level, [(Bv(0), a), (Bv(1), b), (Bv(1), c)]),
            GNode::App([a, b, c, d]) => {
                GNode::App([(Bv(0), a), (Bv(1), b), (Bv(0), c), (Bv(0), d)])
            }
            GNode::Sigma(level, [a, b]) => GNode::Sigma(level, [(Bv(0), a), (Bv(1), b)]),
            GNode::Pair(level, [a, b, c, d]) => {
                GNode::Pair(level, [(Bv(0), a), (Bv(1), b), (Bv(0), c), (Bv(0), d)])
            }
            GNode::Fst([a, b, c]) => GNode::Fst([(Bv(0), a), (Bv(1), b), (Bv(0), c)]),
            GNode::Snd([a, b, c]) => GNode::Snd([(Bv(0), a), (Bv(1), b), (Bv(0), c)]),
            GNode::Ite([a, b, c, d]) => {
                GNode::Ite([(Bv(0), a), (Bv(0), b), (Bv(0), c), (Bv(0), d)])
            }
            GNode::Trunc([a]) => GNode::Trunc([(Bv(0), a)]),
            GNode::Choose([a, b]) => GNode::Choose([(Bv(0), a), (Bv(1), b)]),
            GNode::Nats => GNode::Nats,
            GNode::Zero => GNode::Zero,
            GNode::Succ => GNode::Succ,
            GNode::Natrec([a, b, c, d]) => {
                GNode::Natrec([(Bv(1), a), (Bv(0), b), (Bv(0), c), (Bv(0), d)])
            }
            GNode::Let([a, b]) => GNode::Let([(Bv(0), a), (Bv(1), b)]),
            GNode::Invalid => GNode::Invalid,
            GNode::HasTy([a, b]) => GNode::HasTy([(Bv(0), a), (Bv(0), b)]),
            GNode::Import(import) => GNode::Import(import),
            GNode::Close(close) => GNode::Close(close),
        }
    }

    /// Borrow this node
    pub fn as_ref(&self) -> GNode<&C, &T, &I> {
        match self {
            GNode::Var(x) => GNode::Var(x),
            GNode::Bv(i) => GNode::Bv(*i),
            GNode::U(level) => GNode::U(*level),
            GNode::Unit(level) => GNode::Unit(*level),
            GNode::Null(level) => GNode::Null(*level),
            GNode::Empty(level) => GNode::Empty(*level),
            GNode::Eqn([a, b]) => GNode::Eqn([a, b]),
            GNode::Pi(level, [a, b]) => GNode::Pi(*level, [a, b]),
            GNode::Abs(level, [a, b, c]) => GNode::Abs(*level, [a, b, c]),
            GNode::App([a, b, c, d]) => GNode::App([a, b, c, d]),
            GNode::Sigma(level, [a, b]) => GNode::Sigma(*level, [a, b]),
            GNode::Pair(level, [a, b, c, d]) => GNode::Pair(*level, [a, b, c, d]),
            GNode::Fst([a, b, c]) => GNode::Fst([a, b, c]),
            GNode::Snd([a, b, c]) => GNode::Snd([a, b, c]),
            GNode::Ite([a, b, c, d]) => GNode::Ite([a, b, c, d]),
            GNode::Trunc([a]) => GNode::Trunc([a]),
            GNode::Choose([a, b]) => GNode::Choose([a, b]),
            GNode::Nats => GNode::Nats,
            GNode::Zero => GNode::Zero,
            GNode::Succ => GNode::Succ,
            GNode::Natrec([a, b, c, d]) => GNode::Natrec([a, b, c, d]),
            GNode::Let([a, b]) => GNode::Let([a, b]),
            GNode::Invalid => GNode::Invalid,
            GNode::HasTy([a, b]) => GNode::HasTy([a, b]),
            GNode::Import(import) => GNode::Import(import.as_ref()),
            GNode::Close(close) => GNode::Close(close.as_ref()),
        }
    }

    /// Borrow this node mutably
    pub fn as_mut(&mut self) -> GNode<&mut C, &mut T, &mut I> {
        match self {
            GNode::Var(x) => GNode::Var(x),
            GNode::Bv(i) => GNode::Bv(*i),
            GNode::U(level) => GNode::U(*level),
            GNode::Unit(level) => GNode::Unit(*level),
            GNode::Null(level) => GNode::Null(*level),
            GNode::Empty(level) => GNode::Empty(*level),
            GNode::Eqn([a, b]) => GNode::Eqn([a, b]),
            GNode::Pi(level, [a, b]) => GNode::Pi(*level, [a, b]),
            GNode::Abs(level, [a, b, c]) => GNode::Abs(*level, [a, b, c]),
            GNode::App([a, b, c, d]) => GNode::App([a, b, c, d]),
            GNode::Sigma(level, [a, b]) => GNode::Sigma(*level, [a, b]),
            GNode::Pair(level, [a, b, c, d]) => GNode::Pair(*level, [a, b, c, d]),
            GNode::Fst([a, b, c]) => GNode::Fst([a, b, c]),
            GNode::Snd([a, b, c]) => GNode::Snd([a, b, c]),
            GNode::Ite([a, b, c, d]) => GNode::Ite([a, b, c, d]),
            GNode::Trunc([a]) => GNode::Trunc([a]),
            GNode::Choose([a, b]) => GNode::Choose([a, b]),
            GNode::Nats => GNode::Nats,
            GNode::Zero => GNode::Zero,
            GNode::Succ => GNode::Succ,
            GNode::Natrec([a, b, c, d]) => GNode::Natrec([a, b, c, d]),
            GNode::Let([a, b]) => GNode::Let([a, b]),
            GNode::Invalid => GNode::Invalid,
            GNode::HasTy([a, b]) => GNode::HasTy([a, b]),
            GNode::Import(import) => GNode::Import(import.as_mut()),
            GNode::Close(close) => GNode::Close(close.as_mut()),
        }
    }

    /// Get the children of this term
    ///
    /// Note this only returns children _in the same context_ as this term; in particular, imports
    /// and closures will return an empty slice.
    pub fn children(&self) -> &[T] {
        match self {
            GNode::Var(_) => &[],
            GNode::Bv(_) => &[],
            GNode::U(_) => &[],
            GNode::Unit(_) => &[],
            GNode::Null(_) => &[],
            GNode::Empty(_) => &[],
            GNode::Eqn(xs) => &xs[..],
            GNode::Pi(_, xs) => &xs[..],
            GNode::Abs(_, xs) => &xs[..],
            GNode::App(xs) => &xs[..],
            GNode::Sigma(_, xs) => &xs[..],
            GNode::Pair(_, xs) => &xs[..],
            GNode::Fst(xs) => &xs[..],
            GNode::Snd(xs) => &xs[..],
            GNode::Ite(xs) => &xs[..],
            GNode::Trunc(xs) => &xs[..],
            GNode::Choose(xs) => &xs[..],
            GNode::Nats => &[],
            GNode::Zero => &[],
            GNode::Succ => &[],
            GNode::Natrec(xs) => &xs[..],
            GNode::Let(xs) => &xs[..],
            GNode::Invalid => &[],
            GNode::HasTy(xs) => &xs[..],
            GNode::Import(_) => &[],
            GNode::Close(_) => &[],
        }
    }

    /// Get the children of this term
    ///
    /// Note this only returns children _in the same context_ as this term; in particular, imports
    /// and closures will return an empty slice.
    pub fn children_mut(&mut self) -> &mut [T] {
        match self {
            GNode::Var(_) => &mut [],
            GNode::Bv(_) => &mut [],
            GNode::U(_) => &mut [],
            GNode::Unit(_) => &mut [],
            GNode::Null(_) => &mut [],
            GNode::Empty(_) => &mut [],
            GNode::Eqn(xs) => &mut xs[..],
            GNode::Pi(_, xs) => &mut xs[..],
            GNode::Abs(_, xs) => &mut xs[..],
            GNode::App(xs) => &mut xs[..],
            GNode::Sigma(_, xs) => &mut xs[..],
            GNode::Pair(_, xs) => &mut xs[..],
            GNode::Fst(xs) => &mut xs[..],
            GNode::Snd(xs) => &mut xs[..],
            GNode::Ite(xs) => &mut xs[..],
            GNode::Trunc(xs) => &mut xs[..],
            GNode::Choose(xs) => &mut xs[..],
            GNode::Nats => &mut [],
            GNode::Zero => &mut [],
            GNode::Succ => &mut [],
            GNode::Natrec(xs) => &mut xs[..],
            GNode::Let(xs) => &mut xs[..],
            GNode::Invalid => &mut [],
            GNode::HasTy(xs) => &mut xs[..],
            GNode::Import(_) => &mut [],
            GNode::Close(_) => &mut [],
        }
    }

    /// Compute a bound on this term's unbound variables
    pub fn bvi(&self, mut tm: impl FnMut(&T) -> Bv) -> Bv {
        match self {
            GNode::Bv(i) => i.succ(),
            GNode::Import(i) => i.bvi,
            GNode::Close(_) => Bv(1),
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

    /// Get this node as a universe level
    pub fn as_level(&self) -> Option<ULevel> {
        match self {
            GNode::U(level) => Some(*level),
            _ => None,
        }
    }
}

impl<C, T> Default for GNode<C, T> {
    fn default() -> Self {
        GNode::Invalid
    }
}

/// A bound variable
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Bv(pub u32);

impl Bv {
    /// Get the successor of this bound variable
    pub fn succ(self) -> Bv {
        Bv(self.0.checked_add(1).expect("bound variable overflow"))
    }
}

impl Add for Bv {
    type Output = Bv;

    fn add(self, rhs: Bv) -> Bv {
        Bv(self.0.checked_add(rhs.0).expect("bound variable overflow"))
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
        write!(f, "#{}", self.0)
    }
}

/// A universe level
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ULevel {
    level: u32,
}

impl ULevel {
    pub const PROP: Self = ULevel { level: 0 };
    pub const SET: Self = ULevel { level: 1 };

    /// Get the successor of this universe level
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::term::ULevel;
    /// assert_eq!(ULevel::PROP.succ(), ULevel::SET);
    /// ```
    pub fn succ(self) -> Self {
        ULevel {
            level: self.level + 1,
        }
    }
}

impl Debug for ULevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#U{}", self.level)
    }
}

/// An import from another context
pub struct Import<C, T> {
    /// The context being imported from
    pub ctx: C,
    /// The term being imported
    pub term: T,
    /// An upper bound on the number of unbound variables in the import
    ///
    /// If this upper bound is invalid, the import is invalid
    pub bvi: Bv,
}

impl<C, T> Import<C, T> {
    /// Borrow this import
    pub fn as_ref(&self) -> Import<&C, &T> {
        Import {
            ctx: &self.ctx,
            term: &self.term,
            bvi: self.bvi,
        }
    }

    /// Borrow this import mutably
    pub fn as_mut(&mut self) -> Import<&mut C, &mut T> {
        Import {
            ctx: &mut self.ctx,
            term: &mut self.term,
            bvi: self.bvi,
        }
    }
}

/// An import from another context, closing over that context's parameter
///
/// If the imported term is not locally closed, this is invalid
///
/// Note that, unlike unary substitutions, we do not provide the equivalent of `Let` to close over
/// a variable `x`, since this does _not_ necessarily respect the rewriting relation.
pub struct Close<C, T> {
    /// The context being imported from
    pub ctx: C,
    /// The term being imported
    pub term: T,
}

impl<C, T> Close<C, T> {
    /// Borrow this import
    pub fn as_ref(&self) -> Close<&C, &T> {
        Close {
            ctx: &self.ctx,
            term: &self.term,
        }
    }

    /// Borrow this import mutably
    pub fn as_mut(&mut self) -> Close<&mut C, &mut T> {
        Close {
            ctx: &mut self.ctx,
            term: &mut self.term,
        }
    }
}

impl<C, T> From<Bv> for GNode<C, T> {
    fn from(bv: Bv) -> Self {
        GNode::Bv(bv)
    }
}

impl<C, T> From<ULevel> for GNode<C, T> {
    fn from(level: ULevel) -> Self {
        GNode::U(level)
    }
}

impl<C, T> From<bool> for GNode<C, T> {
    fn from(value: bool) -> Self {
        if value {
            GNode::Unit(ULevel::PROP)
        } else {
            GNode::Empty(ULevel::PROP)
        }
    }
}

impl<C, T> From<Import<C, T>> for GNode<C, T> {
    fn from(import: Import<C, T>) -> Self {
        GNode::Import(import)
    }
}

impl<C, T> From<Close<C, T>> for GNode<C, T> {
    fn from(close: Close<C, T>) -> Self {
        GNode::Close(close)
    }
}
