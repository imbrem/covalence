use std::{
    fmt::{self, Debug},
    ops::{Add, Sub},
};

/// A term in `covalence`'s core calculus
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum GNode<C, T, I = T> {
    // == Term formers, corresponding to Tm from `gt3-lean` ==
    /// A free variable
    Fv(Gv<C>),
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
    Invalid,

    // == Syntax extensions ==
    /// A substitution under `k` binders
    Let(Bv, [T; 2]),
    /// A weakening under `k` binders
    Wk1(Bv, [T; 1]),
    /// A variable closure under `k` binders
    Close(Close<C, T>),

    // == Imports from other contexts ==
    /// A direct import from another context
    Import(Import<C, I>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum GDisc<C, T, I = T> {
    Fv(Gv<C>),
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
    Wk1(Bv),
    Close(Close<C, T>),
    Import(Import<C, I>),
}

impl<C, T, I> GNode<C, T, I> {
    /// Get this node's discriminant
    pub fn disc(self) -> GDisc<C, T, I> {
        match self {
            GNode::Fv(x) => GDisc::Fv(x),
            GNode::Bv(i) => GDisc::Bv(i),
            GNode::U(level) => GDisc::U(level),
            GNode::Empty => GDisc::Empty,
            GNode::Unit => GDisc::Unit,
            GNode::Null => GDisc::Null,
            GNode::Eqn(_) => GDisc::Eqn,
            GNode::Pi(_) => GDisc::Pi,
            GNode::Sigma(_) => GDisc::Sigma,
            GNode::Abs(_) => GDisc::Abs,
            GNode::App(_) => GDisc::App,
            GNode::Pair(_) => GDisc::Pair,
            GNode::Fst(_) => GDisc::Fst,
            GNode::Snd(_) => GDisc::Snd,
            GNode::Ite(_) => GDisc::Ite,
            GNode::Trunc(_) => GDisc::Trunc,
            GNode::Choose(_) => GDisc::Choose,
            GNode::Nats => GDisc::Nats,
            GNode::N64(n) => GDisc::N64(n),
            GNode::Succ(_) => GDisc::Succ,
            GNode::Natrec(_) => GDisc::Natrec,
            GNode::HasTy(_) => GDisc::HasTy,
            GNode::Invalid => GDisc::Invalid,
            GNode::Let(k, _) => GDisc::Let(k),
            GNode::Wk1(k, _) => GDisc::Wk1(k),
            GNode::Close(close) => GDisc::Close(close),
            GNode::Import(import) => GDisc::Import(import),
        }
    }

    /// Map this node's children
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> GNode<C, U, I> {
        match self {
            GNode::Fv(x) => GNode::Fv(x),
            GNode::Bv(i) => GNode::Bv(i),
            GNode::U(level) => GNode::U(level),
            GNode::Empty => GNode::Empty,
            GNode::Unit => GNode::Unit,
            GNode::Null => GNode::Null,
            GNode::Eqn([a, b]) => GNode::Eqn([f(a), f(b)]),
            GNode::Pi([a, b]) => GNode::Pi([f(a), f(b)]),
            GNode::Sigma([a, b]) => GNode::Sigma([f(a), f(b)]),
            GNode::Abs([a, b]) => GNode::Abs([f(a), f(b)]),
            GNode::App([a, b]) => GNode::App([f(a), f(b)]),
            GNode::Pair([a, b]) => GNode::Pair([f(a), f(b)]),
            GNode::Fst([a]) => GNode::Fst([f(a)]),
            GNode::Snd([a]) => GNode::Snd([f(a)]),
            GNode::Ite([a, b, c]) => GNode::Ite([f(a), f(b), f(c)]),
            GNode::Trunc([a]) => GNode::Trunc([f(a)]),
            GNode::Choose([a, b]) => GNode::Choose([f(a), f(b)]),
            GNode::Nats => GNode::Nats,
            GNode::N64(n) => GNode::N64(n),
            GNode::Succ([a]) => GNode::Succ([f(a)]),
            GNode::Natrec([a, b, c]) => GNode::Natrec([f(a), f(b), f(c)]),
            GNode::HasTy([a, b]) => GNode::HasTy([f(a), f(b)]),
            GNode::Invalid => GNode::Invalid,
            GNode::Let(k, [a, b]) => GNode::Let(k, [f(a), f(b)]),
            GNode::Wk1(k, [a]) => GNode::Wk1(k, [f(a)]),
            GNode::Close(close) => GNode::Close(Close {
                under: close.under,
                var: close.var,
                ix: close.ix,
                tm: f(close.tm),
            }),
            GNode::Import(import) => GNode::Import(import),
        }
    }

    /// Map this node's children, potentially returning an error
    pub fn try_map<U, E>(self, mut f: impl FnMut(T) -> Result<U, E>) -> Result<GNode<C, U, I>, E> {
        match self {
            GNode::Fv(x) => Ok(GNode::Fv(x)),
            GNode::Bv(i) => Ok(GNode::Bv(i)),
            GNode::U(level) => Ok(GNode::U(level)),
            GNode::Empty => Ok(GNode::Empty),
            GNode::Unit => Ok(GNode::Unit),
            GNode::Null => Ok(GNode::Null),
            GNode::Eqn([a, b]) => Ok(GNode::Eqn([f(a)?, f(b)?])),
            GNode::Pi([a, b]) => Ok(GNode::Pi([f(a)?, f(b)?])),
            GNode::Sigma([a, b]) => Ok(GNode::Sigma([f(a)?, f(b)?])),
            GNode::Abs([a, b]) => Ok(GNode::Abs([f(a)?, f(b)?])),
            GNode::App([a, b]) => Ok(GNode::App([f(a)?, f(b)?])),
            GNode::Pair([a, b]) => Ok(GNode::Pair([f(a)?, f(b)?])),
            GNode::Fst([a]) => Ok(GNode::Fst([f(a)?])),
            GNode::Snd([a]) => Ok(GNode::Snd([f(a)?])),
            GNode::Ite([a, b, c]) => Ok(GNode::Ite([f(a)?, f(b)?, f(c)?])),
            GNode::Trunc([a]) => Ok(GNode::Trunc([f(a)?])),
            GNode::Choose([a, b]) => Ok(GNode::Choose([f(a)?, f(b)?])),
            GNode::Nats => Ok(GNode::Nats),
            GNode::N64(n) => Ok(GNode::N64(n)),
            GNode::Succ([a]) => Ok(GNode::Succ([f(a)?])),
            GNode::Natrec([a, b, c]) => Ok(GNode::Natrec([f(a)?, f(b)?, f(c)?])),
            GNode::HasTy([a, b]) => Ok(GNode::HasTy([f(a)?, f(b)?])),
            GNode::Invalid => Ok(GNode::Invalid),
            GNode::Let(k, [a, b]) => Ok(GNode::Let(k, [f(a)?, f(b)?])),
            GNode::Wk1(k, [a]) => Ok(GNode::Wk1(k, [f(a)?])),
            GNode::Close(close) => Ok(GNode::Close(Close {
                under: close.under,
                ix: close.ix,
                var: close.var,
                tm: f(close.tm)?,
            })),
            GNode::Import(import) => Ok(GNode::Import(import)),
        }
    }

    /// Annotate this node's children with binders
    pub fn with_binders(self) -> GNode<C, (Bv, T), I> {
        match self {
            GNode::Fv(x) => GNode::Fv(x),
            GNode::Bv(i) => GNode::Bv(i),
            GNode::U(level) => GNode::U(level),
            GNode::Empty => GNode::Empty,
            GNode::Unit => GNode::Unit,
            GNode::Null => GNode::Null,
            GNode::Eqn([a, b]) => GNode::Eqn([(Bv(0), a), (Bv(0), b)]),
            GNode::Pi([a, b]) => GNode::Pi([(Bv(0), a), (Bv(1), b)]),
            GNode::Sigma([a, b]) => GNode::Sigma([(Bv(0), a), (Bv(1), b)]),
            GNode::Abs([a, b]) => GNode::Abs([(Bv(0), a), (Bv(1), b)]),
            GNode::App([a, b]) => GNode::App([(Bv(0), a), (Bv(0), b)]),
            GNode::Pair([a, b]) => GNode::Pair([(Bv(0), a), (Bv(0), b)]),
            GNode::Fst([a]) => GNode::Fst([(Bv(0), a)]),
            GNode::Snd([a]) => GNode::Snd([(Bv(0), a)]),
            GNode::Ite([a, b, c]) => GNode::Ite([(Bv(0), a), (Bv(0), b), (Bv(0), c)]),
            GNode::Trunc([a]) => GNode::Trunc([(Bv(0), a)]),
            GNode::Choose([a, b]) => GNode::Choose([(Bv(0), a), (Bv(1), b)]),
            GNode::Nats => GNode::Nats,
            GNode::N64(n) => GNode::N64(n),
            GNode::Succ([a]) => GNode::Succ([(Bv(0), a)]),
            GNode::Natrec([a, b, c]) => GNode::Natrec([(Bv(0), a), (Bv(0), b), (Bv(0), c)]),
            GNode::HasTy([a, b]) => GNode::HasTy([(Bv(0), a), (Bv(0), b)]),
            GNode::Invalid => GNode::Invalid,
            GNode::Let(k, [a, b]) => GNode::Let(k, [(Bv(0), a), (Bv(1), b)]),
            GNode::Wk1(k, [a]) => GNode::Wk1(k, [(Bv(0), a)]),
            GNode::Close(close) => GNode::Close(Close {
                under: close.under,
                var: close.var,
                ix: close.ix,
                tm: (Bv(0), close.tm),
            }),
            GNode::Import(import) => GNode::Import(import),
        }
    }

    /// Borrow this node
    pub fn as_ref(&self) -> GNode<&C, &T, &I> {
        match self {
            GNode::Fv(x) => GNode::Fv(x.as_ref()),
            GNode::Bv(i) => GNode::Bv(*i),
            GNode::U(level) => GNode::U(*level),
            GNode::Empty => GNode::Empty,
            GNode::Unit => GNode::Unit,
            GNode::Null => GNode::Null,
            GNode::Eqn([a, b]) => GNode::Eqn([a, b]),
            GNode::Pi([a, b]) => GNode::Pi([a, b]),
            GNode::Sigma([a, b]) => GNode::Sigma([a, b]),
            GNode::Abs([a, b]) => GNode::Abs([a, b]),
            GNode::App([a, b]) => GNode::App([a, b]),
            GNode::Pair([a, b]) => GNode::Pair([a, b]),
            GNode::Fst([a]) => GNode::Fst([a]),
            GNode::Snd([a]) => GNode::Snd([a]),
            GNode::Ite([a, b, c]) => GNode::Ite([a, b, c]),
            GNode::Trunc([a]) => GNode::Trunc([a]),
            GNode::Choose([a, b]) => GNode::Choose([a, b]),
            GNode::Nats => GNode::Nats,
            GNode::N64(n) => GNode::N64(*n),
            GNode::Succ([a]) => GNode::Succ([a]),
            GNode::Natrec([a, b, c]) => GNode::Natrec([a, b, c]),
            GNode::HasTy([a, b]) => GNode::HasTy([a, b]),
            GNode::Invalid => GNode::Invalid,
            GNode::Let(k, [a, b]) => GNode::Let(*k, [a, b]),
            GNode::Wk1(k, [a]) => GNode::Wk1(*k, [a]),
            GNode::Close(close) => GNode::Close(close.as_ref()),
            GNode::Import(import) => GNode::Import(import.as_ref()),
        }
    }

    /// Borrow this node mutably
    pub fn as_mut(&mut self) -> GNode<&mut C, &mut T, &mut I> {
        match self {
            GNode::Fv(x) => GNode::Fv(x.as_mut()),
            GNode::Bv(i) => GNode::Bv(*i),
            GNode::U(level) => GNode::U(*level),
            GNode::Empty => GNode::Empty,
            GNode::Unit => GNode::Unit,
            GNode::Null => GNode::Null,
            GNode::Eqn([a, b]) => GNode::Eqn([a, b]),
            GNode::Pi([a, b]) => GNode::Pi([a, b]),
            GNode::Sigma([a, b]) => GNode::Sigma([a, b]),
            GNode::Abs([a, b]) => GNode::Abs([a, b]),
            GNode::App([a, b]) => GNode::App([a, b]),
            GNode::Pair([a, b]) => GNode::Pair([a, b]),
            GNode::Fst([a]) => GNode::Fst([a]),
            GNode::Snd([a]) => GNode::Snd([a]),
            GNode::Ite([a, b, c]) => GNode::Ite([a, b, c]),
            GNode::Trunc([a]) => GNode::Trunc([a]),
            GNode::Choose([a, b]) => GNode::Choose([a, b]),
            GNode::Nats => GNode::Nats,
            GNode::N64(n) => GNode::N64(*n),
            GNode::Succ([a]) => GNode::Succ([a]),
            GNode::Natrec([a, b, c]) => GNode::Natrec([a, b, c]),
            GNode::HasTy([a, b]) => GNode::HasTy([a, b]),
            GNode::Invalid => GNode::Invalid,
            GNode::Let(k, [a, b]) => GNode::Let(*k, [a, b]),
            GNode::Wk1(k, [a]) => GNode::Wk1(*k, [a]),
            GNode::Close(close) => GNode::Close(close.as_mut()),
            GNode::Import(import) => GNode::Import(import.as_mut()),
        }
    }

    /// Get the children of this term
    ///
    /// Note this only returns children _in the same context_ as this term; in particular, imports
    /// and closures will return an empty slice.
    pub fn children(&self) -> &[T] {
        match self {
            GNode::Fv(_) => &[],
            GNode::Bv(_) => &[],
            GNode::U(_) => &[],
            GNode::Empty => &[],
            GNode::Unit => &[],
            GNode::Null => &[],
            GNode::Eqn(xs) => &xs[..],
            GNode::Pi(xs) => &xs[..],
            GNode::Sigma(xs) => &xs[..],
            GNode::Abs(xs) => &xs[..],
            GNode::App(xs) => &xs[..],
            GNode::Pair(xs) => &xs[..],
            GNode::Fst(xs) => &xs[..],
            GNode::Snd(xs) => &xs[..],
            GNode::Ite(xs) => &xs[..],
            GNode::Trunc(xs) => &xs[..],
            GNode::Choose(xs) => &xs[..],
            GNode::Nats => &[],
            GNode::N64(_) => &[],
            GNode::Succ(xs) => &xs[..],
            GNode::Natrec(xs) => &xs[..],
            GNode::HasTy(xs) => &xs[..],
            GNode::Invalid => &[],
            GNode::Let(_, xs) => &xs[..],
            GNode::Wk1(_, xs) => &xs[..],
            GNode::Close(_) => &[],
            GNode::Import(_) => &[],
        }
    }

    /// Get the children of this term
    ///
    /// Note this only returns children _in the same context_ as this term; in particular, imports
    /// and closures will return an empty slice.
    pub fn children_mut(&mut self) -> &mut [T] {
        match self {
            GNode::Fv(_) => &mut [],
            GNode::Bv(_) => &mut [],
            GNode::U(_) => &mut [],
            GNode::Empty => &mut [],
            GNode::Unit => &mut [],
            GNode::Null => &mut [],
            GNode::Eqn(xs) => &mut xs[..],
            GNode::Pi(xs) => &mut xs[..],
            GNode::Sigma(xs) => &mut xs[..],
            GNode::Abs(xs) => &mut xs[..],
            GNode::App(xs) => &mut xs[..],
            GNode::Pair(xs) => &mut xs[..],
            GNode::Fst(xs) => &mut xs[..],
            GNode::Snd(xs) => &mut xs[..],
            GNode::Ite(xs) => &mut xs[..],
            GNode::Trunc(xs) => &mut xs[..],
            GNode::Choose(xs) => &mut xs[..],
            GNode::Nats => &mut [],
            GNode::N64(_) => &mut [],
            GNode::Succ(xs) => &mut xs[..],
            GNode::Natrec(xs) => &mut xs[..],
            GNode::HasTy(xs) => &mut xs[..],
            GNode::Invalid => &mut [],
            GNode::Let(_, xs) => &mut xs[..],
            GNode::Wk1(_, xs) => &mut xs[..],
            GNode::Close(_) => &mut [],
            GNode::Import(_) => &mut [],
        }
    }

    /// Compute a bound on this term's unbound variables
    pub fn bvi(&self, mut tm: impl FnMut(&T) -> Bv) -> Bv {
        match self {
            GNode::Bv(i) => i.succ(),
            GNode::Import(i) => i.bvi,
            GNode::Close(Close {
                under: k, tm: a, ..
            })
            | GNode::Wk1(k, [a]) => {
                let b = tm(&a);
                if b < *k { b } else { b.succ() }
            }
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
    pub fn as_level(&self) -> Option<ULvl> {
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

/// A variable index in `covalence`'s core calculus
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Gv<C> {
    pub ctx: C,
    pub ix: u32,
}

impl<C> Gv<C> {
    pub fn as_ref(&self) -> Gv<&C> {
        Gv {
            ctx: &self.ctx,
            ix: self.ix,
        }
    }

    pub fn as_mut(&mut self) -> Gv<&mut C> {
        Gv {
            ctx: &mut self.ctx,
            ix: self.ix,
        }
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
    pub var: C,
    /// The index of the variable being closed over
    pub ix: u32,
    /// The term being closed over (in `this`, _not_ necessarily `ctx`)
    pub tm: T,
}

impl<C, T> Close<C, T> {
    /// Borrow this closure
    pub fn as_ref(&self) -> Close<&C, &T> {
        Close {
            under: self.under,
            var: &self.var,
            ix: self.ix,
            tm: &self.tm,
        }
    }

    /// Borrow this closure mutably
    pub fn as_mut(&mut self) -> Close<&mut C, &mut T> {
        Close {
            under: self.under,
            var: &mut self.var,
            ix: self.ix,
            tm: &mut self.tm,
        }
    }
}

/// An import from another context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Import<C, T> {
    /// The context being imported from
    pub ctx: C,
    /// The term being imported (in `ctx`)
    pub tm: T,
    /// The number of unbound variables in the import
    ///
    /// If this bound is incorrect, the import is invalid
    pub bvi: Bv,
}

impl<C, T> Import<C, T> {
    /// Borrow this import
    pub fn as_ref(&self) -> Import<&C, &T> {
        Import {
            ctx: &self.ctx,
            tm: &self.tm,
            bvi: self.bvi,
        }
    }

    /// Borrow this import mutably
    pub fn as_mut(&mut self) -> Import<&mut C, &mut T> {
        Import {
            ctx: &mut self.ctx,
            tm: &mut self.tm,
            bvi: self.bvi,
        }
    }
}

impl<C, T> From<Bv> for GNode<C, T> {
    fn from(bv: Bv) -> Self {
        GNode::Bv(bv)
    }
}

impl<C, T> From<ULvl> for GNode<C, T> {
    fn from(level: ULvl) -> Self {
        GNode::U(level)
    }
}

impl<C, T> From<bool> for GNode<C, T> {
    fn from(value: bool) -> Self {
        if value { GNode::Unit } else { GNode::Empty }
    }
}

impl<C, T> From<Import<C, T>> for GNode<C, T> {
    fn from(copy: Import<C, T>) -> Self {
        GNode::Import(copy)
    }
}

impl<C, T> From<Close<C, T>> for GNode<C, T> {
    fn from(close: Close<C, T>) -> Self {
        GNode::Close(close)
    }
}
