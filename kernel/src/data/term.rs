use std::{
    fmt::{self, Debug},
    ops::{Add, Sub},
};

pub use crate::univ::ULvl;

/// A term in `covalence`'s core calculus
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub enum Node<C, T, I = TmIn<C, T>> {
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

/// The discriminant of a term node
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum DiscT<C, T, I = TmIn<C, T>> {
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
    Eqn,
    /// A pi type
    Pi,
    /// A sigma type
    Sigma,
    /// An abstraction
    Abs,
    /// An application
    App,
    /// A pair
    Pair,
    /// The first projection of a pair
    Fst,
    /// The second projection of a pair
    Snd,
    /// A dependent if-then-else
    Ite,
    /// A propositional truncation
    Trunc,
    /// Hilbert choice
    Choose,
    /// The type of natural numbers
    Nats,
    /// A small natural number
    N64(u64),
    /// The successor of a natural number
    Succ,
    /// Recursion on natural numbers
    Natrec,
    /// An assertion that a term has the given type
    HasTy,
    /// A known-invalid term
    Invalid,
    /// A substitution under `k` binders
    Subst1(Bv),
    /// A weakening by a shift
    BWk(Shift),
    /// A variable closure under `k` binders
    Close(Close<C, T>),
    /// A direct import from another context
    Import(I),
}

/// A syntactic discriminant, over a given import type
pub type SynDiscIT<C, I> = DiscT<C, (), I>;

/// A syntactic discriminant
pub type SynDiscT<C, T> = SynDiscIT<C, TmIn<C, T>>;

impl<C, T, I> Node<C, T, I> {
    /// Construct a bound variable
    pub const fn bv(ix: u32) -> Node<C, T, I> {
        Node::Bv(Bv::new(ix))
    }

    /// Construct a substitution
    pub const fn subst1(bound: T, body: T) -> Node<C, T, I> {
        Node::Subst1(Bv::new(0), [bound, body])
    }

    /// Get this node's discriminant
    pub fn disc(self) -> DiscT<C, T, I> {
        match self {
            Node::Fv(x) => DiscT::Fv(x),
            Node::Bv(i) => DiscT::Bv(i),
            Node::U(level) => DiscT::U(level),
            Node::Empty => DiscT::Empty,
            Node::Unit => DiscT::Unit,
            Node::Null => DiscT::Null,
            Node::Eqn(_) => DiscT::Eqn,
            Node::Pi(_) => DiscT::Pi,
            Node::Sigma(_) => DiscT::Sigma,
            Node::Abs(_) => DiscT::Abs,
            Node::App(_) => DiscT::App,
            Node::Pair(_) => DiscT::Pair,
            Node::Fst(_) => DiscT::Fst,
            Node::Snd(_) => DiscT::Snd,
            Node::Ite(_) => DiscT::Ite,
            Node::Trunc(_) => DiscT::Trunc,
            Node::Choose(_) => DiscT::Choose,
            Node::Nats => DiscT::Nats,
            Node::N64(n) => DiscT::N64(n),
            Node::Succ(_) => DiscT::Succ,
            Node::Natrec(_) => DiscT::Natrec,
            Node::HasTy(_) => DiscT::HasTy,
            Node::Invalid => DiscT::Invalid,
            Node::Subst1(k, _) => DiscT::Subst1(k),
            Node::BWk(s, _) => DiscT::BWk(s),
            Node::Close(close) => DiscT::Close(close),
            Node::Import(import) => DiscT::Import(import),
        }
    }

    /// Get this node's syntactic discriminant
    pub fn syn_disc(self) -> SynDiscIT<C, I> {
        match self {
            Node::Fv(x) => DiscT::Fv(x),
            Node::Bv(i) => DiscT::Bv(i),
            Node::U(level) => DiscT::U(level),
            Node::Empty => DiscT::Empty,
            Node::Unit => DiscT::Unit,
            Node::Null => DiscT::Null,
            Node::Eqn(_) => DiscT::Eqn,
            Node::Pi(_) => DiscT::Pi,
            Node::Sigma(_) => DiscT::Sigma,
            Node::Abs(_) => DiscT::Abs,
            Node::App(_) => DiscT::App,
            Node::Pair(_) => DiscT::Pair,
            Node::Fst(_) => DiscT::Fst,
            Node::Snd(_) => DiscT::Snd,
            Node::Ite(_) => DiscT::Ite,
            Node::Trunc(_) => DiscT::Trunc,
            Node::Choose(_) => DiscT::Choose,
            Node::Nats => DiscT::Nats,
            Node::N64(n) => DiscT::N64(n),
            Node::Succ(_) => DiscT::Succ,
            Node::Natrec(_) => DiscT::Natrec,
            Node::HasTy(_) => DiscT::HasTy,
            Node::Invalid => DiscT::Invalid,
            Node::Subst1(k, _) => DiscT::Subst1(k),
            Node::BWk(s, _) => DiscT::BWk(s),
            Node::Close(close) => DiscT::Close(close.op()),
            Node::Import(import) => DiscT::Import(import),
        }
    }

    /// Map this node's subterms and imports
    pub fn map<U, J>(self, mut f: impl FnMut(T) -> U, g: impl FnOnce(I) -> J) -> Node<C, U, J> {
        match self {
            Node::Fv(x) => Node::Fv(x),
            Node::Bv(i) => Node::Bv(i),
            Node::U(level) => Node::U(level),
            Node::Empty => Node::Empty,
            Node::Unit => Node::Unit,
            Node::Null => Node::Null,
            Node::Eqn([a, b]) => Node::Eqn([f(a), f(b)]),
            Node::Pi([a, b]) => Node::Pi([f(a), f(b)]),
            Node::Sigma([a, b]) => Node::Sigma([f(a), f(b)]),
            Node::Abs([a, b]) => Node::Abs([f(a), f(b)]),
            Node::App([a, b]) => Node::App([f(a), f(b)]),
            Node::Pair([a, b]) => Node::Pair([f(a), f(b)]),
            Node::Fst([a]) => Node::Fst([f(a)]),
            Node::Snd([a]) => Node::Snd([f(a)]),
            Node::Ite([a, b, c]) => Node::Ite([f(a), f(b), f(c)]),
            Node::Trunc([a]) => Node::Trunc([f(a)]),
            Node::Choose([a, b]) => Node::Choose([f(a), f(b)]),
            Node::Nats => Node::Nats,
            Node::N64(n) => Node::N64(n),
            Node::Succ([a]) => Node::Succ([f(a)]),
            Node::Natrec([a, b, c]) => Node::Natrec([f(a), f(b), f(c)]),
            Node::HasTy([a, b]) => Node::HasTy([f(a), f(b)]),
            Node::Invalid => Node::Invalid,
            Node::Subst1(k, [a, b]) => Node::Subst1(k, [f(a), f(b)]),
            Node::BWk(k, [a]) => Node::BWk(k, [f(a)]),
            Node::Close(close) => Node::Close(Close {
                under: close.under,
                var: close.var,
                tm: f(close.tm),
            }),
            Node::Import(import) => Node::Import(g(import)),
        }
    }

    /// Map this node's subterms
    pub fn map_subterms<U>(self, f: impl FnMut(T) -> U) -> Node<C, U, I> {
        self.map(f, |x| x)
    }

    /// Map this node's imports
    pub fn map_import<J>(self, g: impl FnOnce(I) -> J) -> Node<C, T, J> {
        self.map(|x| x, g)
    }

    /// Map this node's subterms and imports, potentially returning an error
    pub fn try_map<U, J, E>(
        self,
        mut f: impl FnMut(T) -> Result<U, E>,
        g: impl FnOnce(I) -> Result<J, E>,
    ) -> Result<Node<C, U, J>, E> {
        match self {
            Node::Fv(x) => Ok(Node::Fv(x)),
            Node::Bv(i) => Ok(Node::Bv(i)),
            Node::U(level) => Ok(Node::U(level)),
            Node::Empty => Ok(Node::Empty),
            Node::Unit => Ok(Node::Unit),
            Node::Null => Ok(Node::Null),
            Node::Eqn([a, b]) => Ok(Node::Eqn([f(a)?, f(b)?])),
            Node::Pi([a, b]) => Ok(Node::Pi([f(a)?, f(b)?])),
            Node::Sigma([a, b]) => Ok(Node::Sigma([f(a)?, f(b)?])),
            Node::Abs([a, b]) => Ok(Node::Abs([f(a)?, f(b)?])),
            Node::App([a, b]) => Ok(Node::App([f(a)?, f(b)?])),
            Node::Pair([a, b]) => Ok(Node::Pair([f(a)?, f(b)?])),
            Node::Fst([a]) => Ok(Node::Fst([f(a)?])),
            Node::Snd([a]) => Ok(Node::Snd([f(a)?])),
            Node::Ite([a, b, c]) => Ok(Node::Ite([f(a)?, f(b)?, f(c)?])),
            Node::Trunc([a]) => Ok(Node::Trunc([f(a)?])),
            Node::Choose([a, b]) => Ok(Node::Choose([f(a)?, f(b)?])),
            Node::Nats => Ok(Node::Nats),
            Node::N64(n) => Ok(Node::N64(n)),
            Node::Succ([a]) => Ok(Node::Succ([f(a)?])),
            Node::Natrec([a, b, c]) => Ok(Node::Natrec([f(a)?, f(b)?, f(c)?])),
            Node::HasTy([a, b]) => Ok(Node::HasTy([f(a)?, f(b)?])),
            Node::Invalid => Ok(Node::Invalid),
            Node::Subst1(k, [a, b]) => Ok(Node::Subst1(k, [f(a)?, f(b)?])),
            Node::BWk(k, [a]) => Ok(Node::BWk(k, [f(a)?])),
            Node::Close(close) => Ok(Node::Close(Close {
                under: close.under,
                var: close.var,
                tm: f(close.tm)?,
            })),
            Node::Import(import) => Ok(Node::Import(g(import)?)),
        }
    }

    /// Map this node's children, potentially returning an error
    pub fn try_map_subterms<U, E>(
        self,
        f: impl FnMut(T) -> Result<U, E>,
    ) -> Result<Node<C, U, I>, E> {
        self.try_map(f, Ok)
    }

    /// Map this node's imports, potentially returning an error
    pub fn try_map_import<J, E>(
        self,
        g: impl FnOnce(I) -> Result<J, E>,
    ) -> Result<Node<C, T, J>, E> {
        self.try_map(Ok, g)
    }

    /// Annotate this node's subterms with binders
    pub fn with_binders(self) -> Node<C, (Bv, T), I> {
        match self {
            Node::Fv(x) => Node::Fv(x),
            Node::Bv(i) => Node::Bv(i),
            Node::U(level) => Node::U(level),
            Node::Empty => Node::Empty,
            Node::Unit => Node::Unit,
            Node::Null => Node::Null,
            Node::Eqn([a, b]) => Node::Eqn([(Bv(0), a), (Bv(0), b)]),
            Node::Pi([a, b]) => Node::Pi([(Bv(0), a), (Bv(1), b)]),
            Node::Sigma([a, b]) => Node::Sigma([(Bv(0), a), (Bv(1), b)]),
            Node::Abs([a, b]) => Node::Abs([(Bv(0), a), (Bv(1), b)]),
            Node::App([a, b]) => Node::App([(Bv(0), a), (Bv(0), b)]),
            Node::Pair([a, b]) => Node::Pair([(Bv(0), a), (Bv(0), b)]),
            Node::Fst([a]) => Node::Fst([(Bv(0), a)]),
            Node::Snd([a]) => Node::Snd([(Bv(0), a)]),
            Node::Ite([a, b, c]) => Node::Ite([(Bv(0), a), (Bv(0), b), (Bv(0), c)]),
            Node::Trunc([a]) => Node::Trunc([(Bv(0), a)]),
            Node::Choose([a, b]) => Node::Choose([(Bv(0), a), (Bv(1), b)]),
            Node::Nats => Node::Nats,
            Node::N64(n) => Node::N64(n),
            Node::Succ([a]) => Node::Succ([(Bv(0), a)]),
            Node::Natrec([a, b, c]) => Node::Natrec([(Bv(0), a), (Bv(0), b), (Bv(0), c)]),
            Node::HasTy([a, b]) => Node::HasTy([(Bv(0), a), (Bv(0), b)]),
            Node::Invalid => Node::Invalid,
            Node::Subst1(k, [a, b]) => Node::Subst1(k, [(Bv(0), a), (Bv(1), b)]),
            Node::BWk(k, [a]) => Node::BWk(k, [(Bv(0), a)]),
            Node::Close(close) => Node::Close(Close {
                under: close.under,
                var: close.var,
                tm: (Bv(0), close.tm),
            }),
            Node::Import(import) => Node::Import(import),
        }
    }

    /// Borrow this node
    pub fn as_ref(&self) -> Node<&C, &T, &I> {
        match self {
            Node::Fv(x) => Node::Fv(x.as_ref()),
            Node::Bv(i) => Node::Bv(*i),
            Node::U(level) => Node::U(*level),
            Node::Empty => Node::Empty,
            Node::Unit => Node::Unit,
            Node::Null => Node::Null,
            Node::Eqn([a, b]) => Node::Eqn([a, b]),
            Node::Pi([a, b]) => Node::Pi([a, b]),
            Node::Sigma([a, b]) => Node::Sigma([a, b]),
            Node::Abs([a, b]) => Node::Abs([a, b]),
            Node::App([a, b]) => Node::App([a, b]),
            Node::Pair([a, b]) => Node::Pair([a, b]),
            Node::Fst([a]) => Node::Fst([a]),
            Node::Snd([a]) => Node::Snd([a]),
            Node::Ite([a, b, c]) => Node::Ite([a, b, c]),
            Node::Trunc([a]) => Node::Trunc([a]),
            Node::Choose([a, b]) => Node::Choose([a, b]),
            Node::Nats => Node::Nats,
            Node::N64(n) => Node::N64(*n),
            Node::Succ([a]) => Node::Succ([a]),
            Node::Natrec([a, b, c]) => Node::Natrec([a, b, c]),
            Node::HasTy([a, b]) => Node::HasTy([a, b]),
            Node::Invalid => Node::Invalid,
            Node::Subst1(k, [a, b]) => Node::Subst1(*k, [a, b]),
            Node::BWk(k, [a]) => Node::BWk(*k, [a]),
            Node::Close(close) => Node::Close(close.as_ref()),
            Node::Import(import) => Node::Import(import),
        }
    }

    /// Borrow this node mutably
    pub fn as_mut(&mut self) -> Node<&mut C, &mut T, &mut I> {
        match self {
            Node::Fv(x) => Node::Fv(x.as_mut()),
            Node::Bv(i) => Node::Bv(*i),
            Node::U(level) => Node::U(*level),
            Node::Empty => Node::Empty,
            Node::Unit => Node::Unit,
            Node::Null => Node::Null,
            Node::Eqn([a, b]) => Node::Eqn([a, b]),
            Node::Pi([a, b]) => Node::Pi([a, b]),
            Node::Sigma([a, b]) => Node::Sigma([a, b]),
            Node::Abs([a, b]) => Node::Abs([a, b]),
            Node::App([a, b]) => Node::App([a, b]),
            Node::Pair([a, b]) => Node::Pair([a, b]),
            Node::Fst([a]) => Node::Fst([a]),
            Node::Snd([a]) => Node::Snd([a]),
            Node::Ite([a, b, c]) => Node::Ite([a, b, c]),
            Node::Trunc([a]) => Node::Trunc([a]),
            Node::Choose([a, b]) => Node::Choose([a, b]),
            Node::Nats => Node::Nats,
            Node::N64(n) => Node::N64(*n),
            Node::Succ([a]) => Node::Succ([a]),
            Node::Natrec([a, b, c]) => Node::Natrec([a, b, c]),
            Node::HasTy([a, b]) => Node::HasTy([a, b]),
            Node::Invalid => Node::Invalid,
            Node::Subst1(k, [a, b]) => Node::Subst1(*k, [a, b]),
            Node::BWk(k, [a]) => Node::BWk(*k, [a]),
            Node::Close(close) => Node::Close(close.as_mut()),
            Node::Import(import) => Node::Import(import),
        }
    }

    /// Get the children of this term
    ///
    /// Note that the argument of a closure does _not_ count as a child of the closure, since
    /// closure does _not_ respect congruence!
    pub fn children(&self) -> &[T] {
        match self {
            Node::Fv(_) => &[],
            Node::Bv(_) => &[],
            Node::U(_) => &[],
            Node::Empty => &[],
            Node::Unit => &[],
            Node::Null => &[],
            Node::Eqn(xs) => &xs[..],
            Node::Pi(xs) => &xs[..],
            Node::Sigma(xs) => &xs[..],
            Node::Abs(xs) => &xs[..],
            Node::App(xs) => &xs[..],
            Node::Pair(xs) => &xs[..],
            Node::Fst(xs) => &xs[..],
            Node::Snd(xs) => &xs[..],
            Node::Ite(xs) => &xs[..],
            Node::Trunc(xs) => &xs[..],
            Node::Choose(xs) => &xs[..],
            Node::Nats => &[],
            Node::N64(_) => &[],
            Node::Succ(xs) => &xs[..],
            Node::Natrec(xs) => &xs[..],
            Node::HasTy(xs) => &xs[..],
            Node::Invalid => &[],
            Node::Subst1(_, xs) => &xs[..],
            Node::BWk(_, xs) => &xs[..],
            Node::Close(_) => &[],
            Node::Import(_) => &[],
        }
    }

    /// Get the children of this term
    ///
    /// Note this only returns children _in the same context_ as this term; in particular, imports
    /// and closures will return an empty slice.
    pub fn children_mut(&mut self) -> &mut [T] {
        match self {
            Node::Fv(_) => &mut [],
            Node::Bv(_) => &mut [],
            Node::U(_) => &mut [],
            Node::Empty => &mut [],
            Node::Unit => &mut [],
            Node::Null => &mut [],
            Node::Eqn(xs) => &mut xs[..],
            Node::Pi(xs) => &mut xs[..],
            Node::Sigma(xs) => &mut xs[..],
            Node::Abs(xs) => &mut xs[..],
            Node::App(xs) => &mut xs[..],
            Node::Pair(xs) => &mut xs[..],
            Node::Fst(xs) => &mut xs[..],
            Node::Snd(xs) => &mut xs[..],
            Node::Ite(xs) => &mut xs[..],
            Node::Trunc(xs) => &mut xs[..],
            Node::Choose(xs) => &mut xs[..],
            Node::Nats => &mut [],
            Node::N64(_) => &mut [],
            Node::Succ(xs) => &mut xs[..],
            Node::Natrec(xs) => &mut xs[..],
            Node::HasTy(xs) => &mut xs[..],
            Node::Invalid => &mut [],
            Node::Subst1(_, xs) => &mut xs[..],
            Node::BWk(_, xs) => &mut xs[..],
            Node::Close(_) => &mut [],
            Node::Import(_) => &mut [],
        }
    }

    /// Get the _syntactic_ children of this term
    ///
    /// Note that this includes the argument of a closure, unlike [`children`](#method.children).
    pub fn syn_children(&self) -> &[T] {
        match self {
            Node::Close(cl) => std::slice::from_ref(&cl.tm),
            _ => self.children(),
        }
    }

    /// Get the _syntactic_ children of this term
    ///
    /// Note that this includes the argument of a closure, unlike
    /// [`children_mut`](#method.children_mut).
    pub fn syn_children_mut(&mut self) -> &mut [T] {
        match self {
            Node::Close(cl) => std::slice::from_mut(&mut cl.tm),
            _ => self.children_mut(),
        }
    }

    /// Check whether this term is relocatable
    pub fn is_relocatable(&self) -> bool {
        matches!(
            self,
            Node::Fv(_)
                | Node::Bv(_)
                | Node::U(_)
                | Node::Empty
                | Node::Unit
                | Node::Null
                | Node::Nats
                | Node::N64(_)
                | Node::Invalid
                | Node::Import(_)
        )
    }

    /// If this term has no dependencies, return it
    pub fn relocate(self) -> Option<Node<C, T, I>> {
        if self.is_relocatable() {
            Some(self)
        } else {
            None
        }
    }

    /// Compute a bound on this term's unbound variables
    pub fn bvi_with(&self, mut tm: impl FnMut(&T) -> Bv) -> Bv {
        match self {
            Node::Bv(i) => i.succ(),
            Node::Import(_) => Bv::INVALID,
            Node::Close(Close {
                under: k,
                tm: a,
                var,
            }) => tm(a).bvi_add_under(Bv(var.ix).succ(), *k),
            Node::BWk(s, [a]) => s.bvi(tm(a)),
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
            Node::Import(import) => Some(import),
            _ => None,
        }
    }

    /// Get this node as a universe level
    pub fn as_level(&self) -> Option<ULvl> {
        match self {
            Node::U(level) => Some(*level),
            _ => None,
        }
    }

    /// Get whether this node can be unfolded
    pub fn is_unfoldable(&self) -> bool {
        matches!(
            self,
            Node::Subst1(_, _) | Node::BWk(_, _) | Node::Close(_) | Node::Import(_)
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

/// A bound variable, represented by a de-Bruijn index
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
            "cannot use new to construct an invalid de-Bruijn index"
        );
        Bv(ix)
    }

    /// Get the successor of this bound variable
    ///
    /// Panics if this would overflow
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::data::term::Bv;
    /// for x in 0..100 {
    ///     assert_eq!(Bv(x).succ(), Bv(x + 1));
    /// }
    /// assert_eq!(Bv::INVALID.succ(), Bv::INVALID);
    /// ```
    pub fn succ(self) -> Bv {
        if self.0 == u32::MAX - 1 {
            panic!("de-Bruijn index overflow");
        }
        Bv(self.0.saturating_add(1))
    }

    /// Get the predecessory of this bound variable
    ///
    /// Panics if:
    /// - The bound variable is invalid
    ///     ```rust,should_panic
    ///     # use covalence::kernel::data::term::Bv;
    ///     Bv::INVALID.pred();
    ///     ```
    ///     
    /// - The bound variable is zero
    ///     ```rust,should_panic
    ///     # use covalence::kernel::data::term::Bv;
    ///     Bv(0).pred();
    ///     ```
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::data::term::Bv;
    /// for x in 0..100 {
    ///     assert_eq!(Bv(x).succ().pred(), Bv(x));
    /// }
    /// ```
    pub fn pred(self) -> Bv {
        if !self.is_valid() {
            panic!("attempted to take predecessor of invalid de-Bruijn index")
        }
        if self == Bv(0) {
            panic!("attempted to take predecessor of de-Bruijn index 0")
        }
        Bv(self.0 - 1)
    }

    /// Get whether this bound variable is valid
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::data::term::Bv;
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
    pub fn bvi_add_under(self, shift: Bv, under: Bv) -> Bv {
        if self < under { self } else { self + shift }
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
    pub under: Bv,
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
    /// # use covalence::kernel::data::term::*;
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
    /// Construct a new closure, under no variables
    pub fn new(var: Fv<C>, tm: T) -> Close<C, T> {
        Close {
            under: Bv(0),
            var,
            tm,
        }
    }

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

    /// Get this closure as an operation
    pub fn op(self) -> Close<C, ()> {
        Close {
            under: self.under,
            var: self.var,
            tm: (),
        }
    }
}

/// An import from another context
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

pub type NodeVT<C, T> = Node<C, TmIn<C, T>, TmIn<C, T>>;

pub type NodeT2<C, T> = Node<C, Node<C, T>, TmIn<C, T>>;

pub type NodeVT2<C, T> = Node<C, NodeVT<C, T>, TmIn<C, T>>;

impl<C, T> From<Fv<C>> for Node<C, T> {
    fn from(x: Fv<C>) -> Self {
        Node::Fv(x)
    }
}

impl<C: PartialEq, T> PartialEq<Fv<C>> for Node<C, T> {
    fn eq(&self, other: &Fv<C>) -> bool {
        match self {
            Node::Fv(this) => this == other,
            _ => false,
        }
    }
}

impl<C: PartialEq, T> PartialEq<Node<C, T>> for Fv<C> {
    fn eq(&self, other: &Node<C, T>) -> bool {
        other.eq(self)
    }
}

impl<C, T> From<Bv> for Node<C, T> {
    fn from(bv: Bv) -> Self {
        Node::Bv(bv)
    }
}

impl<C, T> PartialEq<Bv> for Node<C, T> {
    fn eq(&self, other: &Bv) -> bool {
        match self {
            Node::Bv(this) => this == other,
            _ => false,
        }
    }
}

impl<C, T> From<ULvl> for Node<C, T> {
    fn from(level: ULvl) -> Self {
        Node::U(level)
    }
}

impl<C, T> From<bool> for Node<C, T> {
    fn from(value: bool) -> Self {
        if value { Node::Unit } else { Node::Empty }
    }
}

impl<C, T> From<TmIn<C, T>> for Node<C, T> {
    fn from(copy: TmIn<C, T>) -> Self {
        Node::Import(copy)
    }
}

impl<C, T> From<Close<C, T>> for Node<C, T> {
    fn from(close: Close<C, T>) -> Self {
        Node::Close(close)
    }
}
