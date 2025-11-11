use super::*;

/// A term in `covalence`'s core calculus
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub enum Node<C, T, I = TmIn<C, T>, S = T> {
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

    //TODO: first/second projection function
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
    /// The identity function on a term
    Id(u64, [T; 1]),

    //TODO: identity tag
    /// A substitution under `k` binders
    Subst1(Bv, [T; 2]),
    /// A weakening by a shift
    BWk(Shift, [T; 1]),
    /// A single variable closure
    Close1(Close1<C, S>),

    //TODO: close segment

    //TODO: segment struct

    //TODO: project n [function]

    //TODO: rest n [function]

    //TODO: project var [function]

    //TODO: rest var [function]

    //TODO: differential segment struct?

    // == Imports from other contexts ==
    /// A direct import from another context
    Quote(I),
}

pub type DiscT<C, T, I = TmIn<C, T>> = Node<C, (), I, T>;

/// A syntactic discriminant, over a given import type
pub type SynDiscIT<C, I> = DiscT<C, (), I>;

/// A syntactic discriminant
pub type SynDiscT<C, T> = SynDiscIT<C, TmIn<C, T>>;

impl<C, T, I, S> Node<C, T, I, S> {
    /// Construct a bound variable
    pub const fn bv(ix: u32) -> Node<C, T, I> {
        Node::Bv(Bv::new(ix))
    }

    /// Construct a substitution
    pub const fn subst1(bound: T, body: T) -> Node<C, T, I> {
        Node::Subst1(Bv::new(0), [bound, body])
    }

    /// Map this node's subterms and imports, potentially returning an error
    pub fn try_map<U, J, V, E>(
        self,
        mut f: impl FnMut(T) -> Result<U, E>,
        g: impl FnOnce(I) -> Result<J, E>,
        syn: impl FnOnce(S) -> Result<V, E>,
    ) -> Result<Node<C, U, J, V>, E> {
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
            Node::Id(n, [a]) => Ok(Node::Id(n, [f(a)?])),
            Node::Subst1(k, [a, b]) => Ok(Node::Subst1(k, [f(a)?, f(b)?])),
            Node::BWk(k, [a]) => Ok(Node::BWk(k, [f(a)?])),
            Node::Close1(close) => Ok(Node::Close1(Close1 {
                under: close.under,
                var: close.var,
                tm: syn(close.tm)?,
            })),
            Node::Quote(import) => Ok(Node::Quote(g(import)?)),
        }
    }

    /// Map this node's children, potentially returning an error
    pub fn try_map_subterms<U, E>(
        self,
        f: impl FnMut(T) -> Result<U, E>,
    ) -> Result<Node<C, U, I, S>, E> {
        self.try_map(f, Ok, Ok)
    }

    /// Map this node's imports, potentially returning an error
    pub fn try_map_import<J, E>(
        self,
        g: impl FnOnce(I) -> Result<J, E>,
    ) -> Result<Node<C, T, J, S>, E> {
        self.try_map(Ok, g, Ok)
    }

    /// Map this node's subterms and imports
    pub fn map<U, J, V>(
        self,
        mut tm: impl FnMut(T) -> U,
        qt: impl FnOnce(I) -> J,
        syn: impl FnOnce(S) -> V,
    ) -> Node<C, U, J, V> {
        let res: Result<Node<C, U, J, V>, Infallible> =
            self.try_map(|x| Ok(tm(x)), |x| Ok(qt(x)), |x| Ok(syn(x)));
        res.unwrap()
    }

    /// Map this node's subterms
    pub fn map_children<U>(self, f: impl FnMut(T) -> U) -> Node<C, U, I, S> {
        self.map(f, |x| x, |x| x)
    }

    /// Map this node's quotes
    pub fn map_quote<J>(self, g: impl FnOnce(I) -> J) -> Node<C, T, J, S> {
        self.map(|x| x, g, |x| x)
    }

    /// Get this node's discriminant
    pub fn disc(self) -> DiscT<C, S, I> {
        self.map_children(|_| ())
    }

    /// Borrow this node
    pub fn as_ref(&self) -> Node<&C, &T, &I, &S> {
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
            Node::Id(n, [a]) => Node::Id(*n, [a]),
            Node::Subst1(k, [a, b]) => Node::Subst1(*k, [a, b]),
            Node::BWk(k, [a]) => Node::BWk(*k, [a]),
            Node::Close1(close) => Node::Close1(close.as_ref()),
            Node::Quote(import) => Node::Quote(import),
        }
    }

    /// Borrow this node mutably
    pub fn as_mut(&mut self) -> Node<&mut C, &mut T, &mut I, &mut S> {
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
            Node::Id(n, [a]) => Node::Id(*n, [a]),
            Node::Subst1(k, [a, b]) => Node::Subst1(*k, [a, b]),
            Node::BWk(k, [a]) => Node::BWk(*k, [a]),
            Node::Close1(close) => Node::Close1(close.as_mut()),
            Node::Quote(import) => Node::Quote(import),
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
            Node::Id(_, xs) => &xs[..],
            Node::Subst1(_, xs) => &xs[..],
            Node::BWk(_, xs) => &xs[..],
            Node::Close1(_) => &[],
            Node::Quote(_) => &[],
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
            Node::Id(_, xs) => &mut xs[..],
            Node::Subst1(_, xs) => &mut xs[..],
            Node::BWk(_, xs) => &mut xs[..],
            Node::Close1(_) => &mut [],
            Node::Quote(_) => &mut [],
        }
    }

    /// Check whether this term former is a congruence
    pub fn is_congr(&self) -> bool {
        !matches!(self, Node::Close1(_))
    }

    /// Get this node as an import
    pub fn as_import(&self) -> Option<&I> {
        match self {
            Node::Quote(import) => Some(import),
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
            Node::Subst1(_, _) | Node::BWk(_, _) | Node::Close1(_) | Node::Quote(_)
        )
    }
}

impl<C> Node<C, Bv, Bv, Bv> {
    pub fn max_bvi(&self) -> Bv {
        match self {
            Node::Fv(_) => Bv::new(0),
            &Node::Bv(i) => i.succ(),
            Node::U(_) => Bv::new(0),
            Node::Empty => Bv::new(0),
            Node::Unit => Bv::new(0),
            Node::Null => Bv::new(0),
            &Node::Eqn([a, b]) => a.max(b),
            &Node::Pi([a, b]) => a.max(b.pred()),
            &Node::Sigma([a, b]) => a.max(b.pred()),
            &Node::Abs([a, b]) => a.max(b.pred()),
            &Node::App([a, b]) => a.max(b),
            &Node::Pair([a, b]) => a.max(b),
            &Node::Fst([a]) => a,
            &Node::Snd([a]) => a,
            &Node::Ite([a, b, c]) => a.max(b.pred()).max(c.pred()),
            &Node::Trunc([a]) => a,
            &Node::Choose([a, b]) => a.max(b.pred()),
            Node::Nats => Bv::new(0),
            Node::N64(_) => Bv::new(0),
            &Node::Succ([a]) => a,
            &Node::Natrec([a, b, c]) => a.max(b.pred()).max(c.pred()),
            &Node::HasTy([a, b]) => a.max(b),
            Node::Invalid => Bv::new(0),
            &Node::Id(_, [a]) => a,
            &Node::Subst1(_, [a, b]) => a.max(b.pred()),
            &Node::BWk(shift, [a]) => shift.bvi(a),
            Node::Close1(close) => close.bvi(),
            &Node::Quote(a) => a,
        }
    }
}

impl<C, LT, RT, LI, RI> Node<C, (LT, RT), (LI, RI)>
where
    C: Copy,
{
    /// Convert a node of pairs into a pair of nodes
    pub fn into_pair(self) -> (Node<C, LT, LI>, Node<C, RT, RI>) {
        match self {
            Node::Fv(x) => (Node::Fv(x), Node::Fv(x)),
            Node::Bv(i) => (Node::Bv(i), Node::Bv(i)),
            Node::U(level) => (Node::U(level), Node::U(level)),
            Node::Empty => (Node::Empty, Node::Empty),
            Node::Unit => (Node::Unit, Node::Unit),
            Node::Null => (Node::Null, Node::Null),
            Node::Eqn([a, b]) => (Node::Eqn([a.0, b.0]), Node::Eqn([a.1, b.1])),
            Node::Pi([a, b]) => (Node::Pi([a.0, b.0]), Node::Pi([a.1, b.1])),
            Node::Sigma([a, b]) => (Node::Sigma([a.0, b.0]), Node::Sigma([a.1, b.1])),
            Node::Abs([a, b]) => (Node::Abs([a.0, b.0]), Node::Abs([a.1, b.1])),
            Node::App([a, b]) => (Node::App([a.0, b.0]), Node::App([a.1, b.1])),
            Node::Pair([a, b]) => (Node::Pair([a.0, b.0]), Node::Pair([a.1, b.1])),
            Node::Fst([a]) => (Node::Fst([a.0]), Node::Fst([a.1])),
            Node::Snd([a]) => (Node::Snd([a.0]), Node::Snd([a.1])),
            Node::Ite([a, b, c]) => (Node::Ite([a.0, b.0, c.0]), Node::Ite([a.1, b.1, c.1])),
            Node::Trunc([a]) => (Node::Trunc([a.0]), Node::Trunc([a.1])),
            Node::Choose([a, b]) => (Node::Choose([a.0, b.0]), Node::Choose([a.1, b.1])),
            Node::Nats => (Node::Nats, Node::Nats),
            Node::N64(n) => (Node::N64(n), Node::N64(n)),
            Node::Succ([a]) => (Node::Succ([a.0]), Node::Succ([a.1])),
            Node::Natrec([a, b, c]) => {
                (Node::Natrec([a.0, b.0, c.0]), Node::Natrec([a.1, b.1, c.1]))
            }
            Node::HasTy([a, b]) => (Node::HasTy([a.0, b.0]), Node::HasTy([a.1, b.1])),
            Node::Invalid => (Node::Invalid, Node::Invalid),
            Node::Id(n, [a]) => (Node::Id(n, [a.0]), Node::Id(n, [a.1])),
            Node::Subst1(k, [a, b]) => (Node::Subst1(k, [a.0, b.0]), Node::Subst1(k, [a.1, b.1])),
            Node::BWk(k, [a]) => (Node::BWk(k, [a.0]), Node::BWk(k, [a.1])),
            Node::Close1(close) => {
                let (lclose, rclose) = close.into_pair();
                (Node::Close1(lclose), Node::Close1(rclose))
            }
            Node::Quote(import) => (Node::Quote(import.0), Node::Quote(import.1)),
        }
    }
}
