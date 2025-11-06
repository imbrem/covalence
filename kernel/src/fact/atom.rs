use super::*;

/// An atomic formula on terms supported by the kernel
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Atom<T> {
    /// A nullary predicate on contexts
    Pred0(Pred0),
    /// A unary predicate on terms-in-context
    Pred1(Pred1, T),
    /// An equation
    Eqn(T, T),
    /// A term has a type
    HasTy(T, T),
}

impl<T> Atom<T> {
    /// A term is well-scoped
    pub const fn is_scoped(tm: T) -> Self {
        Atom::Pred1(IS_SCOPED, tm)
    }

    /// A term is well-formed
    pub const fn is_wf(tm: T) -> Self {
        Atom::Pred1(IS_WF, tm)
    }

    /// A term is a valid type
    pub const fn is_ty(tm: T) -> Self {
        Atom::Pred1(IS_TY, tm)
    }

    /// A term is a proposition
    pub const fn is_prop(tm: T) -> Self {
        Atom::Pred1(IS_PROP, tm)
    }

    /// A term is an inhabited type
    pub const fn is_inhab(tm: T) -> Self {
        Atom::Pred1(IS_INHAB, tm)
    }

    /// A term is an empty type
    pub const fn is_empty(tm: T) -> Self {
        Atom::Pred1(IS_EMPTY, tm)
    }

    /// A term is equal to the true proposition
    pub const fn is_true(tm: T) -> Self {
        Atom::Pred1(IS_TT, tm)
    }

    /// A term is equal to the false proposition
    pub const fn is_false(tm: T) -> Self {
        Atom::Pred1(IS_FF, tm)
    }

    /// A term is a valid typing universe
    pub const fn is_univ(tm: T) -> Self {
        Atom::Pred1(IS_UNIV, tm)
    }
}

/// A unary predicate holds on a term-in-context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HoldsIn<T> {
    pub pred: Pred1,
    pub tm: T,
}

impl<T> HoldsIn<T> {
    pub const fn is_scoped(tm: T) -> Self {
        HoldsIn {
            pred: IS_SCOPED,
            tm,
        }
    }

    pub const fn is_wf(tm: T) -> Self {
        HoldsIn { pred: IS_WF, tm }
    }

    pub const fn is_ty(tm: T) -> Self {
        HoldsIn { pred: IS_TY, tm }
    }

    pub const fn is_prop(tm: T) -> Self {
        HoldsIn { pred: IS_PROP, tm }
    }

    pub const fn is_inhab(tm: T) -> Self {
        HoldsIn { pred: IS_INHAB, tm }
    }

    pub const fn is_empty(tm: T) -> Self {
        HoldsIn { pred: IS_EMPTY, tm }
    }

    pub const fn is_true(tm: T) -> Self {
        HoldsIn { pred: IS_TT, tm }
    }

    pub const fn is_false(tm: T) -> Self {
        HoldsIn { pred: IS_FF, tm }
    }

    pub const fn is_univ(tm: T) -> Self {
        HoldsIn { pred: IS_UNIV, tm }
    }

    pub const fn is_contr(tm: T) -> Self {
        HoldsIn { pred: IS_CONTR, tm }
    }
}

/// A unary predicate holds on a term
pub type Holds<C, T> = Seq<C, HoldsIn<T>>;

/// An equation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Eqn<L, R = L>(pub L, pub R);

/// An equation-in-context
pub type EqnIn<C, L, R = L> = Seq<C, Eqn<L, R>>;

impl<C, L, R> EqnIn<C, L, R> {
    /// Construct a new equation-in-context
    pub const fn new(ctx: C, lhs: L, rhs: R) -> Self {
        Seq {
            ctx,
            stmt: Eqn(lhs, rhs),
        }
    }
}

/// A term has the given type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTy<T> {
    pub tm: T,
    pub ty: T,
}

/// A term has the given type in a context
pub type HasTyIn<C, T> = Seq<C, HasTy<T>>;