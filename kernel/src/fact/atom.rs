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
    pub const fn is_emp(tm: T) -> Self {
        Atom::Pred1(IS_EMP, tm)
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

/// An atomic sequent
pub type AtomSeq<C, T> = Seq<C, Atom<T>>;