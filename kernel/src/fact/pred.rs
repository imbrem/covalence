use bitflags::bitflags;

use super::*;
use crate::data::term::Node;

bitflags! {
    /// A nullary predicate over contexts
    /// ```
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Default, Ord, PartialOrd)]
    pub struct Pred0: u8 {
        /// This context has sealed assumptions
        const ASSUME_SEALED     = 0b00000001;
        /// This context has sealed parents
        const PARENTS_SEALED    = 0b00000010;
        /// This context is locally sealed
        const LOCAL_SEALED      = 0b00000011;
        /// This context has sealed extensions
        const EXTS_SEALED       = 0b00000110;
        /// This context is globally sealed
        const GLOBAL_SEALED     = 0b00000111;
        /// This context is contradictory
        const IS_CONTR          = 0b00001000;
        /// This context is locally inhabited
        const LOCAL_INHAB       = 0b00010001;
        /// This context's extensions are inhabited
        const EXTS_INHAB        = 0b00100110;
        /// This context is globally inhabited
        const GLOBAL_INHAB      = 0b00110111;
    }

    /// A unary predicate on terms-in-context
    ///
    /// We introduce the Π-subgroup and Σ-subgroups of predicates as follows:
    ///
    /// For the Π-predicates `P ∈ {IS_SCOPED, IS_WF, IS_TY, IS_INHAB, IS_PROP, IS_TRUE}`, i.e. `P ≤
    /// IS_TRUE`, we have that
    /// ```text
    /// Γ ⊢ P(Π A . B)
    /// ===
    /// ∀x . Γ, x : A ⊢ P B
    /// ```
    /// and
    /// ```text
    /// ∀x . Γ, x : A ⊢ P B
    /// ===
    /// Γ ⊢ P(Π A . B)
    /// ```
    ///
    /// For the Σ-predicates `P ∈ {IS_SCOPED, IS_WF, IS_TY, IS_EMPTY}`, i.e. `P <= IS_EMPTY`, we
    /// have that
    /// ```text
    /// Γ ⊢ P(Σ A . B)
    /// ===
    /// ∀x . Γ, x : A ⊢ P B
    /// ```
    /// and
    /// ```text
    /// ∀x . Γ, x : A ⊢ P B
    /// ===
    /// Γ ⊢ P(Σ A . B)
    /// ```
    ///
    /// We note the following relationships:
    /// ```rust
    /// # use covalence_kernel::fact::pred::*;
    /// assert!(IS_WF.contains(IS_SCOPED));
    /// assert_ne!(IS_SCOPED, IS_WF);
    /// assert!(IS_TY.contains(IS_WF));
    /// assert_ne!(IS_WF, IS_TY);
    /// assert!(IS_PROP.contains(IS_TY));
    /// assert_ne!(IS_TY, IS_PROP);
    /// assert!(IS_INHAB.contains(IS_TY));
    /// assert_ne!(IS_TY, IS_INHAB);
    /// assert!(IS_EMPTY.contains(IS_TY));
    /// assert_ne!(IS_TY, IS_EMPTY);
    /// assert!(!IS_PROP.contains(IS_INHAB));
    /// assert!(!IS_INHAB.contains(IS_PROP));
    /// assert!(!IS_PROP.contains(IS_EMPTY));
    /// assert!(!IS_EMPTY.contains(IS_PROP));
    /// assert!(!IS_INHAB.contains(IS_EMPTY));
    /// assert!(!IS_EMPTY.contains(IS_INHAB));
    /// assert_eq!(IS_PROP | IS_INHAB, IS_TT);
    /// assert_eq!(IS_PROP | IS_EMPTY, IS_FF);
    /// assert!(IS_UNIV.contains(IS_INHAB));
    /// assert_ne!(IS_INHAB, IS_UNIV);
    /// assert!(!IS_UNIV.contains(IS_PROP));
    /// assert!(!IS_UNIV.contains(IS_EMPTY));
    /// assert_eq!(IS_CONTR, IS_TT | IS_FF | IS_UNIV);
    /// ```
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Default, Ord, PartialOrd)]
    pub struct Pred1: u8 {
        /// This term is well-scoped
        const IS_SCOPED = 0b00000001;
        /// This term is well-formed
        const IS_WF     = 0b00000011;
        /// This term is a well-formed type
        const IS_TY     = 0b00000111;
        /// This term is a well-formed proposition
        const IS_PROP   = 0b00001111;
        /// This term is an inhabited type
        const IS_INHAB  = 0b00010111;
        /// This term is an empty type
        const IS_EMPTY  = 0b00100111;
        /// This term is equal to the true proposition
        const IS_TT     = 0b00011111;
        /// This term is equal to the false proposition
        const IS_FF     = 0b00101111;
        /// This term is a valid typing universe
        const IS_UNIV   = 0b01010111;
        /// A well-formed term under an empty context
        const IS_CONTR = 0b01111111;

        /// The indicating well-formedness
        const WF_BIT = 1 << 1;
        /// The bit indicating typehood
        const TY_BIT = 1 << 2;
        /// The bit indicating propositionality
        const PROP_BIT = 1 << 3;
        /// The bit indicating inhabitance
        const INHAB_BIT = 1 << 4;
        /// The bit indicating emptiness
        const EMPTY_BIT = 1 << 5;
        /// The bit indicating universes
        const UNIV_BIT = 1 << 6;
    }
}

impl Pred0 {
    /// Convert this nullary predicate into a unary predicate on a binder
    pub const fn forall(self) -> Pred1 {
        if self.contains(Pred0::IS_CONTR) {
            Pred1::IS_EMPTY
        } else {
            Pred1::empty()
        }
    }
}

impl Pred1 {
    /// Check whether these flags imply a contradiction
    pub const fn is_contr(self) -> bool {
        self.contains(IS_INHAB.union(IS_EMPTY)) //|| self.contains(IS_UNIV.union(IS_PROP))
    }

    /// Convert a bitset to a valid term
    pub const fn to_valid(self) -> Pred1 {
        let mut result = Pred1::empty();
        if self.contains(Pred1::WF_BIT) {
            result = result.union(Pred1::IS_WF);
        }
        if self.contains(Pred1::TY_BIT) {
            result = result.union(Pred1::IS_TY);
        }
        if self.contains(Pred1::PROP_BIT) {
            result = result.union(Pred1::IS_PROP);
        }
        if self.contains(Pred1::INHAB_BIT) {
            result = result.union(Pred1::IS_INHAB);
        }
        if self.contains(Pred1::EMPTY_BIT) {
            result = result.union(Pred1::IS_EMPTY);
        }
        if self.contains(Pred1::UNIV_BIT) {
            result = result.union(Pred1::IS_UNIV);
        }
        result
    }

    /// Deduce the flags implied by a given bitet
    pub const fn deduce(self) -> Pred1 {
        if self.is_contr() {
            self.union(Pred1::IS_CONTR)
        } else {
            self
        }
    }

    /// Check whether a bitset is valid
    pub const fn is_valid(self) -> bool {
        self.symmetric_difference(self.to_valid()).is_empty()
    }
}

/// A term is well-scoped
pub const IS_SCOPED: Pred1 = Pred1::IS_SCOPED;

/// A term is well-formed
pub const IS_WF: Pred1 = Pred1::IS_WF;

/// A term is a valid type
pub const IS_TY: Pred1 = Pred1::IS_TY;

/// A term is a proposition
pub const IS_PROP: Pred1 = Pred1::IS_PROP;

/// A term is an inhabited type
pub const IS_INHAB: Pred1 = Pred1::IS_INHAB;

/// A term is an empty type
pub const IS_EMPTY: Pred1 = Pred1::IS_EMPTY;

/// A term is equal to the true proposition
pub const IS_TT: Pred1 = Pred1::IS_TT;

/// A term is equal to the false proposition
pub const IS_FF: Pred1 = Pred1::IS_FF;

/// A term is a valid typing universe
pub const IS_UNIV: Pred1 = Pred1::IS_UNIV;

/// A term indicates a contradiction
pub const IS_CONTR: Pred1 = Pred1::IS_CONTR;

impl<C, T> Node<C, T> {
    /// Infer predicates for this term in the given context
    pub fn static_flags(&self) -> Pred1 {
        match self {
            Node::U(_) => Pred1::IS_UNIV,
            Node::Unit => Pred1::IS_TT,
            Node::Empty => Pred1::IS_FF,
            Node::Nats => Pred1::IS_INHAB,
            Node::N64(_) | Node::Null => Pred1::IS_WF,
            _ => Pred1::default(),
        }
    }
}

mod into_pred1_sealed {
    pub trait IntoPred1Sealed {}
}

use into_pred1_sealed::IntoPred1Sealed;

pub trait IntoPred1: IntoPred1Sealed {
    /// Convert this into a unary predicate
    fn into_pred1(self) -> Pred1;
}

impl IntoPred1Sealed for Pred1 {}

impl IntoPred1 for Pred1 {
    fn into_pred1(self) -> Pred1 {
        self
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Wf;

impl IntoPred1Sealed for Wf {}

impl IntoPred1 for Wf {
    fn into_pred1(self) -> Pred1 {
        IS_WF
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Ty;

impl IntoPred1Sealed for Ty {}

impl IntoPred1 for Ty {
    fn into_pred1(self) -> Pred1 {
        IS_TY
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Prop;

impl IntoPred1Sealed for Prop {}

impl IntoPred1 for Prop {
    fn into_pred1(self) -> Pred1 {
        IS_PROP
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Inhab;

impl IntoPred1Sealed for Inhab {}

impl IntoPred1 for Inhab {
    fn into_pred1(self) -> Pred1 {
        IS_INHAB
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Empty;

impl IntoPred1Sealed for Empty {}

impl IntoPred1 for Empty {
    fn into_pred1(self) -> Pred1 {
        IS_EMPTY
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Tt;

impl IntoPred1Sealed for Tt {}

impl IntoPred1 for Tt {
    fn into_pred1(self) -> Pred1 {
        IS_TT
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Ff;

impl IntoPred1Sealed for Ff {}

impl IntoPred1 for Ff {
    fn into_pred1(self) -> Pred1 {
        IS_FF
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Univ;

impl IntoPred1Sealed for Univ {}

impl IntoPred1 for Univ {
    fn into_pred1(self) -> Pred1 {
        IS_UNIV
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Contr;

impl IntoPred1Sealed for Contr {}

impl IntoPred1 for Contr {
    fn into_pred1(self) -> Pred1 {
        IS_CONTR
    }
}

/// A nullary predicate holds for a context
pub type HoldsFor<C> = Seq<C, Pred0>;

/// A unary predicate holds on a term-in-context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Holds<T>(pub Pred1, pub T);

impl<T> Holds<T> {
    pub const fn is_scoped(tm: T) -> Self {
        Holds(IS_SCOPED, tm)
    }

    pub const fn is_wf(tm: T) -> Self {
        Holds(IS_WF, tm)
    }

    pub const fn is_ty(tm: T) -> Self {
        Holds(IS_TY, tm)
    }

    pub const fn is_prop(tm: T) -> Self {
        Holds(IS_PROP, tm)
    }

    pub const fn is_inhab(tm: T) -> Self {
        Holds(IS_INHAB, tm)
    }

    pub const fn is_empty(tm: T) -> Self {
        Holds(IS_EMPTY, tm)
    }

    pub const fn is_true(tm: T) -> Self {
        Holds(IS_TT, tm)
    }

    pub const fn is_false(tm: T) -> Self {
        Holds(IS_FF, tm)
    }

    pub const fn is_univ(tm: T) -> Self {
        Holds(IS_UNIV, tm)
    }

    pub const fn is_contr(tm: T) -> Self {
        Holds(IS_CONTR, tm)
    }
}

/// A unary predicate holds on a term
pub type HoldsIn<C, T> = Seq<C, Holds<T>>;

/// A unary predicate holds on a term-in-context
pub struct Is<P, T>(pub P, pub T);

impl<D, C, P, T> CheckFactIn<C, Is<P, T>> for D
where
    P: IntoPred1 + Copy,
    T: Copy,
    D: CheckFactIn<C, Holds<T>>,
{
    fn check_in(&self, ctx: C, fact: &Is<P, T>) -> bool {
        self.check_in(ctx, &Holds(fact.0.into_pred1(), fact.1))
    }
}

/// A term is well-formed
pub type IsWf<T> = Is<Wf, T>;

/// A term is well-formed in a context
pub type IsWfIn<C, T> = Seq<C, IsWf<T>>;

/// A term is a type
pub type IsTy<T> = Is<Ty, T>;

/// A term is a type in a context
pub type IsTyIn<C, T> = Seq<C, IsTy<T>>;

/// A term is a proposition
pub type IsProp<T> = Is<Prop, T>;

/// A term is a proposition in a context
pub type IsPropIn<C, T> = Seq<C, IsProp<T>>;

/// A term is an inhabited type
pub type IsInhab<T> = Is<Inhab, T>;

/// A term is inhabited in a context
pub type IsInhabIn<C, T> = Seq<C, IsInhab<T>>;

/// A term is an empty type
pub type IsEmpty<T> = Is<Empty, T>;

/// A term is empty in a context
pub type IsEmptyIn<C, T> = Seq<C, IsEmpty<T>>;

/// A term is the true proposition
pub type IsTrue<T> = Is<Tt, T>;

/// A term is the true proposition in a context
pub type IsTrueIn<C, T> = Seq<C, IsTrue<T>>;

/// A term is the false proposition
pub type IsFalse<T> = Is<Ff, T>;

/// A term is the false proposition in a context
pub type IsFalseIn<C, T> = Seq<C, IsFalse<T>>;

impl<P, T> FromIffSealed<Is<P, T>> for Holds<T> where P: IntoPred1 + Copy {}

impl<P, T> FromIff<Is<P, T>> for Holds<T>
where
    P: IntoPred1 + Copy,
{
    fn from_iff(value: Is<P, T>) -> Self {
        Holds(value.0.into_pred1(), value.1)
    }
}
