use bitflags::bitflags;

use super::*;
use crate::{data::term::Node, store::Ctx};

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
        const CONTR          = 0b00001000;
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
    /// For the Π-predicates `P ∈ {SCOPED, WF, TY, INHAB, PROP, TRUE}`, i.e. `P ≤
    /// TRUE`, we have that
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
    /// For the Σ-predicates `P ∈ {SCOPED, WF, TY, EMP}`, i.e. `P <= EMP`, we
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
    /// # use covalence_kernel::formula::pred::*;
    /// assert!(WF.contains(SCOPED));
    /// assert_ne!(SCOPED, WF);
    /// assert!(TY.contains(WF));
    /// assert_ne!(WF, TY);
    /// assert!(PROP.contains(TY));
    /// assert_ne!(TY, PROP);
    /// assert!(INHAB.contains(TY));
    /// assert_ne!(TY, INHAB);
    /// assert!(EMP.contains(TY));
    /// assert_ne!(TY, EMP);
    /// assert!(!PROP.contains(INHAB));
    /// assert!(!INHAB.contains(PROP));
    /// assert!(!PROP.contains(EMP));
    /// assert!(!EMP.contains(PROP));
    /// assert!(!INHAB.contains(EMP));
    /// assert!(!EMP.contains(INHAB));
    /// assert_eq!(PROP | INHAB, TT);
    /// assert_eq!(PROP | EMP, FF);
    /// assert!(UNIV.contains(INHAB));
    /// assert_ne!(INHAB, UNIV);
    /// assert!(!UNIV.contains(PROP));
    /// assert!(!UNIV.contains(EMP));
    /// assert_eq!(CONTR, TT | FF | UNIV);
    /// ```
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Default, Ord, PartialOrd)]
    pub struct Pred1: u8 {
        /// This term is well-scoped
        const SCOPED = 0b00000001;
        /// This term is well-formed
        const WF     = 0b00000011;
        /// This term is a well-formed type
        const TY     = 0b00000111;
        /// This term is a well-formed proposition
        const PROP   = 0b00001111;
        /// This term is an inhabited type
        const INHAB  = 0b00010111;
        /// This term is an empty type
        const EMP    = 0b00100111;
        /// This term is equal to the true proposition
        const TT     = 0b00011111;
        /// This term is equal to the false proposition
        const FF     = 0b00101111;
        /// This term is a valid typing universe
        const UNIV   = 0b01010111;
        /// A well-formed term under an empty context
        const CONTR  = 0b01111111;

        /// The bit indicating scoped-ness
        const SCOPED_BIT    = 1 << 0;
        /// The bit indicating well-formedness
        const WF_BIT        = 1 << 1;
        /// The bit indicating typehood
        const TY_BIT        = 1 << 2;
        /// The bit indicating propositionality
        const PROP_BIT      = 1 << 3;
        /// The bit indicating inhabitance
        const INHAB_BIT     = 1 << 4;
        /// The bit indicating emptiness
        const EMPTY_BIT     = 1 << 5;
        /// The bit indicating universes
        const UNIV_BIT      = 1 << 6;
    }
}

impl Pred0 {
    /// Convert this nullary predicate into a unary predicate on a binder
    pub const fn forall(self) -> Pred1 {
        if self.contains(Pred0::CONTR) {
            Pred1::EMP
        } else {
            Pred1::empty()
        }
    }
}

impl Pred1 {
    /// Check whether these flags imply a contradiction
    pub const fn is_contr(self) -> bool {
        self.contains(INHAB.union(EMP)) //|| self.contains(UNIV.union(PROP))
    }

    /// Convert a bitset to a valid term
    pub const fn to_valid(self) -> Pred1 {
        let mut result = Pred1::empty();
        if self.contains(Pred1::WF_BIT) {
            result = result.union(Pred1::WF);
        }
        if self.contains(Pred1::TY_BIT) {
            result = result.union(Pred1::TY);
        }
        if self.contains(Pred1::PROP_BIT) {
            result = result.union(Pred1::PROP);
        }
        if self.contains(Pred1::INHAB_BIT) {
            result = result.union(Pred1::INHAB);
        }
        if self.contains(Pred1::EMPTY_BIT) {
            result = result.union(Pred1::EMP);
        }
        if self.contains(Pred1::UNIV_BIT) {
            result = result.union(Pred1::UNIV);
        }
        result
    }

    /// Deduce the flags implied by a given bitet
    pub const fn deduce(self) -> Pred1 {
        if self.is_contr() {
            self.union(Pred1::CONTR)
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
pub const SCOPED: Pred1 = Pred1::SCOPED;

/// A term is well-formed
pub const WF: Pred1 = Pred1::WF;

/// A term is a valid type
pub const TY: Pred1 = Pred1::TY;

/// A term is a proposition
pub const PROP: Pred1 = Pred1::PROP;

/// A term is an inhabited type
pub const INHAB: Pred1 = Pred1::INHAB;

/// A term is an empty type
pub const EMP: Pred1 = Pred1::EMP;

/// A term is equal to the true proposition
pub const TT: Pred1 = Pred1::TT;

/// A term is equal to the false proposition
pub const FF: Pred1 = Pred1::FF;

/// A term is a valid typing universe
pub const UNIV: Pred1 = Pred1::UNIV;

/// A term indicates a contradiction
pub const CONTR: Pred1 = Pred1::CONTR;

impl<C, T> Node<C, T> {
    /// Infer predicates for this term in the given context
    pub fn static_flags(&self) -> Pred1 {
        match self {
            Node::U(_) => Pred1::UNIV,
            Node::Unit => Pred1::TT,
            Node::Empty => Pred1::FF,
            Node::Nats => Pred1::INHAB,
            Node::N64(_) | Node::Null => Pred1::WF,
            _ => Pred1::default(),
        }
    }
}

mod into_pred1_sealed {
    pub trait UnaryPredSealed {}
}

pub(crate) use into_pred1_sealed::UnaryPredSealed;

pub trait IntoPred1: UnaryPredSealed {
    /// Convert this into a unary predicate
    fn into_pred1(self) -> Pred1;
}

impl UnaryPredSealed for Pred1 {}

impl IntoPred1 for Pred1 {
    fn into_pred1(self) -> Pred1 {
        self
    }
}

impl UnaryPredSealed for () {}

impl IntoPred1 for () {
    fn into_pred1(self) -> Pred1 {
        Pred1::default()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Scoped;

impl UnaryPredSealed for Scoped {}

impl IntoPred1 for Scoped {
    fn into_pred1(self) -> Pred1 {
        SCOPED
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Wf;

impl UnaryPredSealed for Wf {}

impl IntoPred1 for Wf {
    fn into_pred1(self) -> Pred1 {
        WF
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Ty;

impl UnaryPredSealed for Ty {}

impl IntoPred1 for Ty {
    fn into_pred1(self) -> Pred1 {
        TY
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Prop;

impl UnaryPredSealed for Prop {}

impl IntoPred1 for Prop {
    fn into_pred1(self) -> Pred1 {
        PROP
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Inhab;

impl UnaryPredSealed for Inhab {}

impl IntoPred1 for Inhab {
    fn into_pred1(self) -> Pred1 {
        INHAB
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Emp;

impl UnaryPredSealed for Emp {}

impl IntoPred1 for Emp {
    fn into_pred1(self) -> Pred1 {
        EMP
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Tt;

impl UnaryPredSealed for Tt {}

impl IntoPred1 for Tt {
    fn into_pred1(self) -> Pred1 {
        TT
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Ff;

impl UnaryPredSealed for Ff {}

impl IntoPred1 for Ff {
    fn into_pred1(self) -> Pred1 {
        FF
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Univ;

impl UnaryPredSealed for Univ {}

impl IntoPred1 for Univ {
    fn into_pred1(self) -> Pred1 {
        UNIV
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct Contr;

impl UnaryPredSealed for Contr {}

impl IntoPred1 for Contr {
    fn into_pred1(self) -> Pred1 {
        CONTR
    }
}

/// A unary predicate holds on a term-in-context
pub struct Is<P, T>(pub P, pub T);

// impl<D, C, P, T> CheckFormula<C, Is<P, T>> for D
// where
//     P: IntoPred1 + Copy,
//     T: Copy,
//     D: CheckFormula<C, Is<Pred1, T>>,
// {
//     fn check_in(&self, ctx: C, fact: &Is<P, T>) -> bool {
//         self.check_in(ctx, &Is(fact.0.into_pred1(), fact.1))
//     }
// }

/// A term is well-formed
pub type IsWf<T> = Is<Wf, T>;

/// A term is a type
pub type IsTy<T> = Is<Ty, T>;

/// A term is a proposition
pub type IsProp<T> = Is<Prop, T>;

/// A term is an inhabited type
pub type IsInhab<T> = Is<Inhab, T>;

/// A term is an empty type
pub type IsEmpty<T> = Is<Emp, T>;

/// A term is the true proposition
pub type IsTrue<T> = Is<Tt, T>;

/// A term is the false proposition
pub type IsFalse<T> = Is<Ff, T>;

impl<D, C, P, T> IffIn<C, Is<Pred1, T>, D> for Is<P, T>
where
    C: Ctx<D>,
    P: IntoPred1 + Copy,
{
    fn iff_in(self, _ctx: &C) -> Is<Pred1, T> {
        Is(self.0.into_pred1(), self.1)
    }
}

impl<D, C, P, T> TryIffIn<C, Is<P, T>, D> for Is<Pred1, T>
where
    C: Ctx<D>,
    P: IntoPred1 + Copy + Default,
{
    fn try_iff_in(self, _ctx: &C) -> Result<Is<P, T>, Self> {
        if self.0.contains(P::default().into_pred1()) {
            Ok(Is(P::default(), self.1))
        } else {
            Err(self)
        }
    }
}
