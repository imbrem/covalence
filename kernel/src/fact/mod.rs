/*!
Facts which can be checked in the datastore
*/
use crate::api::store::*;
use crate::data::term::Val;

use bitflags::bitflags;

/// Logical composition for fact types
mod logic;

/// A fact which can be checked using a fact dataset
pub trait Fact<R: ?Sized> {
    /// Check whether this goal is true
    fn check(&self, db: &R) -> bool;
}

/// A fact about ("within") a given context
pub trait FactIn<C, R: ?Sized> {
    /// Check this fact in the given context
    fn check_in(&self, ctx: &C, db: &R) -> bool;
}

/// A quantified fact within a given context
pub trait FactUnder<C, Q, R: ?Sized> {
    /// Check this fact under the given quantifier in the given context
    fn check_under(&self, ctx: &C, binder: &Q, db: &R) -> bool;
}

/// A _sequent_: a pair `Γ ⊢ S` of a context and a statement
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Seq<C, S> {
    /// The context for this sequent
    pub ctx: C,
    /// The statement asserted
    pub stmt: S,
}

impl<C, S, R: ?Sized> Fact<R> for Seq<C, S>
where
    S: FactIn<C, R>,
{
    fn check(&self, db: &R) -> bool {
        self.stmt.check_in(&self.ctx, db)
    }
}

/// A quantified statement, of the form `Q . S`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Quantified<Q, S> {
    /// The quantifier for this statement
    pub binder: Q,
    /// The body of this statement
    pub body: S,
}

impl<C, Q, S, R: ?Sized> FactIn<C, R> for Quantified<Q, S>
where
    Q: FactIn<C, R>,
    S: FactUnder<C, Q, R>,
{
    /// Check this quantified statement in the given context
    fn check_in(&self, ctx: &C, db: &R) -> bool {
        self.body.check_under(ctx, &self.binder, db)
    }
}

bitflags! {
    /// A nullary predicate over contexts
    /// ```
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Default, Ord, PartialOrd)]
    pub struct Pred0: u8 {
        /// This context is contradictory
        const IS_CONTR = 0b00000001;
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
    /// # use covalence_kernel::*;
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

/// An atomic formula on terms supported by the kernel
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Atom<T> {
    /// A nullary predicate predicate on contexts
    Pred0(Pred0),
    /// A unary predicate on terms-in-context
    Pred1(Pred1, T),
    /// Two terms are equal
    Eq(T, T),
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

/// A universal quantifier
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Forall<T>(T);

/// A quantified atomic formula
pub type QAtom<T> = Quantified<Option<Forall<T>>, Atom<T>>;

/// An atomic sequent
pub type AtomSeq<C, T> = Seq<C, Atom<T>>;

/// A quantified atomic sequent
pub type QAtomSeq<C, T> = Seq<C, QAtom<T>>;

impl<C, T> QAtomSeq<C, T> {
    pub fn contr(ctx: C) -> QAtomSeq<C, T> {
        Seq {
            ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::Pred0(Pred0::IS_CONTR),
            },
        }
    }
}

/// An equation in a context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Eqn<C, T> {
    pub ctx: C,
    pub lhs: T,
    pub rhs: T,
}

pub type EqnV<C, T> = Eqn<C, Val<C, T>>;

/// A statement of well-formedness
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsWf<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsWfV<C, T> = IsWf<C, Val<C, T>>;

/// A term is a valid type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsTy<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsTyV<C, T> = IsTy<C, Val<C, T>>;

/// A term is an inhabited type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsInhab<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsInhabV<C, T> = IsInhab<C, Val<C, T>>;

/// A term is an empty type
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsEmpty<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsEmptyV<C, T> = IsEmpty<C, Val<C, T>>;

/// A term is a proposition
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsProp<C, T> {
    pub ctx: C,
    pub tm: T,
}

pub type IsPropV<C, T> = IsProp<C, Val<C, T>>;

/// A typing derivation
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTy<C, T> {
    pub ctx: C,
    pub tm: T,
    pub ty: T,
}

pub type HasTyV<C, T> = HasTy<C, Val<C, T>>;

/// A term is a type under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsTyUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub tm: T,
}

pub type IsTyUnderV<C, T> = IsTyUnder<C, Val<C, T>>;

/// A typing derivation under a binder
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct HasTyUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub tm: T,
    pub ty: T,
}

pub type HasTyUnderV<C, T> = HasTyUnder<C, Val<C, T>>;

/// A universally quantified statement of inhabitance
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ForallInhabUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub ty: T,
}

pub type ForallInhabUnderV<C, T> = ForallInhabUnder<C, Val<C, T>>;

/// An existentially quantified statement of inhabitance
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ExistsInhabUnder<C, T> {
    pub ctx: C,
    pub binder: T,
    pub ty: T,
}

pub type ExistsInhabUnderV<C, T> = ExistsInhabUnder<C, Val<C, T>>;

/// A context is a subcontext of another
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct IsSubctx<C> {
    pub lo: C,
    pub hi: C,
}

impl<C, T> From<Eqn<C, T>> for QAtomSeq<C, T> {
    fn from(g: Eqn<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::Eq(g.lhs, g.rhs),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::Eq(g.lhs, g.rhs)),
        }
    }
}

impl<C, T> From<IsWf<C, T>> for QAtomSeq<C, T>
where
    C: Copy,
    T: Copy,
{
    fn from(g: IsWf<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::is_wf(g.tm),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsWf(g.tm)),
        }
    }
}

impl<C, T> From<IsTy<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsTy<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::is_ty(g.tm),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsTy(g.tm)),
        }
    }
}

impl<C, T> From<IsInhab<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsInhab<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::is_inhab(g.tm),
            },
            // binder: Quant::Null,
            // rel: Some(GoalIn::IsInhab(g.tm)),
        }
    }
}

impl<C, T> From<IsEmpty<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsEmpty<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::is_empty(g.tm),
            },
        }
    }
}

impl<C, T: Copy> From<IsProp<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsProp<C, T>) -> Self {
        QAtomSeq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::is_prop(g.tm),
            },
        }
    }
}

impl<C, T> From<HasTy<C, T>> for QAtomSeq<C, T> {
    fn from(g: HasTy<C, T>) -> Self {
        QAtomSeq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: None,
                body: Atom::HasTy(g.tm, g.ty),
            },
        }
    }
}

impl<C, T> From<IsTyUnder<C, T>> for QAtomSeq<C, T> {
    fn from(g: IsTyUnder<C, T>) -> Self {
        QAtomSeq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Some(Forall(g.binder)),
                body: Atom::is_ty(g.tm),
            },
        }
    }
}

impl<C, T> From<HasTyUnder<C, T>> for QAtomSeq<C, T> {
    fn from(g: HasTyUnder<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Some(Forall(g.binder)),
                body: Atom::HasTy(g.tm, g.ty),
            },
        }
    }
}

impl<C, T> From<ForallInhabUnder<C, T>> for QAtomSeq<C, T> {
    fn from(g: ForallInhabUnder<C, T>) -> Self {
        Seq {
            ctx: g.ctx,
            stmt: Quantified {
                binder: Some(Forall(g.binder)),
                body: Atom::is_inhab(g.ty),
            },
        }
    }
}

impl<C, T, R> FactIn<C, R> for Forall<T>
where
    C: Copy,
    T: Copy,
    R: ReadFacts<C, T> + ?Sized,
{
    /// Check this quantifier in the given context
    fn check_in(&self, &ctx: &C, ker: &R) -> bool {
        todo!()
        //ker.is_ty(ctx, self.0)
    }
}

impl<C, T, R> FactIn<C, R> for Atom<T>
where
    C: Copy,
    T: Copy,
    R: ReadTermFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_in(&self, &ctx: &C, ker: &R) -> bool {
        match *self {
            Atom::Eq(lhs, rhs) => ker.eq_in(ctx, lhs, rhs),
            Atom::Pred1(p, tm) => ker.tm_satisfies(ctx, p, tm),
            Atom::HasTy(tm, ty) => ker.has_ty(ctx, tm, ty),
            Atom::Pred0(p) => ker.ctx_satisfies(ctx, p),
        }
    }
}

impl<C, T, R> FactUnder<C, Forall<T>, R> for Atom<T>
where
    C: Copy,
    T: Copy,
    R: ReadTermFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_under(&self, &ctx: &C, &Forall(binder): &Forall<T>, ker: &R) -> bool {
        match *self {
            // Atom::Eq(lhs, rhs) => ker.forall_eq_in(ctx, binder, lhs, rhs),
            // Atom::Pred1(pred, tm) => ker.forall_unary(ctx, binder, pred, tm),
            // Atom::HasTy(tm, ty) => ker.forall_has_ty(ctx, binder, tm, ty),
            Atom::Pred0(pred) => ker.tm_satisfies(ctx, pred.forall(), binder),
            _ => todo!(),
        }
    }
}

impl<C, T, R> FactUnder<C, Option<Forall<T>>, R> for Atom<T>
where
    C: Copy,
    T: Copy,
    R: ReadTermFacts<C, T> + ?Sized,
{
    /// Check whether this goal is true
    fn check_under(&self, &ctx: &C, binder: &Option<Forall<T>>, ker: &R) -> bool {
        match binder {
            None => self.check_in(&ctx, ker),
            Some(binder) => self.check_under(&ctx, binder, ker),
        }
    }
}
