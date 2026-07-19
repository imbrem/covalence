//! Two S-expression realizations of the natural-number datatype.
//!
//! Both use the same constructor/observation API. [`RawSExprNat`] admits
//! arbitrary S-expressions and therefore has no induction capability.
//! [`RefinedSExprNat`] pairs the same representation with an externally
//! supplied logic term and membership theorem. Induction is available only
//! after attaching [`TheoryNatInduction`].
//!
//! The raw carrier is convenient for interchange and permits cheap structural
//! inspection, but every consumer must handle junk. The refined carrier costs
//! one membership theorem per constructed node and retains a structural
//! derivation, but makes observation total and permits membership-relativized
//! induction. Neither representation claims that every S-expression is a Nat,
//! and this module introduces no theorem constructors.

use covalence_inductive::{
    ArgSort, CtorSpec, IndResult, InductiveError, InductiveSpec, InductiveTheory, Logic, LogicOps,
};

use crate::FreeSExpr;

/// Constructor positions in [`nat_spec`].
pub mod constructor {
    /// `zero`.
    pub const ZERO: usize = 0;
    /// `succ`.
    pub const SUCC: usize = 1;
}

/// The bounded inductive family exercised by these representations.
pub fn nat_spec<X>() -> InductiveSpec<X> {
    InductiveSpec::new(
        "sexpr-nat",
        vec![
            CtorSpec::nullary("zero"),
            CtorSpec::new("succ", [("predecessor", ArgSort::Rec)]),
        ],
    )
}

/// Tags used by the raw S-expression encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NatSymbol {
    /// The nullary constructor.
    Zero,
    /// The head tag of a successor pair.
    Succ,
}

/// One valid observation of a Nat representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NatLayer<N> {
    /// Zero.
    Zero,
    /// A successor and its predecessor.
    Succ(N),
}

/// Shared high-level construction and partial-observation API.
///
/// `view` is partial because a representation may intentionally have junk.
/// Refined implementations document when it is total for values they create.
pub trait NatRepresentation {
    /// Represented Nat values.
    type Value: Clone;
    /// Evidence required when constructing each member.
    type Evidence;

    /// Construct zero with the backend's evidence.
    fn zero(&self, evidence: Self::Evidence) -> Self::Value;
    /// Construct a successor with evidence for the result.
    fn succ(&self, predecessor: Self::Value, evidence: Self::Evidence) -> Self::Value;
    /// Observe a valid constructor layer, or `None` for representation junk.
    fn view(&self, value: &Self::Value) -> Option<NatLayer<Self::Value>>;
}

/// An unrefined S-expression carrier.
///
/// Its public constructor intentionally permits `Nil`, malformed successor
/// pairs, and other junk. Consequently this type implements
/// [`NatRepresentation`] but no induction capability.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSExprNat(pub FreeSExpr<NatSymbol>);

/// Raw Nat construction and observation.
#[derive(Clone, Copy, Debug, Default)]
pub struct RawNat;

impl NatRepresentation for RawNat {
    type Value = RawSExprNat;
    type Evidence = ();

    fn zero(&self, (): ()) -> Self::Value {
        RawSExprNat(FreeSExpr::Atom(NatSymbol::Zero))
    }

    fn succ(&self, predecessor: Self::Value, (): ()) -> Self::Value {
        RawSExprNat(FreeSExpr::Cons(
            Box::new(FreeSExpr::Atom(NatSymbol::Succ)),
            Box::new(predecessor.0),
        ))
    }

    fn view(&self, value: &Self::Value) -> Option<NatLayer<Self::Value>> {
        match &value.0 {
            FreeSExpr::Atom(NatSymbol::Zero) => Some(NatLayer::Zero),
            FreeSExpr::Cons(head, predecessor) if **head == FreeSExpr::Atom(NatSymbol::Succ) => {
                Some(NatLayer::Succ(RawSExprNat((**predecessor).clone())))
            }
            FreeSExpr::Atom(NatSymbol::Succ) | FreeSExpr::Nil | FreeSExpr::Cons(_, _) => None,
        }
    }
}

/// Backend-supplied evidence that an encoded term belongs to the Nat subset.
///
/// Constructing this value does not create a theorem; callers must already
/// possess the logic's unforgeable theorem token.
#[derive(Debug)]
pub struct NatMembership<L: Logic> {
    /// Logic-level term represented by the S-expression.
    pub term: L::Term,
    /// Proof of membership in the Nat subset.
    pub theorem: L::Thm,
}

impl<L: Logic> Clone for NatMembership<L> {
    fn clone(&self) -> Self {
        Self {
            term: self.term.clone(),
            theorem: self.theorem.clone(),
        }
    }
}

/// The S-expression carrier refined by explicit membership evidence.
#[derive(Debug)]
pub struct RefinedSExprNat<L: Logic> {
    raw: RawSExprNat,
    membership: NatMembership<L>,
    shape: RefinedNatShape<L>,
}

#[derive(Debug)]
enum RefinedNatShape<L: Logic> {
    Zero,
    Succ(Box<RefinedSExprNat<L>>),
}

impl<L: Logic> Clone for RefinedNatShape<L> {
    fn clone(&self) -> Self {
        match self {
            Self::Zero => Self::Zero,
            Self::Succ(predecessor) => Self::Succ(Box::new((**predecessor).clone())),
        }
    }
}

impl<L: Logic> Clone for RefinedSExprNat<L> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
            membership: self.membership.clone(),
            shape: self.shape.clone(),
        }
    }
}

impl<L: Logic> RefinedSExprNat<L> {
    /// Underlying unrefined representation.
    pub fn raw(&self) -> &RawSExprNat {
        &self.raw
    }

    /// Logic term and membership theorem carried by this refined value.
    pub fn membership(&self) -> &NatMembership<L> {
        &self.membership
    }
}

/// Refined Nat construction and observation.
#[derive(Clone, Copy, Debug, Default)]
pub struct RefinedNat<L: Logic>(core::marker::PhantomData<fn() -> L>);

impl<L: Logic> RefinedNat<L> {
    /// Construct the capability.
    pub const fn new() -> Self {
        Self(core::marker::PhantomData)
    }
}

impl<L: Logic> NatRepresentation for RefinedNat<L> {
    type Value = RefinedSExprNat<L>;
    type Evidence = NatMembership<L>;

    fn zero(&self, membership: Self::Evidence) -> Self::Value {
        RefinedSExprNat {
            raw: RawNat.zero(()),
            membership,
            shape: RefinedNatShape::Zero,
        }
    }

    fn succ(&self, predecessor: Self::Value, membership: Self::Evidence) -> Self::Value {
        RefinedSExprNat {
            raw: RawNat.succ(predecessor.raw.clone(), ()),
            membership,
            shape: RefinedNatShape::Succ(Box::new(predecessor)),
        }
    }

    fn view(&self, value: &Self::Value) -> Option<NatLayer<Self::Value>> {
        Some(match &value.shape {
            RefinedNatShape::Zero => NatLayer::Zero,
            RefinedNatShape::Succ(predecessor) => NatLayer::Succ((**predecessor).clone()),
        })
    }
}

/// Induction capability for refined Nat values.
///
/// Raw values cannot implement this trait because they carry neither a logic
/// term nor membership evidence.
pub trait NatInduction<L: Logic>: NatRepresentation<Value = RefinedSExprNat<L>> {
    /// Prove `motive value` from the two constructor cases.
    fn induct(
        &self,
        value: &RefinedSExprNat<L>,
        motive: &L::Term,
        zero_case: L::Thm,
        succ_case: L::Thm,
    ) -> IndResult<L::Thm, L>;
}

/// An induction adapter backed by an existing membership-relativized theory.
///
/// Capability absence is static: [`RawNat`] does not implement
/// [`NatInduction`].
///
/// ```compile_fail
/// use covalence_sexpr_api::{NatInduction, RawNat};
///
/// fn require_induction<L: covalence_inductive::Logic>(
///     value: &impl NatInduction<L>,
/// ) {
/// }
///
/// require_induction::<SomeLogic>(&RawNat);
/// # struct SomeLogic;
/// # impl covalence_inductive::Logic for SomeLogic {
/// #   type Type = (); type Term = (); type Thm = ();
/// #   type Error = core::convert::Infallible;
/// # }
/// ```
pub struct TheoryNatInduction<'a, L: LogicOps> {
    logic: &'a L,
    theory: &'a InductiveTheory<L>,
}

impl<'a, L: LogicOps> TheoryNatInduction<'a, L> {
    /// Attach only if the theory realizes the canonical Nat specification.
    pub fn try_new(
        logic: &'a L,
        theory: &'a InductiveTheory<L>,
    ) -> Result<Self, InductiveError<L::Error>> {
        if theory.spec == nat_spec() {
            Ok(Self { logic, theory })
        } else {
            Err(InductiveError::SpecMismatch(
                "expected the canonical S-expression Nat specification".into(),
            ))
        }
    }
}

impl<L: LogicOps> NatRepresentation for TheoryNatInduction<'_, L> {
    type Value = RefinedSExprNat<L>;
    type Evidence = NatMembership<L>;

    fn zero(&self, evidence: Self::Evidence) -> Self::Value {
        RefinedNat::new().zero(evidence)
    }

    fn succ(&self, predecessor: Self::Value, evidence: Self::Evidence) -> Self::Value {
        RefinedNat::new().succ(predecessor, evidence)
    }

    fn view(&self, value: &Self::Value) -> Option<NatLayer<Self::Value>> {
        RefinedNat::new().view(value)
    }
}

impl<L: LogicOps> NatInduction<L> for TheoryNatInduction<'_, L> {
    fn induct(
        &self,
        value: &RefinedSExprNat<L>,
        motive: &L::Term,
        zero_case: L::Thm,
        succ_case: L::Thm,
    ) -> IndResult<L::Thm, L> {
        let guarded = self
            .theory
            .facts
            .induct(motive, vec![zero_case, succ_case])?;
        let at_value = self
            .logic
            .all_elim(guarded, value.membership.term.clone())?;
        Ok(self
            .logic
            .imp_elim(at_value, value.membership.theorem.clone())?)
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;

    #[derive(Clone, Copy, Debug)]
    struct TestLogic;

    impl Logic for TestLogic {
        type Type = String;
        type Term = String;
        type Thm = String;
        type Error = Infallible;
    }

    fn check_zero_succ<R: NatRepresentation>(
        representation: &R,
        zero_evidence: R::Evidence,
        succ_evidence: R::Evidence,
    ) {
        let zero = representation.zero(zero_evidence);
        assert!(matches!(representation.view(&zero), Some(NatLayer::Zero)));
        let one = representation.succ(zero, succ_evidence);
        assert!(matches!(representation.view(&one), Some(NatLayer::Succ(_))));
    }

    fn evidence(term: &str) -> NatMembership<TestLogic> {
        NatMembership {
            term: term.into(),
            theorem: format!("member({term})"),
        }
    }

    #[test]
    fn raw_and_refined_representations_share_constructor_conformance() {
        check_zero_succ(&RawNat, (), ());
        check_zero_succ(
            &RefinedNat::<TestLogic>::new(),
            evidence("zero"),
            evidence("succ zero"),
        );
    }

    #[test]
    fn raw_representation_honestly_exposes_junk() {
        assert_eq!(RawNat.view(&RawSExprNat(FreeSExpr::Nil)), None);
        assert_eq!(
            RawNat.view(&RawSExprNat(FreeSExpr::Atom(NatSymbol::Succ))),
            None
        );
    }

    #[test]
    fn refined_representation_retains_external_membership_evidence() {
        let api = RefinedNat::<TestLogic>::new();
        let zero = api.zero(evidence("zero"));
        let one = api.succ(zero, evidence("succ zero"));
        assert_eq!(one.membership().term, "succ zero");
        assert_eq!(one.membership().theorem, "member(succ zero)");
        assert!(matches!(api.view(&one), Some(NatLayer::Succ(_))));
        assert!(RawNat.view(one.raw()).is_some());
    }

    #[test]
    fn bounded_nat_spec_matches_the_encoding() {
        let spec = nat_spec::<()>();
        spec.validate().unwrap();
        assert_eq!(spec.ctors[constructor::ZERO].arity(), 0);
        assert_eq!(
            spec.ctors[constructor::SUCC]
                .rec_positions()
                .collect::<Vec<_>>(),
            vec![0]
        );
    }
}
