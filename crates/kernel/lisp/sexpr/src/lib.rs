//! S-expressions as an inductive API.
//!
//! @covalence-api {"id":"A0005","title":"S-expressions","status":"experimental","dependsOn":["A0004"]}
//!
//! The fundamental datatype permits dotted pairs:
//!
//! ```text
//! SExpr(P) = μX. Atom(P) + Nil(1) + Cons(X × X)
//! ```
//!
//! Proper lists are derived values whose cons spine ends in `Nil`. This keeps
//! Lisp/ACL2 carriers honest while allowing surface formats that accept only
//! proper lists to implement a narrower capability.

#![forbid(unsafe_code)]

pub mod inductive;
pub mod nat;

use covalence_inductive::{
    FieldSpec, FixpointIsoFacts, FixpointNoConfusionFacts, FixpointSpec, LeastFixpoint,
    LeastFixpointFacts, Logic, NoConfusionLeastFixpoint, PolynomialSpec, Position, VariantCase,
};

pub use inductive::{
    ConstructorLayer, EncodedAtom, EncodingError, EncodingRequest, InductiveRepresentation,
    Membership, RawArgument, RawEncoding, RawInductive, RefinedArgument, RefinedEncoding,
    RefinedInduction, RefinedInductive, TheoryInduction,
};
pub use nat::{
    NatInduction, NatLayer, NatMembership, NatRepresentation, NatSymbol, RawNat, RawSExprNat,
    RefinedNat, RefinedSExprNat, TheoryNatInduction, nat_spec,
};

/// Constructor positions in the canonical S-expression polynomial.
pub mod constructor {
    pub const ATOM: usize = 0;
    pub const NIL: usize = 1;
    pub const CONS: usize = 2;
}

/// The polynomial specification for S-expressions over payload parameter `P`.
pub fn polynomial<P: Clone>(payload: P) -> PolynomialSpec<P> {
    PolynomialSpec::new(
        "sexpr-f",
        vec![
            VariantCase::new(
                "atom",
                vec![FieldSpec::new("payload", Position::Param(payload))],
            ),
            VariantCase::nullary("nil"),
            VariantCase::new(
                "cons",
                vec![
                    FieldSpec::new("head", Position::Var),
                    FieldSpec::new("tail", Position::Var),
                ],
            ),
        ],
    )
}

/// The least-fixpoint specification for S-expressions.
pub fn fixpoint<P: Clone>(payload: P) -> FixpointSpec<P> {
    FixpointSpec::new("sexpr", polynomial(payload))
}

/// One observation layer `P + 1 + X×X`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SExprF<P, X> {
    Atom(P),
    Nil,
    Cons { head: X, tail: X },
}

impl<P, X> SExprF<P, X> {
    pub fn map<Y>(self, mut f: impl FnMut(X) -> Y) -> SExprF<P, Y> {
        match self {
            Self::Atom(payload) => SExprF::Atom(payload),
            Self::Nil => SExprF::Nil,
            Self::Cons { head, tail } => SExprF::Cons {
                head: f(head),
                tail: f(tail),
            },
        }
    }
}

/// Constructors for an S-expression representation.
pub trait SExprSyntax {
    type Payload;
    type Value: Clone;
    type Error;

    fn atom(&self, payload: Self::Payload) -> Result<Self::Value, Self::Error>;
    fn nil(&self) -> Self::Value;
    fn cons(&self, head: Self::Value, tail: Self::Value) -> Result<Self::Value, Self::Error>;
}

/// One-layer observation/destruction.
pub trait SExprView: SExprSyntax {
    fn view(&self, value: &Self::Value) -> Result<SExprF<Self::Payload, Self::Value>, Self::Error>;
}

/// Proper-list construction and observation as a derived capability.
pub trait ProperList: SExprView {
    fn list(
        &self,
        values: impl IntoIterator<Item = Self::Value>,
    ) -> Result<Self::Value, Self::Error> {
        let values: Vec<_> = values.into_iter().collect();
        let mut result = self.nil();
        for value in values.into_iter().rev() {
            result = self.cons(value, result)?;
        }
        Ok(result)
    }

    /// Return elements exactly when the cons spine terminates in nil.
    fn as_list(&self, value: &Self::Value) -> Result<Option<Vec<Self::Value>>, Self::Error> {
        Ok(match self.list_spine(value)? {
            ListSpine::Proper(values) => Some(values),
            ListSpine::Dotted { .. } => None,
        })
    }

    /// Decompose a finite cons spine, retaining a non-nil dotted tail.
    fn list_spine(&self, value: &Self::Value) -> Result<ListSpine<Self::Value>, Self::Error> {
        let mut values = Vec::new();
        let mut cursor = value.clone();
        loop {
            match self.view(&cursor)? {
                SExprF::Nil => return Ok(ListSpine::Proper(values)),
                SExprF::Atom(_) => {
                    return Ok(ListSpine::Dotted {
                        prefix: values,
                        tail: cursor,
                    });
                }
                SExprF::Cons { head, tail } => {
                    values.push(head);
                    cursor = tail;
                }
            }
        }
    }
}

impl<T: SExprView> ProperList for T {}

/// The finite result of following an S-expression's cons spine.
///
/// This distinguishes proper lists from dotted pairs without losing the
/// dotted tail. It is data, not a proof: proof-producing backends expose
/// proper-list theorems as a capability above [`SExprFixpoint`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ListSpine<V> {
    Proper(Vec<V>),
    Dotted { prefix: Vec<V>, tail: V },
}

/// Constructor-named view of the generic proof-bearing least fixpoint.
///
/// This wrapper adds no axioms. Every theorem and term is delegated to the
/// generic inductive bundle; the fixed constructor positions are checked when
/// the wrapper is constructed.
pub struct SExprFixpoint<L: Logic, P> {
    inner: LeastFixpoint<L, P>,
}

/// Proof rules for the proper-list predicate over an S-expression carrier.
///
/// This trait does not construct theorem values itself: a logic backend owns
/// every returned [`Logic::Thm`]. The exact encoding of predicate application,
/// implication, and quantification remains logic-specific.
pub trait ProperListFacts<L: Logic> {
    /// Form the proposition `proper value`.
    fn holds(&self, proper: &L::Term, value: &L::Term) -> Result<L::Term, L::Error>;

    /// Prove `proper nil`.
    fn nil(&self, proper: &L::Term) -> Result<L::Thm, L::Error>;

    /// From `proper tail`, prove `proper (cons head tail)`.
    fn cons(
        &self,
        proper: &L::Term,
        head: &L::Term,
        tail: &L::Term,
        tail_proper: L::Thm,
    ) -> Result<L::Thm, L::Error>;

    /// Proper-list induction.
    ///
    /// `nil_case` proves the motive for `nil`. `cons_case` proves that the
    /// motive is preserved by adding an arbitrary S-expression head to a
    /// proper tail satisfying the motive. The result proves the motive for
    /// every value satisfying the proper-list predicate.
    fn induction(
        &self,
        proper: &L::Term,
        motive: &L::Term,
        nil_case: L::Thm,
        cons_case: L::Thm,
    ) -> Result<L::Thm, L::Error>;
}

/// An S-expression fixpoint equipped with a proof-bearing proper-list
/// predicate.
///
/// This is an optional capability above [`SExprFixpoint`]. In particular, it
/// neither requires nor implies [`SExprNoConfusion`].
pub struct SExprProperList<L: Logic, P> {
    inner: SExprFixpoint<L, P>,
    predicate: L::Term,
    facts: Box<dyn ProperListFacts<L>>,
}

impl<L: Logic, P> SExprProperList<L, P> {
    /// Attach backend-provided proper-list syntax and proofs.
    pub fn new(
        inner: SExprFixpoint<L, P>,
        predicate: L::Term,
        facts: Box<dyn ProperListFacts<L>>,
    ) -> Self {
        Self {
            inner,
            predicate,
            facts,
        }
    }

    /// The underlying canonical S-expression fixpoint.
    pub fn fixpoint(&self) -> &SExprFixpoint<L, P> {
        &self.inner
    }

    /// The backend term denoting the proper-list predicate.
    pub fn predicate(&self) -> &L::Term {
        &self.predicate
    }

    /// Form `proper value`.
    pub fn holds(&self, value: &L::Term) -> Result<L::Term, L::Error> {
        self.facts.holds(&self.predicate, value)
    }

    /// Prove `proper nil`.
    pub fn nil(&self) -> Result<L::Thm, L::Error> {
        self.facts.nil(&self.predicate)
    }

    /// From `proper tail`, prove `proper (cons head tail)`.
    pub fn cons(
        &self,
        head: &L::Term,
        tail: &L::Term,
        tail_proper: L::Thm,
    ) -> Result<L::Thm, L::Error> {
        self.facts.cons(&self.predicate, head, tail, tail_proper)
    }

    /// Apply proper-list induction.
    pub fn induction(
        &self,
        motive: &L::Term,
        nil_case: L::Thm,
        cons_case: L::Thm,
    ) -> Result<L::Thm, L::Error> {
        self.facts
            .induction(&self.predicate, motive, nil_case, cons_case)
    }

    /// Discard the optional proper-list capability.
    pub fn into_fixpoint(self) -> SExprFixpoint<L, P> {
        self.inner
    }
}

/// A canonical S-expression fixpoint with optional no-confusion evidence.
///
/// This wrapper is a strictly stronger capability than [`SExprFixpoint`].
/// Consumers that need only folds or induction continue to accept the smaller
/// type and impose no no-confusion requirement on their backend.
pub struct SExprNoConfusion<L: Logic, P> {
    inner: SExprFixpoint<L, P>,
    facts: Box<dyn FixpointNoConfusionFacts<L>>,
}

impl<L: Logic, P> SExprNoConfusion<L, P> {
    /// Attach separately proved no-confusion laws to a checked S-expression
    /// fixpoint.
    pub fn from_generic(bundle: NoConfusionLeastFixpoint<L, P>) -> Result<Self, LeastFixpoint<L, P>>
    where
        P: Clone + PartialEq,
    {
        let NoConfusionLeastFixpoint {
            fixpoint,
            no_confusion,
        } = bundle;
        let payload = fixpoint
            .core
            .spec
            .functor
            .variants
            .get(constructor::ATOM)
            .and_then(|case| case.fields.first())
            .and_then(|field| match &field.position {
                Position::Param(payload) => Some(payload.clone()),
                Position::Var => None,
            });
        let Some(payload) = payload else {
            return Err(fixpoint);
        };
        SExprFixpoint::try_new(fixpoint, payload).map(|inner| Self {
            inner,
            facts: no_confusion,
        })
    }

    pub fn fixpoint(&self) -> &SExprFixpoint<L, P> {
        &self.inner
    }

    /// `⊢ (atom left = atom right) ⟹ left = right`.
    pub fn atom_injective(&self, left: &L::Term, right: &L::Term) -> Result<L::Thm, L::Error> {
        self.facts.injective(
            constructor::ATOM,
            0,
            core::slice::from_ref(left),
            core::slice::from_ref(right),
        )
    }

    /// `⊢ (cons lh lt = cons rh rt) ⟹ lh = rh`.
    pub fn cons_head_injective(
        &self,
        left_head: &L::Term,
        left_tail: &L::Term,
        right_head: &L::Term,
        right_tail: &L::Term,
    ) -> Result<L::Thm, L::Error> {
        self.facts.injective(
            constructor::CONS,
            0,
            &[left_head.clone(), left_tail.clone()],
            &[right_head.clone(), right_tail.clone()],
        )
    }

    /// `⊢ (cons lh lt = cons rh rt) ⟹ lt = rt`.
    pub fn cons_tail_injective(
        &self,
        left_head: &L::Term,
        left_tail: &L::Term,
        right_head: &L::Term,
        right_tail: &L::Term,
    ) -> Result<L::Thm, L::Error> {
        self.facts.injective(
            constructor::CONS,
            1,
            &[left_head.clone(), left_tail.clone()],
            &[right_head.clone(), right_tail.clone()],
        )
    }

    /// `⊢ (atom payload = nil) ⟹ F`.
    pub fn atom_not_nil(&self, payload: &L::Term) -> Result<L::Thm, L::Error> {
        self.facts.distinct(
            constructor::ATOM,
            constructor::NIL,
            core::slice::from_ref(payload),
            &[],
        )
    }

    /// `⊢ (atom payload = cons head tail) ⟹ F`.
    pub fn atom_not_cons(
        &self,
        payload: &L::Term,
        head: &L::Term,
        tail: &L::Term,
    ) -> Result<L::Thm, L::Error> {
        self.facts.distinct(
            constructor::ATOM,
            constructor::CONS,
            core::slice::from_ref(payload),
            &[head.clone(), tail.clone()],
        )
    }

    /// `⊢ (nil = cons head tail) ⟹ F`.
    pub fn nil_not_cons(&self, head: &L::Term, tail: &L::Term) -> Result<L::Thm, L::Error> {
        self.facts.distinct(
            constructor::NIL,
            constructor::CONS,
            &[],
            &[head.clone(), tail.clone()],
        )
    }

    pub fn into_fixpoint(self) -> SExprFixpoint<L, P> {
        self.inner
    }
}

impl<L: Logic, P: Clone + PartialEq> SExprFixpoint<L, P> {
    /// Accept a proof bundle only when it realizes the canonical
    /// `Atom + Nil + Cons` polynomial for `payload`.
    pub fn try_new(inner: LeastFixpoint<L, P>, payload: P) -> Result<Self, LeastFixpoint<L, P>> {
        if inner.core.spec.as_inner() == &fixpoint(payload) {
            Ok(Self { inner })
        } else {
            Err(inner)
        }
    }

    pub fn carrier(&self) -> &L::Type {
        &self.inner.core.carrier
    }

    pub fn layer(&self) -> &L::Type {
        &self.inner.core.layer
    }

    pub fn roll(&self) -> &L::Term {
        &self.inner.core.roll
    }

    pub fn unroll(&self) -> &L::Term {
        &self.inner.core.unroll
    }

    pub fn iso_facts(&self) -> &dyn FixpointIsoFacts<L> {
        self.inner.core.facts.as_ref()
    }

    pub fn facts(&self) -> &dyn LeastFixpointFacts<L> {
        self.inner.facts.as_ref()
    }

    pub fn fold(&self, algebra: &L::Term) -> Result<L::Term, L::Error> {
        self.facts().fold(algebra)
    }

    pub fn fold_computation(&self, algebra: &L::Term, layer: &L::Term) -> Result<L::Thm, L::Error> {
        self.facts().fold_roll(algebra, layer)
    }

    pub fn induction(&self, predicate: &L::Term, closed: L::Thm) -> Result<L::Thm, L::Error> {
        self.facts().induction(predicate, closed)
    }

    pub fn into_inner(self) -> LeastFixpoint<L, P> {
        self.inner
    }
}

/// Free inductive representation used as a reference backend.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FreeSExpr<P> {
    Atom(P),
    Nil,
    Cons(Box<FreeSExpr<P>>, Box<FreeSExpr<P>>),
}

impl<P> FreeSExpr<P> {
    pub fn cons(head: Self, tail: Self) -> Self {
        Self::Cons(Box::new(head), Box::new(tail))
    }

    pub fn list(values: impl IntoIterator<Item = Self>) -> Self {
        let values: Vec<_> = values.into_iter().collect();
        values
            .into_iter()
            .rev()
            .fold(Self::Nil, |tail, head| Self::cons(head, tail))
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Free<P>(core::marker::PhantomData<fn() -> P>);

impl<P> Free<P> {
    pub const fn new() -> Self {
        Self(core::marker::PhantomData)
    }
}

impl<P: Clone> SExprSyntax for Free<P> {
    type Payload = P;
    type Value = FreeSExpr<P>;
    type Error = core::convert::Infallible;

    fn atom(&self, payload: P) -> Result<FreeSExpr<P>, Self::Error> {
        Ok(FreeSExpr::Atom(payload))
    }

    fn nil(&self) -> FreeSExpr<P> {
        FreeSExpr::Nil
    }

    fn cons(&self, head: FreeSExpr<P>, tail: FreeSExpr<P>) -> Result<FreeSExpr<P>, Self::Error> {
        Ok(FreeSExpr::Cons(Box::new(head), Box::new(tail)))
    }
}

impl<P: Clone> SExprView for Free<P> {
    fn view(&self, value: &FreeSExpr<P>) -> Result<SExprF<P, FreeSExpr<P>>, Self::Error> {
        Ok(match value {
            FreeSExpr::Atom(payload) => SExprF::Atom(payload.clone()),
            FreeSExpr::Nil => SExprF::Nil,
            FreeSExpr::Cons(head, tail) => SExprF::Cons {
                head: (**head).clone(),
                tail: (**tail).clone(),
            },
        })
    }
}

// TODO(cov:sexpr.parser-interpretation, major): Add A0015 adapters and induced same-value PERs for the SMT-LIB, WAT, and egglog S-expression dialects.

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_inductive::{FixpointCore, Validated};
    use std::convert::Infallible;

    #[derive(Clone, Copy, Debug)]
    struct TestLogic;

    impl Logic for TestLogic {
        type Type = String;
        type Term = String;
        type Thm = String;
        type Error = Infallible;
    }

    struct IsoFacts;

    impl FixpointIsoFacts<TestLogic> for IsoFacts {
        fn roll_unroll(&self, x: &String) -> Result<String, Infallible> {
            Ok(format!("roll-unroll({x})"))
        }

        fn unroll_roll(&self, layer: &String) -> Result<String, Infallible> {
            Ok(format!("unroll-roll({layer})"))
        }
    }

    struct LeastFacts;

    impl LeastFixpointFacts<TestLogic> for LeastFacts {
        fn fold(&self, algebra: &String) -> Result<String, Infallible> {
            Ok(format!("fold({algebra})"))
        }

        fn fold_roll(&self, algebra: &String, layer: &String) -> Result<String, Infallible> {
            Ok(format!("fold-roll({algebra},{layer})"))
        }

        fn induction(&self, predicate: &String, closed: String) -> Result<String, Infallible> {
            Ok(format!("induction({predicate},{closed})"))
        }
    }

    struct NoConfusionFacts;

    impl FixpointNoConfusionFacts<TestLogic> for NoConfusionFacts {
        fn injective(
            &self,
            case: usize,
            field: usize,
            left: &[String],
            right: &[String],
        ) -> Result<String, Infallible> {
            Ok(format!("injective({case},{field},{left:?},{right:?})"))
        }

        fn distinct(
            &self,
            left_case: usize,
            right_case: usize,
            left: &[String],
            right: &[String],
        ) -> Result<String, Infallible> {
            Ok(format!(
                "distinct({left_case},{right_case},{left:?},{right:?})"
            ))
        }
    }

    struct TestProperListFacts;

    impl ProperListFacts<TestLogic> for TestProperListFacts {
        fn holds(&self, proper: &String, value: &String) -> Result<String, Infallible> {
            Ok(format!("{proper}({value})"))
        }

        fn nil(&self, proper: &String) -> Result<String, Infallible> {
            Ok(format!("{proper}(nil)"))
        }

        fn cons(
            &self,
            proper: &String,
            head: &String,
            tail: &String,
            tail_proper: String,
        ) -> Result<String, Infallible> {
            Ok(format!("{tail_proper} |- {proper}(cons({head},{tail}))"))
        }

        fn induction(
            &self,
            proper: &String,
            motive: &String,
            nil_case: String,
            cons_case: String,
        ) -> Result<String, Infallible> {
            Ok(format!(
                "proper-induction({proper},{motive},{nil_case},{cons_case})"
            ))
        }
    }

    fn test_fixpoint() -> LeastFixpoint<TestLogic, &'static str> {
        LeastFixpoint {
            core: FixpointCore {
                spec: Validated::try_from(fixpoint("payload")).unwrap(),
                carrier: "sexpr".into(),
                layer: "sexpr-f".into(),
                roll: "roll".into(),
                unroll: "unroll".into(),
                facts: Box::new(IsoFacts),
            },
            facts: Box::new(LeastFacts),
        }
    }

    #[test]
    fn spec_is_recursive_sum_of_products() {
        let spec = fixpoint("payload");
        spec.validate().unwrap();
        assert_eq!(spec.functor.variants.len(), 3);
        assert!(spec.functor.is_recursive());
    }

    #[test]
    fn proper_lists_and_dotted_pairs_are_distinct() {
        let api = Free::<&str>::new();
        let a = api.atom("a").unwrap();
        let b = api.atom("b").unwrap();
        let proper = api.list([a.clone(), b.clone()]).unwrap();
        assert_eq!(
            api.as_list(&proper).unwrap(),
            Some(vec![a.clone(), b.clone()])
        );

        let dotted = api.cons(a, b).unwrap();
        assert_eq!(api.as_list(&dotted).unwrap(), None);
        assert_eq!(
            api.list_spine(&dotted).unwrap(),
            ListSpine::Dotted {
                prefix: vec![FreeSExpr::Atom("a")],
                tail: FreeSExpr::Atom("b"),
            }
        );
    }

    #[test]
    fn constructor_positions_match_the_polynomial() {
        let spec = polynomial("payload");
        assert_eq!(spec.variants[constructor::ATOM].name, "atom");
        assert_eq!(spec.variants[constructor::NIL].name, "nil");
        assert_eq!(spec.variants[constructor::CONS].name, "cons");
    }

    #[test]
    fn no_confusion_is_an_optional_named_capability() {
        // The ordinary fixpoint still requires only iso/fold/induction facts.
        let ordinary = SExprFixpoint::try_new(test_fixpoint(), "payload")
            .ok()
            .expect("canonical test fixpoint");
        assert_eq!(ordinary.carrier(), "sexpr");

        let api = SExprNoConfusion::from_generic(NoConfusionLeastFixpoint {
            fixpoint: ordinary.into_inner(),
            no_confusion: Box::new(NoConfusionFacts),
        })
        .ok()
        .expect("canonical no-confusion fixpoint");

        assert_eq!(
            api.atom_injective(&"a".into(), &"b".into()).unwrap(),
            r#"injective(0,0,["a"],["b"])"#
        );
        assert_eq!(
            api.cons_tail_injective(&"lh".into(), &"lt".into(), &"rh".into(), &"rt".into())
                .unwrap(),
            r#"injective(2,1,["lh", "lt"],["rh", "rt"])"#
        );
        assert_eq!(
            api.nil_not_cons(&"head".into(), &"tail".into()).unwrap(),
            r#"distinct(1,2,[],["head", "tail"])"#
        );
    }

    #[test]
    fn proper_list_proofs_are_optional_and_do_not_require_no_confusion() {
        let ordinary = SExprFixpoint::try_new(test_fixpoint(), "payload")
            .ok()
            .expect("canonical test fixpoint");
        let proper = SExprProperList::new(ordinary, "proper".into(), Box::new(TestProperListFacts));

        assert_eq!(proper.predicate(), "proper");
        assert_eq!(proper.holds(&"xs".into()).unwrap(), "proper(xs)");
        let nil = proper.nil().unwrap();
        assert_eq!(nil, "proper(nil)");
        assert_eq!(
            proper
                .cons(&"x".into(), &"xs".into(), "proper(xs)".into())
                .unwrap(),
            "proper(xs) |- proper(cons(x,xs))"
        );
        assert_eq!(
            proper
                .induction(&"Q".into(), "Q(nil)".into(), "cons-case".into())
                .unwrap(),
            "proper-induction(proper,Q,Q(nil),cons-case)"
        );
        assert_eq!(proper.into_fixpoint().carrier(), "sexpr");
    }
}
