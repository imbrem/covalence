//! S-expressions as an inductive API.
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

use covalence_inductive::{
    FieldSpec, FixpointIsoFacts, FixpointNoConfusionFacts, FixpointSpec, LeastFixpoint,
    LeastFixpointFacts, Logic, NoConfusionLeastFixpoint, PolynomialSpec, Position, VariantCase,
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

// TODO(cov:sexpr.proper-list-proof-capability, major): Define the logic-generic proper-list predicate and its nil/cons/induction theorem bundle above SExprFixpoint.
// TODO(cov:sexpr.parser-interpretation, major): Express each S-expression dialect parser as a covalence-parsing-api byte/text interpretation and expose its induced same-value PER.

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
}
