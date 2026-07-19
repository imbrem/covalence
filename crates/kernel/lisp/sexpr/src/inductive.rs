//! Generic first-order inductive values encoded as tagged S-expressions.
//!
//! The accepted boundary is a validated [`InductiveSpec`]. Nested datatype
//! families and coinductive requests are rejected explicitly; they are not
//! approximated by malformed first-order constructors.

use covalence_inductive::{
    DatatypeFamilyExpr, FixpointSpec, IndResult, InductiveError, InductiveSpec, InductiveTheory,
    Logic, LogicOps, PolynomialSpec, Validated,
};

use crate::FreeSExpr;

/// An atom in the canonical tagged encoding.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum EncodedAtom<X, E> {
    /// Constructor index in declaration order.
    Constructor(usize),
    /// An external argument and its declared sort.
    External { sort: X, value: E },
}

/// A recursive or external constructor argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawArgument<X, E> {
    /// A recursive value.
    Recursive(RawInductive<X, E>),
    /// A value of an external sort.
    External { sort: X, value: E },
}

/// A raw, junk-carrying S-expression representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawInductive<X, E>(pub FreeSExpr<EncodedAtom<X, E>>);

/// One successfully decoded constructor layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorLayer<A> {
    /// Constructor index in declaration order.
    pub constructor: usize,
    /// Arguments in declaration order.
    pub arguments: Vec<A>,
}

/// Why construction or encoding-request validation failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodingError {
    ConstructorIndex { index: usize, arity: usize },
    Arity { expected: usize, got: usize },
    ArgumentKind { position: usize },
    ExternalSort { position: usize },
    NestedFamilyUnsupported,
    CoinductiveUnsupported,
}

/// Requests accepted or explicitly rejected by this first-order encoder.
pub enum EncodingRequest<X> {
    /// Supported directly recursive first-order datatype.
    FirstOrder(Validated<InductiveSpec<X>>),
    /// Nested least fixpoints require a separate realization.
    NestedFamily(DatatypeFamilyExpr<X>),
    /// Greatest-fixpoint realizations require observation/productivity APIs.
    Coinductive(Validated<FixpointSpec<X>>),
}

/// Shared construction and partial-observation surface.
pub trait InductiveRepresentation {
    type Value: Clone;
    type Argument;
    type Evidence;

    fn construct(
        &self,
        constructor: usize,
        arguments: Vec<Self::Argument>,
        evidence: Self::Evidence,
    ) -> Result<Self::Value, EncodingError>;

    fn view(&self, value: &Self::Value) -> Option<ConstructorLayer<Self::Argument>>;
}

/// Raw first-order encoding for one checked specification.
#[derive(Clone, Debug)]
pub struct RawEncoding<X, E> {
    spec: Validated<InductiveSpec<X>>,
    marker: core::marker::PhantomData<fn() -> E>,
}

impl<X, E> RawEncoding<X, E> {
    pub fn new(spec: Validated<InductiveSpec<X>>) -> Self {
        Self {
            spec,
            marker: core::marker::PhantomData,
        }
    }

    /// Accept a named first-order polynomial explicitly at inductive
    /// polarity.
    pub fn from_inductive_fixpoint(spec: Validated<FixpointSpec<X>>) -> Self {
        let spec = InductiveSpec::from_fixpoint(spec.into_inner());
        Self::new(
            Validated::try_from(spec)
                .expect("conversion from a validated first-order fixpoint preserves validity"),
        )
    }

    /// Accept a validated first-order polynomial, using its public name for
    /// the resulting inductive carrier.
    pub fn from_polynomial(spec: Validated<PolynomialSpec<X>>) -> Self {
        let functor = spec.into_inner();
        let name = functor.name.clone();
        Self::from_inductive_fixpoint(
            Validated::try_from(FixpointSpec::new(name, functor))
                .expect("a validated polynomial remains valid as a named fixpoint"),
        )
    }

    /// Validate the requested recursion class at the encoding boundary.
    pub fn from_request(request: EncodingRequest<X>) -> Result<Self, EncodingError> {
        match request {
            EncodingRequest::FirstOrder(spec) => Ok(Self::new(spec)),
            EncodingRequest::NestedFamily(_) => Err(EncodingError::NestedFamilyUnsupported),
            EncodingRequest::Coinductive(_) => Err(EncodingError::CoinductiveUnsupported),
        }
    }

    pub fn spec(&self) -> &Validated<InductiveSpec<X>> {
        &self.spec
    }
}

fn proper_list<A>(items: impl IntoIterator<Item = FreeSExpr<A>>) -> FreeSExpr<A> {
    items
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(FreeSExpr::Nil, |tail, head| {
            FreeSExpr::Cons(Box::new(head), Box::new(tail))
        })
}

fn decode_list<A: Clone>(value: &FreeSExpr<A>) -> Option<Vec<FreeSExpr<A>>> {
    let mut values = Vec::new();
    let mut cursor = value;
    loop {
        match cursor {
            FreeSExpr::Nil => return Some(values),
            FreeSExpr::Cons(head, tail) => {
                values.push((**head).clone());
                cursor = tail;
            }
            FreeSExpr::Atom(_) => return None,
        }
    }
}

impl<X: Clone + PartialEq, E: Clone> InductiveRepresentation for RawEncoding<X, E> {
    type Value = RawInductive<X, E>;
    type Argument = RawArgument<X, E>;
    type Evidence = ();

    fn construct(
        &self,
        constructor: usize,
        arguments: Vec<Self::Argument>,
        (): (),
    ) -> Result<Self::Value, EncodingError> {
        let case = self
            .spec
            .ctors
            .get(constructor)
            .ok_or(EncodingError::ConstructorIndex {
                index: constructor,
                arity: self.spec.ctors.len(),
            })?;
        if arguments.len() != case.args.len() {
            return Err(EncodingError::Arity {
                expected: case.args.len(),
                got: arguments.len(),
            });
        }
        let mut encoded = Vec::with_capacity(arguments.len() + 1);
        encoded.push(FreeSExpr::Atom(EncodedAtom::Constructor(constructor)));
        for (position, (argument, (_, sort))) in arguments.into_iter().zip(&case.args).enumerate() {
            let value = match (argument, sort) {
                (RawArgument::Recursive(value), covalence_inductive::ArgSort::Rec) => value.0,
                (
                    RawArgument::External {
                        sort: actual,
                        value,
                    },
                    covalence_inductive::ArgSort::Ext(expected),
                ) if &actual == expected => FreeSExpr::Atom(EncodedAtom::External {
                    sort: actual,
                    value,
                }),
                (RawArgument::External { .. }, covalence_inductive::ArgSort::Ext(_)) => {
                    return Err(EncodingError::ExternalSort { position });
                }
                _ => return Err(EncodingError::ArgumentKind { position }),
            };
            encoded.push(value);
        }
        Ok(RawInductive(proper_list(encoded)))
    }

    fn view(&self, value: &Self::Value) -> Option<ConstructorLayer<Self::Argument>> {
        let mut encoded = decode_list(&value.0)?;
        let FreeSExpr::Atom(EncodedAtom::Constructor(constructor)) = encoded.first()? else {
            return None;
        };
        let constructor = *constructor;
        encoded.remove(0);
        let case = self.spec.ctors.get(constructor)?;
        if encoded.len() != case.args.len() {
            return None;
        }
        let mut arguments = Vec::with_capacity(encoded.len());
        for (encoded, (_, sort)) in encoded.into_iter().zip(&case.args) {
            arguments.push(match (encoded, sort) {
                (value, covalence_inductive::ArgSort::Rec) => {
                    RawArgument::Recursive(RawInductive(value))
                }
                (
                    FreeSExpr::Atom(EncodedAtom::External {
                        sort: actual,
                        value,
                    }),
                    covalence_inductive::ArgSort::Ext(expected),
                ) if &actual == expected => RawArgument::External {
                    sort: actual,
                    value,
                },
                _ => return None,
            });
        }
        Some(ConstructorLayer {
            constructor,
            arguments,
        })
    }
}

/// Logic term and theorem proving membership in the represented subset.
#[derive(Debug)]
pub struct Membership<L: Logic> {
    pub term: L::Term,
    pub theorem: L::Thm,
}

impl<L: Logic> Clone for Membership<L> {
    fn clone(&self) -> Self {
        Self {
            term: self.term.clone(),
            theorem: self.theorem.clone(),
        }
    }
}

/// A refined recursive or external argument.
#[derive(Debug)]
pub enum RefinedArgument<L: Logic, E> {
    Recursive(RefinedInductive<L, E>),
    External { sort: L::Type, value: E },
}

impl<L: Logic, E: Clone> Clone for RefinedArgument<L, E> {
    fn clone(&self) -> Self {
        match self {
            Self::Recursive(value) => Self::Recursive(value.clone()),
            Self::External { sort, value } => Self::External {
                sort: sort.clone(),
                value: value.clone(),
            },
        }
    }
}

/// Raw encoding plus an explicit membership theorem and checked layer.
#[derive(Debug)]
pub struct RefinedInductive<L: Logic, E> {
    raw: RawInductive<L::Type, E>,
    membership: Membership<L>,
    layer: ConstructorLayer<RefinedArgument<L, E>>,
}

impl<L: Logic, E: Clone> Clone for RefinedInductive<L, E> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
            membership: self.membership.clone(),
            layer: self.layer.clone(),
        }
    }
}

impl<L: Logic, E> RefinedInductive<L, E> {
    pub fn raw(&self) -> &RawInductive<L::Type, E> {
        &self.raw
    }

    pub fn membership(&self) -> &Membership<L> {
        &self.membership
    }
}

/// Refined construction for a checked first-order specification.
pub struct RefinedEncoding<L: Logic, E> {
    raw: RawEncoding<L::Type, E>,
    marker: core::marker::PhantomData<fn() -> L>,
}

impl<L: Logic, E> RefinedEncoding<L, E> {
    pub fn new(spec: Validated<InductiveSpec<L::Type>>) -> Self {
        Self {
            raw: RawEncoding::new(spec),
            marker: core::marker::PhantomData,
        }
    }

    /// Accept a named first-order polynomial explicitly at inductive
    /// polarity.
    pub fn from_inductive_fixpoint(spec: Validated<FixpointSpec<L::Type>>) -> Self {
        Self {
            raw: RawEncoding::from_inductive_fixpoint(spec),
            marker: core::marker::PhantomData,
        }
    }

    /// Accept a validated first-order polynomial at inductive polarity.
    pub fn from_polynomial(spec: Validated<PolynomialSpec<L::Type>>) -> Self {
        Self {
            raw: RawEncoding::from_polynomial(spec),
            marker: core::marker::PhantomData,
        }
    }

    pub fn spec(&self) -> &Validated<InductiveSpec<L::Type>> {
        self.raw.spec()
    }
}

impl<L: Logic, E: Clone> InductiveRepresentation for RefinedEncoding<L, E> {
    type Value = RefinedInductive<L, E>;
    type Argument = RefinedArgument<L, E>;
    type Evidence = Membership<L>;

    fn construct(
        &self,
        constructor: usize,
        arguments: Vec<Self::Argument>,
        membership: Self::Evidence,
    ) -> Result<Self::Value, EncodingError> {
        let raw_arguments = arguments
            .iter()
            .map(|argument| match argument {
                RefinedArgument::Recursive(value) => RawArgument::Recursive(value.raw.clone()),
                RefinedArgument::External { sort, value } => RawArgument::External {
                    sort: sort.clone(),
                    value: value.clone(),
                },
            })
            .collect();
        let raw = self.raw.construct(constructor, raw_arguments, ())?;
        Ok(RefinedInductive {
            raw,
            membership,
            layer: ConstructorLayer {
                constructor,
                arguments,
            },
        })
    }

    fn view(&self, value: &Self::Value) -> Option<ConstructorLayer<Self::Argument>> {
        Some(value.layer.clone())
    }
}

/// Induction exists only for refined values attached to a supplied theory.
pub trait RefinedInduction<L: Logic, E>:
    InductiveRepresentation<Value = RefinedInductive<L, E>>
{
    fn induct(
        &self,
        value: &RefinedInductive<L, E>,
        motive: &L::Term,
        cases: Vec<L::Thm>,
    ) -> IndResult<L::Thm, L>;
}

/// Delegates induction and membership discharge to an existing theory.
///
/// ```compile_fail
/// use covalence_sexpr_api::{RawEncoding, RefinedInduction};
///
/// fn needs_induction<L: covalence_inductive::Logic, E>(
///     backend: &impl RefinedInduction<L, E>,
/// ) {}
///
/// # let spec = covalence_inductive::Validated::try_from(
/// #   covalence_inductive::InductiveSpec::<()>::enum_of("bit", ["zero", "one"])
/// # ).unwrap();
/// let raw = RawEncoding::<(), ()>::new(spec);
/// needs_induction::<SomeLogic, ()>(&raw);
/// # struct SomeLogic;
/// # impl covalence_inductive::Logic for SomeLogic {
/// #   type Type = (); type Term = (); type Thm = ();
/// #   type Error = core::convert::Infallible;
/// # }
/// ```
pub struct TheoryInduction<'a, L: LogicOps, E> {
    logic: &'a L,
    theory: &'a InductiveTheory<L>,
    encoding: RefinedEncoding<L, E>,
}

impl<'a, L: LogicOps, E> TheoryInduction<'a, L, E> {
    pub fn try_new(
        logic: &'a L,
        theory: &'a InductiveTheory<L>,
        spec: Validated<InductiveSpec<L::Type>>,
    ) -> Result<Self, InductiveError<L::Error>> {
        if &theory.spec != spec.as_inner() {
            return Err(InductiveError::SpecMismatch(
                "the S-expression encoding and induction theory differ".into(),
            ));
        }
        Ok(Self {
            logic,
            theory,
            encoding: RefinedEncoding::new(spec),
        })
    }
}

impl<L: LogicOps, E: Clone> InductiveRepresentation for TheoryInduction<'_, L, E> {
    type Value = RefinedInductive<L, E>;
    type Argument = RefinedArgument<L, E>;
    type Evidence = Membership<L>;

    fn construct(
        &self,
        constructor: usize,
        arguments: Vec<Self::Argument>,
        evidence: Self::Evidence,
    ) -> Result<Self::Value, EncodingError> {
        self.encoding.construct(constructor, arguments, evidence)
    }

    fn view(&self, value: &Self::Value) -> Option<ConstructorLayer<Self::Argument>> {
        self.encoding.view(value)
    }
}

impl<L: LogicOps, E: Clone> RefinedInduction<L, E> for TheoryInduction<'_, L, E> {
    fn induct(
        &self,
        value: &RefinedInductive<L, E>,
        motive: &L::Term,
        cases: Vec<L::Thm>,
    ) -> IndResult<L::Thm, L> {
        let guarded = self.theory.facts.induct(motive, cases)?;
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

    use covalence_inductive::{ArgSort, CtorSpec};

    use super::*;

    #[derive(Clone, Copy, Debug)]
    struct TestLogic;

    impl Logic for TestLogic {
        type Type = String;
        type Term = String;
        type Thm = String;
        type Error = Infallible;
    }

    fn list_spec<X>(element: X) -> Validated<InductiveSpec<X>> {
        Validated::try_from(InductiveSpec::new(
            "list",
            vec![
                CtorSpec::nullary("nil"),
                CtorSpec::new(
                    "cons",
                    [("head", ArgSort::Ext(element)), ("tail", ArgSort::Rec)],
                ),
            ],
        ))
        .unwrap()
    }

    fn tree_spec() -> Validated<InductiveSpec<()>> {
        Validated::try_from(InductiveSpec::new(
            "tree",
            vec![
                CtorSpec::nullary("leaf"),
                CtorSpec::new("branch", [("left", ArgSort::Rec), ("right", ArgSort::Rec)]),
            ],
        ))
        .unwrap()
    }

    fn membership(term: &str) -> Membership<TestLogic> {
        Membership {
            term: term.into(),
            theorem: format!("member({term})"),
        }
    }

    #[test]
    fn raw_and_refined_lists_share_constructor_and_view_shapes() {
        let raw = RawEncoding::<String, &str>::new(list_spec("element".into()));
        let nil = raw.construct(0, vec![], ()).unwrap();
        let cons = raw
            .construct(
                1,
                vec![
                    RawArgument::External {
                        sort: "element".into(),
                        value: "a",
                    },
                    RawArgument::Recursive(nil),
                ],
                (),
            )
            .unwrap();
        let raw_layer = raw.view(&cons).unwrap();
        assert_eq!(raw_layer.constructor, 1);
        assert_eq!(raw_layer.arguments.len(), 2);
        let nil = raw.construct(0, vec![], ()).unwrap();
        assert_eq!(
            raw.construct(
                1,
                vec![
                    RawArgument::External {
                        sort: "wrong".into(),
                        value: "a",
                    },
                    RawArgument::Recursive(nil),
                ],
                (),
            ),
            Err(EncodingError::ExternalSort { position: 0 })
        );

        let refined = RefinedEncoding::<TestLogic, &str>::new(list_spec("element".to_string()));
        let nil = refined.construct(0, vec![], membership("nil")).unwrap();
        let cons = refined
            .construct(
                1,
                vec![
                    RefinedArgument::External {
                        sort: "element".into(),
                        value: "a",
                    },
                    RefinedArgument::Recursive(nil),
                ],
                membership("cons a nil"),
            )
            .unwrap();
        let refined_layer = refined.view(&cons).unwrap();
        assert_eq!(refined_layer.constructor, raw_layer.constructor);
        assert_eq!(refined_layer.arguments.len(), raw_layer.arguments.len());
        assert_eq!(cons.membership().theorem, "member(cons a nil)");
    }

    #[test]
    fn generic_tree_checks_arity_recursive_positions_and_junk() {
        let encoding = RawEncoding::<(), ()>::new(tree_spec());
        let leaf = encoding.construct(0, vec![], ()).unwrap();
        let branch = encoding
            .construct(
                1,
                vec![
                    RawArgument::Recursive(leaf.clone()),
                    RawArgument::Recursive(leaf),
                ],
                (),
            )
            .unwrap();
        assert_eq!(encoding.view(&branch).unwrap().arguments.len(), 2);
        assert_eq!(
            encoding.construct(1, vec![], ()),
            Err(EncodingError::Arity {
                expected: 2,
                got: 0
            })
        );
        assert!(
            encoding
                .view(&RawInductive(FreeSExpr::Atom(EncodedAtom::Constructor(1))))
                .is_none()
        );
    }

    #[test]
    fn first_order_polynomial_uses_the_same_encoding_boundary() {
        let fixpoint = Validated::try_from(tree_spec().into_inner().into_fixpoint()).unwrap();
        let encoding = RawEncoding::<(), ()>::from_inductive_fixpoint(fixpoint);
        assert_eq!(encoding.spec().ctors.len(), 2);
        assert!(encoding.construct(0, vec![], ()).is_ok());

        let polynomial =
            Validated::try_from(tree_spec().into_inner().into_fixpoint().functor).unwrap();
        let encoding = RawEncoding::<(), ()>::from_polynomial(polynomial);
        assert_eq!(encoding.spec().ctors.len(), 2);
    }

    #[test]
    fn unsupported_recursion_classes_are_rejected_at_the_boundary() {
        let nested = EncodingRequest::NestedFamily(DatatypeFamilyExpr::<()>::least(
            DatatypeFamilyExpr::Bound(0),
        ));
        assert!(matches!(
            RawEncoding::<(), ()>::from_request(nested),
            Err(EncodingError::NestedFamilyUnsupported)
        ));

        let coinductive = EncodingRequest::Coinductive(
            Validated::try_from(tree_spec().into_inner().into_fixpoint()).unwrap(),
        );
        assert!(matches!(
            RawEncoding::<(), ()>::from_request(coinductive),
            Err(EncodingError::CoinductiveUnsupported)
        ));
    }
}
