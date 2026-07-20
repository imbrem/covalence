//! Capabilities connecting partial Lisp execution to total logical functions.
//!
//! A finite execution trace proves only `MayEval`. Languages such as ACL2 add
//! a separate admission layer establishing termination and uniqueness for all
//! inputs in a logical world. These types make that boundary explicit without
//! granting theorem authority to a syntactic checker.
//!
//! @covalence-api {"id":"A0024","title":"Lisp admission and totalization","status":"experimental","dependsOn":["A0022"]}

use crate::{CoreExpr, Parameter};

/// A frontend-neutral named definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Definition<S, E> {
    pub name: S,
    pub parameters: Vec<S>,
    pub rest: Option<S>,
    pub body: E,
}

impl<S, E> Definition<S, E> {
    pub fn fixed(name: S, parameters: Vec<S>, body: E) -> Self {
        Self {
            name,
            parameters,
            rest: None,
            body,
        }
    }

    pub fn variadic(name: S, parameters: Vec<S>, rest: S, body: E) -> Self {
        Self {
            name,
            parameters,
            rest: Some(rest),
            body,
        }
    }
}

impl<S, D, P> Definition<S, CoreExpr<S, D, P>> {
    /// Turn a named definition into the recursive closure expression executed
    /// by the common partial semantics.
    ///
    /// This is a structural operation only. It neither checks termination nor
    /// grants the resulting closure a total logical interpretation.
    pub fn into_recursive_lambda(self) -> CoreExpr<S, D, P> {
        CoreExpr::Lambda {
            name: Some(self.name),
            parameters: self.parameters.into_iter().map(Parameter::new).collect(),
            rest: self.rest.map(Parameter::new),
            body: Box::new(self.body),
        }
    }
}

/// A canonical lowered definition paired with its source-body provenance.
///
/// Names and formals occur only in `core`, preventing source and lowered
/// metadata from drifting apart. Source-oriented policies may inspect
/// `source_body`; execution and semantic backends consume `core.body`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourcedDefinition<S, Source, Core> {
    pub core: Definition<S, Core>,
    pub source_body: Source,
}

impl<S, Source, Core> SourcedDefinition<S, Source, Core> {
    pub fn new(core: Definition<S, Core>, source_body: Source) -> Self {
        Self { core, source_body }
    }
}

/// One recursive call discovered in a candidate definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveCall<S, E> {
    pub callee: S,
    pub arguments: Vec<E>,
}

/// Plain termination-certificate data.
///
/// `M` describes the measure/order and `W` is the witness format accepted by
/// a replay backend. Possessing this value does not itself prove termination.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TerminationCertificate<M, W> {
    pub measure: M,
    pub witness: W,
}

/// A definition paired with checked candidate certificate data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmittedDefinition<D, C> {
    pub definition: D,
    pub certificate: C,
}

/// Host-side inspection/checking policy.
///
/// This may reject malformed witnesses early, but its result remains plain
/// data until replayed by [`AdmissionReplay`].
pub trait AdmissionPolicy<D> {
    type Certificate;
    type Error;

    fn inspect(&self, definition: &D) -> Result<Self::Certificate, Self::Error>;
}

/// Proof-producing replay of termination/admissibility evidence.
///
/// This phase may establish that a definition has a total logical model, but
/// it does not by itself connect that model to the common partial Lisp
/// execution relation. That connection belongs to [`ExecutionAdequacyReplay`].
pub trait AdmissionReplay<D, C> {
    type Termination;
    type Error;

    fn replay_termination(
        &self,
        definition: &D,
        certificate: &C,
    ) -> Result<Self::Termination, Self::Error>;
}

/// Evidence that relational evaluation has at least one result.
///
/// The carrier is deliberately backend-defined: in a HOL backend it will
/// normally be a theorem universally quantified over the definition's inputs.
#[derive(Clone, Debug)]
pub struct EvaluationExistence<T> {
    pub theorem: T,
}

/// Evidence that any two relational evaluation results are equal.
///
/// Existence and uniqueness are kept as different types because proof systems
/// frequently represent or derive them differently.
#[derive(Clone, Debug)]
pub struct EvaluationUniqueness<T> {
    pub theorem: T,
}

/// Evidence that the common relational evaluation result exists and is unique.
#[derive(Clone, Debug)]
pub struct ExistenceUniqueness<E, U = E> {
    pub existence: EvaluationExistence<E>,
    pub uniqueness: EvaluationUniqueness<U>,
}

/// Proof-producing bridge from language admission to the common partial Lisp
/// execution relation.
///
/// For a definition `d`, implementations must replay the two universal facts
///
/// ```text
/// ∀ inputs. ∃ value. MayEval(d inputs, value)
/// ∀ inputs value₁ value₂.
///   MayEval(d inputs, value₁) ∧ MayEval(d inputs, value₂) → value₁ = value₂
/// ```
///
/// against the same operational semantics used by checked finite traces.
/// Host execution, syntactic termination checks, and a defining equation for
/// an independently constructed total model are not sufficient evidence.
pub trait ExecutionAdequacyReplay<D, T> {
    type Existence;
    type Uniqueness;
    type Error;

    fn replay_execution_adequacy(
        &self,
        definition: &D,
        termination: &T,
    ) -> Result<ExistenceUniqueness<Self::Existence, Self::Uniqueness>, Self::Error>;
}

/// Capability for conservatively introducing a total interpretation only
/// after existence and uniqueness have been established.
pub trait Totalization<D, E, U = E> {
    type Constant;
    type Theorem;
    type Error;

    fn define_total(
        &self,
        definition: &D,
        evidence: ExistenceUniqueness<E, U>,
    ) -> Result<(Self::Constant, Self::Theorem), Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct TerminationProof(&'static str);

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct ExistenceProof(&'static str);

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct UniquenessProof(&'static str);

    struct MockAdequacy;

    impl ExecutionAdequacyReplay<&'static str, TerminationProof> for MockAdequacy {
        type Existence = ExistenceProof;
        type Uniqueness = UniquenessProof;
        type Error = &'static str;

        fn replay_execution_adequacy(
            &self,
            definition: &&'static str,
            termination: &TerminationProof,
        ) -> Result<ExistenceUniqueness<Self::Existence, Self::Uniqueness>, Self::Error> {
            if *definition != "append" || termination.0 != "structural recursion" {
                return Err("wrong evidence");
            }
            Ok(ExistenceUniqueness {
                existence: EvaluationExistence {
                    theorem: ExistenceProof("every input reaches a value"),
                },
                uniqueness: EvaluationUniqueness {
                    theorem: UniquenessProof("reachable values are equal"),
                },
            })
        }
    }

    #[test]
    fn fixed_and_variadic_definitions_become_named_recursive_lambdas() {
        let fixed = Definition::fixed(
            "identity",
            vec!["value"],
            CoreExpr::<&str, (), ()>::Variable("value"),
        )
        .into_recursive_lambda();
        assert!(matches!(
            fixed,
            CoreExpr::Lambda {
                name: Some("identity"),
                parameters,
                rest: None,
                ..
            } if parameters[0].name == "value"
        ));

        let variadic = Definition::variadic(
            "list",
            Vec::<&str>::new(),
            "values",
            CoreExpr::<&str, (), ()>::Variable("values"),
        )
        .into_recursive_lambda();
        assert!(matches!(
            variadic,
            CoreExpr::Lambda {
                name: Some("list"),
                parameters,
                rest: Some(Parameter { name: "values" }),
                ..
            } if parameters.is_empty()
        ));
    }

    #[test]
    fn execution_adequacy_keeps_existence_and_uniqueness_distinct() {
        let evidence = MockAdequacy
            .replay_execution_adequacy(&"append", &TerminationProof("structural recursion"))
            .unwrap();
        assert_eq!(
            evidence.existence.theorem,
            ExistenceProof("every input reaches a value")
        );
        assert_eq!(
            evidence.uniqueness.theorem,
            UniquenessProof("reachable values are equal")
        );
    }
}
