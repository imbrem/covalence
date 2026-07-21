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

/// An atomic mutually recursive definition group.
///
/// A group rejects duplicate binders before any backend allocates an
/// environment generation. It carries no termination or totality claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinitionGroup<S, E> {
    definitions: Vec<Definition<S, E>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuplicateDefinition<S> {
    pub name: S,
    pub first: usize,
    pub duplicate: usize,
}

impl<S: PartialEq, E> DefinitionGroup<S, E> {
    pub fn new(definitions: Vec<Definition<S, E>>) -> Result<Self, DuplicateDefinition<S>>
    where
        S: Clone,
    {
        for duplicate in 0..definitions.len() {
            if let Some(first) = definitions[..duplicate]
                .iter()
                .position(|definition| definition.name == definitions[duplicate].name)
            {
                return Err(DuplicateDefinition {
                    name: definitions[duplicate].name.clone(),
                    first,
                    duplicate,
                });
            }
        }
        Ok(Self { definitions })
    }

    pub fn definitions(&self) -> &[Definition<S, E>] {
        &self.definitions
    }

    pub fn into_definitions(self) -> Vec<Definition<S, E>> {
        self.definitions
    }
}

impl<S: Clone, D, P> DefinitionGroup<S, CoreExpr<S, D, P>> {
    /// Consume the group as named recursive closure expressions.
    pub fn into_recursive_bindings(self) -> Vec<(S, CoreExpr<S, D, P>)> {
        self.definitions
            .into_iter()
            .map(|definition| {
                let name = definition.name.clone();
                (name, definition.into_recursive_lambda())
            })
            .collect()
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
        evidence: &ExistenceUniqueness<E, U>,
    ) -> Result<(Self::Constant, Self::Theorem), Self::Error>;
}

/// Every retained artifact from the checked admission pipeline.
#[derive(Clone, Debug)]
pub struct TotalAdmission<C, T, E, U, K, Th> {
    pub certificate: C,
    pub termination: T,
    pub adequacy: ExistenceUniqueness<E, U>,
    pub constant: K,
    pub defining_theorem: Th,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdmissionPipelineError<I, T, A, D> {
    Inspect(I),
    Termination(T),
    Adequacy(A),
    Totalization(D),
}

/// Run the four authority-bearing admission phases in their required order.
///
/// In particular, a termination replay or independently conservative model is
/// never accepted as a substitute for existence and uniqueness in the common
/// partial execution relation.
pub fn admit_total<D, P, R, A, Z>(
    definition: &D,
    policy: &P,
    termination_replay: &R,
    adequacy_replay: &A,
    totalization: &Z,
) -> Result<
    TotalAdmission<
        P::Certificate,
        R::Termination,
        A::Existence,
        A::Uniqueness,
        Z::Constant,
        Z::Theorem,
    >,
    AdmissionPipelineError<P::Error, R::Error, A::Error, Z::Error>,
>
where
    P: AdmissionPolicy<D>,
    R: AdmissionReplay<D, P::Certificate>,
    A: ExecutionAdequacyReplay<D, R::Termination>,
    Z: Totalization<D, A::Existence, A::Uniqueness>,
{
    let certificate = policy
        .inspect(definition)
        .map_err(AdmissionPipelineError::Inspect)?;
    let termination = termination_replay
        .replay_termination(definition, &certificate)
        .map_err(AdmissionPipelineError::Termination)?;
    let adequacy = adequacy_replay
        .replay_execution_adequacy(definition, &termination)
        .map_err(AdmissionPipelineError::Adequacy)?;
    let (constant, defining_theorem) = totalization
        .define_total(definition, &adequacy)
        .map_err(AdmissionPipelineError::Totalization)?;
    Ok(TotalAdmission {
        certificate,
        termination,
        adequacy,
        constant,
        defining_theorem,
    })
}

#[cfg(test)]
mod tests {
    use core::cell::Cell;

    use super::*;

    #[test]
    fn definition_group_rejects_duplicate_binders() {
        let definitions = vec![
            Definition::fixed("even", vec!["n"], "body-a"),
            Definition::fixed("odd", vec!["n"], "body-b"),
            Definition::fixed("even", vec!["n"], "body-c"),
        ];
        assert_eq!(
            DefinitionGroup::new(definitions),
            Err(DuplicateDefinition {
                name: "even",
                first: 0,
                duplicate: 2,
            })
        );
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct TerminationProof(&'static str);

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct ExistenceProof(&'static str);

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct UniquenessProof(&'static str);

    struct MockAdequacy;

    struct MockPolicy;

    impl AdmissionPolicy<&'static str> for MockPolicy {
        type Certificate = &'static str;
        type Error = &'static str;

        fn inspect(&self, definition: &&'static str) -> Result<Self::Certificate, Self::Error> {
            (*definition == "append")
                .then_some("structural certificate")
                .ok_or("inspection failed")
        }
    }

    struct MockTermination;

    impl AdmissionReplay<&'static str, &'static str> for MockTermination {
        type Termination = TerminationProof;
        type Error = &'static str;

        fn replay_termination(
            &self,
            _definition: &&'static str,
            certificate: &&'static str,
        ) -> Result<Self::Termination, Self::Error> {
            (*certificate == "structural certificate")
                .then_some(TerminationProof("structural recursion"))
                .ok_or("termination failed")
        }
    }

    struct MockTotalization<'a>(&'a Cell<bool>);

    impl Totalization<&'static str, ExistenceProof, UniquenessProof> for MockTotalization<'_> {
        type Constant = &'static str;
        type Theorem = &'static str;
        type Error = &'static str;

        fn define_total(
            &self,
            _definition: &&'static str,
            evidence: &ExistenceUniqueness<ExistenceProof, UniquenessProof>,
        ) -> Result<(Self::Constant, Self::Theorem), Self::Error> {
            assert_eq!(
                evidence.existence.theorem,
                ExistenceProof("every input reaches a value")
            );
            self.0.set(true);
            Ok(("append-total", "append agrees with MayEval"))
        }
    }

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

    #[test]
    fn totalization_runs_only_after_common_execution_adequacy() {
        let called = Cell::new(false);
        let admitted = admit_total(
            &"append",
            &MockPolicy,
            &MockTermination,
            &MockAdequacy,
            &MockTotalization(&called),
        )
        .unwrap();
        assert!(called.get());
        assert_eq!(admitted.constant, "append-total");
        assert_eq!(admitted.defining_theorem, "append agrees with MayEval");
    }
}
