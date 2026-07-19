//! Native HOL realization seam for computation theories.
//!
//! This module does not define a particular machine datatype. It validates a
//! caller-supplied HOL vocabulary and proof-bearing law bundle, then exposes
//! the already kernel-checked theorems through `covalence-computation`.

pub mod automata;
pub mod automata_hol_api;
pub mod minsky;
pub mod turing;

use core::fmt;

use covalence_computation::theory::{TheoremArtifact, Theory, TransitionLaws};
use covalence_core::{Error, Term, Type};
use covalence_hol_eval::EvalThm as Thm;

use super::inductive::hol::{Hol, NativeHol};

pub mod blc;
mod concrete;
pub mod identity_replay;
pub mod lambda_to_ski;
pub mod ski;

/// A theorem paired with the exact proposition it is advertised as proving.
#[derive(Clone, Debug)]
pub struct SuppliedLaw {
    pub proposition: Term,
    pub theorem: Thm,
}

/// A native transition vocabulary and its three required universal laws.
///
/// Construction grants no authority. Call [`validate_transition_bundle`] to
/// check the vocabulary signatures and theorem boundaries.
#[derive(Clone, Debug)]
pub struct NativeTransitionBundle {
    pub theory: Theory<NativeHol>,
    pub initialization_closed: SuppliedLaw,
    pub step_closed: SuppliedLaw,
    pub halting_output: SuppliedLaw,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransitionLaw {
    InitializationClosed,
    StepClosed,
    HaltingOutput,
}

/// Metadata retained alongside each validated theorem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeCertificateMetadata {
    pub law: TransitionLaw,
}

pub type NativeCertificate = TheoremArtifact<NativeHol, NativeCertificateMetadata>;

/// Proof facts returned only after [`validate_transition_bundle`] succeeds.
#[derive(Clone, Debug)]
pub struct ValidatedTransitionFacts {
    initialization_closed: NativeCertificate,
    step_closed: NativeCertificate,
    halting_output: NativeCertificate,
}

impl TransitionLaws<NativeHol> for ValidatedTransitionFacts {
    type Certificate = NativeCertificate;

    fn initialization_closed(&self) -> Result<Self::Certificate, Error> {
        Ok(self.initialization_closed.clone())
    }

    fn step_closed(&self) -> Result<Self::Certificate, Error> {
        Ok(self.step_closed.clone())
    }

    fn halting_output(&self) -> Result<Self::Certificate, Error> {
        Ok(self.halting_output.clone())
    }
}

#[derive(Debug)]
pub enum NativeTheoryError {
    Kernel(Error),
    TypeMismatch {
        field: &'static str,
        expected: Type,
        actual: Type,
    },
    LawPropositionNotBoolean {
        law: TransitionLaw,
        actual: Type,
    },
    LawConclusionMismatch {
        law: TransitionLaw,
        advertised: Term,
        actual: Term,
    },
    LawHasHypotheses {
        law: TransitionLaw,
        count: usize,
    },
}

impl fmt::Display for NativeTheoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Kernel(error) => write!(f, "HOL kernel rejected computation theory: {error}"),
            Self::TypeMismatch {
                field,
                expected,
                actual,
            } => write!(
                f,
                "computation theory field `{field}` has type {actual}, expected {expected}"
            ),
            Self::LawPropositionNotBoolean { law, actual } => {
                write!(f, "{law:?} proposition has type {actual}, expected bool")
            }
            Self::LawConclusionMismatch {
                law,
                advertised,
                actual,
            } => write!(
                f,
                "{law:?} theorem concludes `{actual}`, not advertised proposition `{advertised}`"
            ),
            Self::LawHasHypotheses { law, count } => {
                write!(f, "{law:?} theorem has {count} undischarged hypothesis(es)")
            }
        }
    }
}

impl std::error::Error for NativeTheoryError {}

impl From<Error> for NativeTheoryError {
    fn from(error: Error) -> Self {
        Self::Kernel(error)
    }
}

/// Validate a supplied native transition theory without adding axioms.
///
/// Successful facts contain the caller's existing kernel theorem values; this
/// function never constructs a theorem.
pub fn validate_transition_bundle(
    bundle: NativeTransitionBundle,
) -> Result<(Theory<NativeHol>, ValidatedTransitionFacts), NativeTheoryError> {
    validate_vocabulary(&bundle.theory)?;
    let initialization_closed = validate_law(
        TransitionLaw::InitializationClosed,
        bundle.initialization_closed,
    )?;
    let step_closed = validate_law(TransitionLaw::StepClosed, bundle.step_closed)?;
    let halting_output = validate_law(TransitionLaw::HaltingOutput, bundle.halting_output)?;
    Ok((
        bundle.theory,
        ValidatedTransitionFacts {
            initialization_closed,
            step_closed,
            halting_output,
        },
    ))
}

fn validate_vocabulary(theory: &Theory<NativeHol>) -> Result<(), NativeTheoryError> {
    let hol = NativeHol;
    check_type(
        &hol,
        "machine",
        &theory.machine,
        theory.machine_type.clone(),
    )?;
    check_type(
        &hol,
        "initialize",
        &theory.initialize,
        arrow(
            theory.machine_type.clone(),
            arrow(theory.input_type.clone(), theory.state_type.clone()),
        ),
    )?;
    check_type(
        &hol,
        "step",
        &theory.step,
        arrow(
            theory.machine_type.clone(),
            arrow(
                theory.state_type.clone(),
                arrow(theory.state_type.clone(), Type::bool()),
            ),
        ),
    )?;
    check_type(
        &hol,
        "output",
        &theory.output,
        arrow(
            theory.machine_type.clone(),
            arrow(theory.state_type.clone(), theory.output_type.clone()),
        ),
    )?;
    check_type(
        &hol,
        "halts",
        &theory.halts,
        arrow(
            theory.machine_type.clone(),
            arrow(theory.state_type.clone(), Type::bool()),
        ),
    )
}

fn arrow(domain: Type, codomain: Type) -> Type {
    Type::fun(domain, codomain)
}

fn check_type(
    hol: &NativeHol,
    field: &'static str,
    term: &Term,
    expected: Type,
) -> Result<(), NativeTheoryError> {
    let actual = Hol::type_of(hol, term)?;
    if actual == expected {
        Ok(())
    } else {
        Err(NativeTheoryError::TypeMismatch {
            field,
            expected,
            actual,
        })
    }
}

fn validate_law(
    law: TransitionLaw,
    supplied: SuppliedLaw,
) -> Result<NativeCertificate, NativeTheoryError> {
    let hol = NativeHol;
    let actual_type = Hol::type_of(&hol, &supplied.proposition)?;
    if actual_type != Type::bool() {
        return Err(NativeTheoryError::LawPropositionNotBoolean {
            law,
            actual: actual_type,
        });
    }
    let actual = Hol::concl(&hol, &supplied.theorem);
    if actual != supplied.proposition {
        return Err(NativeTheoryError::LawConclusionMismatch {
            law,
            advertised: supplied.proposition,
            actual,
        });
    }
    let hypotheses = Hol::hyps(&hol, &supplied.theorem);
    if !hypotheses.is_empty() {
        return Err(NativeTheoryError::LawHasHypotheses {
            law,
            count: hypotheses.len(),
        });
    }
    Ok(TheoremArtifact {
        theorem: supplied.theorem,
        metadata: NativeCertificateMetadata { law },
    })
}

// TODO(cov:computation.native-definitions, major): Define native HOL
// realizations and witness replay for BLC, SKI, Turing, Minsky, and automata specs.

#[cfg(test)]
mod tests {
    use covalence_computation::theory::TheoremCertificate;

    use super::*;

    fn theory() -> Theory<NativeHol> {
        let machine_type = Type::tfree("machine");
        let input_type = Type::tfree("input");
        let state_type = Type::tfree("state");
        let output_type = Type::tfree("output");
        Theory {
            machine: Term::free("machine", machine_type.clone()),
            initialize: Term::free(
                "initialize",
                arrow(
                    machine_type.clone(),
                    arrow(input_type.clone(), state_type.clone()),
                ),
            ),
            step: Term::free(
                "step",
                arrow(
                    machine_type.clone(),
                    arrow(state_type.clone(), arrow(state_type.clone(), Type::bool())),
                ),
            ),
            output: Term::free(
                "output",
                arrow(
                    machine_type.clone(),
                    arrow(state_type.clone(), output_type.clone()),
                ),
            ),
            halts: Term::free(
                "halts",
                arrow(
                    machine_type.clone(),
                    arrow(state_type.clone(), Type::bool()),
                ),
            ),
            machine_type,
            input_type,
            state_type,
            output_type,
        }
    }

    fn closed_law(name: &str) -> SuppliedLaw {
        let proposition = Term::free(name, Type::bool());
        let theorem = NativeHol.refl(proposition.clone()).unwrap();
        let equality = NativeHol.concl(&theorem);
        SuppliedLaw {
            proposition: equality,
            theorem,
        }
    }

    #[test]
    fn validates_signatures_and_preserves_kernel_theorems() {
        let original = closed_law("initialization_closed");
        let original_theorem = original.theorem.clone();
        let (_, facts) = validate_transition_bundle(NativeTransitionBundle {
            theory: theory(),
            initialization_closed: original,
            step_closed: closed_law("step_closed"),
            halting_output: closed_law("halting_output"),
        })
        .unwrap();
        let artifact = facts.initialization_closed().unwrap();
        assert_eq!(
            NativeHol.concl(artifact.theorem()),
            NativeHol.concl(&original_theorem)
        );
        assert_eq!(artifact.metadata.law, TransitionLaw::InitializationClosed);
    }

    #[test]
    fn rejects_wrong_vocabulary_type() {
        let mut invalid = theory();
        invalid.halts = Term::free("halts", Type::bool());
        let error = validate_transition_bundle(NativeTransitionBundle {
            theory: invalid,
            initialization_closed: closed_law("initialization_closed"),
            step_closed: closed_law("step_closed"),
            halting_output: closed_law("halting_output"),
        })
        .unwrap_err();
        assert!(matches!(
            error,
            NativeTheoryError::TypeMismatch { field: "halts", .. }
        ));
    }

    #[test]
    fn rejects_theorems_with_undischarged_hypotheses() {
        let proposition = Term::free("law", Type::bool());
        let assumed = NativeHol.assume(proposition.clone()).unwrap();
        let error = validate_transition_bundle(NativeTransitionBundle {
            theory: theory(),
            initialization_closed: SuppliedLaw {
                proposition,
                theorem: assumed,
            },
            step_closed: closed_law("step_closed"),
            halting_output: closed_law("halting_output"),
        })
        .unwrap_err();
        assert!(matches!(
            error,
            NativeTheoryError::LawHasHypotheses {
                law: TransitionLaw::InitializationClosed,
                count: 1
            }
        ));
    }
}
