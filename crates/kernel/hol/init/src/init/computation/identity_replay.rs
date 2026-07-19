//! Closed identity-translation replay milestone.
//!
//! Host computation searches for the familiar bracket-abstraction candidate
//! `λ.0 ↦ I`. [`IdentityTranslationReplay`] does not trust that candidate: it
//! recomputes both encodings, checks the exact source and target theories and
//! the zero-step compilation accounting, then derives a closed HOL theorem
//! binding those theories to the canonical encodings.
//!
//! The theorem is intentionally bounded:
//!
//! ```text
//! ⊢ source_machine = encode(λ.0) ∧ target_machine = encode(I)
//! ```
//!
//! It is a compiler/replay seam, not the still-open universal claim that
//! bracket abstraction preserves every BLC reduction.
//!
//! @covalence-api-impl {"api":"A0009","name":"IdentityTranslationReplay","representation":"native HOL replay of the closed BLC identity to SKI I translation"}

use core::fmt;

use covalence_computation::{
    blc,
    compiler::{CompilerReplayBackend, CompilerSearchWitness, StepMapping},
    ski,
    theory::{TheoremArtifact, Theory},
};
use covalence_core::{Error, Term};

use super::{concrete::bit_list, lambda_to_ski::LambdaToSki};
use crate::init::inductive::hol::{Hol, NativeHol};

/// Plain-data candidate produced by identity-translation search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentityTranslationWitness {
    pub source_bits: Vec<bool>,
    pub target_bits: Vec<bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IdentityTranslationMetadata {
    pub source_bits: usize,
    pub target_bits: usize,
}

pub type IdentityTranslationCertificate = TheoremArtifact<NativeHol, IdentityTranslationMetadata>;

/// Errors raised while replaying an untrusted identity-translation candidate.
#[derive(Clone, Debug)]
pub enum IdentityTranslationError {
    ForgedSource,
    ForgedTarget,
    WrongStepMapping { advertised: StepMapping },
    SourceTheoryMismatch,
    TargetTheoryMismatch,
    Translation(super::lambda_to_ski::LambdaToSkiError),
    Kernel(Error),
}

impl fmt::Display for IdentityTranslationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ForgedSource => f.write_str("identity translation source encoding is forged"),
            Self::ForgedTarget => f.write_str("identity translation target encoding is forged"),
            Self::WrongStepMapping { advertised } => write!(
                f,
                "identity translation is a zero-step compilation milestone, not {:?}",
                advertised
            ),
            Self::SourceTheoryMismatch => {
                f.write_str("source theory is not the canonical closed BLC identity")
            }
            Self::TargetTheoryMismatch => {
                f.write_str("target theory is not the canonical SKI I program")
            }
            Self::Translation(error) => write!(f, "identity translation failed: {error}"),
            Self::Kernel(error) => write!(f, "HOL replay failed: {error}"),
        }
    }
}

impl std::error::Error for IdentityTranslationError {}

impl From<Error> for IdentityTranslationError {
    fn from(error: Error) -> Self {
        Self::Kernel(error)
    }
}

impl From<super::lambda_to_ski::LambdaToSkiError> for IdentityTranslationError {
    fn from(error: super::lambda_to_ski::LambdaToSkiError) -> Self {
        Self::Translation(error)
    }
}

/// Untrusted search for the closed identity translation.
///
/// Returning this value proves nothing; authority enters only through
/// [`IdentityTranslationReplay::replay_simulation`].
pub fn search_identity_translation()
-> Result<CompilerSearchWitness<IdentityTranslationWitness>, IdentityTranslationError> {
    let source = identity_source();
    let target = LambdaToSki::new(source.clone())?.translate()?;
    Ok(CompilerSearchWitness {
        step_mapping: StepMapping {
            source_steps: 0,
            target_steps: 0,
        },
        candidate: IdentityTranslationWitness {
            source_bits: source.encode(),
            target_bits: target.encode(),
        },
    })
}

/// Native replay backend for the single closed identity translation.
#[derive(Clone, Copy, Debug, Default)]
pub struct IdentityTranslationReplay;

impl CompilerReplayBackend<NativeHol, NativeHol, IdentityTranslationWitness>
    for IdentityTranslationReplay
{
    type Certificate = IdentityTranslationCertificate;
    type Error = IdentityTranslationError;

    fn replay_simulation(
        &self,
        source_logic: &NativeHol,
        source_theory: &Theory<NativeHol>,
        target_logic: &NativeHol,
        target_theory: &Theory<NativeHol>,
        witness: &CompilerSearchWitness<IdentityTranslationWitness>,
    ) -> Result<Self::Certificate, Self::Error> {
        let source_bits = identity_source().encode();
        let target_bits = identity_target().encode();

        if witness.candidate.source_bits != source_bits {
            return Err(IdentityTranslationError::ForgedSource);
        }
        if witness.candidate.target_bits != target_bits {
            return Err(IdentityTranslationError::ForgedTarget);
        }
        if witness.step_mapping
            != (StepMapping {
                source_steps: 0,
                target_steps: 0,
            })
        {
            return Err(IdentityTranslationError::WrongStepMapping {
                advertised: witness.step_mapping,
            });
        }

        let encoded_source = bit_list(source_bits.iter().copied())?;
        let encoded_target = bit_list(target_bits.iter().copied())?;
        if source_theory.machine != encoded_source {
            return Err(IdentityTranslationError::SourceTheoryMismatch);
        }
        if target_theory.machine != encoded_target {
            return Err(IdentityTranslationError::TargetTheoryMismatch);
        }

        // Structural equality was checked above. REFL and conjunction
        // introduction now reconstruct the closed theorem inside native HOL.
        let source_theorem = source_logic.refl(encoded_source)?;
        let target_theorem = target_logic.refl(encoded_target)?;
        let theorem = source_logic.and_intro(source_theorem, target_theorem)?;
        Ok(TheoremArtifact {
            theorem,
            metadata: IdentityTranslationMetadata {
                source_bits: source_bits.len(),
                target_bits: target_bits.len(),
            },
        })
    }
}

fn identity_source() -> blc::Term {
    blc::Term::abs(blc::Term::var(0))
}

fn identity_target() -> ski::Term {
    ski::Term::I
}

/// Exact proposition reconstructed by a successful identity replay.
pub fn identity_translation_proposition() -> Result<Term, Error> {
    let hol = NativeHol;
    let source = bit_list(identity_source().encode())?;
    let target = bit_list(identity_target().encode())?;
    hol.and(
        hol.eq(source.clone(), source)?,
        hol.eq(target.clone(), target)?,
    )
}

#[cfg(test)]
mod tests {
    use covalence_computation::{compiler::CompilerReplayBackend, theory::TheoremCertificate};

    use super::*;

    fn theories() -> (Theory<NativeHol>, Theory<NativeHol>) {
        (
            super::super::blc::realize(&identity_source())
                .unwrap()
                .theory,
            super::super::ski::realize(&identity_target())
                .unwrap()
                .theory,
        )
    }

    #[test]
    fn search_is_replayed_into_the_exact_closed_hol_theorem() {
        let witness = search_identity_translation().unwrap();
        let (source, target) = theories();
        let certificate = IdentityTranslationReplay
            .replay_simulation(&NativeHol, &source, &NativeHol, &target, &witness)
            .unwrap();

        assert_eq!(
            NativeHol.concl(certificate.theorem()),
            identity_translation_proposition().unwrap()
        );
        assert!(NativeHol.hyps(certificate.theorem()).is_empty());
        assert_eq!(
            certificate.metadata.source_bits,
            witness.candidate.source_bits.len()
        );
        assert_eq!(
            certificate.metadata.target_bits,
            witness.candidate.target_bits.len()
        );
    }

    #[test]
    fn replay_rejects_a_forged_target_encoding() {
        let mut witness = search_identity_translation().unwrap();
        witness.candidate.target_bits.push(false);
        let (source, target) = theories();
        assert!(matches!(
            IdentityTranslationReplay
                .replay_simulation(&NativeHol, &source, &NativeHol, &target, &witness),
            Err(IdentityTranslationError::ForgedTarget)
        ));
    }

    #[test]
    fn replay_rejects_forged_cost_accounting() {
        let mut witness = search_identity_translation().unwrap();
        witness.step_mapping.target_steps = 1;
        let (source, target) = theories();
        assert!(matches!(
            IdentityTranslationReplay
                .replay_simulation(&NativeHol, &source, &NativeHol, &target, &witness),
            Err(IdentityTranslationError::WrongStepMapping { .. })
        ));
    }

    #[test]
    fn replay_rejects_a_substituted_source_theory() {
        let witness = search_identity_translation().unwrap();
        let (mut source, target) = theories();
        source.machine = bit_list([false]).unwrap();
        assert!(matches!(
            IdentityTranslationReplay
                .replay_simulation(&NativeHol, &source, &NativeHol, &target, &witness),
            Err(IdentityTranslationError::SourceTheoryMismatch)
        ));
    }
}
