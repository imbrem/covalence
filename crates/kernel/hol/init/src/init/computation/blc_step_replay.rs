//! Checked replay for one concrete BLC normal-order beta step.
//!
//! This is intentionally an instance relation, not a claimed definition of
//! universal BLC reduction. For canonical host terms `M` and `N`, the bounded
//! relation on HOL bit strings is
//!
//! `before = encode(M) ∧ after = encode(N)`.
//!
//! Replay re-decodes both untrusted codes, checks `M →β N` using the A0012
//! reference semantics, rejects substituted theory endpoints, and reconstructs
//! the conjunction from kernel reflexivity.
//!
//! @covalence-api-impl {"api":"A0012","name":"NativeHolBoundedStepReplay","representation":"A0010 HOL List<Bool> endpoint relation"}

// TODO(cov:computation.blc-symbolic-reduction, major): Replace bounded replay with proved symbolic decoding, substitution, and reduction over inductive/Nat/Bits APIs.

use core::fmt;

use covalence_computation::blc;
use covalence_core::{Error, Term};
use covalence_kernel_data::BitsSyntax;

use crate::init::inductive::hol::{Hol, NativeHol};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlcStepWitness {
    pub before: Vec<bool>,
    pub after: Vec<bool>,
}

#[derive(Clone, Debug)]
pub struct BlcStepCertificate {
    pub theorem: covalence_hol_eval::EvalThm,
    pub before_bits: usize,
    pub after_bits: usize,
}

#[derive(Clone, Debug)]
pub enum BlcStepReplayError {
    InvalidBefore(blc::DecodeError),
    InvalidAfter(blc::DecodeError),
    NotNormalOrderStep,
    SourceMismatch,
    EndpointMismatch,
    Kernel(Error),
}

impl fmt::Display for BlcStepReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBefore(error) => write!(f, "invalid BLC source code: {error}"),
            Self::InvalidAfter(error) => write!(f, "invalid BLC endpoint code: {error}"),
            Self::NotNormalOrderStep => {
                f.write_str("advertised endpoint is not one normal-order beta step")
            }
            Self::SourceMismatch => f.write_str("source term is not the replay instance source"),
            Self::EndpointMismatch => {
                f.write_str("endpoint term is not the replay instance endpoint")
            }
            Self::Kernel(error) => write!(f, "HOL replay failed: {error}"),
        }
    }
}

impl std::error::Error for BlcStepReplayError {}

impl From<Error> for BlcStepReplayError {
    fn from(error: Error) -> Self {
        Self::Kernel(error)
    }
}

/// Canonical bounded relation proposition for one checked BLC step.
pub fn step_instance_proposition(
    canonical_before: &[bool],
    canonical_after: &[bool],
    before: Term,
    after: Term,
) -> Result<Term, Error> {
    let hol = NativeHol;
    let expected_before = hol.bits_literal(canonical_before)?;
    let expected_after = hol.bits_literal(canonical_after)?;
    hol.and(
        hol.eq(before, expected_before)?,
        hol.eq(after, expected_after)?,
    )
}

/// Validate and replay a concrete BLC step against fixed HOL endpoints.
pub fn replay_step(
    canonical_source: &blc::Term,
    source_endpoint: &Term,
    target_endpoint: &Term,
    witness: &BlcStepWitness,
) -> Result<BlcStepCertificate, BlcStepReplayError> {
    let decoded_before =
        blc::Term::decode(&witness.before).map_err(BlcStepReplayError::InvalidBefore)?;
    let decoded_after =
        blc::Term::decode(&witness.after).map_err(BlcStepReplayError::InvalidAfter)?;
    if &decoded_before != canonical_source {
        return Err(BlcStepReplayError::SourceMismatch);
    }
    if decoded_before.beta_step().as_ref() != Some(&decoded_after) {
        return Err(BlcStepReplayError::NotNormalOrderStep);
    }

    let hol = NativeHol;
    let expected_before = hol.bits_literal(&witness.before)?;
    let expected_after = hol.bits_literal(&witness.after)?;
    if source_endpoint != &expected_before || target_endpoint != &expected_after {
        return Err(BlcStepReplayError::EndpointMismatch);
    }

    let before_eq = hol.refl(expected_before)?;
    let after_eq = hol.refl(expected_after)?;
    let theorem = hol.and_intro(before_eq, after_eq)?;
    Ok(BlcStepCertificate {
        theorem,
        before_bits: witness.before.len(),
        after_bits: witness.after.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nontrivial_step() -> (blc::Term, blc::Term) {
        let body = blc::Term::abs(blc::Term::var(1));
        let argument = blc::Term::abs(blc::Term::var(0));
        let source = blc::Term::app(blc::Term::abs(body), argument);
        let target = source.beta_step().unwrap();
        (source, target)
    }

    #[test]
    fn replays_nontrivial_beta_step_into_exact_relation() {
        let (source, target) = nontrivial_step();
        let witness = BlcStepWitness {
            before: source.encode(),
            after: target.encode(),
        };
        let hol = NativeHol;
        let before = hol.bits_literal(&witness.before).unwrap();
        let after = hol.bits_literal(&witness.after).unwrap();
        let certificate = replay_step(&source, &before, &after, &witness).unwrap();
        assert_eq!(
            hol.concl(&certificate.theorem),
            step_instance_proposition(&witness.before, &witness.after, before, after).unwrap()
        );
        assert!(hol.hyps(&certificate.theorem).is_empty());
    }

    #[test]
    fn rejects_forged_code_and_endpoint() {
        let (source, target) = nontrivial_step();
        let hol = NativeHol;
        let valid = BlcStepWitness {
            before: source.encode(),
            after: target.encode(),
        };
        let before = hol.bits_literal(&valid.before).unwrap();
        let after = hol.bits_literal(&valid.after).unwrap();

        let mut forged_code = valid.clone();
        forged_code.after = blc::Term::var(0).encode();
        assert!(matches!(
            replay_step(&source, &before, &after, &forged_code),
            Err(BlcStepReplayError::NotNormalOrderStep)
        ));

        let forged_endpoint = hol.bits_literal(&[false]).unwrap();
        assert!(matches!(
            replay_step(&source, &before, &forged_endpoint, &valid),
            Err(BlcStepReplayError::EndpointMismatch)
        ));
    }
}
