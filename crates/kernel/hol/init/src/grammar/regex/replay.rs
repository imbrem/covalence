//! Checked replay of bounded byte-regex evaluator witnesses.
//!
//! [`covalence_regex_parsing`] performs bounded host search and returns plain
//! data. This module treats that data as entirely untrusted: replay checks the
//! copied regex, input, spans, remainder, and endpoint; reruns bounded
//! evaluation; checks the supplied reified theory term; and finally rebuilds
//! an exact HOL derivation using the regex introduction rules.
//!
//! A successful replay proves only the concrete prefix instance
//!
//! ```text
//! ⊢ Matches ⌜regex⌝ consumed-prefix
//! ```
//!
//! It does not turn budget exhaustion or a missing witness into a theorem of
//! non-membership, and it does not claim soundness or completeness of the host
//! evaluator.
//!
//! @covalence-api-impl {"api":"A0013","name":"BoundedByteRegexReplay","representation":"checked native HOL Matches derivation for one bounded host prefix witness"}

use core::fmt;

use covalence_core::{Error, Term};
use covalence_grammar::Regex;
use covalence_hol_eval::EvalThm;
use covalence_parsing_api::{ByteParseError, ByteParseWitness, ByteParserRelation, ParseBudget};
use covalence_regex_parsing::{ByteRegexParser, RegexMatchWitness};

use super::{compile, tactic};
use crate::init::inductive::hol::{Hol, NativeHol};

/// The caller-supplied object-logic vocabulary for this bounded instance.
///
/// This value carries no authority. Replay compares it with a fresh
/// compilation of the canonical regex before constructing a theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundedByteRegexTheory {
    pub regex: Term,
}

/// Plain-data candidate selected by bounded host evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteRegexReplayWitness {
    pub regex: Regex<u8>,
    pub input: Vec<u8>,
    pub parse: ByteParseWitness<RegexMatchWitness>,
}

/// Auditable metadata paired with the checked theorem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteRegexReplayMetadata {
    pub input_bytes: usize,
    pub consumed_bytes: usize,
}

#[derive(Clone, Debug)]
pub struct ByteRegexReplayCertificate {
    pub theorem: EvalThm,
    pub metadata: ByteRegexReplayMetadata,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ByteRegexReplayError {
    RegexMismatch,
    InputMismatch,
    InvalidSpan,
    EndpointMismatch,
    EvaluatorRejected(ByteParseError),
    ForgedMatch,
    TheoryMismatch,
    ProofConstruction,
}

impl fmt::Display for ByteRegexReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for ByteRegexReplayError {}

/// Compile the canonical regex into the only theory accepted by replay.
pub fn bounded_byte_regex_theory(regex: &Regex<u8>) -> BoundedByteRegexTheory {
    BoundedByteRegexTheory {
        regex: compile(regex),
    }
}

/// Select one accepted prefix using bounded host evaluation.
///
/// The returned candidate is deliberately redundant so replay can reject
/// substitution of the regex, source, span, remainder, or evaluator endpoint.
pub fn search_byte_regex_prefix(
    regex: &Regex<u8>,
    input: &[u8],
    accepting_end: usize,
    budget: ParseBudget,
) -> Result<ByteRegexReplayWitness, ByteRegexReplayError> {
    let parser = ByteRegexParser::new(regex.clone());
    let candidates = parser
        .parse_relational(input, budget)
        .map_err(ByteRegexReplayError::EvaluatorRejected)?;
    let parse = candidates
        .into_iter()
        .map(|(_, witness)| witness)
        .find(|witness| witness.consumed.end == accepting_end)
        .ok_or(ByteRegexReplayError::ForgedMatch)?;
    Ok(ByteRegexReplayWitness {
        regex: regex.clone(),
        input: input.to_vec(),
        parse,
    })
}

/// Replay a host match candidate into an exact, closed HOL theorem.
///
/// `canonical_regex`, `canonical_input`, and `budget` are trusted only as the
/// replay request—not as proof evidence. The HOL theorem itself is rebuilt
/// from existing regex rules and checked by the kernel.
pub fn replay_byte_regex_prefix(
    canonical_regex: &Regex<u8>,
    canonical_input: &[u8],
    budget: ParseBudget,
    theory: &BoundedByteRegexTheory,
    witness: &ByteRegexReplayWitness,
) -> Result<ByteRegexReplayCertificate, ByteRegexReplayError> {
    if &witness.regex != canonical_regex {
        return Err(ByteRegexReplayError::RegexMismatch);
    }
    if witness.input != canonical_input {
        return Err(ByteRegexReplayError::InputMismatch);
    }
    if !witness.parse.is_valid_for(canonical_input.len()) {
        return Err(ByteRegexReplayError::InvalidSpan);
    }
    if witness.parse.evidence.accepting_end != witness.parse.consumed.end {
        return Err(ByteRegexReplayError::EndpointMismatch);
    }

    let expected_theory = bounded_byte_regex_theory(canonical_regex);
    if theory != &expected_theory {
        return Err(ByteRegexReplayError::TheoryMismatch);
    }

    let parser = ByteRegexParser::new(canonical_regex.clone());
    let candidates = parser
        .parse_relational(canonical_input, budget)
        .map_err(ByteRegexReplayError::EvaluatorRejected)?;
    if !candidates
        .iter()
        .any(|(_, candidate)| candidate == &witness.parse)
    {
        return Err(ByteRegexReplayError::ForgedMatch);
    }

    let consumed = &canonical_input[..witness.parse.consumed.end];
    let theorem = tactic::prove_matches(canonical_regex, consumed)
        .map_err(map_kernel_error)?
        .ok_or(ByteRegexReplayError::ProofConstruction)?;
    if NativeHol.hyps(&theorem).is_empty() {
        Ok(ByteRegexReplayCertificate {
            theorem,
            metadata: ByteRegexReplayMetadata {
                input_bytes: canonical_input.len(),
                consumed_bytes: consumed.len(),
            },
        })
    } else {
        Err(ByteRegexReplayError::ProofConstruction)
    }
}

fn map_kernel_error(_: Error) -> ByteRegexReplayError {
    ByteRegexReplayError::ProofConstruction
}

#[cfg(test)]
mod tests {
    use covalence_grammar::parse_regex_u8;

    use super::*;

    const BUDGET: ParseBudget = ParseBudget::new(128, 4_000, 128);

    fn fixture() -> (
        Regex<u8>,
        Vec<u8>,
        BoundedByteRegexTheory,
        ByteRegexReplayWitness,
    ) {
        let regex = parse_regex_u8("a(b|c)+").unwrap();
        let input = b"abc!".to_vec();
        let theory = bounded_byte_regex_theory(&regex);
        let witness = search_byte_regex_prefix(&regex, &input, 3, BUDGET).unwrap();
        (regex, input, theory, witness)
    }

    #[test]
    fn replays_to_the_exact_closed_matches_theorem() {
        let (regex, input, theory, witness) = fixture();
        let certificate =
            replay_byte_regex_prefix(&regex, &input, BUDGET, &theory, &witness).unwrap();
        let independently_rebuilt = tactic::prove_matches(&regex, b"abc").unwrap().unwrap();

        assert_eq!(
            NativeHol.concl(&certificate.theorem),
            NativeHol.concl(&independently_rebuilt)
        );
        assert!(NativeHol.hyps(&certificate.theorem).is_empty());
        assert_eq!(
            certificate.metadata,
            ByteRegexReplayMetadata {
                input_bytes: 4,
                consumed_bytes: 3,
            }
        );
    }

    #[test]
    fn rejects_forged_regex_input_span_endpoint_and_theory() {
        let (regex, input, theory, witness) = fixture();

        let mut forged_regex = witness.clone();
        forged_regex.regex = parse_regex_u8("abc").unwrap();
        assert_eq!(
            replay_byte_regex_prefix(&regex, &input, BUDGET, &theory, &forged_regex).unwrap_err(),
            ByteRegexReplayError::RegexMismatch
        );

        let mut forged_input = witness.clone();
        forged_input.input[0] = b'x';
        assert_eq!(
            replay_byte_regex_prefix(&regex, &input, BUDGET, &theory, &forged_input).unwrap_err(),
            ByteRegexReplayError::InputMismatch
        );

        let mut forged_span = witness.clone();
        forged_span.parse.remainder.start = 2;
        assert_eq!(
            replay_byte_regex_prefix(&regex, &input, BUDGET, &theory, &forged_span).unwrap_err(),
            ByteRegexReplayError::InvalidSpan
        );

        let mut forged_endpoint = witness.clone();
        forged_endpoint.parse.evidence.accepting_end = 2;
        assert_eq!(
            replay_byte_regex_prefix(&regex, &input, BUDGET, &theory, &forged_endpoint)
                .unwrap_err(),
            ByteRegexReplayError::EndpointMismatch
        );

        let forged_theory = BoundedByteRegexTheory {
            regex: compile(&parse_regex_u8("abc").unwrap()),
        };
        assert_eq!(
            replay_byte_regex_prefix(&regex, &input, BUDGET, &forged_theory, &witness).unwrap_err(),
            ByteRegexReplayError::TheoryMismatch
        );
    }

    #[test]
    fn rejects_well_formed_but_unaccepted_prefix() {
        let (regex, input, theory, mut witness) = fixture();
        witness.parse.consumed.end = 1;
        witness.parse.remainder.start = 1;
        witness.parse.evidence.accepting_end = 1;
        assert_eq!(
            replay_byte_regex_prefix(&regex, &input, BUDGET, &theory, &witness).unwrap_err(),
            ByteRegexReplayError::ForgedMatch
        );
    }
}
