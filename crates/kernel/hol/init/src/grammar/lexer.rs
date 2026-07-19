//! Checked NativeHol replay of bounded A0016 byte-lexer traces.
//!
//! Replay first validates the complete functional tokenization using A0016's
//! proof-free checker, then rebuilds a closed HOL `Matches` theorem for every
//! selected rule segment using A0013 regex replay. The returned theorem vector
//! is aligned with the trace, including skipped rules.
//!
//! Whole-instance replay additionally conjoins those membership theorems with
//! literal records of every host-checked policy decision and extent. That
//! proposition is exact and closed, but deliberately is not advertised as a
//! universal theorem of lexical analysis: NativeHol does not yet quantify over
//! rival tokenizations inside the object logic.
//!
//! @covalence-api-impl {"api":"A0016","name":"BoundedByteLexerReplay","representation":"checked functional trace, closed native HOL Matches theorems, and an exact closed whole-instance record"}

use core::fmt;

use covalence_core::{Term, Type};
use covalence_hol_eval::EvalThm;
use covalence_lexer_parsing::replay::{
    ByteLexerReplay, ByteLexerReplayError, ByteLexerStepTheorems, ByteLexerTheory,
    ByteLexerTheoryBackend, ByteLexingWitness, CheckedByteLexer,
};
use covalence_lexer_parsing::{LexerBudget, LexerPolicy, TiePolicy, TokenRule};
use covalence_parsing_api::{ByteRegexLanguageBackend, ByteRegexLanguageTheory, ParseBudget};

use super::regex::replay::{
    BoundedByteRegexReplay, ByteRegexReplayError, bounded_byte_regex_theory,
    replay_byte_regex_prefix, search_byte_regex_prefix,
};
use crate::init::inductive::hol::{Hol, NativeHol};

/// Native backend for one bounded functional lexing instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundedByteLexerReplay {
    pub lexer_budget: LexerBudget,
}

impl BoundedByteLexerReplay {
    fn regex_budget(&self) -> ParseBudget {
        ParseBudget::new(
            self.lexer_budget.max_source_units,
            self.lexer_budget.regex_fuel,
            self.lexer_budget.max_regex_results,
        )
    }

    /// Replay and reify one exact bounded functional lexer instance.
    pub fn replay_whole_byte_lexing<K: Clone + PartialEq + NativeLexerKind>(
        &self,
        rules: &[TokenRule<K, u8>],
        policy: LexerPolicy,
        source: &[u8],
        theory: &ByteLexerTheory<ByteRegexLanguageTheory<NativeHol>>,
        witness: &ByteLexingWitness<K>,
    ) -> Result<WholeByteLexerReplayCertificate<K>, NativeByteLexerReplayError> {
        ensure_kind_codes_injective(rules)?;
        let checked = self.replay_byte_lexing(rules, policy, source, theory, witness)?;

        let mut conjuncts = checked.rule_matches.clone();
        for language in &theory.rule_languages {
            conjuncts.push(
                EvalThm::refl(language.regex.clone())
                    .map_err(|_| NativeByteLexerReplayError::ProofConstruction)?,
            );
        }
        let facts = [
            encode_rules(rules),
            vec![tie_code(policy.tie)],
            source.iter().map(|byte| u64::from(*byte)).collect(),
            encode_tokens(&witness.claim.lexing.tokens),
            encode_trace(&witness.claim.lexing.trace),
            encode_selections(rules, &witness.claim.lexing.trace)?,
            encode_coverage(source.len(), &witness.claim.lexing.trace)?,
        ];
        for fact in facts {
            let literal =
                nat_list(fact).map_err(|_| NativeByteLexerReplayError::ProofConstruction)?;
            conjuncts.push(
                EvalThm::refl(literal)
                    .map_err(|_| NativeByteLexerReplayError::ProofConstruction)?,
            );
        }
        let theorem = crate::metalogic::conj_thms(conjuncts)
            .map_err(|_| NativeByteLexerReplayError::ProofConstruction)?;
        if !NativeHol.hyps(&theorem).is_empty() {
            return Err(NativeByteLexerReplayError::ProofConstruction);
        }
        Ok(WholeByteLexerReplayCertificate { checked, theorem })
    }
}

fn ensure_kind_codes_injective<K: PartialEq + NativeLexerKind>(
    rules: &[TokenRule<K, u8>],
) -> Result<(), NativeByteLexerReplayError> {
    for (i, left) in rules.iter().enumerate() {
        for right in &rules[i + 1..] {
            if left.kind != right.kind
                && left.kind.lexer_kind_code() == right.kind.lexer_kind_code()
            {
                return Err(NativeByteLexerReplayError::KindEncodingCollision);
            }
        }
    }
    Ok(())
}

fn nat_list(values: Vec<u64>) -> Result<Term, covalence_core::Error> {
    crate::init::list::list_of(
        &Type::nat(),
        values.into_iter().map(covalence_hol_eval::mk_nat).collect(),
    )
}

fn encode_rules<K: NativeLexerKind>(rules: &[TokenRule<K, u8>]) -> Vec<u64> {
    let mut out = vec![rules.len() as u64];
    for (index, rule) in rules.iter().enumerate() {
        out.extend([
            index as u64,
            rule.kind.lexer_kind_code(),
            u64::from(rule.priority),
            u64::from(rule.skip),
        ]);
    }
    out
}

fn tie_code(tie: TiePolicy) -> u64 {
    match tie {
        TiePolicy::EarlierRule => 0,
        TiePolicy::LaterRule => 1,
        TiePolicy::RejectAmbiguous => 2,
    }
}

fn encode_span(out: &mut Vec<u64>, span: covalence_lexer_parsing::SourceSpan) {
    out.extend([span.units.start as u64, span.units.end as u64]);
    match span.bytes {
        Some(bytes) => out.extend([1, bytes.start as u64, bytes.end as u64]),
        None => out.extend([0, 0, 0]),
    }
}

fn encode_tokens<K: NativeLexerKind>(
    tokens: &[covalence_lexer_parsing::SpannedToken<K>],
) -> Vec<u64> {
    let mut out = vec![tokens.len() as u64];
    for token in tokens {
        out.extend([token.rule_index as u64, token.kind.lexer_kind_code()]);
        encode_span(&mut out, token.span);
    }
    out
}

fn encode_trace(trace: &[covalence_lexer_parsing::LexStep]) -> Vec<u64> {
    let mut out = vec![trace.len() as u64];
    for step in trace {
        out.extend([step.rule_index as u64, u64::from(step.skipped)]);
        encode_span(&mut out, step.span);
    }
    out
}

fn encode_selections<K>(
    rules: &[TokenRule<K, u8>],
    trace: &[covalence_lexer_parsing::LexStep],
) -> Result<Vec<u64>, NativeByteLexerReplayError> {
    let mut out = vec![trace.len() as u64];
    for step in trace {
        let rule =
            rules
                .get(step.rule_index)
                .ok_or(NativeByteLexerReplayError::InvalidRuleIndex {
                    rule_index: step.rule_index,
                })?;
        out.extend([
            step.span.units.start as u64,
            (step.span.units.end - step.span.units.start) as u64,
            u64::from(rule.priority),
            step.rule_index as u64,
        ]);
    }
    Ok(out)
}

fn encode_coverage(
    source_len: usize,
    trace: &[covalence_lexer_parsing::LexStep],
) -> Result<Vec<u64>, NativeByteLexerReplayError> {
    let mut out = vec![source_len as u64, trace.len() as u64];
    let mut cursor = 0;
    for step in trace {
        if step.span.units.start != cursor {
            return Err(NativeByteLexerReplayError::InvalidByteSpan);
        }
        out.extend([cursor as u64, step.span.units.end as u64]);
        cursor = step.span.units.end;
    }
    if cursor != source_len {
        return Err(NativeByteLexerReplayError::InvalidByteSpan);
    }
    out.push(cursor as u64);
    Ok(out)
}

/// Checked trace plus one closed theorem for every trace step.
#[derive(Clone, Debug)]
pub struct ByteLexerReplayCertificate<K> {
    pub witness: ByteLexingWitness<K>,
    pub rule_matches: Vec<EvalThm>,
}

/// Stable, injective numeric encoding of a finite token-kind vocabulary.
pub trait NativeLexerKind {
    fn lexer_kind_code(&self) -> u64;
}

/// One closed theorem recording the complete checked lexer instance.
///
/// The right-nested conjunction contains the real `Matches` theorem for every
/// trace step, followed by literal facts for ordered rule languages and
/// metadata, policy, source, emitted tokens, the emitted-plus-skipped trace,
/// selection decisions, spans, and contiguous source coverage.
#[derive(Clone, Debug)]
pub struct WholeByteLexerReplayCertificate<K> {
    pub checked: ByteLexerReplayCertificate<K>,
    pub theorem: EvalThm,
}

impl<K> ByteLexerStepTheorems<NativeHol> for ByteLexerReplayCertificate<K> {
    fn step_theorems(&self) -> &[EvalThm] {
        &self.rule_matches
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeByteLexerReplayError {
    Checked(ByteLexerReplayError),
    Regex(ByteRegexReplayError),
    InvalidRuleIndex { rule_index: usize },
    InvalidByteSpan,
    KindEncodingCollision,
    ProofConstruction,
}

impl fmt::Display for NativeByteLexerReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for NativeByteLexerReplayError {}

impl<K> ByteLexerTheoryBackend<K> for BoundedByteLexerReplay {
    type RuleLanguage = ByteRegexLanguageTheory<NativeHol>;
    type Error = NativeByteLexerReplayError;

    fn realize_byte_lexer_theory(
        &self,
        rules: &[TokenRule<K, u8>],
        _policy: LexerPolicy,
    ) -> Result<ByteLexerTheory<Self::RuleLanguage>, Self::Error> {
        let regex_backend = BoundedByteRegexReplay {
            budget: self.regex_budget(),
        };
        let mut rule_languages = Vec::with_capacity(rules.len());
        for rule in rules {
            rule_languages.push(
                regex_backend
                    .realize_regex_language(&NativeHol, &rule.regex)
                    .map_err(NativeByteLexerReplayError::Regex)?,
            );
        }
        Ok(ByteLexerTheory { rule_languages })
    }
}

impl<K: Clone + PartialEq> ByteLexerReplay<K> for BoundedByteLexerReplay {
    type Witness = ByteLexingWitness<K>;
    type Certificate = ByteLexerReplayCertificate<K>;
    type ReplayError = NativeByteLexerReplayError;

    fn replay_byte_lexing(
        &self,
        rules: &[TokenRule<K, u8>],
        policy: LexerPolicy,
        source: &[u8],
        theory: &ByteLexerTheory<Self::RuleLanguage>,
        witness: &Self::Witness,
    ) -> Result<Self::Certificate, Self::ReplayError> {
        let checker = CheckedByteLexer {
            budget: self.lexer_budget,
        };
        let reference_theory = checker
            .realize_byte_lexer_theory(rules, policy)
            .map_err(NativeByteLexerReplayError::Checked)?;
        checker
            .replay_byte_lexing(rules, policy, source, &reference_theory, witness)
            .map_err(NativeByteLexerReplayError::Checked)?;

        let expected_theory = self.realize_byte_lexer_theory(rules, policy)?;
        if theory != &expected_theory {
            return Err(NativeByteLexerReplayError::Checked(
                ByteLexerReplayError::TheoryMismatch,
            ));
        }

        let mut rule_matches = Vec::with_capacity(witness.claim.lexing.trace.len());
        for step in &witness.claim.lexing.trace {
            let rule =
                rules
                    .get(step.rule_index)
                    .ok_or(NativeByteLexerReplayError::InvalidRuleIndex {
                        rule_index: step.rule_index,
                    })?;
            if step.span.bytes != Some(step.span.units)
                || step.span.units.end > source.len()
                || step.span.units.start >= step.span.units.end
            {
                return Err(NativeByteLexerReplayError::InvalidByteSpan);
            }
            let suffix = &source[step.span.units.start..];
            let consumed = step.span.units.end - step.span.units.start;
            let match_witness =
                search_byte_regex_prefix(&rule.regex, suffix, consumed, self.regex_budget())
                    .map_err(NativeByteLexerReplayError::Regex)?;
            let certificate = replay_byte_regex_prefix(
                &rule.regex,
                suffix,
                self.regex_budget(),
                &theory.rule_languages[step.rule_index],
                &match_witness,
            )
            .map_err(NativeByteLexerReplayError::Regex)?;
            rule_matches.push(certificate.theorem);
        }

        Ok(ByteLexerReplayCertificate {
            witness: witness.clone(),
            rule_matches,
        })
    }
}

// TODO(cov:parsing.lexer.native-hol-universal-semantics, major): Define and
// prove universal HOL lexer semantics; the closed instance record carries
// every checked decision but does not quantify over rival tokenizations.

#[cfg(test)]
mod tests {
    use covalence_grammar::parse_regex_u8;
    use covalence_lexer_parsing::replay::ByteLexerSearch;
    use covalence_lexer_parsing::{LexerPolicy, SourceSpan};

    use super::*;
    use crate::init::inductive::hol::Hol;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Kind {
        Name,
        Space,
    }

    impl NativeLexerKind for Kind {
        fn lexer_kind_code(&self) -> u64 {
            match self {
                Self::Name => 0,
                Self::Space => 1,
            }
        }
    }

    const BUDGET: LexerBudget = LexerBudget::new(64, 2_000, 64, 64, 64, 64);

    fn fixture() -> (
        BoundedByteLexerReplay,
        Vec<TokenRule<Kind, u8>>,
        ByteLexerTheory<ByteRegexLanguageTheory<NativeHol>>,
        ByteLexingWitness<Kind>,
    ) {
        let backend = BoundedByteLexerReplay {
            lexer_budget: BUDGET,
        };
        let rules = vec![
            TokenRule::token(Kind::Name, parse_regex_u8("[a-z]+").unwrap(), 1),
            TokenRule::skip(Kind::Space, parse_regex_u8(" +").unwrap(), 0),
        ];
        let theory = backend
            .realize_byte_lexer_theory(&rules, LexerPolicy::default())
            .unwrap();
        let witness = CheckedByteLexer { budget: BUDGET }
            .search_byte_lexing(&rules, LexerPolicy::default(), b"hi there")
            .unwrap();
        (backend, rules, theory, witness)
    }

    #[test]
    fn replays_each_selected_and_skipped_segment_to_closed_hol() {
        let (backend, rules, theory, witness) = fixture();
        let certificate = backend
            .replay_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &theory,
                &witness,
            )
            .unwrap();
        assert_eq!(certificate.rule_matches.len(), 3);
        assert!(
            certificate
                .rule_matches
                .iter()
                .all(|theorem| NativeHol.hyps(theorem).is_empty())
        );
    }

    #[test]
    fn replays_one_exact_closed_whole_instance_theorem() {
        let (backend, rules, theory, witness) = fixture();
        let certificate = backend
            .replay_whole_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &theory,
                &witness,
            )
            .unwrap();
        assert_eq!(certificate.checked.rule_matches.len(), 3);
        assert!(NativeHol.hyps(&certificate.theorem).is_empty());
        assert_eq!(certificate.checked.witness, witness);
    }

    #[test]
    fn whole_replay_rejects_substituted_policy() {
        let (backend, rules, theory, witness) = fixture();
        let substituted = LexerPolicy {
            tie: TiePolicy::LaterRule,
        };
        assert!(matches!(
            backend.replay_whole_byte_lexing(&rules, substituted, b"hi there", &theory, &witness,),
            Err(NativeByteLexerReplayError::Checked(
                ByteLexerReplayError::PolicyMismatch
            ))
        ));
    }

    #[test]
    fn rejects_forged_rule_source_token_trace_extent_and_theory() {
        let (backend, rules, theory, witness) = fixture();

        let mut forged_rule = witness.clone();
        forged_rule.rules[1].skip = false;
        assert!(matches!(
            backend.replay_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &theory,
                &forged_rule,
            ),
            Err(NativeByteLexerReplayError::Checked(
                ByteLexerReplayError::RulesMismatch
            ))
        ));

        let mut forged_source = witness.clone();
        forged_source.claim.source[0] = b'x';
        assert!(matches!(
            backend.replay_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &theory,
                &forged_source,
            ),
            Err(NativeByteLexerReplayError::Checked(
                ByteLexerReplayError::SourceMismatch
            ))
        ));

        let mut forged_token = witness.clone();
        forged_token.claim.lexing.tokens[0].rule_index = 1;
        assert!(matches!(
            backend.replay_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &theory,
                &forged_token,
            ),
            Err(NativeByteLexerReplayError::Checked(
                ByteLexerReplayError::TokensMismatch
            ))
        ));

        let mut forged_trace = witness.clone();
        forged_trace.claim.lexing.trace[1].skipped = false;
        assert!(matches!(
            backend.replay_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &theory,
                &forged_trace,
            ),
            Err(NativeByteLexerReplayError::Checked(
                ByteLexerReplayError::TraceMismatch
            ))
        ));

        let mut forged_extent = witness.clone();
        forged_extent.claim.lexing.trace[0].span = SourceSpan {
            units: covalence_parsing_api::Span::new(0, 1).unwrap(),
            bytes: Some(covalence_parsing_api::Span::new(0, 1).unwrap()),
        };
        assert!(matches!(
            backend.replay_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &theory,
                &forged_extent,
            ),
            Err(NativeByteLexerReplayError::Checked(
                ByteLexerReplayError::TraceMismatch
            ))
        ));

        let mut forged_theory = theory;
        forged_theory.rule_languages[0] =
            bounded_byte_regex_theory(&covalence_grammar::Regex::lit(b'x'));
        assert!(matches!(
            backend.replay_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &forged_theory,
                &witness,
            ),
            Err(NativeByteLexerReplayError::Checked(
                ByteLexerReplayError::TheoryMismatch
            ))
        ));
    }
}
