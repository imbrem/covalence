//! Checked NativeHol replay of bounded A0016 byte-lexer traces.
//!
//! Replay first validates the complete functional tokenization using A0016's
//! proof-free checker, then rebuilds a closed HOL `Matches` theorem for every
//! selected rule segment using A0013 regex replay. The returned theorem vector
//! is aligned with the trace, including skipped rules.
//!
//! This is deliberately not advertised as one theorem of lexical analysis:
//! NativeHol does not yet reify maximal munch, rule priority, tie-breaking,
//! skipping, spans, or trace concatenation as an object-language relation.
//!
//! @covalence-api-impl {"api":"A0016","name":"BoundedByteLexerReplay","representation":"checked functional trace plus one closed native HOL Matches theorem per selected segment"}

use core::fmt;

use covalence_hol_eval::EvalThm;
use covalence_lexer_parsing::replay::{
    ByteLexerReplay, ByteLexerReplayError, ByteLexerStepTheorems, ByteLexerTheory,
    ByteLexerTheoryBackend, ByteLexingWitness, CheckedByteLexer,
};
use covalence_lexer_parsing::{LexerBudget, LexerPolicy, TokenRule};
use covalence_parsing_api::{ByteRegexLanguageBackend, ByteRegexLanguageTheory, ParseBudget};

use super::regex::replay::{
    BoundedByteRegexReplay, ByteRegexReplayError, bounded_byte_regex_theory,
    replay_byte_regex_prefix, search_byte_regex_prefix,
};
use crate::init::inductive::hol::NativeHol;

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
}

/// Checked trace plus one closed theorem for every trace step.
#[derive(Clone, Debug)]
pub struct ByteLexerReplayCertificate<K> {
    pub witness: ByteLexingWitness<K>,
    pub rule_matches: Vec<EvalThm>,
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

// TODO(cov:parsing.lexer.native-hol-whole-judgment, major): Reify the functional
// lexer relation (rule order, maximal munch, priority, ties, skipping, spans,
// and trace concatenation) and replay one exact closed theorem rather than only
// its per-step regex membership premises.

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
