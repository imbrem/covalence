//! Backend-neutral search and checked replay for bounded byte lexing.
//!
//! A [`ByteLexingWitness`] is deliberately redundant, untrusted data. Replay
//! checks its copied rules, policy, source, emitted tokens, trace, spans, skip
//! decisions, and selected rule indices by rerunning the bounded evaluator.
//! Successful host evaluation alone never constructs theorem evidence.

use core::fmt;

use covalence_grammar::Regex;
use covalence_logic_api::Logic;

use crate::{ByteLexer, LexerBudget, LexerError, LexerPolicy, Lexing, TokenRule};

/// One concrete positive tokenization claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteLexingClaim<K> {
    pub source: Vec<u8>,
    pub lexing: Lexing<K>,
}

/// Redundant plain-data candidate returned by search.
///
/// Rules and policy are copied so replay can reject substitution of matching,
/// priority, tie-breaking, or skip semantics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteLexingWitness<K> {
    pub rules: Vec<TokenRule<K, u8>>,
    pub policy: LexerPolicy,
    pub claim: ByteLexingClaim<K>,
}

/// Backend-selected vocabulary for the canonical rules.
///
/// The carrier is intentionally generic. A proof-free backend can store plain
/// syntax; a logic backend can store reified regex-language terms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteLexerTheory<R> {
    pub rule_languages: Vec<R>,
}

/// Search for one bounded functional tokenization.
///
/// Search returns only untrusted data. In particular, failure or exhausted
/// bounds do not prove that no tokenization exists.
pub trait ByteLexerSearch<K> {
    type Witness;
    type Error;

    fn search_byte_lexing(
        &self,
        rules: &[TokenRule<K, u8>],
        policy: LexerPolicy,
        source: &[u8],
    ) -> Result<Self::Witness, Self::Error>;
}

/// Realize the rule languages in a backend-selected vocabulary.
pub trait ByteLexerTheoryBackend<K> {
    type RuleLanguage;
    type Error;

    fn realize_byte_lexer_theory(
        &self,
        rules: &[TokenRule<K, u8>],
        policy: LexerPolicy,
    ) -> Result<ByteLexerTheory<Self::RuleLanguage>, Self::Error>;
}

/// Replay an untrusted positive tokenization.
///
/// This capability is intentionally independent of theorem production. Its
/// certificate may be checked host data, a collection of per-rule theorems, or
/// eventually one theorem for a reified lexer judgment.
pub trait ByteLexerReplay<K>: ByteLexerTheoryBackend<K> {
    type Witness;
    type Certificate;
    type ReplayError;

    fn replay_byte_lexing(
        &self,
        rules: &[TokenRule<K, u8>],
        policy: LexerPolicy,
        source: &[u8],
        theory: &ByteLexerTheory<Self::RuleLanguage>,
        witness: &Self::Witness,
    ) -> Result<Self::Certificate, Self::ReplayError>;
}

/// Optional projection for certificates carrying per-step rule-membership
/// theorems.
///
/// These theorems certify each positive regex match. They do not by themselves
/// prove the global maximal-munch, priority, tie, skip, or concatenation
/// judgment; a backend must expose a separate whole-lexer theorem for that.
pub trait ByteLexerStepTheorems<L: Logic> {
    fn step_theorems(&self) -> &[L::Thm];
}

/// Proof-free reference search/replay backend.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckedByteLexer {
    pub budget: LexerBudget,
}

/// Syntax-only language realized by the reference backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceRuleLanguage {
    pub regex: Regex<u8>,
}

/// Checked positive result. This is not theorem evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedByteLexing<K> {
    pub claim: ByteLexingClaim<K>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ByteLexerReplayError {
    Build(crate::LexerBuildError),
    Evaluation(LexerError),
    NoTokenization(crate::LexerDiagnostic),
    RulesMismatch,
    PolicyMismatch,
    SourceMismatch,
    TokensMismatch,
    TraceMismatch,
    TheoryMismatch,
}

impl fmt::Display for ByteLexerReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for ByteLexerReplayError {}

impl<K: Clone> ByteLexerSearch<K> for CheckedByteLexer {
    type Witness = ByteLexingWitness<K>;
    type Error = ByteLexerReplayError;

    fn search_byte_lexing(
        &self,
        rules: &[TokenRule<K, u8>],
        policy: LexerPolicy,
        source: &[u8],
    ) -> Result<Self::Witness, Self::Error> {
        let lexing = ByteLexer::new(rules.to_vec(), policy)
            .map_err(ByteLexerReplayError::Build)?
            .lex(source, self.budget)
            .map_err(ByteLexerReplayError::Evaluation)?
            .map_err(ByteLexerReplayError::NoTokenization)?;
        Ok(ByteLexingWitness {
            rules: rules.to_vec(),
            policy,
            claim: ByteLexingClaim {
                source: source.to_vec(),
                lexing,
            },
        })
    }
}

impl<K: Clone> ByteLexerTheoryBackend<K> for CheckedByteLexer {
    type RuleLanguage = ReferenceRuleLanguage;
    type Error = ByteLexerReplayError;

    fn realize_byte_lexer_theory(
        &self,
        rules: &[TokenRule<K, u8>],
        _policy: LexerPolicy,
    ) -> Result<ByteLexerTheory<Self::RuleLanguage>, Self::Error> {
        Ok(ByteLexerTheory {
            rule_languages: rules
                .iter()
                .map(|rule| ReferenceRuleLanguage {
                    regex: rule.regex.clone(),
                })
                .collect(),
        })
    }
}

impl<K: Clone + PartialEq> ByteLexerReplay<K> for CheckedByteLexer {
    type Witness = ByteLexingWitness<K>;
    type Certificate = CheckedByteLexing<K>;
    type ReplayError = ByteLexerReplayError;

    fn replay_byte_lexing(
        &self,
        rules: &[TokenRule<K, u8>],
        policy: LexerPolicy,
        source: &[u8],
        theory: &ByteLexerTheory<Self::RuleLanguage>,
        witness: &Self::Witness,
    ) -> Result<Self::Certificate, Self::ReplayError> {
        if witness.rules != rules {
            return Err(ByteLexerReplayError::RulesMismatch);
        }
        if witness.policy != policy {
            return Err(ByteLexerReplayError::PolicyMismatch);
        }
        if witness.claim.source != source {
            return Err(ByteLexerReplayError::SourceMismatch);
        }
        let expected_theory = self.realize_byte_lexer_theory(rules, policy)?;
        if theory != &expected_theory {
            return Err(ByteLexerReplayError::TheoryMismatch);
        }
        let expected = self.search_byte_lexing(rules, policy, source)?;
        if witness.claim.lexing.tokens != expected.claim.lexing.tokens {
            return Err(ByteLexerReplayError::TokensMismatch);
        }
        if witness.claim.lexing.trace != expected.claim.lexing.trace {
            return Err(ByteLexerReplayError::TraceMismatch);
        }
        Ok(CheckedByteLexing {
            claim: witness.claim.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use covalence_grammar::parse_regex_u8;

    use super::*;
    use crate::{LexerPolicy, SourceSpan, Span};

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Kind {
        Name,
        Space,
    }

    const BUDGET: LexerBudget = LexerBudget::new(64, 2_000, 64, 64, 64, 64);

    fn fixture() -> (
        CheckedByteLexer,
        Vec<TokenRule<Kind, u8>>,
        ByteLexerTheory<ReferenceRuleLanguage>,
        ByteLexingWitness<Kind>,
    ) {
        let backend = CheckedByteLexer { budget: BUDGET };
        let rules = vec![
            TokenRule::token(Kind::Name, parse_regex_u8("[a-z]+").unwrap(), 1),
            TokenRule::skip(Kind::Space, parse_regex_u8(" +").unwrap(), 0),
        ];
        let theory = backend
            .realize_byte_lexer_theory(&rules, LexerPolicy::default())
            .unwrap();
        let witness = backend
            .search_byte_lexing(&rules, LexerPolicy::default(), b"hi there")
            .unwrap();
        (backend, rules, theory, witness)
    }

    #[test]
    fn checked_replay_accepts_the_exact_tokenization() {
        let (backend, rules, theory, witness) = fixture();
        let checked = backend
            .replay_byte_lexing(
                &rules,
                LexerPolicy::default(),
                b"hi there",
                &theory,
                &witness,
            )
            .unwrap();
        assert_eq!(checked.claim, witness.claim);
    }

    #[test]
    fn rejects_forged_rules_source_tokens_trace_extents_and_theory() {
        let (backend, rules, theory, witness) = fixture();

        let mut forged_rules = witness.clone();
        forged_rules.rules[0].priority = 99;
        assert_eq!(
            backend
                .replay_byte_lexing(
                    &rules,
                    LexerPolicy::default(),
                    b"hi there",
                    &theory,
                    &forged_rules,
                )
                .unwrap_err(),
            ByteLexerReplayError::RulesMismatch
        );

        let mut forged_source = witness.clone();
        forged_source.claim.source[0] = b'x';
        assert_eq!(
            backend
                .replay_byte_lexing(
                    &rules,
                    LexerPolicy::default(),
                    b"hi there",
                    &theory,
                    &forged_source,
                )
                .unwrap_err(),
            ByteLexerReplayError::SourceMismatch
        );

        let mut forged_token = witness.clone();
        forged_token.claim.lexing.tokens[0].rule_index = 1;
        assert_eq!(
            backend
                .replay_byte_lexing(
                    &rules,
                    LexerPolicy::default(),
                    b"hi there",
                    &theory,
                    &forged_token,
                )
                .unwrap_err(),
            ByteLexerReplayError::TokensMismatch
        );

        let mut forged_trace = witness.clone();
        forged_trace.claim.lexing.trace[1].skipped = false;
        assert_eq!(
            backend
                .replay_byte_lexing(
                    &rules,
                    LexerPolicy::default(),
                    b"hi there",
                    &theory,
                    &forged_trace,
                )
                .unwrap_err(),
            ByteLexerReplayError::TraceMismatch
        );

        let mut forged_extent = witness.clone();
        forged_extent.claim.lexing.trace[0].span = SourceSpan {
            units: Span::new(0, 1).unwrap(),
            bytes: Some(Span::new(0, 1).unwrap()),
        };
        assert_eq!(
            backend
                .replay_byte_lexing(
                    &rules,
                    LexerPolicy::default(),
                    b"hi there",
                    &theory,
                    &forged_extent,
                )
                .unwrap_err(),
            ByteLexerReplayError::TraceMismatch
        );

        let mut forged_theory = theory;
        forged_theory.rule_languages.swap(0, 1);
        assert_eq!(
            backend
                .replay_byte_lexing(
                    &rules,
                    LexerPolicy::default(),
                    b"hi there",
                    &forged_theory,
                    &witness,
                )
                .unwrap_err(),
            ByteLexerReplayError::TheoryMismatch
        );
    }
}
