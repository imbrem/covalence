//! Bounded parsing over raw bytes.
//!
//! This layer does not decode characters. It separates declarative parser
//! syntax, host evaluation, relational enumeration, and proof-bearing laws.
//! Host witnesses are ordinary data and confer no theorem authority.
//!
//! @covalence-api {"id":"A0013","title":"Parsing over raw bytes","status":"experimental","dependsOn":["A0001","A0003"]}

use covalence_logic_api::Logic;

/// A half-open byte range `[start, end)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ByteSpan {
    pub start: usize,
    pub end: usize,
}

impl ByteSpan {
    pub fn new(start: usize, end: usize) -> Option<Self> {
        (start <= end).then_some(Self { start, end })
    }

    pub fn len(self) -> usize {
        self.end - self.start
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }
}

/// Bounds that make host parser behavior predictable under hostile inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseBudget {
    pub max_input_bytes: usize,
    /// Parser-specific work units. A literal comparison consumes one unit.
    pub fuel: usize,
    /// Maximum number of positive results returned by relational evaluation.
    pub max_results: usize,
}

impl ParseBudget {
    pub const fn new(max_input_bytes: usize, fuel: usize, max_results: usize) -> Self {
        Self {
            max_input_bytes,
            fuel,
            max_results,
        }
    }
}

/// A positive parse records exactly what was consumed and what remains.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteParseWitness<W> {
    pub consumed: ByteSpan,
    pub remainder: ByteSpan,
    pub evidence: W,
}

impl<W> ByteParseWitness<W> {
    pub fn prefix(input_len: usize, consumed_len: usize, evidence: W) -> Option<Self> {
        (consumed_len <= input_len).then_some(Self {
            consumed: ByteSpan {
                start: 0,
                end: consumed_len,
            },
            remainder: ByteSpan {
                start: consumed_len,
                end: input_len,
            },
            evidence,
        })
    }

    pub fn is_valid_for(&self, input_len: usize) -> bool {
        self.consumed.start == 0
            && self.consumed.end == self.remainder.start
            && self.remainder.end == input_len
            && self.consumed.end <= input_len
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseFailure {
    NoMatch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteParseDiagnostic {
    pub span: ByteSpan,
    pub failure: ParseFailure,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ByteParseError {
    InputTooLarge { actual: usize, limit: usize },
    FuelExhausted { required: usize, available: usize },
    ResultLimitExceeded { limit: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ByteParseOutcome<V, W> {
    Match {
        value: V,
        witness: ByteParseWitness<W>,
    },
    NoMatch(ByteParseDiagnostic),
}

/// Partial functional evaluation of a raw-byte parser.
pub trait ByteParser {
    type Value;
    type Witness;

    fn parse_bytes(
        &self,
        input: &[u8],
        budget: ParseBudget,
    ) -> Result<ByteParseOutcome<Self::Value, Self::Witness>, ByteParseError>;
}

/// Bounded enumeration of a parsing relation.
///
/// An empty vector is not a proof that no interpretation exists.
pub trait ByteParserRelation {
    type Value;
    type Witness;

    fn parse_relational(
        &self,
        input: &[u8],
        budget: ParseBudget,
    ) -> Result<Vec<(Self::Value, ByteParseWitness<Self::Witness>)>, ByteParseError>;
}

/// Object-language vocabulary supplied by a logic backend.
pub trait ByteParserTheory<L: Logic> {
    fn parser_type(&self, logic: &L) -> L::Type;
    fn value_type(&self, logic: &L) -> L::Type;
    /// `parses parser source consumed remainder value`.
    fn parses_relation(&self, logic: &L) -> L::Term;
    /// The partial equivalence relation induced by denoting the same value.
    fn same_value_relation(&self, logic: &L) -> L::Term;
}

/// Terms participating in one positive object-language parse judgment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteParseJudgment<L: Logic> {
    pub parser: L::Term,
    pub source: L::Term,
    pub consumed: L::Term,
    pub remainder: L::Term,
    pub value: L::Term,
}

/// Supplied proof objects. Merely evaluating a host parser cannot construct
/// this bundle.
pub trait ByteParseLaws<L: Logic>: ByteParserTheory<L> {
    /// Host/backend-specific universal soundness statement.
    fn soundness(&self, logic: &L) -> Result<L::Thm, L::Error>;
    /// Completeness is deliberately independent from soundness.
    fn completeness(&self, logic: &L) -> Result<L::Thm, L::Error>;
    fn same_value_reflexive_on_valid(&self, logic: &L) -> Result<L::Thm, L::Error>;
    fn same_value_symmetric(&self, logic: &L) -> Result<L::Thm, L::Error>;
    fn same_value_transitive(&self, logic: &L) -> Result<L::Thm, L::Error>;
}

/// Backend-selected object-language carriers for a byte-regex language.
///
/// This is syntax, not evidence: the terms may be inspected or substituted by
/// untrusted callers, and a replay backend must validate them before returning
/// any proof-bearing certificate.
#[derive(Clone, Debug)]
pub struct ByteRegexLanguageTheory<L: Logic> {
    pub regex_type: L::Type,
    pub word_type: L::Type,
    pub regex: L::Term,
}

impl<L: Logic> PartialEq for ByteRegexLanguageTheory<L> {
    fn eq(&self, other: &Self) -> bool {
        self.regex_type == other.regex_type
            && self.word_type == other.word_type
            && self.regex == other.regex
    }
}

impl<L: Logic> Eq for ByteRegexLanguageTheory<L> {}

/// Interpret a host regex specification into one logic backend.
///
/// Keeping `Specification` generic lets the neutral parsing layer avoid
/// depending on a particular grammar AST. Implementations may use
/// `covalence_grammar::Regex<u8>`, a content-addressed syntax object, or a
/// different equivalent representation.
pub trait ByteRegexLanguageBackend<L: Logic, Specification: ?Sized> {
    type Error;

    fn realize_regex_language(
        &self,
        logic: &L,
        specification: &Specification,
    ) -> Result<ByteRegexLanguageTheory<L>, Self::Error>;
}

/// Replay one untrusted positive match candidate.
///
/// This capability deliberately says nothing about failed search and does not
/// imply either universal soundness or completeness. A proof backend should
/// recompute/check the witness and the supplied theory before constructing its
/// certificate.
pub trait ByteRegexMembershipReplay<L: Logic, Specification: ?Sized, Witness: ?Sized>:
    ByteRegexLanguageBackend<L, Specification>
{
    type Certificate;
    type ReplayError;

    fn replay_regex_membership(
        &self,
        logic: &L,
        specification: &Specification,
        input: &[u8],
        theory: &ByteRegexLanguageTheory<L>,
        witness: &Witness,
    ) -> Result<Self::Certificate, Self::ReplayError>;
}

/// Optional projection for replay certificates that actually contain a
/// backend theorem.
///
/// Proof-free checkers intentionally need not implement this trait.
pub trait ByteRegexMembershipCertificate<L: Logic> {
    fn membership_theorem(&self) -> &L::Thm;
}

/// Convenience marker for theorem-producing replay backends.
pub trait TheoremByteRegexMembershipReplay<L: Logic, Specification: ?Sized, Witness: ?Sized>:
    ByteRegexMembershipReplay<L, Specification, Witness>
where
    Self::Certificate: ByteRegexMembershipCertificate<L>,
{
}

impl<L, Specification, Witness, Replay> TheoremByteRegexMembershipReplay<L, Specification, Witness>
    for Replay
where
    L: Logic,
    Specification: ?Sized,
    Witness: ?Sized,
    Replay: ByteRegexMembershipReplay<L, Specification, Witness>,
    Replay::Certificate: ByteRegexMembershipCertificate<L>,
{
}

/// Optional universal laws for a realized regex language.
///
/// These are separate from [`ByteRegexMembershipReplay`]: supporting checked
/// concrete instances does not grant a theorem quantifying over all words.
/// Soundness and completeness remain separate methods so a backend can expose
/// either result without claiming the other.
pub trait ByteRegexLanguageLaws<L: Logic> {
    fn derivation_soundness(
        &self,
        logic: &L,
        theory: &ByteRegexLanguageTheory<L>,
    ) -> Result<L::Thm, L::Error>;

    fn derivation_completeness(
        &self,
        logic: &L,
        theory: &ByteRegexLanguageTheory<L>,
    ) -> Result<L::Thm, L::Error>;
}

/// Dependency-light reference parser for one fixed byte prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralBytes {
    expected: Vec<u8>,
}

impl LiteralBytes {
    pub fn new(expected: impl Into<Vec<u8>>) -> Self {
        Self {
            expected: expected.into(),
        }
    }

    pub fn expected(&self) -> &[u8] {
        &self.expected
    }

    fn check_limits(&self, input: &[u8], budget: ParseBudget) -> Result<(), ByteParseError> {
        if input.len() > budget.max_input_bytes {
            return Err(ByteParseError::InputTooLarge {
                actual: input.len(),
                limit: budget.max_input_bytes,
            });
        }
        if self.expected.len() > budget.fuel {
            return Err(ByteParseError::FuelExhausted {
                required: self.expected.len(),
                available: budget.fuel,
            });
        }
        Ok(())
    }
}

impl ByteParser for LiteralBytes {
    type Value = Vec<u8>;
    type Witness = ();

    fn parse_bytes(
        &self,
        input: &[u8],
        budget: ParseBudget,
    ) -> Result<ByteParseOutcome<Vec<u8>, ()>, ByteParseError> {
        self.check_limits(input, budget)?;
        if input.starts_with(&self.expected) {
            return Ok(ByteParseOutcome::Match {
                value: self.expected.clone(),
                witness: ByteParseWitness::prefix(input.len(), self.expected.len(), ())
                    .expect("starts_with implies a valid prefix"),
            });
        }
        let mismatch = self
            .expected
            .iter()
            .zip(input)
            .position(|(expected, actual)| expected != actual)
            .unwrap_or(input.len().min(self.expected.len()));
        Ok(ByteParseOutcome::NoMatch(ByteParseDiagnostic {
            span: ByteSpan {
                start: mismatch,
                end: (mismatch + 1).min(input.len()),
            },
            failure: ParseFailure::NoMatch,
        }))
    }
}

impl ByteParserRelation for LiteralBytes {
    type Value = Vec<u8>;
    type Witness = ();

    fn parse_relational(
        &self,
        input: &[u8],
        budget: ParseBudget,
    ) -> Result<Vec<(Vec<u8>, ByteParseWitness<()>)>, ByteParseError> {
        match self.parse_bytes(input, budget)? {
            ByteParseOutcome::Match { value, witness } => {
                if budget.max_results == 0 {
                    Err(ByteParseError::ResultLimitExceeded { limit: 0 })
                } else {
                    Ok(vec![(value, witness)])
                }
            }
            ByteParseOutcome::NoMatch(_) => Ok(Vec::new()),
        }
    }
}

// TODO(cov:parsing.bytes.cfg-integration, major): Interpret CFG and PEG derivations as bounded A0013 relational witnesses with ambiguity and completeness tracked explicitly.

#[cfg(test)]
mod tests {
    use core::convert::Infallible;

    use super::*;

    const BUDGET: ParseBudget = ParseBudget::new(64, 64, 4);

    #[derive(Clone, Copy, Debug)]
    struct SymbolicLogic;

    impl Logic for SymbolicLogic {
        type Kind = ();
        type Type = &'static str;
        type Term = Vec<u8>;
        type Thm = Infallible;
        type Error = Infallible;
    }

    /// Proof-free reference adapter: a byte slice specifies its singleton
    /// literal language. This demonstrates that replay capability shape does
    /// not itself mint or require theorem values.
    struct LiteralLanguageReplay;

    impl ByteRegexLanguageBackend<SymbolicLogic, [u8]> for LiteralLanguageReplay {
        type Error = Infallible;

        fn realize_regex_language(
            &self,
            _logic: &SymbolicLogic,
            specification: &[u8],
        ) -> Result<ByteRegexLanguageTheory<SymbolicLogic>, Self::Error> {
            Ok(ByteRegexLanguageTheory {
                regex_type: "literal-byte-regex",
                word_type: "bytes",
                regex: specification.to_vec(),
            })
        }
    }

    impl ByteRegexMembershipReplay<SymbolicLogic, [u8], ByteParseWitness<()>>
        for LiteralLanguageReplay
    {
        type Certificate = ByteSpan;
        type ReplayError = &'static str;

        fn replay_regex_membership(
            &self,
            _logic: &SymbolicLogic,
            specification: &[u8],
            input: &[u8],
            theory: &ByteRegexLanguageTheory<SymbolicLogic>,
            witness: &ByteParseWitness<()>,
        ) -> Result<Self::Certificate, Self::ReplayError> {
            let expected = self
                .realize_regex_language(&SymbolicLogic, specification)
                .expect("infallible reference realization");
            if theory != &expected || !witness.is_valid_for(input.len()) {
                return Err("substituted theory or invalid span");
            }
            if witness.consumed.end != specification.len() || !input.starts_with(specification) {
                return Err("not a member of the literal language");
            }
            Ok(witness.consumed)
        }
    }

    #[test]
    fn literal_reports_consumed_prefix_and_remainder() {
        let parsed = LiteralBytes::new(b"let".to_vec())
            .parse_bytes(b"let x", BUDGET)
            .unwrap();
        let ByteParseOutcome::Match { value, witness } = parsed else {
            panic!("expected match");
        };
        assert_eq!(value, b"let");
        assert_eq!(witness.consumed, ByteSpan { start: 0, end: 3 });
        assert_eq!(witness.remainder, ByteSpan { start: 3, end: 5 });
        assert!(witness.is_valid_for(5));
    }

    #[test]
    fn limits_are_explicit_and_checked_before_parsing() {
        let parser = LiteralBytes::new(b"abc".to_vec());
        assert_eq!(
            parser.parse_bytes(b"abc", ParseBudget::new(2, 99, 1)),
            Err(ByteParseError::InputTooLarge {
                actual: 3,
                limit: 2
            })
        );
        assert_eq!(
            parser.parse_bytes(b"abc", ParseBudget::new(3, 2, 1)),
            Err(ByteParseError::FuelExhausted {
                required: 3,
                available: 2
            })
        );
    }

    #[test]
    fn mismatch_has_a_source_span() {
        let parsed = LiteralBytes::new(b"abc".to_vec())
            .parse_bytes(b"ax", BUDGET)
            .unwrap();
        assert_eq!(
            parsed,
            ByteParseOutcome::NoMatch(ByteParseDiagnostic {
                span: ByteSpan { start: 1, end: 2 },
                failure: ParseFailure::NoMatch,
            })
        );
    }

    #[test]
    fn relational_result_limit_is_not_silent() {
        assert_eq!(
            LiteralBytes::new(b"a".to_vec()).parse_relational(b"a", ParseBudget::new(1, 1, 0)),
            Err(ByteParseError::ResultLimitExceeded { limit: 0 })
        );
    }

    #[test]
    fn replay_capability_does_not_require_a_proof_bearing_backend() {
        let specification = b"let";
        let input = b"let x";
        let theory = LiteralLanguageReplay
            .realize_regex_language(&SymbolicLogic, specification)
            .unwrap();
        let witness = ByteParseWitness::prefix(input.len(), specification.len(), ()).unwrap();
        assert_eq!(
            LiteralLanguageReplay
                .replay_regex_membership(&SymbolicLogic, specification, input, &theory, &witness,)
                .unwrap(),
            ByteSpan { start: 0, end: 3 }
        );
    }
}
