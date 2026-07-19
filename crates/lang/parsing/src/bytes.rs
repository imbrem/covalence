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

// TODO(cov:parsing.bytes.regex-integration, major): Interpret regular-expression relations through A0013 and replay derivative witnesses without conflating bounded evaluation with completeness.
// TODO(cov:parsing.bytes.cfg-integration, major): Interpret CFG and PEG derivations as bounded A0013 relational witnesses with ambiguity and completeness tracked explicitly.

#[cfg(test)]
mod tests {
    use super::*;

    const BUDGET: ParseBudget = ParseBudget::new(64, 64, 4);

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
}
