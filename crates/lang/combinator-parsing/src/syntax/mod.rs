//! Encoding F — the reference spine: first-order combinator syntax as data,
//! evaluated against caller-supplied environments by three bounded evaluators.
//!
//! The fragment axis (which operators a program may contain) and the capability
//! axis (total / partial / relational) are different axes:
//!
//! | fragment | environment | evaluator | capability |
//! |---|---|---|---|
//! | [`Deterministic`] | [`TotalEnv`] | [`TotalEvaluator`] | total |
//! | [`Deterministic`] via [`deterministic_into_ordered`] | [`OrderedEnv`] | [`PartialEvaluator`] | partial |
//! | [`Ordered`] | [`OrderedEnv`] | [`PartialEvaluator`] | partial |
//! | [`Relational`] | [`RelationalEnv`] | [`RelationalEvaluator`] | relational |
//!
//! The deterministic fragment is total or partial depending on *which
//! environment interprets its primitives*, not on its syntax. Totality is
//! therefore enforced in the environment's signature — [`TotalEnv::total_step`]
//! returns no `Option`, so an implementation cannot report non-match — and not by
//! an honour-system marker trait.
//!
//! Each fragment ties the recursive knot of [`Core`] at its own type, so a node
//! built for one fragment cannot reach another fragment's evaluator by coercion,
//! subtyping, or a blanket impl.
//!
//! # What the evaluators guarantee, and what they do not
//!
//! Budgets are supplied by the caller at the evaluation boundary and charged
//! *before* recursion, never after; a post-hoc check is not a bound. No bound is
//! stored on a combinator node, because a per-node bound makes union
//! associativity fail as a resource artifact rather than a semantic disagreement.
//!
//! `Err` is evaluator failure — resource exhaustion, an undefined rule, left
//! recursion through a rule reference, or an environment error. Ordinary
//! non-match is never an `Err`: the partial evaluator reports it as
//! `ParseAttempt::NoMatch` and the relational evaluator as an empty enumeration.
//!
//! Left recursion is detected structurally only through [`Core::Rule`], by an
//! `(offset, rule)` memo. Recursion through [`Core::Bind`] passes through the
//! environment and is not structurally detectable; it is bounded only by
//! `max_continuation_resolutions`. That asymmetry is permanent.
//!
//! Witnesses are untrusted data and grant no theorem authority.

mod embed;
mod env;
mod partial;
mod relational;
mod signature;
mod term;
mod total;
mod witness;

pub use embed::{deterministic_into_ordered, deterministic_into_relational};
pub use env::{OrderedEnv, PrimitiveMatch, RelationalEnv, SignatureEnv, TotalEnv};
pub use partial::PartialEvaluator;
pub use relational::{RelationalEvaluator, RelationalMode};
pub use signature::Signature;
pub use term::{Core, Deterministic, Ordered, Relational};
pub use total::TotalEvaluator;
pub use witness::{CoreWitness, DeterministicWitness, OrderedWitness, RelationalWitness};

// TODO(cov:lang.combinator-parsing.stackless-eval, major): Syntax evaluators are recursive
// descent bounded by max_depth; deep programs need an explicit work stack.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::budget::{
        CombinatorBudget, CombinatorDiagnosticKind, CombinatorEvalError, CombinatorResource,
        RelationalLimits,
    };
    use crate::host::{RelationalPrefixParser, TotalPrefixParser};
    use covalence_parsing_api::{ParseAttempt, PartialPrefixParser};

    /// The reference signature: decimal digits over bytes.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Digits;

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Value {
        Num(u64),
        Pair(Box<Value>, Box<Value>),
        Fn(FnSym),
    }

    /// Value-level function symbols, so `Ap` has something to apply.
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum FnSym {
        PairWith,
        PairedWith(Box<Value>),
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Primitive {
        Digit,
        Literal(u8),
        Eof,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Function {
        Succ,
        Identity,
    }

    /// Continuations are defunctionalized: `ExpectSame` matches the digit just parsed
    /// again, `Nothing` declines, `Yield` succeeds consuming nothing.
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Continuation {
        ExpectSame,
        Nothing,
        Yield,
    }

    impl Signature for Digits {
        type Atom = u8;
        type Value = Value;
        type Primitive = Primitive;
        type Function = Function;
        type Continuation = Continuation;
        type PrimitiveWitness = u8;
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct DigitsError(&'static str);

    /// Rule tables built coherently across the three fragments, so cross-fragment
    /// agreement is meaningful rather than accidental.
    struct DigitsEnv {
        total_rules: Vec<Deterministic<Digits>>,
        ordered_rules: Vec<Ordered<Digits>>,
        relational_rules: Vec<Relational<Digits>>,
    }

    impl DigitsEnv {
        fn new() -> Self {
            let digit = Deterministic(Core::Prim(Primitive::Digit));
            Self {
                total_rules: vec![digit.clone()],
                ordered_rules: vec![deterministic_into_ordered(&digit)],
                relational_rules: vec![deterministic_into_relational(&digit)],
            }
        }
    }

    impl SignatureEnv<Digits> for DigitsEnv {
        type Error = DigitsError;

        fn apply_function(
            &self,
            function: &Function,
            argument: Value,
        ) -> Result<Value, DigitsError> {
            match (function, argument) {
                (Function::Identity, value) => Ok(value),
                (Function::Succ, Value::Num(n)) => Ok(Value::Num(n + 1)),
                (Function::Succ, _) => Err(DigitsError("succ of a non-number")),
            }
        }

        fn apply_value(&self, function: Value, argument: Value) -> Result<Value, DigitsError> {
            match function {
                Value::Fn(FnSym::PairWith) => Ok(Value::Fn(FnSym::PairedWith(Box::new(argument)))),
                Value::Fn(FnSym::PairedWith(left)) => Ok(Value::Pair(left, Box::new(argument))),
                // Ill-typed application is evaluator failure, never a non-match.
                _ => Err(DigitsError("applied a non-function")),
            }
        }

        fn step(
            &self,
            primitive: &Primitive,
            source: &[u8],
            at: usize,
        ) -> Result<Option<PrimitiveMatch<Digits>>, DigitsError> {
            Ok(match primitive {
                Primitive::Digit => match source.get(at) {
                    Some(byte @ b'0'..=b'9') => Some(PrimitiveMatch {
                        value: Value::Num(u64::from(byte - b'0')),
                        witness: *byte,
                        end: at + 1,
                    }),
                    _ => None,
                },
                Primitive::Literal(expected) => match source.get(at) {
                    Some(byte) if byte == expected => Some(PrimitiveMatch {
                        value: Value::Num(u64::from(*byte)),
                        witness: *byte,
                        end: at + 1,
                    }),
                    _ => None,
                },
                Primitive::Eof => (at >= source.len()).then_some(PrimitiveMatch {
                    value: Value::Num(0),
                    witness: 0,
                    end: at,
                }),
            })
        }
    }

    impl TotalEnv<Digits> for DigitsEnv {
        /// No `Option`: an unmatched digit yields zero rather than declining. That is what
        /// "total" costs, and it is why totality is a signature property here.
        fn total_step(
            &self,
            primitive: &Primitive,
            source: &[u8],
            at: usize,
        ) -> Result<PrimitiveMatch<Digits>, DigitsError> {
            Ok(match self.step(primitive, source, at)? {
                Some(matched) => matched,
                None => PrimitiveMatch {
                    value: Value::Num(0),
                    witness: 0,
                    end: at,
                },
            })
        }

        fn total_rule(&self, rule: usize) -> Option<&Deterministic<Digits>> {
            self.total_rules.get(rule)
        }

        fn total_resolve(
            &self,
            continuation: &Continuation,
            value: &Value,
        ) -> Result<Deterministic<Digits>, DigitsError> {
            Ok(match continuation {
                Continuation::Yield | Continuation::Nothing => {
                    Deterministic(Core::Pure(value.clone()))
                }
                Continuation::ExpectSame => match value {
                    Value::Num(n) => Deterministic(Core::Prim(Primitive::Literal(
                        b'0' + u8::try_from(*n).unwrap_or(0),
                    ))),
                    _ => return Err(DigitsError("expect-same needs a number")),
                },
            })
        }
    }

    impl OrderedEnv<Digits> for DigitsEnv {
        fn ordered_rule(&self, rule: usize) -> Option<&Ordered<Digits>> {
            self.ordered_rules.get(rule)
        }

        fn ordered_resolve(
            &self,
            continuation: &Continuation,
            value: &Value,
        ) -> Result<Ordered<Digits>, DigitsError> {
            Ok(match continuation {
                Continuation::Yield => Ordered::Core(Core::Pure(value.clone())),
                // A continuation that should not match resolves to `Fail`, not to `Err`.
                Continuation::Nothing => Ordered::Fail,
                Continuation::ExpectSame => match value {
                    Value::Num(n) => Ordered::Core(Core::Prim(Primitive::Literal(
                        b'0' + u8::try_from(*n).unwrap_or(0),
                    ))),
                    _ => return Err(DigitsError("expect-same needs a number")),
                },
            })
        }
    }

    impl RelationalEnv<Digits> for DigitsEnv {
        fn relational_rule(&self, rule: usize) -> Option<&Relational<Digits>> {
            self.relational_rules.get(rule)
        }

        fn relational_resolve(
            &self,
            continuation: &Continuation,
            value: &Value,
        ) -> Result<Relational<Digits>, DigitsError> {
            Ok(match continuation {
                Continuation::Yield => Relational::Core(Core::Pure(value.clone())),
                // A continuation that should yield nothing resolves to `Void`.
                Continuation::Nothing => Relational::Void,
                Continuation::ExpectSame => match value {
                    Value::Num(n) => Relational::Core(Core::Prim(Primitive::Literal(
                        b'0' + u8::try_from(*n).unwrap_or(0),
                    ))),
                    _ => return Err(DigitsError("expect-same needs a number")),
                },
            })
        }
    }

    fn budget() -> CombinatorBudget {
        CombinatorBudget::new(1024, 1024, 64, 1024, 64)
    }

    fn limits() -> RelationalLimits {
        RelationalLimits::new(64, 64)
    }

    fn digit() -> Ordered<Digits> {
        Ordered::Core(Core::Prim(Primitive::Digit))
    }

    #[test]
    fn partial_evaluator_matches_a_prefix_and_reports_the_remainder() {
        let env = DigitsEnv::new();
        let program = digit();
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        let ParseAttempt::Match(parsed) = evaluator.parse_prefix(b"7x", 0).unwrap() else {
            panic!("expected a match");
        };
        assert_eq!(parsed.value, Value::Num(7));
        assert_eq!(parsed.remainder, 1);
        assert_eq!(parsed.consumed.len(), 1);
    }

    #[test]
    fn non_match_is_a_diagnostic_and_never_an_error() {
        let env = DigitsEnv::new();
        let program = digit();
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        let ParseAttempt::NoMatch(diagnostic) = evaluator.parse_prefix(b"x", 0).unwrap() else {
            panic!("expected a non-match");
        };
        assert_eq!(diagnostic.kind, CombinatorDiagnosticKind::NoMatch);
    }

    #[test]
    fn start_past_the_end_is_a_diagnostic_not_an_evaluator_failure() {
        let env = DigitsEnv::new();
        let program = digit();
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        assert_eq!(
            evaluator.parse_prefix(b"7", 9).unwrap(),
            ParseAttempt::NoMatch(crate::budget::CombinatorDiagnostic::new(
                9,
                CombinatorDiagnosticKind::StartOutOfBounds
            ))
        );
    }

    #[test]
    fn ordered_choice_commits_to_its_first_matching_alternative() {
        let env = DigitsEnv::new();
        // The second alternative would also match, and is never consulted.
        let program = Ordered::OrderedChoice(vec![
            digit(),
            Ordered::Core(Core::Map(Function::Succ, Box::new(digit()))),
        ]);
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        let ParseAttempt::Match(parsed) = evaluator.parse_prefix(b"4", 0).unwrap() else {
            panic!("expected a match");
        };
        assert_eq!(parsed.value, Value::Num(4));
        let OrderedWitness::OrderedChoice { chosen, .. } = parsed.witness else {
            panic!("expected a choice witness");
        };
        assert_eq!(chosen, 0);
    }

    #[test]
    fn union_retains_every_alternative_and_is_not_idempotent() {
        let env = DigitsEnv::new();
        let branch = Relational::Core(Core::Prim(Primitive::Digit));
        let program = Relational::Union(vec![branch.clone(), branch]);
        let evaluator = RelationalEvaluator::new(&program, &env, budget(), limits());
        // Ordered choice would yield one result here; union yields both copies.
        assert_eq!(evaluator.parse_prefixes(b"4", 0).unwrap().len(), 2);
    }

    #[test]
    fn total_evaluator_produces_an_interpretation_without_a_non_match_channel() {
        let env = DigitsEnv::new();
        let program = Deterministic(Core::Prim(Primitive::Digit));
        let evaluator = TotalEvaluator::new(&program, &env, budget());
        // `x` is not a digit, and the total environment still produces a value.
        let parsed = evaluator.parse_prefix_total(b"x", 0).unwrap();
        assert_eq!(parsed.value, Value::Num(0));
        assert_eq!(parsed.remainder, 0);
    }

    #[test]
    fn ordered_bind_does_not_retry_its_head() {
        let env = DigitsEnv::new();
        let program = Ordered::Core(Core::Bind(Box::new(digit()), Continuation::ExpectSame));
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        let ParseAttempt::Match(parsed) = evaluator.parse_prefix(b"44", 0).unwrap() else {
            panic!("expected a match");
        };
        assert_eq!(parsed.remainder, 2);
        assert!(matches!(
            evaluator.parse_prefix(b"45", 0).unwrap(),
            ParseAttempt::NoMatch(_)
        ));
    }

    #[test]
    fn relational_bind_continues_every_head_result() {
        let env = DigitsEnv::new();
        let branch = Relational::Core(Core::Prim(Primitive::Digit));
        let head = Relational::Union(vec![branch.clone(), branch]);
        let program = Relational::Core(Core::Bind(Box::new(head), Continuation::Yield));
        let evaluator = RelationalEvaluator::new(&program, &env, budget(), limits());
        assert_eq!(evaluator.parse_prefixes(b"4", 0).unwrap().len(), 2);
    }

    #[test]
    fn a_declining_continuation_is_syntax_not_an_error() {
        let env = DigitsEnv::new();
        let program = Ordered::Core(Core::Bind(Box::new(digit()), Continuation::Nothing));
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        assert!(matches!(
            evaluator.parse_prefix(b"4", 0).unwrap(),
            ParseAttempt::NoMatch(_)
        ));
    }

    #[test]
    fn ill_typed_application_is_an_environment_error_not_a_non_match() {
        let env = DigitsEnv::new();
        let program = Ordered::Core(Core::Ap(Box::new(digit()), Box::new(digit())));
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        assert_eq!(
            evaluator.parse_prefix(b"44", 0),
            Err(CombinatorEvalError::Environment(DigitsError(
                "applied a non-function"
            )))
        );
    }

    #[test]
    fn ap_sequences_left_to_right_with_a_parsed_function() {
        let env = DigitsEnv::new();
        let pair = Ordered::Core(Core::Pure(Value::Fn(FnSym::PairWith)));
        let program = Ordered::Core(Core::Ap(
            Box::new(Ordered::Core(Core::Ap(Box::new(pair), Box::new(digit())))),
            Box::new(digit()),
        ));
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        let ParseAttempt::Match(parsed) = evaluator.parse_prefix(b"25", 0).unwrap() else {
            panic!("expected a match");
        };
        assert_eq!(
            parsed.value,
            Value::Pair(Box::new(Value::Num(2)), Box::new(Value::Num(5)))
        );
        assert_eq!(parsed.remainder, 2);
    }

    #[test]
    fn exact_parsing_rejects_trailing_input() {
        use covalence_parsing_api::PartialExactParser;
        let env = DigitsEnv::new();
        let program = digit();
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        let ParseAttempt::NoMatch(diagnostic) = evaluator.parse_exact(b"44").unwrap() else {
            panic!("expected a non-match");
        };
        assert_eq!(diagnostic.kind, CombinatorDiagnosticKind::TrailingInput);
    }

    #[test]
    fn a_zero_width_primitive_matches_without_consuming() {
        let env = DigitsEnv::new();
        let program = Ordered::Core(Core::Ap(
            Box::new(Ordered::Core(Core::Ap(
                Box::new(Ordered::Core(Core::Pure(Value::Fn(FnSym::PairWith)))),
                Box::new(digit()),
            ))),
            Box::new(Ordered::Core(Core::Prim(Primitive::Eof))),
        ));
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        let ParseAttempt::Match(parsed) = evaluator.parse_prefix(b"4", 0).unwrap() else {
            panic!("expected a match");
        };
        assert_eq!(parsed.remainder, 1);
        assert!(matches!(
            evaluator.parse_prefix(b"44", 0).unwrap(),
            ParseAttempt::NoMatch(_)
        ));
    }

    #[test]
    fn parser_syntax_returns_the_program_unchanged() {
        use covalence_parsing_api::ParserSyntax;
        let env = DigitsEnv::new();
        let program = digit();
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        assert_eq!(evaluator.syntax(), &program);
    }

    #[test]
    fn an_undefined_rule_is_an_evaluator_failure() {
        let env = DigitsEnv::new();
        let program = Ordered::Core(Core::Rule(9));
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        assert_eq!(
            evaluator.parse_prefix(b"4", 0),
            Err(CombinatorEvalError::UndefinedRule { rule: 9 })
        );
    }

    #[test]
    fn left_recursion_through_a_rule_is_reported_rather_than_overflowing() {
        let env = DigitsEnv {
            total_rules: Vec::new(),
            ordered_rules: vec![Ordered::Core(Core::Rule(0))],
            relational_rules: Vec::new(),
        };
        let program = Ordered::Core(Core::Rule(0));
        let evaluator = PartialEvaluator::new(&program, &env, budget());
        assert_eq!(
            evaluator.parse_prefix(b"4", 0),
            Err(CombinatorEvalError::LeftRecursion { rule: 0, offset: 0 })
        );
    }

    #[test]
    fn embedding_preserves_the_skeleton_across_fragments() {
        let program = Deterministic(Core::Map(
            Function::Identity,
            Box::new(Deterministic(Core::Prim(Primitive::Digit))),
        ));
        assert_eq!(
            deterministic_into_ordered(&program),
            Ordered::Core(Core::Map(Function::Identity, Box::new(digit())))
        );
        assert_eq!(
            deterministic_into_relational(&program),
            Relational::Core(Core::Map(
                Function::Identity,
                Box::new(Relational::Core(Core::Prim(Primitive::Digit)))
            ))
        );
    }

    /// One case per [`CombinatorResource`] variant. An unconstructible variant would mean
    /// the corresponding bound is not implemented.
    #[test]
    fn every_bound_is_observable() {
        let env = DigitsEnv::new();
        let program = Ordered::Core(Core::Map(Function::Identity, Box::new(digit())));
        let relational = Relational::Union(vec![
            Relational::Core(Core::Prim(Primitive::Digit)),
            Relational::Core(Core::Prim(Primitive::Digit)),
        ]);

        let exhausted = |budget: CombinatorBudget| {
            let evaluator = PartialEvaluator::new(&program, &env, budget);
            match evaluator.parse_prefix(b"4", 0) {
                Err(CombinatorEvalError::ResourceExhausted(limit)) => limit.resource,
                other => panic!("expected exhaustion, got {other:?}"),
            }
        };

        assert_eq!(
            exhausted(CombinatorBudget::new(0, 64, 64, 64, 64)),
            CombinatorResource::SourceUnits
        );
        assert_eq!(
            exhausted(CombinatorBudget::new(64, 0, 64, 64, 64)),
            CombinatorResource::Work
        );
        assert_eq!(
            exhausted(CombinatorBudget::new(64, 64, 0, 64, 64)),
            CombinatorResource::Depth
        );
        assert_eq!(
            exhausted(CombinatorBudget::new(64, 64, 64, 0, 64)),
            CombinatorResource::WitnessNodes
        );

        let binding = Ordered::Core(Core::Bind(Box::new(digit()), Continuation::Yield));
        let evaluator =
            PartialEvaluator::new(&binding, &env, CombinatorBudget::new(64, 64, 64, 64, 0));
        assert_eq!(
            evaluator.parse_prefix(b"4", 0),
            Err(CombinatorEvalError::ResourceExhausted(
                crate::budget::CombinatorLimit::new(CombinatorResource::ContinuationResolutions, 0)
            ))
        );

        let evaluator =
            RelationalEvaluator::new(&relational, &env, budget(), RelationalLimits::new(0, 64));
        assert_eq!(
            evaluator.parse_prefixes(b"4", 0),
            Err(CombinatorEvalError::ResourceExhausted(
                crate::budget::CombinatorLimit::new(CombinatorResource::Results, 0)
            ))
        );

        let evaluator =
            RelationalEvaluator::new(&relational, &env, budget(), RelationalLimits::new(64, 1));
        assert_eq!(
            evaluator.parse_prefixes(b"4", 0),
            Err(CombinatorEvalError::ResourceExhausted(
                crate::budget::CombinatorLimit::new(CombinatorResource::ResultsPerNode, 1)
            ))
        );
    }
}
