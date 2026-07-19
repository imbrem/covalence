//! The falsifiers: the tests that would go green if the three interpretations
//! quietly collapsed into one.
//!
//! Every test here is a *negative* guarantee — something this crate must **not**
//! do — or an assertion that the corpus is strong enough for the positive tests
//! to mean anything. A suite of only positive law checks over a weak corpus is
//! green and worthless, which is the failure mode these exist to prevent.
//!
//! The four `compile_fail,E0277` doctests that pin the discrete trait graph live
//! on the traits themselves, in `host::mod` and `host::partial`, plus one on
//! `morphism::WithoutFailureInhabitant`; `cargo test --doc` runs them.

use covalence_combinator_parsing::budget::CombinatorEvalError;
use covalence_combinator_parsing::conformance::host::{
    PartialLawFixture, check_applicative_laws as host_applicative_laws,
    check_fixture_is_not_vacuous, check_functor_laws as host_functor_laws,
    check_monad_laws as host_monad_laws,
    check_ordered_choice_is_not_commutative as host_choice_is_not_commutative,
    check_ordered_choice_laws as host_choice_laws, fixture_corpus,
};
use covalence_combinator_parsing::conformance::reference::{
    self as reference, BUDGET, Continuation, Env, LIMITS, Reference, Value,
};
use covalence_combinator_parsing::conformance::syntax as f_laws;
use covalence_combinator_parsing::host::cursor::CombinatorError;
use covalence_combinator_parsing::host::{RelationalPrefixParser, TotalPrefixParser, partial};
use covalence_combinator_parsing::morphism::{
    self, AgreeBy, CollectionPolicy, PartialObserved, RelationalObserved, TotalObserved,
    WidenPartialToRelational, WidenTotalToPartial, WidenTotalToRelational, compile_deterministic,
    compile_ordered, observe_partial, observe_relational, observe_total,
};
use covalence_combinator_parsing::syntax::{
    Core, Deterministic, Ordered, PartialEvaluator, Relational, RelationalEvaluator, TotalEvaluator,
};
use covalence_parsing_api::{
    ParseAttempt, PartialPrefixParser, PrefixInterpretation, PrefixParseResult, Span,
};

// ---------------------------------------------------------------------------
// Observers over the reference encoding
// ---------------------------------------------------------------------------

type Failure = CombinatorEvalError<reference::ReferenceError>;

fn ordered_observer(
    program: &Ordered<Reference>,
) -> impl FnMut(&[u8], usize) -> PartialObserved<Value, Failure> + '_ {
    move |source, start| {
        observe_partial(PartialEvaluator::new(program, &Env, BUDGET).parse_prefix(source, start))
    }
}

fn relational_observer(
    program: &Relational<Reference>,
) -> impl FnMut(&[u8], usize) -> RelationalObserved<Value, Failure> + '_ {
    move |source, start| {
        observe_relational(
            RelationalEvaluator::new(program, &Env, BUDGET, LIMITS).parse_prefixes(source, start),
        )
    }
}

fn total_observer(
    program: &Deterministic<Reference>,
) -> impl FnMut(&[u8], usize) -> TotalObserved<Value, Failure> + '_ {
    move |source, start| {
        observe_total(TotalEvaluator::new(program, &Env, BUDGET).parse_prefix_total(source, start))
    }
}

fn agreement() -> AgreeBy<fn(&Value, &Value) -> bool> {
    AgreeBy(|left, right| left == right)
}

// ---------------------------------------------------------------------------
// The five falsifiers
// ---------------------------------------------------------------------------

/// **The single highest-value test in the crate.**
///
/// Ordered choice *commits*: once the first alternative matches, the second is
/// never evaluated at all. That is an operational fact, not a statement about
/// results, so it is observed by giving the second alternative an evaluator that
/// **fails if invoked**.
///
/// Take-first-of-union would return `Err` here, because a union must evaluate
/// both alternatives before it can take the first result. The two operators are
/// therefore distinguishable by an observation no amount of result-comparison
/// could reach — which is why there is no `take_first` in this API.
#[test]
fn ordered_choice_does_not_evaluate_its_second_arm() {
    let committing = Ordered::OrderedChoice(vec![reference::atom(1), reference::poison()]);
    let matched = PartialEvaluator::new(&committing, &Env, BUDGET)
        .parse_prefix(b"ab", 0)
        .expect("the poisoned alternative must never be reached");
    assert!(matches!(matched, ParseAttempt::Match(_)));

    // The union *does* reach it, which is what makes the contrast meaningful
    // rather than an accident of this particular program.
    let exploring = Relational::Union(vec![
        reference::relational_atom(1),
        reference::relational_poison(),
    ]);
    assert!(
        RelationalEvaluator::new(&exploring, &Env, BUDGET, LIMITS)
            .parse_prefixes(b"ab", 0)
            .is_err(),
        "if the union did not reach the poison, this test proves nothing"
    );
}

/// When both alternatives match, ordered choice yields one result and union
/// yields two. This is the concrete reason the positive refinement is an
/// implication and never an equation.
#[test]
fn ordered_choice_and_union_disagree_when_both_alternatives_match() {
    let ordered = reference::overlapping_choice();
    let relational = reference::ambiguous_union();

    let ParseAttempt::Match(matched) = PartialEvaluator::new(&ordered, &Env, BUDGET)
        .parse_prefix(b"ab", 0)
        .expect("no evaluator failure")
    else {
        panic!("expected a match");
    };
    let enumerated = RelationalEvaluator::new(&relational, &Env, BUDGET, LIMITS)
        .parse_prefixes(b"ab", 0)
        .expect("no evaluator failure");

    assert_eq!(matched.value, Value::Tag(1));
    assert_eq!(enumerated.len(), 2);
    // ...and the second union member is one ordered choice will never produce.
    assert_eq!(enumerated[1].value, Value::Tag(2));
    // Same extent: this is genuine ambiguity, not two parses of different lengths.
    assert_eq!(enumerated[0].consumed, enumerated[1].consumed);
}

/// **Two operators that disagree on left-distributivity are two operators.**
///
/// Union distributes over bind; ordered choice does not. This is the sharpest
/// separating law and the reason the refinement is stated about whole
/// observations rather than as a rewrite rule on programs.
#[test]
fn union_distributes_over_bind_and_ordered_choice_does_not() {
    let mut union_inputs = reference::union_inputs();
    union_inputs.k = Continuation::RejectOne;
    let distributes = f_laws::check_union_distributes_over_bind(
        &Env,
        &union_inputs,
        &reference::corpus(),
        BUDGET,
        LIMITS,
        &mut reference::agreement(),
        &CollectionPolicy::AS_ENUMERATED,
    );
    assert!(distributes.is_holding(), "{:?}", distributes.agreement);

    let does_not = f_laws::check_ordered_choice_does_not_distribute_over_bind(
        &Env,
        &reference::atom(1),
        &reference::atom(2),
        &Continuation::RejectOne,
        &reference::corpus(),
        BUDGET,
        &mut reference::agreement(),
    );
    assert!(
        does_not.exhibited(),
        "the ordered corpus lacks the separating shape: {does_not:?}"
    );
}

/// The shipped host fixture's continuations genuinely branch on their argument,
/// **at the values the monad laws thread into them** — all three of them.
///
/// A fixture whose continuations ignore their argument makes every monad law hold
/// structurally regardless of whether `Bind` threads offsets correctly. So does
/// one that branches only at some value the laws never produce — which is why the
/// guard takes no probe values and derives them from the fixture instead.
///
/// Make **any one** of `continuation_k`, `continuation_h` or `pure_continuation`
/// constant across the fixture's own threaded values (for instance by guarding a
/// decline on a value `parser` and `sample_value` never yield, or by ignoring the
/// argument outright) and this must go red naming that continuation. The three
/// are reported separately for exactly that reason: a merged report would let a
/// branching `k` certify a constant `h`.
///
/// **Run this before trusting any host law below it.**
#[test]
fn fixture_is_not_vacuous() {
    let mut fixture = Fixture;
    let report = check_fixture_is_not_vacuous(&mut fixture);
    assert!(
        report.exhibited(),
        "these fixture continuations do not depend on their argument anywhere \
         the monad laws reach: {:?} — full report {report:?}",
        report.constant()
    );
}

// ---------------------------------------------------------------------------
// Tier (iii) — the refinement laws over the reference corpus
// ---------------------------------------------------------------------------

#[test]
fn total_embeds_in_partial() {
    let program = reference::deterministic_atom(3);
    let widened = WidenTotalToPartial(TotalEvaluator::new(&program, &Env, BUDGET));
    let mut total = total_observer(&program);
    let mut partial =
        |source: &[u8], start: usize| observe_partial(widened.parse_prefix(source, start));
    let report = morphism::check_total_embeds_in_partial(
        &mut total,
        &mut partial,
        &reference::corpus(),
        &mut agreement(),
    );
    assert!(report.is_agreeing() && !report.is_vacuous(), "{report:?}");
}

#[test]
fn partial_embeds_in_relational_with_cardinality_at_most_one() {
    let program = reference::atom(3);
    let widened = WidenPartialToRelational(PartialEvaluator::new(&program, &Env, BUDGET));
    let mut partial = ordered_observer(&program);
    let mut relational =
        |source: &[u8], start: usize| observe_relational(widened.parse_prefixes(source, start));
    let report = morphism::check_partial_embeds_in_relational(
        &mut partial,
        &mut relational,
        &reference::corpus(),
        &mut agreement(),
        &CollectionPolicy::AS_ENUMERATED,
    );
    assert!(report.is_agreeing() && !report.is_vacuous(), "{report:?}");
}

/// M5, checked **directly** rather than as M1 followed by M2. The exactly-one
/// cardinality is strictly stronger than the at-most-one M2 gives, and
/// heterogeneous agreements do not compose in any case.
#[test]
fn total_embeds_in_relational_with_cardinality_exactly_one() {
    let program = reference::deterministic_atom(3);
    let widened = WidenTotalToRelational(TotalEvaluator::new(&program, &Env, BUDGET));
    let mut total = total_observer(&program);
    let mut relational =
        |source: &[u8], start: usize| observe_relational(widened.parse_prefixes(source, start));
    let report = morphism::check_total_embeds_in_relational(
        &mut total,
        &mut relational,
        &reference::corpus(),
        &mut agreement(),
    );
    assert!(report.is_agreeing() && !report.is_vacuous(), "{report:?}");
}

/// **M3⁺ and M3⁻, and the corpus obligation that makes them mean anything.**
///
/// Both laws are conditional, so both are satisfied on every sample of a corpus
/// whose programs never match — a decline against an empty enumeration agrees
/// with everything. `is_agreeing()` on its own therefore certifies nothing here,
/// which is why each report is additionally required to have *matched at least
/// once*: `checked > 0`, with the trivially-satisfied samples segregated into
/// `hypothesis_unsatisfied`.
///
/// Replace either subject with a never-matching program (`Ordered::Fail`,
/// `Relational::Void`) and these assertions must go red.
#[test]
fn ordered_choice_refines_union_positively_and_agrees_on_emptiness() {
    let ordered = reference::overlapping_choice();
    let relational = reference::ambiguous_union();

    let positive = {
        let mut left = ordered_observer(&ordered);
        let mut right = relational_observer(&relational);
        morphism::check_choice_refines_union(
            &mut left,
            &mut right,
            &reference::corpus(),
            &mut agreement(),
        )
    };
    assert!(positive.is_agreeing(), "{positive:?}");
    assert!(
        !positive.is_vacuous(),
        "M3+ never saw a match: the corpus satisfies it only vacuously: {positive:?}"
    );

    let negative = {
        let mut left = ordered_observer(&ordered);
        let mut right = relational_observer(&relational);
        morphism::check_choice_and_union_agree_on_emptiness(
            &mut left,
            &mut right,
            &reference::corpus(),
        )
    };
    assert!(negative.is_agreeing(), "{negative:?}");
    assert!(
        !negative.is_vacuous(),
        "M3- saw only doubly-empty samples, which any pair of programs satisfies: {negative:?}"
    );
}

/// **M4's scope, measured rather than assumed.**
///
/// The take-first agreement is true on the image of the partial-to-relational
/// widening and false under a bind above a choice. This asserts the corpus
/// actually contains the divergence — a run finding none would mean the corpus is
/// too weak, and the report type cannot be misread as a pass.
#[test]
fn take_first_agreement_is_scoped_and_the_corpus_proves_it() {
    let ordered = Ordered::Core(Core::Bind(
        Box::new(reference::overlapping_choice()),
        Continuation::RejectOne,
    ));
    let relational = Relational::Core(Core::Bind(
        Box::new(reference::ambiguous_union()),
        Continuation::RejectOne,
    ));
    let mut left = ordered_observer(&ordered);
    let mut right = relational_observer(&relational);
    let report = morphism::check_take_first_agreement_is_scoped(
        &mut left,
        &mut right,
        &reference::corpus(),
        &mut agreement(),
    );
    assert!(
        report.exhibited(),
        "M4 never diverged; the corpus lacks a bind above a choice: {report:?}"
    );
}

/// The corpus obligation of the relational side, asserted in its own right.
#[test]
fn corpus_contains_a_genuinely_ambiguous_parser() {
    let program = reference::ambiguous_union();
    let mut observer = relational_observer(&program);
    let audit = morphism::audit_relational_ambiguity(&mut observer, &reference::corpus());
    assert!(audit.is_genuinely_ambiguous(), "{audit:?}");
}

// ---------------------------------------------------------------------------
// Tier (ii) — the two encodings agree
// ---------------------------------------------------------------------------

/// **N1.** The same program, evaluated as data and compiled to host combinators.
///
/// Only the trichotomy and the positive projection are compared. Diagnostic
/// payloads are outside the law by construction, and nothing here looks at one.
#[test]
fn the_two_encodings_agree_on_the_ordered_fragment() {
    let program = Ordered::OrderedChoice(vec![
        f_laws::ordered_bind(reference::atom(1), Continuation::RejectOne),
        f_laws::ordered_map(reference::Function::Succ, reference::atom(2)),
    ]);
    let compiled = compile_ordered(&program, &Env, BUDGET);
    let mut syntax = ordered_observer(&program);
    let mut host =
        |source: &[u8], start: usize| observe_partial(compiled.parse_prefix(source, start));
    let report = morphism::check_encodings_agree_partial(
        &mut syntax,
        &mut host,
        &reference::corpus(),
        &mut agreement(),
    );
    assert!(report.is_agreeing() && !report.is_vacuous(), "{report:?}");
}

/// A deterministic program that exercises **every compiled core arm the total
/// fragment can reach**: `Ap` applies a parsed function to a parsed argument,
/// `Bind` resolves a continuation against the value produced, and `Map` applies
/// an environment function symbol to the result.
///
/// # The nesting is load-bearing, not incidental
///
/// Each arm's output must be *observable in the final value*, or that arm is
/// present in the program and unmeasured by the law. The obvious spelling —
/// `Map(Succ, Bind(Ap(..), ThenAtom))` — fails this: `ThenAtom` resolves to
/// `Prim(Atom(9))` **regardless of the value handed to it**, so it discards the
/// `Ap` result and a compiled `Ap` that skipped `apply_value` agrees with the
/// evaluator everywhere. That version was written first and verified to survive
/// the mutation.
///
/// So `Bind` sits *under* `Ap`, on the argument side. The value threads:
/// `AtomAsAdder(2)` yields `Fun(Add(2))`; the argument is `Atom(5)` bound through
/// `ThenAtom` to `Atom(9)`, yielding `Tag(9)`; `Ap` combines them into `Tag(11)`;
/// `Succ` lifts that to `Tag(12)`. Dropping any one of the three environment
/// calls moves the final value, and dropping `Bind`'s offset threading moves the
/// remainder.
///
/// `Continuation::RejectOne` is deliberately absent: it is *unexpressible* in the
/// deterministic fragment — [`Env`]'s `total_resolve` reports it as an
/// environment error rather than reinterpreting it — because this fragment has no
/// failure operator.
fn deterministic_composite() -> Deterministic<Reference> {
    let function = Deterministic(Core::Prim(reference::Primitive::AtomAsAdder(2)));
    let argument = Deterministic(Core::Prim(reference::Primitive::Atom(5)));
    let sequenced = Deterministic(Core::Bind(Box::new(argument), Continuation::ThenAtom));
    let applied = Deterministic(Core::Ap(Box::new(function), Box::new(sequenced)));
    Deterministic(Core::Map(reference::Function::Succ, Box::new(applied)))
}

/// **N1 on the deterministic fragment** — the total half of the axis-2
/// compilation law, over a corpus that reaches `Map`, `Ap` and `Bind`.
///
/// The total value type must have no distinguished failure inhabitant, or "the
/// total side always produced" is satisfiable by producing a value that *means*
/// failure; [`Value`] carries the [`WithoutFailureInhabitant`] bound this law
/// requires, and the compiler enforces it at this call.
///
/// Delete any environment call from `compile`'s `total_step` — the
/// `env.apply_function` in the `Core::Map` arm, say — and this must go red.
///
/// [`WithoutFailureInhabitant`]: covalence_combinator_parsing::morphism::WithoutFailureInhabitant
#[test]
fn the_two_encodings_agree_on_the_deterministic_fragment() {
    let program = deterministic_composite();
    let compiled = compile_deterministic(&program, &Env, BUDGET);
    let mut syntax = total_observer(&program);
    let mut host =
        |source: &[u8], start: usize| observe_total(compiled.parse_prefix_total(source, start));
    let report = morphism::check_encodings_agree_total(
        &mut syntax,
        &mut host,
        &reference::corpus(),
        &mut agreement(),
    );
    assert!(report.is_agreeing(), "{report:?}");
    assert!(
        !report.is_vacuous(),
        "N1(total) ran on no samples: {report:?}"
    );
}

/// The corpus obligation for the test above: the composite's `Map`, `Ap` and
/// `Bind` arms each contribute to the value that comes out, so none of them can
/// be silently skipped by a compiled arm while the agreement stays green.
///
/// The expected value is written out here independently of either evaluator, so
/// this is a check on the *program*, not on the agreement between two encodings
/// that might both be wrong in the same way.
#[test]
fn the_deterministic_composite_exercises_map_ap_and_bind() {
    let program = deterministic_composite();
    let produced = TotalEvaluator::new(&program, &Env, BUDGET)
        .parse_prefix_total(b"abc", 0)
        .expect("no evaluator failure");
    // Bind: Tag(5) through ThenAtom is Tag(9); Ap: Add(2) applied to it is
    // Tag(11); Map by Succ lifts it to Tag(12). Three atoms consumed, one per
    // primitive, which pins that Bind threaded the *offset* and not only the
    // value.
    assert_eq!(produced.value, Value::Tag(12));
    assert_eq!(produced.remainder, 3);
}

/// The two `Core` arms [`deterministic_composite`] never reaches: `Core::Rule`
/// and `Core::Pure`.
///
/// Both rule bodies are referenced, and they differ in *both* observable
/// coordinates: [`reference::RULE_PURE_ADDER`] contributes a value and no extent,
/// [`reference::RULE_ATOM`] an extent and a different value. So a compiled
/// `Core::Rule` arm that resolved the wrong body, dropped the body's value, or
/// dropped the body's extent each moves the observation, and none of the three can
/// hide behind the other two.
///
/// The value threads: rule 0 is `Pure(Fun(Add(4)))`, consuming nothing; rule 1 is
/// `Atom(3)`, yielding `Tag(3)` and consuming one atom; `Ap` applies the first to
/// the second giving `Tag(7)`; `Succ` lifts it to `Tag(8)`.
fn rule_reference_program() -> Deterministic<Reference> {
    let adder = Deterministic(Core::Rule(reference::RULE_PURE_ADDER));
    let tagged = Deterministic(Core::Rule(reference::RULE_ATOM));
    let applied = Deterministic(Core::Ap(Box::new(adder), Box::new(tagged)));
    Deterministic(Core::Map(reference::Function::Succ, Box::new(applied)))
}

/// **N1 on the deterministic fragment, through rule references.**
///
/// `Env::total_rule` returned `None` unconditionally until it was given
/// [`TOTAL_RULES`], which left the `Core::Rule` arm of both total evaluators
/// entirely unexercised — an exported code path with no test caller, where
/// breaking the implementation left the suite green.
///
/// Break either `Core::Rule` arm — resolve a fixed rule index instead of the one
/// asked for, or return `at` in place of the body's `end` — and this must go red.
///
/// [`TOTAL_RULES`]: covalence_combinator_parsing::conformance::reference
#[test]
fn the_two_encodings_agree_on_rule_references_and_pure() {
    let program = rule_reference_program();
    let compiled = compile_deterministic(&program, &Env, BUDGET);
    let mut syntax = total_observer(&program);
    let mut host =
        |source: &[u8], start: usize| observe_total(compiled.parse_prefix_total(source, start));
    let report = morphism::check_encodings_agree_total(
        &mut syntax,
        &mut host,
        &reference::corpus(),
        &mut agreement(),
    );
    assert!(report.is_agreeing(), "{report:?}");
    assert!(
        !report.is_vacuous(),
        "N1(total) over rule references ran on no samples: {report:?}"
    );
}

/// The corpus obligation for the test above, written out independently of either
/// evaluator: both rule bodies and the `Pure` inside one of them contribute to
/// the observation, so no arm can be skipped while the agreement stays green.
#[test]
fn the_rule_reference_program_threads_pure_and_both_rule_bodies() {
    let program = rule_reference_program();
    let produced = TotalEvaluator::new(&program, &Env, BUDGET)
        .parse_prefix_total(b"abc", 0)
        .expect("no evaluator failure");
    assert_eq!(produced.value, Value::Tag(8));
    // Exactly one atom: `Pure` consumed nothing and `Atom(3)` consumed one, which
    // pins that `Ap` threaded the offset through the rule reference.
    assert_eq!(produced.remainder, 1);
}

/// **The left-recursion guard fires, in both encodings.**
///
/// This cannot be an agreement law: both sides failing is
/// `AgreementOutcome::Inconclusive` by design, and no law in this crate compares
/// error payloads across encodings. So the guard is pinned by asserting the error
/// each encoding produces *within* its own carrier, which is where the payload is
/// meaningful.
///
/// Disable either check — `if false && st.active.contains(..)`, or drop the push
/// onto `active` — and this must go red: the recursion then runs until some
/// unrelated budget trips, reporting `ResourceExhausted` in place of the specific
/// diagnosis.
#[test]
fn both_encodings_report_left_recursion_rather_than_exhausting_a_budget() {
    let program = Deterministic(Core::Rule(reference::RULE_LEFT_RECURSIVE));

    let syntax = TotalEvaluator::new(&program, &Env, BUDGET).parse_prefix_total(b"abc", 0);
    assert!(
        matches!(
            &syntax,
            Err(CombinatorEvalError::LeftRecursion { rule, offset })
                if *rule == reference::RULE_LEFT_RECURSIVE && *offset == 0
        ),
        "the syntax encoding did not diagnose left recursion: {:?}",
        syntax.map(|produced| produced.value)
    );

    let compiled = compile_deterministic(&program, &Env, BUDGET);
    let host = compiled.parse_prefix_total(b"abc", 0);
    assert!(
        matches!(
            &host,
            Err(CombinatorEvalError::LeftRecursion { rule, offset })
                if *rule == reference::RULE_LEFT_RECURSIVE && *offset == 0
        ),
        "the compiled encoding did not diagnose left recursion: {:?}",
        host.map(|produced| produced.value)
    );
}

/// The `None` arm of the rule table, which is now reachable rather than universal:
/// an index no rule occupies is an *evaluator failure* naming the rule, never a
/// non-match.
#[test]
fn an_undefined_rule_is_an_evaluator_failure_in_both_encodings() {
    const ABSENT: usize = 99;
    let program = Deterministic(Core::Rule(ABSENT));

    let syntax = TotalEvaluator::new(&program, &Env, BUDGET).parse_prefix_total(b"abc", 0);
    assert!(
        matches!(&syntax, Err(CombinatorEvalError::UndefinedRule { rule }) if *rule == ABSENT),
        "{:?}",
        syntax.map(|produced| produced.value)
    );

    let compiled = compile_deterministic(&program, &Env, BUDGET);
    let host = compiled.parse_prefix_total(b"abc", 0);
    assert!(
        matches!(&host, Err(CombinatorEvalError::UndefinedRule { rule }) if *rule == ABSENT),
        "{:?}",
        host.map(|produced| produced.value)
    );
}

// ---------------------------------------------------------------------------
// Tier (i), host encoding — a fixture defined outside the crate
// ---------------------------------------------------------------------------

/// A leaf parser with three behaviours, so that continuations can branch.
#[derive(Clone, Copy, Debug)]
enum Leaf {
    /// Declines, with a diagnostic.
    Decline,
    /// Consumes one atom and yields `t`.
    Consume(u8),
    /// Consumes one atom and yields **the atom itself**.
    ///
    /// This is what makes the fixture's `parser` source-dependent: with a
    /// constant-valued subject, associativity threads exactly one value into
    /// `continuation_k` and the continuation has nothing to branch on.
    ConsumeAtom,
    /// Consumes nothing and yields `t`.
    Yield(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Missing(u8);

impl PartialPrefixParser for Leaf {
    type Source = [u8];
    type Value = u8;
    type Witness = ();
    type Diagnostic = Missing;
    type Error = CombinatorError<()>;

    fn parse_prefix(
        &self,
        source: &[u8],
        start: usize,
    ) -> PrefixParseResult<u8, (), Missing, CombinatorError<()>> {
        let interpretation = |value: u8, end: usize| PrefixInterpretation {
            value,
            witness: (),
            consumed: Span::new(start, end).expect("forward"),
            remainder: end,
        };
        Ok(match *self {
            Leaf::Decline => ParseAttempt::NoMatch(Missing(0)),
            Leaf::Yield(value) => ParseAttempt::Match(interpretation(value, start)),
            Leaf::Consume(value) => match source.get(start) {
                Some(_) => ParseAttempt::Match(interpretation(value, start + 1)),
                None => ParseAttempt::NoMatch(Missing(value)),
            },
            Leaf::ConsumeAtom => match source.get(start) {
                Some(&atom) => ParseAttempt::Match(interpretation(atom, start + 1)),
                None => ParseAttempt::NoMatch(Missing(0)),
            },
        })
    }
}

struct Fixture;

impl PartialLawFixture for Fixture {
    type Source = [u8];
    type Owned = Vec<u8>;
    type Value = u8;
    type Witness = ();
    type Diagnostic = Missing;
    type Failure = ();
    type Parser = Leaf;

    /// **Source-dependent by construction.** A constant subject would give
    /// `continuation_k` a single argument across every monad law, so the
    /// branching this fixture advertises would never be reached.
    fn parser(&self) -> Leaf {
        Leaf::ConsumeAtom
    }

    fn alternative(&self) -> Leaf {
        Leaf::Consume(1)
    }

    /// **Matches where the other two decline**, which is the only way the third
    /// operand of the associativity instance is reached at all: `ConsumeAtom` and
    /// `Consume(1)` both need an atom, so at a start past the end of a source
    /// neither produces and the choice falls through to here.
    ///
    /// [`choice_associativity_needs_a_general_third_operand`] is the test that
    /// makes this concrete, by exhibiting a defective choice that the previous
    /// `r = Fail` instance could not see.
    fn third(&self) -> Leaf {
        Leaf::Yield(7)
    }

    fn sources(&self) -> Vec<Vec<u8>> {
        vec![b"abc".to_vec(), b"ab".to_vec(), b"z".to_vec()]
    }

    fn starts(&self) -> Vec<usize> {
        vec![0, 1]
    }

    fn sample_value(&self) -> u8 {
        3
    }

    fn sample_witness(&self) {}

    fn f(&self, value: u8) -> u8 {
        value.wrapping_add(1)
    }

    fn g(&self, value: u8) -> u8 {
        value.wrapping_mul(3)
    }

    /// **Branches on its argument**, which is what keeps the monad laws from
    /// holding structurally.
    ///
    /// The declining branch fires on `b'z'`, a byte [`Fixture::sources`]
    /// actually contains, so `parser` genuinely drives it — a branch guarded on
    /// a value the laws never thread is dead code wearing the costume of
    /// coverage, and is exactly what `check_fixture_is_not_vacuous` now refuses.
    fn continuation_k(&self, value: u8) -> Leaf {
        if value == b'z' {
            Leaf::Decline
        } else {
            Leaf::Consume(value.wrapping_add(10))
        }
    }

    fn continuation_h(&self, value: u8) -> Leaf {
        Leaf::Consume(value.wrapping_mul(2))
    }

    fn pure_continuation(&self, value: u8) -> Leaf {
        Leaf::Yield(value)
    }

    fn failure_diagnostic(&self) -> Missing {
        Missing(255)
    }

    fn merge(&self, left: Missing, _right: Missing) -> Missing {
        left
    }

    fn agree(&mut self, left: &u8, right: &u8) -> bool {
        left == right
    }
}

#[test]
fn host_functor_laws_hold() {
    let mut fixture = Fixture;
    let report = host_functor_laws(&mut fixture);
    assert!(report.is_holding_nonvacuously(), "{:?}", report.failures());
}

/// Identity and homomorphism only — interchange and composition are checked in
/// the syntax encoding instead, for the reason given in `conformance::host`'s
/// module doc: a fixture fixes one `Value`, and the function-carrying side of
/// `Ap` reaches it only through boxed endomorphisms.
#[test]
fn host_applicative_laws_hold() {
    let mut fixture = Fixture;
    let report = host_applicative_laws(&mut fixture);
    assert!(report.is_holding_nonvacuously(), "{:?}", report.failures());
}

#[test]
fn host_monad_laws_hold() {
    let mut fixture = Fixture;
    let report = host_monad_laws(&mut fixture);
    assert!(report.is_holding_nonvacuously(), "{:?}", report.failures());
}

#[test]
fn host_ordered_choice_laws_hold_in_the_diagnostic_forgetting_quotient() {
    let mut fixture = Fixture;
    let report = host_choice_laws(&mut fixture);
    assert!(report.is_holding_nonvacuously(), "{:?}", report.failures());
}

/// **The associativity instance is blind at `r = Fail`, and this exhibits it.**
///
/// `oc(oc(p, q), fail)` and `oc(p, oc(q, fail))` both reduce to `oc(p, q)` on
/// positive content, so an associativity checked with the unit in the third
/// position measures the right-unit law over again. The bundle's docstring
/// nevertheless said "choice is associative".
///
/// The gap is not hypothetical, and this test is the demonstration. `SkewedChoice`
/// is a *defective* ordered choice that consults its second alternative one atom
/// past the offset it was asked about. The two associations place the third
/// operand at different nesting depths — outer-second on the left, inner-second on
/// the right — so under the defect the left side reaches it one atom late and the
/// right side two. That difference is observable only when the third operand can
/// *match*:
///
/// - with `fail` there, both sides decline identically and the defect is invisible;
/// - with [`Fixture::third`] there, the two sides report different remainders.
///
/// So the first half of this test is the audited weakness, executed, and the
/// second half is the coverage that closes it. Revert
/// [`PartialLawFixture::third`] to `partial::fail` in the associativity instance
/// and the bundle goes back to certifying the defect.
///
/// Nothing here weakens the side condition of §e.3: associativity still holds only
/// in the diagnostic-forgetting quotient (or for an associative `merge`), and this
/// test compares observations, which carry no diagnostic.
#[test]
fn choice_associativity_needs_a_general_third_operand() {
    /// Consults its second alternative at `start + 1`. Correct choice would use
    /// `start`.
    struct SkewedChoice<P, Q> {
        first: P,
        second: Q,
    }

    type Pinned = CombinatorError<()>;

    impl<P, Q> PartialPrefixParser for SkewedChoice<P, Q>
    where
        P: PartialPrefixParser<
                Source = [u8],
                Value = u8,
                Witness = (),
                Diagnostic = Missing,
                Error = Pinned,
            >,
        Q: PartialPrefixParser<
                Source = [u8],
                Value = u8,
                Witness = (),
                Diagnostic = Missing,
                Error = Pinned,
            >,
    {
        type Source = [u8];
        type Value = u8;
        type Witness = ();
        type Diagnostic = Missing;
        type Error = Pinned;

        fn parse_prefix(
            &self,
            source: &[u8],
            start: usize,
        ) -> PrefixParseResult<u8, (), Missing, Pinned> {
            match self.first.parse_prefix(source, start)? {
                ParseAttempt::Match(matched) => Ok(ParseAttempt::Match(matched)),
                ParseAttempt::NoMatch(_) => self.second.parse_prefix(source, start + 1),
            }
        }
    }

    let owned = Fixture.sources();
    let borrowed: Vec<&[u8]> = owned.iter().map(Vec::as_slice).collect();
    let starts = Fixture.starts();
    let corpus = fixture_corpus::<Fixture>(&borrowed, &starts);

    let p = Fixture.parser();
    let q = Fixture.alternative();
    let unit = || partial::fail::<[u8], u8, (), Missing, Pinned>(Missing(255));

    let left = SkewedChoice {
        first: SkewedChoice {
            first: p,
            second: q,
        },
        second: unit(),
    };
    let right = SkewedChoice {
        first: p,
        second: SkewedChoice {
            first: q,
            second: unit(),
        },
    };
    let blind = {
        let mut left =
            |source: &[u8], start: usize| observe_partial(left.parse_prefix(source, start));
        let mut right =
            |source: &[u8], start: usize| observe_partial(right.parse_prefix(source, start));
        morphism::check_encodings_agree_partial(
            &mut left,
            &mut right,
            &corpus,
            &mut AgreeBy(|left: &u8, right: &u8| left == right),
        )
    };
    assert!(
        blind.is_agreeing() && !blind.is_vacuous(),
        "the unit third operand was expected to hide the defect; if this is now red the \
         demonstration has changed shape and the coverage claim below needs restating: {blind:?}"
    );

    let r = Fixture.third();
    let left = SkewedChoice {
        first: SkewedChoice {
            first: p,
            second: q,
        },
        second: r,
    };
    let right = SkewedChoice {
        first: p,
        second: SkewedChoice {
            first: q,
            second: r,
        },
    };
    let caught = {
        let mut left =
            |source: &[u8], start: usize| observe_partial(left.parse_prefix(source, start));
        let mut right =
            |source: &[u8], start: usize| observe_partial(right.parse_prefix(source, start));
        morphism::check_encodings_agree_partial(
            &mut left,
            &mut right,
            &corpus,
            &mut AgreeBy(|left: &u8, right: &u8| left == right),
        )
    };
    assert!(
        !caught.is_agreeing(),
        "a general third operand did not reach the third position: the fixture's `third` \
         never matches where `parser` and `alternative` both decline, so the associativity \
         instance is still degenerate: {caught:?}"
    );
}

#[test]
fn host_ordered_choice_is_not_commutative() {
    let mut fixture = Fixture;
    let report = host_choice_is_not_commutative(&mut fixture);
    assert!(report.exhibited(), "{report:?}");
}

/// The fixture's own samples, reused by a *cross-capability* law — which is what
/// [`fixture_corpus`] exists for and, until now, nothing did.
///
/// The tier-(i) bundles above run over `Fixture::sources()` internally; M2 takes
/// a [`Corpus`] instead. Rebuilding one by hand here would let the two drift, so
/// the corpus is derived from the fixture and the host encoding's own parser is
/// the subject.
///
/// [`Corpus`]: covalence_combinator_parsing::morphism::Corpus
#[test]
fn the_fixture_corpus_drives_partial_embeds_in_relational() {
    let owned = Fixture.sources();
    let borrowed: Vec<&[u8]> = owned.iter().map(Vec::as_slice).collect();
    let starts = Fixture.starts();
    let corpus = fixture_corpus::<Fixture>(&borrowed, &starts);

    let subject = Fixture.parser();
    let widened = WidenPartialToRelational(subject);
    let mut partial =
        |source: &[u8], start: usize| observe_partial(subject.parse_prefix(source, start));
    let mut relational =
        |source: &[u8], start: usize| observe_relational(widened.parse_prefixes(source, start));
    let report = morphism::check_partial_embeds_in_relational(
        &mut partial,
        &mut relational,
        &corpus,
        &mut AgreeBy(|left: &u8, right: &u8| left == right),
        &CollectionPolicy::AS_ENUMERATED,
    );
    assert!(report.is_agreeing() && !report.is_vacuous(), "{report:?}");
}

// ---------------------------------------------------------------------------
// The suite can fail
// ---------------------------------------------------------------------------

/// **A mutation test for the harness itself.**
///
/// Every other test here asserts a report is green. That is only evidence if a
/// wrong claim would make it red — so this feeds the functor bundle a *false*
/// claim about `g ∘ f` and requires the failure to be reported.
#[test]
fn the_harness_reports_a_false_claim_as_a_failure() {
    let mut inputs = reference::functor_inputs();
    // `Succ ∘ Succ` is `Twice`, not `Identity`.
    inputs.g_after_f = reference::Function::Identity;
    let report = f_laws::check_functor_laws(
        &Env,
        &inputs,
        &reference::corpus(),
        BUDGET,
        &mut reference::agreement(),
    );
    assert!(
        !report.is_holding(),
        "a false composition claim was reported as holding"
    );
    assert!(!report.failures().is_empty());
}

/// The corresponding mutation for the collection policy: comparing two
/// differently-ordered unions as enumerated sequences must fail, since
/// enumeration order is meaningful data rather than an artifact.
#[test]
fn order_sensitivity_is_real_and_not_merely_documented() {
    let forward = Relational::Union(vec![
        reference::relational_atom(1),
        reference::relational_atom(2),
    ]);
    let backward = Relational::Union(vec![
        reference::relational_atom(2),
        reference::relational_atom(1),
    ]);
    let mut left = relational_observer(&forward);
    let mut right = relational_observer(&backward);
    let as_enumerated = morphism::check_encodings_agree_relational(
        &mut left,
        &mut right,
        &reference::corpus(),
        &mut agreement(),
        &CollectionPolicy::AS_ENUMERATED,
    );
    assert!(
        !as_enumerated.is_agreeing(),
        "order-sensitive comparison did not see the reordering"
    );

    let mut left = relational_observer(&forward);
    let mut right = relational_observer(&backward);
    let up_to_permutation = morphism::check_encodings_agree_relational(
        &mut left,
        &mut right,
        &reference::corpus(),
        &mut agreement(),
        &CollectionPolicy::UP_TO_PERMUTATION,
    );
    assert!(up_to_permutation.is_agreeing(), "{up_to_permutation:?}");
}

/// The reassociation used to relate the two sides of bind-associativity round
/// trips in both directions and preserves **both** split offsets.
///
/// Without this the associativity law is worthless: a reassociation that dropped
/// a split would make it pass vacuously, which is the failure one of the source
/// designs discovered at runtime and the reason the sequence witness carries a
/// split at all.
#[test]
fn reassociation_round_trips_and_preserves_splits() {
    use covalence_combinator_parsing::host::{SeqWitness, reassociate_left, reassociate_right};
    let left_nested = SeqWitness {
        first: SeqWitness {
            first: 'a',
            second: 'b',
            split: 3,
        },
        second: 'c',
        split: 7,
    };
    let right_nested = reassociate_right(left_nested.clone());
    assert_eq!(right_nested.split, 3);
    assert_eq!(right_nested.second.split, 7);
    assert_eq!(reassociate_left(right_nested), left_nested);
}
