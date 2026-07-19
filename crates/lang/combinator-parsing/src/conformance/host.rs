//! Tier (i) for encoding T — the host encoding, where programs are Rust values.
//!
//! Host combinator values contain closures, so they cannot be generated: there is
//! no way to enumerate arbitrary `Fn`s. Subjects are therefore supplied by a
//! [`PartialLawFixture`] rather than produced by a generator, and this tier is
//! correspondingly weaker than the syntax tier. That asymmetry is the second
//! reason the syntax encoding is kept.
//!
//! # Honest limitations of a fixture-driven tier
//!
//! 1. **The fixture fixes `Value`,** so functor and applicative laws are checked
//!    over endomorphisms `V → V` rather than over all `A → B`. That is strictly
//!    weaker than parametric law checking and **cannot detect a violation that
//!    only appears at a type change**.
//! 2. **The composite `g ∘ f` is constructed here**, unlike in the syntax
//!    encoding where it must be supplied as a caller claim. Host functions are
//!    real closures and are closed under composition, so there is nothing to
//!    claim — but it also means this tier cannot exercise the `Unavailable`
//!    channel, and a suite that only ran here would never see it.
//! 3. **Applicative coverage is partial.** See the marker in the parent module:
//!    `host::partial::Ap` requires the function-carrying parser's value to be
//!    callable, which a single fixed `Value` type reaches only through boxed
//!    function values. Identity and homomorphism are checked; interchange and
//!    composition are checked in the syntax encoding instead.
//!
//! # The fixture must not be stateless
//!
//! A fixture whose `Parser` is a unit struct cannot have a continuation that
//! depends on its argument, and **every monad law then holds structurally**
//! regardless of whether `Bind` threads offsets correctly. Such a fixture tests
//! nothing while reporting green. [`check_fixture_is_not_vacuous`] asserts the
//! shipped fixture's continuations actually branch on their argument, and it
//! should be run before any other law in this module.
//!
//! The guard takes **no probe values**: hand-picked probes are the failure mode
//! it exists to prevent, since a fixture whose continuation branches only at a
//! value the laws never thread is exactly as vacuous as one that never branches
//! at all. It derives its probes from the fixture instead — see
//! [`check_fixture_is_not_vacuous`]. A corollary obligation falls on the
//! fixture: `parser` must produce a value that **depends on the source**, or the
//! only value associativity ever threads is a constant and the probe set
//! collapses to one point.
//!
//! **All three continuations are measured, separately.** `continuation_h` is
//! threaded by associativity exactly as `continuation_k` is — it is the outer
//! continuation on the left association and the inner one on the right — and
//! `pure_continuation` carries the entire content of right identity, since
//! `bind p pure ≡ p` is structurally true the moment `pure_continuation`
//! collapses to a constant. Measuring only `continuation_k` leaves two of the
//! three monad laws resting on unmeasured assumptions. The per-continuation
//! reports are kept apart in [`VacuityReport`] rather than folded into one,
//! because a `continuation_k` that branches would otherwise mask a
//! `continuation_h` that does not.

use crate::conformance::{ConformanceReport, LawReport};
use crate::host::cursor::{CombinatorError, SourceExtent};
use crate::host::partial;
use crate::morphism::agreement::{AgreementOutcome, Corpus, ScopeReport, ValueAgreement};
use crate::morphism::check::compare_partial;
use crate::morphism::{PartialObserved, observe_partial};
use core::borrow::Borrow;
use covalence_parsing_api::{ParseAttempt, PartialPrefixParser};

/// A caller-supplied subject for the host-encoding law bundles.
///
/// **Deviation from the brief**, forced: the brief's `type Error` is split into
/// `type Failure` with the parser's error pinned to
/// `CombinatorError<Self::Failure>`. Host `Ap`, `Bind` and `OrderedChoice`
/// already require that convention — they join two extents and must be able to
/// report a cursor violation as evaluator failure — so a fixture free to choose
/// any error type could not be plugged into them at all.
pub trait PartialLawFixture {
    type Source: ?Sized + SourceExtent;
    /// `Source: ?Sized` cannot be owned, so the corpus is owned separately and
    /// borrowed.
    type Owned: Borrow<Self::Source>;
    type Value;
    type Witness;
    /// `Clone` because `partial::Fail` reports the same diagnostic at every
    /// offset it is asked about.
    type Diagnostic: Clone;
    type Failure;
    /// **Must be a value-carrying type, not a unit struct** — see the module doc
    /// and [`check_fixture_is_not_vacuous`].
    type Parser: PartialPrefixParser<
            Source = Self::Source,
            Value = Self::Value,
            Witness = Self::Witness,
            Diagnostic = Self::Diagnostic,
            Error = CombinatorError<Self::Failure>,
        >;

    /// **Its value must depend on the source.** Associativity threads
    /// `parser`'s output into `continuation_k`, so a constant-valued `parser`
    /// gives the continuation a single input to branch on and the law holds
    /// structurally. [`check_fixture_is_not_vacuous`] measures this indirectly:
    /// its probe set is derived from exactly these values.
    fn parser(&self) -> Self::Parser;
    /// A second, *behaviourally different* parser. Choice associativity with
    /// three copies of one parser survives argument-ordering bugs.
    fn alternative(&self) -> Self::Parser;
    /// A third parser, **behaviourally different from both of the above**, used
    /// as the third operand of the associativity instance in
    /// [`check_ordered_choice_laws`].
    ///
    /// The unit will not do here, and this method exists because it was being
    /// used. `oc(oc(p, q), fail)` and `oc(p, oc(q, fail))` both reduce to
    /// `oc(p, q)` on positive content, so an associativity checked at `r = fail`
    /// degenerates into the right-unit law already checked beside it — the bundle
    /// then claims "choice is associative" while measuring an instance of a law
    /// it has already measured. It is blind, in particular, to any defect that
    /// only moves the *third* operand: the two associations put `r` at different
    /// nesting depths, so a choice that consulted its second alternative at the
    /// wrong offset reaches a different offset on the two sides only when `r` is
    /// a parser that can match.
    ///
    /// **Give it a behaviour the other two do not have** — one that matches where
    /// they both decline is the strongest choice, since it is the only way the
    /// third position is reached at all.
    ///
    /// The law this feeds holds only in the diagnostic-forgetting quotient, or
    /// when [`merge`](Self::merge) is itself associative; that side condition is
    /// unchanged by the third operand and is stated on
    /// [`check_ordered_choice_laws`].
    fn third(&self) -> Self::Parser;
    fn sources(&self) -> Vec<Self::Owned>;
    fn starts(&self) -> Vec<usize>;

    /// A value and a witness the `pure` laws can construct afresh on each call.
    /// A factory rather than a stored value, because `Box<dyn Fn>` is `Fn` but
    /// not `Clone`.
    fn sample_value(&self) -> Self::Value;
    fn sample_witness(&self) -> Self::Witness;

    fn f(&self, value: Self::Value) -> Self::Value;
    fn g(&self, value: Self::Value) -> Self::Value;

    /// Two *distinct, non-trivial* continuations. One is not enough:
    /// associativity with `k = h` survives argument-ordering and offset-threading
    /// bugs routinely.
    ///
    /// **All three must branch on their argument**, and
    /// [`check_fixture_is_not_vacuous`] measures each one separately. `h` is
    /// threaded by associativity exactly as `k` is, and `pure_continuation` is
    /// the whole content of right identity: `bind p pure ≡ p` holds structurally
    /// for a constant `pure_continuation` whatever `Bind` does with offsets.
    fn continuation_k(&self, value: Self::Value) -> Self::Parser;
    fn continuation_h(&self, value: Self::Value) -> Self::Parser;
    fn pure_continuation(&self, value: Self::Value) -> Self::Parser;

    fn failure_diagnostic(&self) -> Self::Diagnostic;
    fn merge(&self, left: Self::Diagnostic, right: Self::Diagnostic) -> Self::Diagnostic;

    /// Caller-supplied agreement. **There is no `Value: PartialEq` bound
    /// anywhere**; this method is the only equality the harness has.
    fn agree(&mut self, left: &Self::Value, right: &Self::Value) -> bool;
}

type Observed<F> = PartialObserved<
    <F as PartialLawFixture>::Value,
    CombinatorError<<F as PartialLawFixture>::Failure>,
>;

/// One sample: `(source index, start, left observation, right observation)`.
type Samples<F> = Vec<(usize, usize, Observed<F>, Observed<F>)>;

/// Bridges the fixture's `agree` into the harness's agreement trait, so that the
/// comparison path is shared with every other tier rather than reimplemented.
struct FixtureAgreement<'a, F>(&'a mut F);

impl<F: PartialLawFixture> ValueAgreement<F::Value, F::Value> for FixtureAgreement<'_, F> {
    type Evidence = ();

    fn agree(&mut self, left: &F::Value, right: &F::Value) -> Option<()> {
        self.0.agree(left, right).then_some(())
    }
}

/// Observe both sides of a law over the fixture's corpus.
///
/// Collected in a first pass that borrows the fixture immutably, so that the
/// second pass may take it mutably for `agree`. Observations own their values, so
/// nothing borrowed survives the first pass.
fn collect<F, L, R>(fixture: &F, left: &L, right: &R) -> Samples<F>
where
    F: PartialLawFixture,
    L: PartialPrefixParser<
            Source = F::Source,
            Value = F::Value,
            Diagnostic = F::Diagnostic,
            Error = CombinatorError<F::Failure>,
        >,
    R: PartialPrefixParser<
            Source = F::Source,
            Value = F::Value,
            Diagnostic = F::Diagnostic,
            Error = CombinatorError<F::Failure>,
        >,
{
    let owned = fixture.sources();
    let starts = fixture.starts();
    let mut samples = Vec::new();
    for (index, source) in owned.iter().enumerate() {
        let source = source.borrow();
        for &start in &starts {
            samples.push((
                index,
                start,
                observe_partial(left.parse_prefix(source, start)),
                observe_partial(right.parse_prefix(source, start)),
            ));
        }
    }
    samples
}

fn judge<F: PartialLawFixture>(
    law: &'static str,
    fixture: &mut F,
    samples: Samples<F>,
) -> LawReport {
    let mut report = LawReport::new(law);
    let mut agreement = FixtureAgreement(fixture);
    for (index, start, left, right) in samples {
        let outcome = compare_partial(left, right, &mut agreement);
        report.record(index, start, outcome);
    }
    report
}

/// > **identity** `map id p ≡ p`
/// > **composition** `map g (map f p) ≡ map (g ∘ f) p`
///
/// Over endomorphisms only — see the module doc. Witnesses differ between the two
/// sides of composition by construction, and nothing here compares them.
pub fn check_functor_laws<F: PartialLawFixture>(fixture: &mut F) -> ConformanceReport {
    let mut report = ConformanceReport::new("host functor");

    let samples = {
        let subject = fixture.parser();
        collect::<F, _, _>(
            fixture,
            &partial::Map {
                parser: partial::Ref(&subject),
                function: |value: F::Value| value,
            },
            &partial::Ref(&subject),
        )
    };
    report.push(judge("host functor identity", fixture, samples));

    let samples = {
        let subject = fixture.parser();
        collect::<F, _, _>(
            fixture,
            &partial::Map {
                parser: partial::Map {
                    parser: partial::Ref(&subject),
                    function: |value: F::Value| fixture.f(value),
                },
                function: |value: F::Value| fixture.g(value),
            },
            &partial::Map {
                parser: partial::Ref(&subject),
                function: |value: F::Value| fixture.g(fixture.f(value)),
            },
        )
    };
    report.push(judge("host functor composition", fixture, samples));

    report
}

/// > **identity** `ap (pure id) p ≡ p`
/// > **homomorphism** `ap (pure f) (pure x) ≡ pure (f x)`
///
/// Interchange and composition are **not** checked here; see limitation 3 in the
/// module doc and the marker in the parent module. They are checked in full in
/// the syntax encoding, where application goes through the environment and the
/// value universe is single-sorted.
pub fn check_applicative_laws<F: PartialLawFixture>(fixture: &mut F) -> ConformanceReport {
    type Endo<'a, V> = Box<dyn Fn(V) -> V + 'a>;
    let mut report = ConformanceReport::new("host applicative");

    let samples = {
        let subject = fixture.parser();
        collect::<F, _, _>(
            fixture,
            &partial::Ap {
                functions: partial::pure::<F::Source, _, F::Diagnostic, CombinatorError<F::Failure>>(
                    || {
                        (
                            Box::new(|value: F::Value| value) as Endo<'_, F::Value>,
                            fixture.sample_witness(),
                        )
                    },
                ),
                arguments: partial::Ref(&subject),
            },
            &partial::Ref(&subject),
        )
    };
    report.push(judge("host applicative identity", fixture, samples));

    let samples = collect::<F, _, _>(
        fixture,
        &partial::Ap {
            functions: partial::pure::<F::Source, _, F::Diagnostic, CombinatorError<F::Failure>>(
                || {
                    (
                        Box::new(|value: F::Value| fixture.f(value)) as Endo<'_, F::Value>,
                        fixture.sample_witness(),
                    )
                },
            ),
            arguments: partial::pure::<F::Source, _, F::Diagnostic, CombinatorError<F::Failure>>(
                || (fixture.sample_value(), fixture.sample_witness()),
            ),
        },
        &partial::pure::<F::Source, _, F::Diagnostic, CombinatorError<F::Failure>>(|| {
            (fixture.f(fixture.sample_value()), fixture.sample_witness())
        }),
    );
    report.push(judge("host applicative homomorphism", fixture, samples));

    report
}

/// > **left identity** `bind (pure v) k ≡ k v`
/// > **right identity** `bind p pure ≡ p`
/// > **associativity** `bind (bind p k) h ≡ bind p (\x -> bind (k x) h)`
///
/// Associativity **only up to the observation projection**: the two sides carry
/// `SeqWitness<SeqWitness<A,B>,C>` and `SeqWitness<A,SeqWitness<B,C>>`
/// respectively, which are different types, so the on-the-nose statement is not
/// expressible. A reassociation between them exists and round-trips, but its
/// iso-hood is unproved, so this is the honest check.
pub fn check_monad_laws<F: PartialLawFixture>(fixture: &mut F) -> ConformanceReport {
    let mut report = ConformanceReport::new("host monad");

    let samples = {
        let resolved = fixture.continuation_k(fixture.sample_value());
        collect::<F, _, _>(
            fixture,
            &partial::Bind {
                parser: partial::pure::<F::Source, _, F::Diagnostic, CombinatorError<F::Failure>>(
                    || (fixture.sample_value(), fixture.sample_witness()),
                ),
                continuation: |value: F::Value| fixture.continuation_k(value),
            },
            &partial::Ref(&resolved),
        )
    };
    report.push(judge("host monad left identity", fixture, samples));

    let samples = {
        let subject = fixture.parser();
        collect::<F, _, _>(
            fixture,
            &partial::Bind {
                parser: partial::Ref(&subject),
                continuation: |value: F::Value| fixture.pure_continuation(value),
            },
            &partial::Ref(&subject),
        )
    };
    report.push(judge("host monad right identity", fixture, samples));

    let samples = {
        let subject = fixture.parser();
        collect::<F, _, _>(
            fixture,
            &partial::Bind {
                parser: partial::Bind {
                    parser: partial::Ref(&subject),
                    continuation: |value: F::Value| fixture.continuation_k(value),
                },
                continuation: |value: F::Value| fixture.continuation_h(value),
            },
            &partial::Bind {
                parser: partial::Ref(&subject),
                continuation: |value: F::Value| partial::Bind {
                    parser: fixture.continuation_k(value),
                    continuation: |inner: F::Value| fixture.continuation_h(inner),
                },
            },
        )
    };
    report.push(judge("host monad associativity", fixture, samples));

    report
}

/// The left-biased monoid laws, in the diagnostic-forgetting quotient.
///
/// > `Fail` is a two-sided unit; choice is associative and idempotent.
///
/// Associativity is checked over three *general* operands —
/// [`parser`](PartialLawFixture::parser),
/// [`alternative`](PartialLawFixture::alternative) and
/// [`third`](PartialLawFixture::third) — and never with the unit in the third
/// position, which would reduce the instance to the right-unit law checked beside
/// it. What the bundle measures is therefore what its wording claims.
///
/// # Associativity is checked *inside* a quotient this harness cannot see out of
///
/// The two associations fold diagnostics as `merge(merge(dp, dq), dr)` against
/// `merge(dp, merge(dq, dr))`, and are equal only when the caller's `merge` is
/// itself associative. Observations carry no diagnostic, so a green result here
/// says nothing about the unquotiented law. This is a limitation of the check,
/// not a vindication — and `host::partial`'s own tests demonstrate the difference
/// with a deliberately non-associative merge. The law's name in the report keeps
/// the side condition attached rather than relying on this doc being read.
///
/// Commutativity is not among them; see [`check_ordered_choice_is_not_commutative`].
pub fn check_ordered_choice_laws<F: PartialLawFixture>(fixture: &mut F) -> ConformanceReport {
    let mut report = ConformanceReport::new("host ordered choice");

    let samples = {
        let subject = fixture.parser();
        let diagnostic = fixture.failure_diagnostic();
        collect::<F, _, _>(
            fixture,
            &partial::OrderedChoice {
                first: partial::fail::<F::Source, F::Value, F::Witness, _, _>(diagnostic),
                second: partial::Ref(&subject),
                merge: |left, right| fixture.merge(left, right),
            },
            &partial::Ref(&subject),
        )
    };
    report.push(judge("host choice left unit", fixture, samples));

    let samples = {
        let subject = fixture.parser();
        let diagnostic = fixture.failure_diagnostic();
        collect::<F, _, _>(
            fixture,
            &partial::OrderedChoice {
                first: partial::Ref(&subject),
                second: partial::fail::<F::Source, F::Value, F::Witness, _, _>(diagnostic),
                merge: |left, right| fixture.merge(left, right),
            },
            &partial::Ref(&subject),
        )
    };
    report.push(judge("host choice right unit", fixture, samples));

    let samples = {
        let subject = fixture.parser();
        collect::<F, _, _>(
            fixture,
            &partial::OrderedChoice {
                first: partial::Ref(&subject),
                second: partial::Ref(&subject),
                merge: |left, right| fixture.merge(left, right),
            },
            &partial::Ref(&subject),
        )
    };
    report.push(judge("host choice idempotence", fixture, samples));

    let samples = {
        let subject = fixture.parser();
        let alternative = fixture.alternative();
        // The third operand is a *general* parser, never the unit: with `fail`
        // here both associations collapse onto `oc(subject, alternative)` and the
        // instance says no more than the right-unit law above it. See
        // [`PartialLawFixture::third`].
        let third = fixture.third();
        collect::<F, _, _>(
            fixture,
            &partial::OrderedChoice {
                first: partial::OrderedChoice {
                    first: partial::Ref(&subject),
                    second: partial::Ref(&alternative),
                    merge: |left, right| fixture.merge(left, right),
                },
                second: partial::Ref(&third),
                merge: |left, right| fixture.merge(left, right),
            },
            &partial::OrderedChoice {
                first: partial::Ref(&subject),
                second: partial::OrderedChoice {
                    first: partial::Ref(&alternative),
                    second: partial::Ref(&third),
                    merge: |left, right| fixture.merge(left, right),
                },
                merge: |left, right| fixture.merge(left, right),
            },
        )
    };
    report.push(judge(
        "host choice associativity (diagnostic-forgetting quotient only)",
        fixture,
        samples,
    ));

    report
}

/// **Ordered choice is not commutative**, asserted as a positive claim.
///
/// Success is [`ScopeReport::exhibited`]: a run finding no divergence means the
/// fixture's `parser` and `alternative` never both matched at one offset, so the
/// corpus is too weak — not that ordered choice is commutative.
pub fn check_ordered_choice_is_not_commutative<F: PartialLawFixture>(
    fixture: &mut F,
) -> ScopeReport {
    let samples = {
        let subject = fixture.parser();
        let alternative = fixture.alternative();
        collect::<F, _, _>(
            fixture,
            &partial::OrderedChoice {
                first: partial::Ref(&subject),
                second: partial::Ref(&alternative),
                merge: |left, right| fixture.merge(left, right),
            },
            &partial::OrderedChoice {
                first: partial::Ref(&alternative),
                second: partial::Ref(&subject),
                merge: |left, right| fixture.merge(left, right),
            },
        )
    };
    let mut report = ScopeReport::new("host ordered choice is not commutative");
    let mut agreement = FixtureAgreement(fixture);
    for (index, start, left, right) in samples {
        match compare_partial(left, right, &mut agreement) {
            AgreementOutcome::Agreed => report.record_agreement(),
            AgreementOutcome::Disagreed(_) => report.record_divergence(index, start),
            AgreementOutcome::Inconclusive { .. } => report.record_inconclusive(),
        }
    }
    report
}

/// The values [`check_monad_laws`] actually threads into the fixture's
/// continuations: `sample_value`, which left identity binds directly, followed by
/// every value `parser` produces over the fixture's own corpus, which
/// associativity threads through `Bind`.
///
/// Recomputed on every call rather than collected once and reused, because
/// `F::Value` carries no `Clone` bound anywhere in this trait — that is the same
/// reason `sample_value` is a factory. Callers therefore index a *fresh* list per
/// probe, and a fixture that fails to reproduce its own values is reported
/// inconclusive rather than panicking.
fn threaded_values<F: PartialLawFixture>(fixture: &F) -> Vec<F::Value> {
    let parser = fixture.parser();
    let owned = fixture.sources();
    let starts = fixture.starts();
    let mut values = vec![fixture.sample_value()];
    for source in &owned {
        let source = source.borrow();
        for &start in &starts {
            if let Ok(ParseAttempt::Match(interpretation)) = parser.parse_prefix(source, start) {
                values.push(interpretation.value);
            }
        }
    }
    values
}

fn nth_threaded_value<F: PartialLawFixture>(fixture: &F, index: usize) -> Option<F::Value> {
    threaded_values(fixture).into_iter().nth(index)
}

/// One continuation's worth of evidence: does it *behave* differently at two
/// different threaded values?
///
/// Factored out so that the three continuations are measured by identical code
/// over an identical, fixture-derived probe set. A per-continuation variant of
/// this loop would be exactly the place a hand-picked probe crept back in.
fn probe_continuation<F: PartialLawFixture>(
    claim: &'static str,
    fixture: &mut F,
    continuation: fn(&F, F::Value) -> F::Parser,
) -> ScopeReport {
    let mut report = ScopeReport::new(claim);
    let probes = threaded_values(fixture).len();
    for left in 0..probes {
        for right in (left + 1)..probes {
            let samples = {
                let (Some(left), Some(right)) = (
                    nth_threaded_value(fixture, left),
                    nth_threaded_value(fixture, right),
                ) else {
                    report.record_inconclusive();
                    continue;
                };
                let from_left = continuation(fixture, left);
                let from_right = continuation(fixture, right);
                collect::<F, _, _>(
                    fixture,
                    &partial::Ref(&from_left),
                    &partial::Ref(&from_right),
                )
            };
            let mut agreement = FixtureAgreement(fixture);
            for (index, start, l, r) in samples {
                match compare_partial(l, r, &mut agreement) {
                    AgreementOutcome::Agreed => report.record_agreement(),
                    AgreementOutcome::Disagreed(_) => report.record_divergence(index, start),
                    AgreementOutcome::Inconclusive { .. } => report.record_inconclusive(),
                }
            }
        }
    }
    report
}

/// Per-continuation vacuity evidence, deliberately **not merged into one report**.
///
/// A single [`ScopeReport`] is [`exhibited`](ScopeReport::exhibited) as soon as
/// *any* divergence is found anywhere in it, so folding the three continuations
/// together would let a branching `continuation_k` certify a constant
/// `continuation_h` — the precise vacuity this guard exists to catch, reproduced
/// inside the guard. Each continuation therefore carries its own report and
/// [`Self::exhibited`] is a conjunction.
#[derive(Clone, Debug)]
pub struct VacuityReport {
    pub continuation_k: ScopeReport,
    pub continuation_h: ScopeReport,
    pub pure_continuation: ScopeReport,
}

impl VacuityReport {
    fn reports(&self) -> [&ScopeReport; 3] {
        [
            &self.continuation_k,
            &self.continuation_h,
            &self.pure_continuation,
        ]
    }

    /// **The success condition: every continuation branched somewhere.** A
    /// `false` here means the fixture is too weak for the monad laws to measure
    /// anything, not that a law is false.
    pub fn exhibited(&self) -> bool {
        self.reports().iter().all(|report| report.exhibited())
    }

    /// The claims of the continuations that never diverged — what to name in an
    /// assertion message, so a failure says *which* continuation is constant
    /// rather than only that one is.
    pub fn constant(&self) -> Vec<&'static str> {
        self.reports()
            .iter()
            .filter(|report| !report.exhibited())
            .map(|report| report.claim)
            .collect()
    }
}

/// **The fixture actually branches on its argument, at the values the laws
/// thread.**
///
/// A fixture whose continuations ignore their argument makes every monad law hold
/// structurally, regardless of whether `Bind` threads offsets correctly — green,
/// and worthless. So does a fixture whose continuation branches only at some
/// value the laws never produce: the branch exists in the source and is dead in
/// the check.
///
/// The probe set is therefore **derived from the fixture, never passed in**. It
/// is [`threaded_values`]: `sample_value` together with every value `parser`
/// yields over the corpus — precisely the arguments [`check_monad_laws`] hands to
/// its continuations. Every unordered pair of probes is run through the
/// continuation and the two resulting parsers are required to *behave*
/// differently somewhere in the corpus.
///
/// **All three continuations are measured**, over that same probe set:
///
/// - `continuation_k` — threaded by left identity and by both associations.
/// - `continuation_h` — threaded by associativity exactly as `k` is, as the
///   outer continuation on the left association and the inner one on the right.
/// - `pure_continuation` — the entire content of right identity, which holds
///   structurally for a constant `pure_continuation` however `Bind` behaves.
///
/// Success is [`VacuityReport::exhibited`], a conjunction over the three.
/// **Run this before any other law in this module**; a failure here invalidates
/// all of them.
pub fn check_fixture_is_not_vacuous<F: PartialLawFixture>(fixture: &mut F) -> VacuityReport {
    VacuityReport {
        continuation_k: probe_continuation(
            "continuation_k depends on its argument",
            fixture,
            F::continuation_k,
        ),
        continuation_h: probe_continuation(
            "continuation_h depends on its argument",
            fixture,
            F::continuation_h,
        ),
        pure_continuation: probe_continuation(
            "pure_continuation depends on its argument",
            fixture,
            F::pure_continuation,
        ),
    }
}

/// The fixture's corpus, borrowed, for callers who want to run the cross-encoding
/// tiers against the same samples.
pub fn fixture_corpus<'a, F: PartialLawFixture>(
    owned: &'a [&'a F::Source],
    starts: &'a [usize],
) -> Corpus<'a, F::Source> {
    Corpus::new(owned, starts)
}
