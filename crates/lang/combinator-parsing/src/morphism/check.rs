//! Tier (ii) and tier (iii): the cross-encoding and cross-capability laws.
//!
//! Tier (ii) runs along the **encoding axis**: a syntax program evaluated
//! directly against the same program compiled to a host combinator value. Tier
//! (iii) runs along the **capability axis**: the widening adapters and the
//! one-way refinement between ordered choice and relational union.
//!
//! Every function here takes its own two observers. **No law in this module is
//! obtained by chaining two others through the harness**, because caller-supplied
//! heterogeneous agreements do not compose: an agreement between `A` and `B` and
//! one between `B` and `C` induce nothing between `A` and `C`. M5 is the live
//! example — its exact-cardinality claim is strictly stronger than anything the
//! composite of M1 and M2 could give, so it gets its own function rather than
//! being read off a chain.
//!
//! # What is compared, and what is not
//!
//! The trichotomy and the positive projection, always. Diagnostic payloads,
//! never: the syntax encoding builds a flat diagnostic and the host encoding
//! builds whatever the caller's merge builds, and agreement there is neither
//! claimed nor testable. Error payloads, never. Witnesses, never.
//!
//! Failure on either side yields [`AgreementOutcome::Inconclusive`], never a
//! violation. Reassociating an expression changes its resource profile, so one
//! side genuinely can exhaust where the other succeeds, and calling that a law
//! failure would report a resource artifact as a semantic disagreement.
//!
//! # Conditional laws are vacuous until their hypothesis fires
//!
//! M3⁺ is an implication and M3⁻ a biconditional, and both are satisfied on
//! every sample of a corpus whose programs never match. Such a sample increments
//! [`AgreementReport::hypothesis_unsatisfied`], never `checked`, so
//! [`AgreementReport::is_vacuous`] tells the truth about a corpus too weak to
//! exercise them. `is_agreeing()` alone is not evidence for either law.

use crate::morphism::agreement::{
    AgreementOutcome, AgreementReport, CollectionPolicy, Corpus, Disagreement, PartialObserver,
    RelationalObserver, ScopeReport, Side, TotalObserver, ValueAgreement, same_collection_by,
    same_observation_by,
};
use crate::morphism::{
    Observation, PartialObserved, RelationalObserved, TotalObserved, partial_as_relational,
    total_as_partial,
};

/// A caller assertion that a value type has **no distinguished failure
/// inhabitant** — no `None`, no `Err`, no sentinel that a producer could use to
/// mean "did not match".
///
/// # Why this is a trait and not a comment
///
/// "Total" is a claim about a parser's *channel structure*, and a total parser
/// whose value type can encode failure has smuggled the non-match channel back
/// inside the value. Every totality law then holds by construction while
/// measuring nothing. Requiring this bound on the total laws makes the corpus
/// obligation a type error rather than a review note.
///
/// # What this bound does and does not enforce
///
/// **Enforced.** `Option<T>` and `Result<T, E>` — the two types whose *shape* is
/// "a value, or the absence of one" — have no impl, and a downstream crate
/// cannot add one: both the trait and those types are foreign to it, so the
/// orphan rule rejects the impl. A total parser cannot be handed to the laws
/// below with a value type that carries a structural non-match channel.
///
/// ```compile_fail,E0277
/// use covalence_combinator_parsing::morphism::WithoutFailureInhabitant;
/// fn assert_no_failure_inhabitant<V: WithoutFailureInhabitant>() {}
/// // A total parser whose value type can encode failure makes M5 vacuous.
/// assert_no_failure_inhabitant::<Option<u8>>();
/// ```
///
/// **Not enforced, and not enforceable by a trait bound.** A *sentinel
/// convention* in an inhabited type. `Value = Vec<u8>` with the empty vector
/// meaning "did not match", `Value = String` with `""`, `Value = u8` with `0`,
/// `Value = bool` with `false` — every one of these satisfies this bound and is
/// as vacuous as `Option`. Nothing in the type distinguishes them from the same
/// types used honestly, and excluding them would exclude the legitimate uses
/// too. This bound is a *shape* check, not a semantics check, and the earlier
/// wording here ("the obligation is therefore enforced rather than merely
/// documented") overstated it; the corpus obligation of §e.7 remains a caller
/// obligation for anything but the two structural cases above.
///
/// `()` is deliberately **excluded** despite having no failure inhabitant: a
/// single-inhabitant value type makes every [`ValueAgreement`] accept every
/// pair, so every value comparison in every law below succeeds by construction.
/// That is the same vacuity by a different route, and it *is* decidable from the
/// type, so it is decided here.
///
/// ```compile_fail,E0277
/// use covalence_combinator_parsing::morphism::WithoutFailureInhabitant;
/// fn assert_no_failure_inhabitant<V: WithoutFailureInhabitant>() {}
/// // A unit value type makes every value agreement total, so the laws below
/// // compare nothing.
/// assert_no_failure_inhabitant::<()>();
/// ```
pub trait WithoutFailureInhabitant {}

// TODO(cov:lang.combinator-parsing.sentinel-values-undetected, minor): The
// §e.7 corpus obligation is only shape-enforced — a total parser using an
// in-band sentinel (empty `Vec`, `""`, `0`) as "no match" passes
// `WithoutFailureInhabitant` and makes M1/M5 vacuous while green. Add the
// audit counterpart of `audit_relational_ambiguity`: run the caller's
// agreement over the corpus and report whether it ever *distinguished* two
// produced values, so a constant-valued total parser is caught the way a
// non-ambiguous relational corpus already is.

macro_rules! without_failure_inhabitant {
    ($($ty:ty),* $(,)?) => { $(impl WithoutFailureInhabitant for $ty {})* };
}

without_failure_inhabitant!(
    bool, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, char, String,
);

impl<T: WithoutFailureInhabitant> WithoutFailureInhabitant for Vec<T> {}
impl<T: WithoutFailureInhabitant> WithoutFailureInhabitant for Box<T> {}
impl<A: WithoutFailureInhabitant, B: WithoutFailureInhabitant> WithoutFailureInhabitant for (A, B) {}

/// Compare two partial observations on the trichotomy and positive projection.
pub(crate) fn compare_partial<V1, V2, E1, E2, G>(
    left: PartialObserved<V1, E1>,
    right: PartialObserved<V2, E2>,
    agreement: &mut G,
) -> AgreementOutcome
where
    G: ValueAgreement<V1, V2>,
{
    match (left, right) {
        (PartialObserved::Failed(_), _) => AgreementOutcome::Inconclusive { side: Side::Left },
        (_, PartialObserved::Failed(_)) => AgreementOutcome::Inconclusive { side: Side::Right },
        (PartialObserved::Declined, PartialObserved::Declined) => AgreementOutcome::Agreed,
        (PartialObserved::Matched(l), PartialObserved::Matched(r)) => {
            match same_observation_by(&l, &r, agreement) {
                None => AgreementOutcome::Agreed,
                Some(disagreement) => AgreementOutcome::Disagreed(disagreement),
            }
        }
        _ => AgreementOutcome::Disagreed(Disagreement::ShapeMismatch),
    }
}

/// Compare two relational observations under the caller's collection policy.
pub(crate) fn compare_relational<V1, V2, E1, E2, G>(
    left: RelationalObserved<V1, E1>,
    right: RelationalObserved<V2, E2>,
    agreement: &mut G,
    policy: &CollectionPolicy,
) -> AgreementOutcome
where
    G: ValueAgreement<V1, V2>,
{
    match (left, right) {
        (RelationalObserved::Failed(_), _) => AgreementOutcome::Inconclusive { side: Side::Left },
        (_, RelationalObserved::Failed(_)) => AgreementOutcome::Inconclusive { side: Side::Right },
        (RelationalObserved::Enumerated(l), RelationalObserved::Enumerated(r)) => {
            match same_collection_by(&l, &r, agreement, policy) {
                None => AgreementOutcome::Agreed,
                Some(disagreement) => AgreementOutcome::Disagreed(disagreement),
            }
        }
    }
}

/// Compare two total observations.
pub(crate) fn compare_total<V1, V2, E1, E2, G>(
    left: TotalObserved<V1, E1>,
    right: TotalObserved<V2, E2>,
    agreement: &mut G,
) -> AgreementOutcome
where
    G: ValueAgreement<V1, V2>,
{
    match (left, right) {
        (TotalObserved::Failed(_), _) => AgreementOutcome::Inconclusive { side: Side::Left },
        (_, TotalObserved::Failed(_)) => AgreementOutcome::Inconclusive { side: Side::Right },
        (TotalObserved::Produced(l), TotalObserved::Produced(r)) => {
            match same_observation_by(&l, &r, agreement) {
                None => AgreementOutcome::Agreed,
                Some(disagreement) => AgreementOutcome::Disagreed(disagreement),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tier (iii) — axis 1, the refinement laws
// ---------------------------------------------------------------------------

/// **M1 · total ↪ partial.**
///
/// > `P⟦widen(p)⟧(s,i)` is `Match(m)` exactly where `T⟦p⟧(s,i)` is `Ok(m)`.
///
/// # Status: injective, information-preserving embedding
///
/// The adapter's `Diagnostic = Infallible` is what makes this a type-level fact
/// on the image rather than a comment: non-match there is *uninhabited*, not
/// merely unused. This function checks the pointwise consequence.
///
/// The value type is required to have no distinguished failure inhabitant — see
/// [`WithoutFailureInhabitant`]. Without that, "the total side always produced"
/// is satisfiable by producing a value that *means* failure.
pub fn check_total_embeds_in_partial<Src, V1, V2, E1, E2, G>(
    total: TotalObserver<'_, Src, V1, E1>,
    partial: PartialObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
    agreement: &mut G,
) -> AgreementReport
where
    Src: ?Sized,
    V1: WithoutFailureInhabitant,
    G: ValueAgreement<V1, V2>,
{
    let mut report = AgreementReport::new("M1: total embeds in partial");
    for (index, source, start) in corpus.samples() {
        let observed = total_as_partial(total(source, start));
        let outcome = compare_partial(observed, partial(source, start), agreement);
        report.record(index, start, outcome);
    }
    report
}

/// **M2 · partial ↪ relational**, together with its cardinality corollary.
///
/// > `Match(m) ↦ [m]`, `NoMatch(_) ↦ []`, and the result has length **at most 1**.
///
/// # Status: one-way refinement; lossy, non-injective, **no retraction**
///
/// The diagnostic is discarded, so two partial parsers differing only in the
/// diagnostic they report have identical relational behaviour. No law of the
/// shape `narrow(widen(p)) == p` holds, and none is checked here.
pub fn check_partial_embeds_in_relational<Src, V1, V2, E1, E2, G>(
    partial: PartialObserver<'_, Src, V1, E1>,
    relational: RelationalObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
    agreement: &mut G,
    policy: &CollectionPolicy,
) -> AgreementReport
where
    Src: ?Sized,
    G: ValueAgreement<V1, V2>,
{
    let mut report = AgreementReport::new("M2: partial embeds in relational");
    for (index, source, start) in corpus.samples() {
        let widened = partial_as_relational(partial(source, start));
        let observed = relational(source, start);
        // The cardinality corollary is checked on the *relational* side, which is
        // where a violation could actually live.
        if let RelationalObserved::Enumerated(members) = &observed
            && members.len() > 1
        {
            report.record(
                index,
                start,
                AgreementOutcome::Disagreed(Disagreement::CardinalityMismatch),
            );
            continue;
        }
        let outcome = compare_relational(widened, observed, agreement, policy);
        report.record(index, start, outcome);
    }
    report
}

/// **M5 · total ↪ relational**, with the strictly stronger cardinality law.
///
/// > the result is `Err` or has length **exactly** 1.
///
/// # Status: one-way refinement, checked directly
///
/// This is **not** derived from M1 followed by M2, and it must not be. M2 gives
/// only `≤ 1`; the exactly-1 claim is strictly stronger, and heterogeneous
/// agreements do not compose in any case. It is the only behavioural pin on
/// "total" the host can apply — and it is still per-sample, never a proof.
pub fn check_total_embeds_in_relational<Src, V1, V2, E1, E2, G>(
    total: TotalObserver<'_, Src, V1, E1>,
    relational: RelationalObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
    agreement: &mut G,
) -> AgreementReport
where
    Src: ?Sized,
    V1: WithoutFailureInhabitant,
    G: ValueAgreement<V1, V2>,
{
    let mut report = AgreementReport::new("M5: total embeds in relational");
    for (index, source, start) in corpus.samples() {
        let produced = match total(source, start) {
            TotalObserved::Produced(observation) => observation,
            TotalObserved::Failed(_) => {
                report.record(
                    index,
                    start,
                    AgreementOutcome::Inconclusive { side: Side::Left },
                );
                continue;
            }
        };
        let members = match relational(source, start) {
            RelationalObserved::Enumerated(members) => members,
            RelationalObserved::Failed(_) => {
                report.record(
                    index,
                    start,
                    AgreementOutcome::Inconclusive { side: Side::Right },
                );
                continue;
            }
        };
        let outcome = match members.as_slice() {
            [single] => match same_observation_by(&produced, single, agreement) {
                None => AgreementOutcome::Agreed,
                Some(disagreement) => AgreementOutcome::Disagreed(disagreement),
            },
            _ => AgreementOutcome::Disagreed(Disagreement::CardinalityMismatch),
        };
        report.record(index, start, outcome);
    }
    report
}

/// **M3⁺ · ordered choice refines union — the positive direction, one way.**
///
/// > `P⟦oc(p,q)⟧(s,i) == Match(m)` **⟹** some member of
/// > `R⟦union(widen p, widen q)⟧(s,i)` agrees with `m`.
///
/// # Status: one-way **implication**. The converse is false.
///
/// Membership in the union does not imply ordered choice selects it: when both
/// alternatives match, the union has two members and ordered choice yields only
/// the first. Stating this as an equation would be a false law, and turning it
/// into a rewrite rule on programs would be worse — it fails outright under any
/// `bind` above the choice.
///
/// # A declined sample is vacuous, and is counted as such
///
/// A decline satisfies the implication because the hypothesis is what fails —
/// but it pins nothing, and counting it as `checked` was how a corpus of
/// programs that **never match** produced a green, apparently-non-vacuous run:
/// every sample "agreed", the membership branch below never executed, and
/// `is_vacuous()` said the law had run. So declines increment
/// [`AgreementReport::hypothesis_unsatisfied`] instead, and a corpus that never
/// matches is now vacuous by the report's own measure.
///
/// **Assert `!report.is_vacuous()` alongside `report.is_agreeing()`.** The first
/// without the second is not evidence about this law.
pub fn check_choice_refines_union<Src, V1, V2, E1, E2, G>(
    ordered: PartialObserver<'_, Src, V1, E1>,
    union: RelationalObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
    agreement: &mut G,
) -> AgreementReport
where
    Src: ?Sized,
    G: ValueAgreement<V1, V2>,
{
    let mut report = AgreementReport::new("M3+: ordered choice refines union");
    for (index, source, start) in corpus.samples() {
        let matched = match ordered(source, start) {
            PartialObserved::Matched(observation) => observation,
            // The hypothesis fails; the implication holds, vacuously.
            PartialObserved::Declined => {
                report.record_hypothesis_unsatisfied();
                continue;
            }
            PartialObserved::Failed(_) => {
                report.record(
                    index,
                    start,
                    AgreementOutcome::Inconclusive { side: Side::Left },
                );
                continue;
            }
        };
        let members = match union(source, start) {
            RelationalObserved::Enumerated(members) => members,
            RelationalObserved::Failed(_) => {
                report.record(
                    index,
                    start,
                    AgreementOutcome::Inconclusive { side: Side::Right },
                );
                continue;
            }
        };
        let present = members
            .iter()
            .any(|member| same_observation_by(&matched, member, agreement).is_none());
        let outcome = if present {
            AgreementOutcome::Agreed
        } else {
            AgreementOutcome::Disagreed(Disagreement::MissingMember)
        };
        report.record(index, start, outcome);
    }
    report
}

/// **M3⁻ · the emptiness biconditional — the only place the two agree exactly.**
///
/// > `P⟦oc(p,q)⟧(s,i)` declines **⟺** `R⟦union(widen p, widen q)⟧(s,i)` is empty.
///
/// # Status: biconditional, exact — and only because it relates two *evaluators*
///
/// This is **not** a claim that nothing matches. An empty enumeration proves no
/// negative fact; it records that this evaluator, under this budget, enumerated
/// nothing. Reworded as "nothing matches", the statement is false, and its
/// converse — "`v` is not in the union, therefore ordered choice declines" — is
/// not merely untested but not statable as a host test at all.
///
/// No value agreement appears in the signature, deliberately: emptiness is
/// structural and comparing values here would weaken an exact law into an
/// approximate one.
///
/// # The doubly-empty sample is vacuous, and is counted as such
///
/// A biconditional is trivially satisfied when *both* sides are empty, and a
/// corpus of programs that never match is doubly-empty everywhere. That run
/// distinguishes nothing — in particular it does not distinguish this law from
/// the constantly-true one — so those samples increment
/// [`AgreementReport::hypothesis_unsatisfied`] rather than `checked`. Only a
/// sample where ordered choice **matched** and the union enumerated **something**
/// exercises the biconditional's content; the mixed samples, where the two
/// disagree, are the failures the law exists to catch and are recorded as such.
///
/// **Assert `!report.is_vacuous()` alongside `report.is_agreeing()`.**
pub fn check_choice_and_union_agree_on_emptiness<Src, V1, V2, E1, E2>(
    ordered: PartialObserver<'_, Src, V1, E1>,
    union: RelationalObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
) -> AgreementReport
where
    Src: ?Sized,
{
    let mut report = AgreementReport::new("M3-: choice and union agree on emptiness");
    for (index, source, start) in corpus.samples() {
        let declined = match ordered(source, start) {
            PartialObserved::Declined => true,
            PartialObserved::Matched(_) => false,
            PartialObserved::Failed(_) => {
                report.record(
                    index,
                    start,
                    AgreementOutcome::Inconclusive { side: Side::Left },
                );
                continue;
            }
        };
        let empty = match union(source, start) {
            RelationalObserved::Enumerated(members) => members.is_empty(),
            RelationalObserved::Failed(_) => {
                report.record(
                    index,
                    start,
                    AgreementOutcome::Inconclusive { side: Side::Right },
                );
                continue;
            }
        };
        if declined && empty {
            // Both sides trivially empty: the biconditional holds and says nothing.
            report.record_hypothesis_unsatisfied();
            continue;
        }
        let outcome = if declined == empty {
            AgreementOutcome::Agreed
        } else {
            AgreementOutcome::Disagreed(Disagreement::ShapeMismatch)
        };
        report.record(index, start, outcome);
    }
    report
}

/// **M4 · the scoped collapse — true, and therefore dangerous.**
///
/// > `P⟦oc(p,q)⟧(s,i)` agrees with the *first* member of
/// > `R⟦union(widen p, widen q)⟧(s,i)`.
///
/// # Status: true **only** on the image of the partial-to-relational widening
///
/// It is false the moment either operand is genuinely relational — two results at
/// one offset — or any `bind` sits above the choice. It is checked here so that
/// its *scope* is measured, not because it should be offered: there is no
/// `take_first` in this API, and there is a severe marker forbidding one.
///
/// # This function succeeds by finding a divergence
///
/// A corpus built only from widened partial parsers confirms M4 everywhere and
/// proves nothing. So the return type is a [`ScopeReport`], whose success
/// condition is [`ScopeReport::exhibited`] — the corpus actually contained a case
/// where ordered choice and the first union result disagree. A green run with
/// zero divergences means the corpus was too weak, and this type cannot be
/// misread as a pass.
pub fn check_take_first_agreement_is_scoped<Src, V1, V2, E1, E2, G>(
    ordered: PartialObserver<'_, Src, V1, E1>,
    union: RelationalObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
    agreement: &mut G,
) -> ScopeReport
where
    Src: ?Sized,
    G: ValueAgreement<V1, V2>,
{
    let mut report = ScopeReport::new("M4: take-first agreement is scoped, not general");
    for (index, source, start) in corpus.samples() {
        let observed = ordered(source, start);
        let members = match union(source, start) {
            RelationalObserved::Enumerated(members) => members,
            RelationalObserved::Failed(_) => {
                report.record_inconclusive();
                continue;
            }
        };
        let first: Option<&Observation<V2>> = members.first();
        let agrees = match (&observed, first) {
            (PartialObserved::Failed(_), _) => {
                report.record_inconclusive();
                continue;
            }
            (PartialObserved::Declined, None) => true,
            (PartialObserved::Matched(matched), Some(member)) => {
                same_observation_by(matched, member, agreement).is_none()
            }
            _ => false,
        };
        if agrees {
            report.record_agreement();
        } else {
            report.record_divergence(index, start);
        }
    }
    report
}

// ---------------------------------------------------------------------------
// Tier (ii) — axis 2, the cross-encoding laws
// ---------------------------------------------------------------------------

/// **N1 (ordered fragment).** A syntax program evaluated directly against the
/// same program compiled to a host combinator value.
///
/// > The two agree on the match / no-match / error trichotomy and, on a match, on
/// > the positive projection under the caller's agreement.
///
/// # Status: semantics-preserving translation, non-surjective, no inverse
///
/// **Diagnostic payloads are outside the law.** The syntax encoding builds a flat
/// diagnostic; the host encoding builds whatever the caller's merge builds.
/// Agreement there is neither claimed nor testable, and nothing in this function
/// looks at one.
///
/// # Side condition, unchecked
///
/// The law quantifies over `(program, environment)` **pairs**, never over
/// programs alone: rule references and bind continuations resolve through the
/// environment, so two programs equal as data denote different parsers under
/// different environments. Cross-fragment claims additionally require environment
/// coherence between the fragments' resolvers.
pub fn check_encodings_agree_partial<Src, V1, V2, E1, E2, G>(
    syntax: PartialObserver<'_, Src, V1, E1>,
    host: PartialObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
    agreement: &mut G,
) -> AgreementReport
where
    Src: ?Sized,
    G: ValueAgreement<V1, V2>,
{
    let mut report = AgreementReport::new("N1: encodings agree (partial)");
    for (index, source, start) in corpus.samples() {
        let outcome = compare_partial(syntax(source, start), host(source, start), agreement);
        report.record(index, start, outcome);
    }
    report
}

/// **N1 (relational fragment).**
///
/// Compared **in enumeration order** by default: order is meaningful data in this
/// family, and comparing up to permutation is an explicit caller policy rather
/// than a default. There is no diagnostic on either side, permanently.
pub fn check_encodings_agree_relational<Src, V1, V2, E1, E2, G>(
    syntax: RelationalObserver<'_, Src, V1, E1>,
    host: RelationalObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
    agreement: &mut G,
    policy: &CollectionPolicy,
) -> AgreementReport
where
    Src: ?Sized,
    G: ValueAgreement<V1, V2>,
{
    let mut report = AgreementReport::new("N1: encodings agree (relational)");
    for (index, source, start) in corpus.samples() {
        let outcome = compare_relational(
            syntax(source, start),
            host(source, start),
            agreement,
            policy,
        );
        report.record(index, start, outcome);
    }
    report
}

/// **N1 (deterministic fragment).**
///
/// The value type must have no distinguished failure inhabitant, for the reason
/// given on [`WithoutFailureInhabitant`].
pub fn check_encodings_agree_total<Src, V1, V2, E1, E2, G>(
    syntax: TotalObserver<'_, Src, V1, E1>,
    host: TotalObserver<'_, Src, V2, E2>,
    corpus: &Corpus<'_, Src>,
    agreement: &mut G,
) -> AgreementReport
where
    Src: ?Sized,
    V1: WithoutFailureInhabitant,
    G: ValueAgreement<V1, V2>,
{
    let mut report = AgreementReport::new("N1: encodings agree (total)");
    for (index, source, start) in corpus.samples() {
        let outcome = compare_total(syntax(source, start), host(source, start), agreement);
        report.record(index, start, outcome);
    }
    report
}

// ---------------------------------------------------------------------------
// Corpus obligations — §e.2 and §e.7, as checkable predicates
// ---------------------------------------------------------------------------

/// What an ambiguity audit of a relational corpus found.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct AmbiguityAudit {
    /// Samples enumerating two or more results.
    pub multiple_results: usize,
    /// Samples enumerating two or more results that **consume the same extent**.
    /// This is the sharper form of ambiguity, and the one a corpus of widened
    /// partial parsers can never exhibit.
    pub same_extent: usize,
}

impl AmbiguityAudit {
    /// The generator obligation of §e.2, obligation 1. **Assert this in its own
    /// test.** Without it, the entire non-collapse suite is vacuous while green.
    pub fn is_genuinely_ambiguous(&self) -> bool {
        self.same_extent > 0
    }
}

/// Audit a relational observer for genuine ambiguity over a corpus.
///
/// A corpus built only from widened partial parsers has cardinality at most one
/// everywhere, confirms the scoped take-first agreement in every sample, and
/// proves nothing. This is how that is detected rather than assumed.
pub fn audit_relational_ambiguity<Src, V, E>(
    relational: RelationalObserver<'_, Src, V, E>,
    corpus: &Corpus<'_, Src>,
) -> AmbiguityAudit
where
    Src: ?Sized,
{
    let mut audit = AmbiguityAudit::default();
    for (_, source, start) in corpus.samples() {
        let RelationalObserved::Enumerated(members) = relational(source, start) else {
            continue;
        };
        if members.len() < 2 {
            continue;
        }
        audit.multiple_results += 1;
        let shares_extent = members.iter().enumerate().any(|(index, member)| {
            members[index + 1..]
                .iter()
                .any(|other| member.extent() == other.extent())
        });
        if shares_extent {
            audit.same_extent += 1;
        }
    }
    audit
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::morphism::agreement::AgreeBy;
    use covalence_parsing_api::Span;

    fn observation(value: u8, end: usize) -> Observation<u8> {
        Observation {
            value,
            consumed: Span::new(0, end).expect("well-ordered"),
            remainder: end,
        }
    }

    fn identity() -> AgreeBy<impl FnMut(&u8, &u8) -> bool> {
        AgreeBy(|left: &u8, right: &u8| left == right)
    }

    const SOURCES: &[&[u8]] = &[b"ab"];
    const STARTS: &[usize] = &[0];

    fn corpus() -> Corpus<'static, [u8]> {
        Corpus::new(SOURCES, STARTS)
    }

    /// M5 is strictly stronger than the chain of M1 and M2: a relational side
    /// enumerating *two* results passes the `<= 1`-free part of M2's shape check
    /// but must fail M5. This is why the composite has its own function.
    #[test]
    fn the_exact_cardinality_law_is_not_the_chain_of_two_weaker_ones() {
        let mut total = |_: &[u8], _: usize| TotalObserved::<u8, ()>::Produced(observation(1, 1));
        let mut relational = |_: &[u8], _: usize| {
            RelationalObserved::<u8, ()>::Enumerated(vec![observation(1, 1), observation(1, 1)])
        };
        let report = check_total_embeds_in_relational(
            &mut total,
            &mut relational,
            &corpus(),
            &mut identity(),
        );
        assert_eq!(
            report.failures,
            vec![(0, 0, Disagreement::CardinalityMismatch)]
        );
    }

    /// Evaluator failure is inconclusive, never a violation — the budget-asymmetry
    /// rule, exercised.
    #[test]
    fn failure_on_one_side_is_inconclusive() {
        let mut total = |_: &[u8], _: usize| TotalObserved::<u8, &str>::Failed("exhausted");
        let mut partial =
            |_: &[u8], _: usize| PartialObserved::<u8, ()>::Matched(observation(1, 1));
        let report =
            check_total_embeds_in_partial(&mut total, &mut partial, &corpus(), &mut identity());
        assert!(report.is_agreeing() && report.is_vacuous());
        assert_eq!(report.inconclusive, 1);
    }

    /// A decline satisfies M3⁺ *vacuously*, because the implication's hypothesis
    /// is what fails. This is checked so nobody "strengthens" it into an
    /// equation — **and** so that the vacuity is visible in the report rather
    /// than laundered into `checked`.
    #[test]
    fn a_decline_satisfies_the_positive_refinement_vacuously() {
        let mut ordered = |_: &[u8], _: usize| PartialObserved::<u8, ()>::Declined;
        let mut union =
            |_: &[u8], _: usize| RelationalObserved::<u8, ()>::Enumerated(vec![observation(9, 1)]);
        let report =
            check_choice_refines_union(&mut ordered, &mut union, &corpus(), &mut identity());
        assert!(report.is_agreeing());
        // The law held on every sample and measured nothing on every sample.
        assert_eq!((report.checked, report.hypothesis_unsatisfied), (0, 1));
        assert!(report.is_vacuous());
    }

    /// A corpus that never matches makes **both** M3 laws vacuous rather than
    /// agreeing. This is the exact shape that previously read as a clean,
    /// non-vacuous run: ordered choice that always declines against a union that
    /// always enumerates nothing.
    #[test]
    fn a_never_matching_corpus_is_vacuous_for_both_m3_laws() {
        let mut ordered = |_: &[u8], _: usize| PartialObserved::<u8, ()>::Declined;
        let mut union = |_: &[u8], _: usize| RelationalObserved::<u8, ()>::Enumerated(Vec::new());

        let positive =
            check_choice_refines_union(&mut ordered, &mut union, &corpus(), &mut identity());
        assert!(positive.is_agreeing() && positive.is_vacuous());
        assert_eq!(positive.hypothesis_unsatisfied, 1);

        let negative =
            check_choice_and_union_agree_on_emptiness(&mut ordered, &mut union, &corpus());
        assert!(negative.is_agreeing() && negative.is_vacuous());
        assert_eq!(negative.hypothesis_unsatisfied, 1);
    }

    /// A matching sample against a union that contains the match is the one that
    /// actually exercises both laws — `checked`, not `hypothesis_unsatisfied`.
    #[test]
    fn a_match_against_a_nonempty_union_is_a_real_check_of_both_m3_laws() {
        let mut ordered =
            |_: &[u8], _: usize| PartialObserved::<u8, ()>::Matched(observation(9, 1));
        let mut union =
            |_: &[u8], _: usize| RelationalObserved::<u8, ()>::Enumerated(vec![observation(9, 1)]);

        let positive =
            check_choice_refines_union(&mut ordered, &mut union, &corpus(), &mut identity());
        assert!(positive.is_agreeing() && !positive.is_vacuous());
        assert_eq!((positive.checked, positive.hypothesis_unsatisfied), (1, 0));

        let negative =
            check_choice_and_union_agree_on_emptiness(&mut ordered, &mut union, &corpus());
        assert!(negative.is_agreeing() && !negative.is_vacuous());
        assert_eq!((negative.checked, negative.hypothesis_unsatisfied), (1, 0));
    }

    /// M3⁺ still catches a match the union does not contain — the vacuity
    /// counter must not have swallowed the membership branch.
    #[test]
    fn a_match_absent_from_the_union_is_still_a_violation() {
        let mut ordered =
            |_: &[u8], _: usize| PartialObserved::<u8, ()>::Matched(observation(9, 1));
        let mut union =
            |_: &[u8], _: usize| RelationalObserved::<u8, ()>::Enumerated(vec![observation(4, 1)]);
        let report =
            check_choice_refines_union(&mut ordered, &mut union, &corpus(), &mut identity());
        assert_eq!(report.failures, vec![(0, 0, Disagreement::MissingMember)]);
    }

    /// ...but emptiness is a biconditional, and that same pair violates it.
    #[test]
    fn the_emptiness_law_is_a_biconditional_and_catches_what_the_implication_does_not() {
        let mut ordered = |_: &[u8], _: usize| PartialObserved::<u8, ()>::Declined;
        let mut union =
            |_: &[u8], _: usize| RelationalObserved::<u8, ()>::Enumerated(vec![observation(9, 1)]);
        let report = check_choice_and_union_agree_on_emptiness(&mut ordered, &mut union, &corpus());
        assert_eq!(report.failures, vec![(0, 0, Disagreement::ShapeMismatch)]);
    }

    /// A corpus of at-most-one-result parsers is *not* genuinely ambiguous, and
    /// the audit says so rather than reporting a clean bill.
    #[test]
    fn a_widened_partial_corpus_fails_the_ambiguity_obligation() {
        let mut widened =
            |_: &[u8], _: usize| RelationalObserved::<u8, ()>::Enumerated(vec![observation(1, 1)]);
        let audit = audit_relational_ambiguity(&mut widened, &corpus());
        assert!(!audit.is_genuinely_ambiguous());

        let mut ambiguous = |_: &[u8], _: usize| {
            RelationalObserved::<u8, ()>::Enumerated(vec![observation(1, 1), observation(2, 1)])
        };
        let audit = audit_relational_ambiguity(&mut ambiguous, &corpus());
        assert!(audit.is_genuinely_ambiguous());
    }

    /// Two results at the same offset but *different extents* are not the sharp
    /// form of ambiguity the obligation asks for.
    #[test]
    fn differing_extents_are_not_the_ambiguity_the_obligation_requires() {
        let mut staggered = |_: &[u8], _: usize| {
            RelationalObserved::<u8, ()>::Enumerated(vec![observation(1, 1), observation(1, 2)])
        };
        let audit = audit_relational_ambiguity(&mut staggered, &corpus());
        assert_eq!(audit.multiple_results, 1);
        assert!(!audit.is_genuinely_ambiguous());
    }
}
