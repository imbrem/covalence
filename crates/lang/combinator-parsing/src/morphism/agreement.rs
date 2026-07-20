//! The comparison half of the harness: what "agree" means, and who decides.
//!
//! Every equality this crate performs on a *value* is supplied by the caller
//! through [`ValueAgreement`]. There is no `PartialEq` bound on a value type in
//! any signature in this module, and that absence is the enforcement: a harness
//! that reached for host `==` would silently impose an equality the object
//! language never agreed to.
//!
//! Two equalities are *not* caller-supplied, and both are deliberate:
//!
//! - **Extents.** Spans and remainders are host offsets — parsing-API data, not
//!   object values — so they are compared with `==`. This is valid **within one
//!   carrier only**: a byte-indexed and a scalar-indexed encoding of the "same"
//!   parser produce different spans for the same source, so every law here is
//!   indexed by carrier and cross-carrier comparison must go through a decoding.
//! - **The trichotomy.** Whether an observation matched, declined, or failed is
//!   structural. Error *payloads* are never compared; they differ across
//!   encodings by construction.
//!
//! # Three outcomes, not two
//!
//! [`AgreementOutcome::Inconclusive`] is first class because budget asymmetry is
//! real: reassociating an expression changes its resource profile, so one side
//! can exhaust where the other succeeds. That is neither a pass nor a violation,
//! and reporting it as either would be a resource artifact dressed as a semantic
//! claim. A report whose `inconclusive` is a large fraction of `checked` is not
//! evidence of anything, which is why the count is kept rather than swallowed.
//!
//! # Agreements do not compose
//!
//! An agreement between `A` and `B` and one between `B` and `C` do **not** induce
//! one between `A` and `C`. No function in this crate derives a law by chaining
//! two others through this harness; every law function takes its own two
//! observers and is checked directly. Composite claims — M5's exact-cardinality
//! law is the live example — get their own function rather than being read off a
//! chain of two weaker ones.

use crate::morphism::Observation;

/// Caller-supplied agreement between two value types.
///
/// Two type parameters, because the two sides of a law need not share a value
/// type: the syntax encoding's single-sorted value universe compared against the
/// host encoding's real Rust types is the motivating case.
///
/// Agreement yields *evidence*; disagreement is `None`. `&mut self` because
/// membership checks call it once per candidate, so it must be `FnMut`-shaped
/// rather than `FnOnce`-shaped.
///
/// # Caller obligation, unchecked
///
/// [`ResultOrdering::UpToPermutation`] and [`Duplicates::CollapseAgreeing`] are
/// well defined **only if this relation is an equivalence**. Nothing here checks
/// that, and a non-transitive agreement makes those two policies order-dependent.
pub trait ValueAgreement<A, B> {
    type Evidence;

    fn agree(&mut self, left: &A, right: &B) -> Option<Self::Evidence>;
}

/// A `ValueAgreement` from a plain closure, for the common case.
pub struct AgreeBy<F>(pub F);

impl<A, B, F: FnMut(&A, &B) -> bool> ValueAgreement<A, B> for AgreeBy<F> {
    type Evidence = ();

    fn agree(&mut self, left: &A, right: &B) -> Option<()> {
        (self.0)(left, right).then_some(())
    }
}

/// How an enumeration's order is treated.
///
/// **`AsEnumerated` is the default, and it is not over-strict.** Relational
/// order is meaningful data in this family — in-house chart parsers sort their
/// derivations and the stability of that order is asserted by test — so treating
/// it as an artifact would discard a real part of the contract. Comparing up to
/// permutation is an explicit caller decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResultOrdering {
    AsEnumerated,
    UpToPermutation,
}

/// How repeated results are treated.
///
/// **`Retain` is the default.** Union is a free/multiset union: `union(p, p)`
/// enumerates twice as many results, and that is the ambiguity retention the
/// relational capability exists to provide. Collapsing is a *comparison* policy
/// and never an evaluator behaviour.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Duplicates {
    Retain,
    CollapseAgreeing,
}

/// The caller's collection-comparison policy. Every field is a decision the
/// harness refuses to make on the caller's behalf.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CollectionPolicy {
    pub ordering: ResultOrdering,
    pub duplicates: Duplicates,
}

impl CollectionPolicy {
    pub const AS_ENUMERATED: Self = Self {
        ordering: ResultOrdering::AsEnumerated,
        duplicates: Duplicates::Retain,
    };

    pub const UP_TO_PERMUTATION: Self = Self {
        ordering: ResultOrdering::UpToPermutation,
        duplicates: Duplicates::Retain,
    };

    /// The only policy under which union idempotence is even statable — see the
    /// idempotence law in [`crate::conformance::syntax`].
    pub const UP_TO_DEDUPLICATION: Self = Self {
        ordering: ResultOrdering::UpToPermutation,
        duplicates: Duplicates::CollapseAgreeing,
    };
}

impl Default for CollectionPolicy {
    fn default() -> Self {
        Self::AS_ENUMERATED
    }
}

/// Which side of a two-sided law could not be evaluated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

/// How two observations failed to agree. Deliberately coarse: a finer taxonomy
/// would tempt callers to compare payloads that are not comparable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Disagreement {
    /// The trichotomy differed: one side matched where the other declined, and so on.
    ShapeMismatch,
    ValueMismatch,
    ExtentMismatch,
    CardinalityMismatch,
    /// A member required by a one-way refinement was absent from the other side.
    MissingMember,
}

/// The outcome of one sample of one law.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AgreementOutcome {
    Agreed,
    Disagreed(Disagreement),
    /// One side failed or exhausted its budget. **Neither a pass nor a
    /// violation**, and never silently discarded.
    Inconclusive {
        side: Side,
    },
}

/// The result of running one law over one corpus.
///
/// `checked` counts only samples on which the law actually ran; inconclusive
/// samples and hypothesis-unsatisfying samples are counted separately and are
/// not evidence in either direction.
#[derive(Clone, Debug)]
pub struct AgreementReport {
    pub law: &'static str,
    pub checked: usize,
    pub inconclusive: usize,
    /// Samples on which both sides evaluated but the law's **hypothesis was not
    /// satisfied**, so the law held trivially and measured nothing.
    ///
    /// This is the [`ScopeReport`]-shaped counter applied to a conditional law:
    /// an implication whose antecedent never fires, or a biconditional both of
    /// whose sides are trivially empty, is *satisfied* on every sample of the
    /// corpus while pinning no behaviour at all. Counting such a sample as
    /// `checked` is exactly how a corpus of never-matching programs reads as a
    /// green, non-vacuous run.
    ///
    /// Only the conditional laws — M3⁺ and M3⁻ — ever record here. For every
    /// other law this stays zero, because those laws' hypotheses are "the corpus
    /// has a sample", which [`Self::is_vacuous`] already measures.
    pub hypothesis_unsatisfied: usize,
    pub failures: Vec<(usize, usize, Disagreement)>,
}

impl AgreementReport {
    pub fn new(law: &'static str) -> Self {
        Self {
            law,
            checked: 0,
            inconclusive: 0,
            hypothesis_unsatisfied: 0,
            failures: Vec::new(),
        }
    }

    pub fn record(&mut self, source_index: usize, start: usize, outcome: AgreementOutcome) {
        match outcome {
            AgreementOutcome::Agreed => self.checked += 1,
            AgreementOutcome::Disagreed(disagreement) => {
                self.checked += 1;
                self.failures.push((source_index, start, disagreement));
            }
            AgreementOutcome::Inconclusive { .. } => self.inconclusive += 1,
        }
    }

    /// Record a sample the law held on **vacuously**. Deliberately not an
    /// [`AgreementOutcome`]: an outcome is what a comparison produced, and here
    /// no comparison was reached.
    ///
    /// It does **not** increment `checked`, which is the whole point — a run
    /// consisting only of such samples is [`Self::is_vacuous`].
    pub fn record_hypothesis_unsatisfied(&mut self) {
        self.hypothesis_unsatisfied += 1;
    }

    /// Failure to falsify. **Not** a proof: read it together with [`Self::is_vacuous`].
    pub fn is_agreeing(&self) -> bool {
        self.failures.is_empty()
    }

    /// The law never actually ran. A vacuous report is green and worthless.
    ///
    /// For a conditional law this is true exactly when its hypothesis was never
    /// satisfied — see [`Self::hypothesis_unsatisfied`], which says *why* the
    /// run was vacuous rather than merely that it was.
    pub fn is_vacuous(&self) -> bool {
        self.checked == 0
    }
}

/// The report shape for a claim whose content is that a *divergence exists*.
///
/// **Deviation from the brief**, deliberate: scope claims (M4's boundary, the
/// non-commutativity of ordered choice, the failure of ordered choice to
/// distribute over bind) cannot honestly be reported as an [`AgreementReport`],
/// because `is_agreeing` is `failures.is_empty()` and a corpus that never
/// exercised the divergence would then read as a pass. That is exactly the
/// vacuously-green failure mode these claims exist to prevent, so they get a type
/// whose success condition is [`Self::exhibited`] — a divergence was actually
/// found — rather than an absence of failures.
#[derive(Clone, Debug)]
pub struct ScopeReport {
    pub claim: &'static str,
    /// Samples on which both sides evaluated.
    pub checked: usize,
    /// Samples on which the two sides agreed. Agreement is expected here; it is
    /// the *scope* of the agreement that is in question.
    pub agreements: usize,
    /// `(source index, start)` of every sample where the two sides diverged.
    pub divergences: Vec<(usize, usize)>,
    pub inconclusive: usize,
}

impl ScopeReport {
    pub fn new(claim: &'static str) -> Self {
        Self {
            claim,
            checked: 0,
            agreements: 0,
            divergences: Vec::new(),
            inconclusive: 0,
        }
    }

    pub fn record_agreement(&mut self) {
        self.checked += 1;
        self.agreements += 1;
    }

    pub fn record_divergence(&mut self, source_index: usize, start: usize) {
        self.checked += 1;
        self.divergences.push((source_index, start));
    }

    pub fn record_inconclusive(&mut self) {
        self.inconclusive += 1;
    }

    /// The corpus actually exercised the boundary. **This is the success
    /// condition.** A `ScopeReport` with no divergences says the corpus was too
    /// weak to test the claim, not that the claim is false.
    pub fn exhibited(&self) -> bool {
        !self.divergences.is_empty()
    }
}

/// A finite corpus: the cross product of sources and start offsets.
///
/// Finite by construction, because every check in this crate is falsification
/// over a finite corpus under a finite budget. Passing is failure to falsify.
pub struct Corpus<'a, Src: ?Sized> {
    pub sources: &'a [&'a Src],
    pub starts: &'a [usize],
}

impl<'a, Src: ?Sized> Corpus<'a, Src> {
    pub fn new(sources: &'a [&'a Src], starts: &'a [usize]) -> Self {
        Self { sources, starts }
    }

    /// `(source index, source, start)` for every sample.
    pub fn samples(&self) -> impl Iterator<Item = (usize, &'a Src, usize)> + '_ {
        self.sources
            .iter()
            .enumerate()
            .flat_map(move |(index, source)| {
                self.starts
                    .iter()
                    .map(move |start| (index, *source, *start))
            })
    }

    pub fn len(&self) -> usize {
        self.sources.len() * self.starts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.sources.is_empty() || self.starts.is_empty()
    }
}

/// A parser under test, supplied as a closure rather than as a type parameter.
///
/// This is what lets the two sides of a law live in different capabilities,
/// different encodings and different crates — and it is the only reason the
/// cross-encoding tier is writable at all.
pub type TotalObserver<'a, Src, V, E> =
    &'a mut dyn FnMut(&Src, usize) -> crate::morphism::TotalObserved<V, E>;
pub type PartialObserver<'a, Src, V, E> =
    &'a mut dyn FnMut(&Src, usize) -> crate::morphism::PartialObserved<V, E>;
pub type RelationalObserver<'a, Src, V, E> =
    &'a mut dyn FnMut(&Src, usize) -> crate::morphism::RelationalObserved<V, E>;

/// Compare two single observations: value under the caller's agreement, extent
/// under host `==`.
pub fn same_observation_by<A, B, G>(
    left: &Observation<A>,
    right: &Observation<B>,
    agreement: &mut G,
) -> Option<Disagreement>
where
    G: ValueAgreement<A, B>,
{
    if agreement.agree(&left.value, &right.value).is_none() {
        return Some(Disagreement::ValueMismatch);
    }
    if left.extent() != right.extent() {
        return Some(Disagreement::ExtentMismatch);
    }
    None
}

/// Positional comparison. Cardinality must match, and so must order.
pub fn same_sequence_by<A, B, G>(
    left: &[Observation<A>],
    right: &[Observation<B>],
    agreement: &mut G,
) -> Option<Disagreement>
where
    G: ValueAgreement<A, B>,
{
    if left.len() != right.len() {
        return Some(Disagreement::CardinalityMismatch);
    }
    left.iter()
        .zip(right)
        .find_map(|(l, r)| same_observation_by(l, r, agreement))
}

/// Multiset comparison by **greedy consuming** bipartite matching.
///
/// Consuming is load-bearing: a non-consuming membership check would report
/// `[a, a, b]` and `[a, b, b]` as equal. Greedy matching agrees with maximum
/// matching **only if the caller's agreement is an equivalence**, which is an
/// unchecked caller obligation stated on [`ValueAgreement`].
pub fn same_multiset_by<A, B, G>(
    left: &[Observation<A>],
    right: &[Observation<B>],
    agreement: &mut G,
) -> bool
where
    G: ValueAgreement<A, B>,
{
    if left.len() != right.len() {
        return false;
    }
    let mut consumed = vec![false; right.len()];
    for candidate in left {
        let matched = right.iter().enumerate().position(|(index, member)| {
            !consumed[index] && same_observation_by(candidate, member, agreement).is_none()
        });
        match matched {
            Some(index) => consumed[index] = true,
            None => return false,
        }
    }
    true
}

/// Mutual containment: every member of each side agrees with *some* member of
/// the other. Cardinality is not compared, which is precisely what
/// [`Duplicates::CollapseAgreeing`] means here.
///
/// # Why this is not "deduplicate, then compare"
///
/// Deduplicating *within* one side would need an agreement between that side and
/// itself, and [`ValueAgreement`] relates two possibly-different value types. So
/// collapsing is realised as mutual containment, which needs only the agreement
/// the caller actually supplied. The consequence is that under
/// `CollapseAgreeing` the [`ResultOrdering`] field is **not consulted**: order is
/// not meaningful once cardinality is not.
pub fn mutually_contained_by<A, B, G>(
    left: &[Observation<A>],
    right: &[Observation<B>],
    agreement: &mut G,
) -> bool
where
    G: ValueAgreement<A, B>,
{
    let every_left_has_a_right = left.iter().all(|candidate| {
        right
            .iter()
            .any(|member| same_observation_by(candidate, member, agreement).is_none())
    });
    let every_right_has_a_left = right.iter().all(|member| {
        left.iter()
            .any(|candidate| same_observation_by(candidate, member, agreement).is_none())
    });
    every_left_has_a_right && every_right_has_a_left
}

/// Compare two enumerations under the caller's policy.
pub fn same_collection_by<A, B, G>(
    left: &[Observation<A>],
    right: &[Observation<B>],
    agreement: &mut G,
    policy: &CollectionPolicy,
) -> Option<Disagreement>
where
    G: ValueAgreement<A, B>,
{
    match policy.duplicates {
        Duplicates::CollapseAgreeing => {
            if mutually_contained_by(left, right, agreement) {
                None
            } else {
                Some(Disagreement::MissingMember)
            }
        }
        Duplicates::Retain => match policy.ordering {
            ResultOrdering::AsEnumerated => same_sequence_by(left, right, agreement),
            ResultOrdering::UpToPermutation => {
                if left.len() != right.len() {
                    Some(Disagreement::CardinalityMismatch)
                } else if same_multiset_by(left, right, agreement) {
                    None
                } else {
                    Some(Disagreement::MissingMember)
                }
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

    /// The consuming half of the matching, which is the whole reason it is not a
    /// containment check.
    #[test]
    fn multiset_matching_consumes() {
        let left = [observation(1, 1), observation(1, 1), observation(2, 1)];
        let right = [observation(1, 1), observation(2, 1), observation(2, 1)];
        assert!(!same_multiset_by(&left, &right, &mut identity()));
        // ...whereas mutual containment cannot see the difference, which is why it
        // is offered only under an explicit `CollapseAgreeing`.
        assert!(mutually_contained_by(&left, &right, &mut identity()));
    }

    #[test]
    fn order_is_meaningful_by_default() {
        let left = [observation(1, 1), observation(2, 2)];
        let right = [observation(2, 2), observation(1, 1)];
        assert_eq!(
            same_collection_by(
                &left,
                &right,
                &mut identity(),
                &CollectionPolicy::AS_ENUMERATED
            ),
            Some(Disagreement::ValueMismatch)
        );
        assert_eq!(
            same_collection_by(
                &left,
                &right,
                &mut identity(),
                &CollectionPolicy::UP_TO_PERMUTATION
            ),
            None
        );
    }

    /// Extents are compared even when values agree: two parses of different
    /// lengths yielding the same value are not the same interpretation.
    #[test]
    fn extents_are_part_of_the_comparison() {
        assert_eq!(
            same_observation_by(&observation(1, 1), &observation(1, 2), &mut identity()),
            Some(Disagreement::ExtentMismatch)
        );
    }

    #[test]
    fn a_report_that_never_ran_is_vacuous_not_agreeing() {
        let report = AgreementReport::new("nothing");
        assert!(report.is_agreeing());
        assert!(report.is_vacuous());
    }

    /// Inconclusive samples do not count as checked, in either direction.
    #[test]
    fn inconclusive_is_neither_pass_nor_failure() {
        let mut report = AgreementReport::new("law");
        report.record(0, 0, AgreementOutcome::Inconclusive { side: Side::Left });
        assert_eq!((report.checked, report.inconclusive), (0, 1));
        assert!(report.is_agreeing() && report.is_vacuous());
    }

    /// A conditional law whose hypothesis never fired is vacuous, not agreeing —
    /// the counter exists so that "green" and "measured something" stay distinct.
    #[test]
    fn a_hypothesis_that_never_fires_is_vacuous_not_agreeing() {
        let mut report = AgreementReport::new("conditional law");
        report.record_hypothesis_unsatisfied();
        report.record_hypothesis_unsatisfied();
        assert_eq!((report.checked, report.hypothesis_unsatisfied), (0, 2));
        assert!(report.is_agreeing() && report.is_vacuous());
    }

    /// A scope claim with no divergence is *not* a pass.
    #[test]
    fn a_scope_report_without_a_divergence_is_not_success() {
        let mut report = ScopeReport::new("claim");
        report.record_agreement();
        report.record_agreement();
        assert!(!report.exhibited());
    }
}
