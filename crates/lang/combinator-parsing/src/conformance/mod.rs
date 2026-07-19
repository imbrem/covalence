//! Tier (i): the algebraic laws, per encoding.
//!
//! Law checking by falsification over a finite corpus under a finite budget.
//! A passing report means the suite *failed to falsify* the law on the samples it
//! was given. It is not a proof and confers no theorem authority.
//!
//! Budget asymmetry is a third outcome, neither pass nor violation: with any
//! per-node resource accounting, one association of a union can trip a limit
//! while the other does not, and reporting that as a law violation would be a
//! resource artifact reported as a semantic disagreement.
//!
//! A fourth outcome, [`LawOutcome::Unavailable`], exists because law bundles take
//! composite symbols **as caller input**. A defunctionalized symbol set need not
//! be closed under composition, and conformance verifies the caller's claim about
//! a composite rather than constructing a composite it has no right to construct.
//! An absent symbol yields `Unavailable { needs }` naming what was missing —
//! never a silent skip, and never a false pass. [`ConformanceReport::checked`]
//! counts only laws that actually ran.
//!
//! # Several "obvious" laws are false and must not be added
//!
//! - **Ordered choice is not unconditionally associative.** The two associations
//!   agree on positive content but fold diagnostics differently, so the monoid
//!   law holds only in the diagnostic-forgetting quotient, or when the caller's
//!   merge is itself associative. Observations carry no diagnostic, so the checks
//!   here run *inside* that quotient — which is a limitation of the check, not a
//!   vindication of the law.
//! - **Ordered choice is not commutative**, and its non-commutativity is asserted
//!   as its own claim rather than merely left unchecked.
//! - **Union is not idempotent.** It is a free/multiset union, so a union of a
//!   parser with itself has twice the results. Idempotence holds only relative to
//!   a caller-supplied dedup policy whose agreement is an equivalence — an
//!   unchecked caller obligation. Deduplicating inside the evaluator instead
//!   would destroy the ambiguity retention relational parsing exists to provide.
//! - **Union is not commutative on the nose**, only up to permutation, and
//!   enumeration order is meaningful data in-house. Comparing as an enumerated
//!   sequence is therefore the default, not an over-strict choice.
//! - **Bind-associativity is not statable on the nose**, because the two sides
//!   have different witness types. It is checkable only under the observation
//!   projection, or up to a reassociation whose iso-hood is itself unverified.
//! - **Ordered choice does not distribute over bind**, though union does. Two
//!   operators that disagree on left-distributivity are two operators, and that
//!   is asserted here as a positive claim.
//!
//! # Corpus obligations, which keep the suite from being vacuous while green
//!
//! 1. The relational corpus must contain parsers producing **two or more results
//!    at the same offset**. Without it the scoped take-first agreement is
//!    confirmed everywhere and looks general. Audited by
//!    [`crate::morphism::audit_relational_ambiguity`].
//! 2. The ordered corpus must contain a **bind above a choice whose continuation
//!    declines on the first alternative's value and succeeds on the second's**.
//!    Without it the divergence is never exercised. Audited by
//!    [`syntax::check_ordered_choice_does_not_distribute_over_bind`].
//! 3. The total corpus must exclude value types with a **distinguished failure
//!    inhabitant**, since such a value type smuggles the non-match channel back
//!    inside the value and makes the totality law vacuous. Enforced as a bound —
//!    see [`crate::morphism::WithoutFailureInhabitant`].
//!
//! # Where equality enters, and where it does not
//!
//! Seven places, each caller-supplied:
//!
//! 1. **The widening laws.** Both sides are the same underlying parser, so
//!    identity agreement is legitimate — but nothing here *assumes* it, because
//!    the two sides may have been reached through different map chains.
//! 2. **Refinement membership.** Value agreement plus extent equality, invoked
//!    once per candidate, hence `&mut self` rather than a one-shot closure.
//! 3. **Collection comparison.** Ordering, duplicate handling and the matching
//!    algorithm, all caller-visible.
//! 4. **The cross-encoding tier.** The two encodings may have different value
//!    types, which is why the agreement trait takes two type parameters.
//! 5. **Extents.** Host `==` on spans and remainders is admitted: these are host
//!    offsets, parsing-API data, not object values. **Valid within one carrier
//!    only.**
//! 6. **Error channels.** Never compared across encodings; only the trichotomy
//!    is. Payloads differ by construction.
//! 7. **Witnesses: never compared in any law.** Two law-equal programs *must*
//!    record different witnesses, so a law demanding witness equality is false.
//!    The one sound witness-level statement is a span projection, offered as an
//!    optional law gated on a caller-supplied projection.
//!
//! No signature in this module or in [`crate::morphism::agreement`] bounds a
//! value type on `PartialEq`. That absence is the enforcement.

pub mod host;
pub mod reference;
pub mod syntax;

use crate::morphism::{AgreementOutcome, AgreementReport, Disagreement, Side};

/// The outcome of one law over one corpus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LawOutcome {
    Held,
    Failed(Disagreement),
    /// The caller did not supply a symbol the law needs. **Not a pass**, and not
    /// a silent skip: `needs` names the missing symbol.
    Unavailable {
        needs: &'static str,
    },
    Inconclusive {
        side: Side,
    },
}

/// One law's result. Wraps an [`AgreementReport`] so the per-sample accounting is
/// shared with the cross-encoding tier, and adds the unavailability channel that
/// only tier (i) needs.
#[derive(Clone, Debug)]
pub struct LawReport {
    pub agreement: AgreementReport,
    /// `Some(needs)` when the law never ran because a caller-supplied symbol was
    /// absent. A law reporting this is **not** counted as holding.
    pub unavailable: Option<&'static str>,
}

impl LawReport {
    pub fn new(law: &'static str) -> Self {
        Self {
            agreement: AgreementReport::new(law),
            unavailable: None,
        }
    }

    pub fn unavailable(law: &'static str, needs: &'static str) -> Self {
        Self {
            agreement: AgreementReport::new(law),
            unavailable: Some(needs),
        }
    }

    pub fn law(&self) -> &'static str {
        self.agreement.law
    }

    pub fn record(&mut self, source_index: usize, start: usize, outcome: AgreementOutcome) {
        self.agreement.record(source_index, start, outcome);
    }

    /// The law ran on at least one sample and was not falsified.
    pub fn is_holding(&self) -> bool {
        self.unavailable.is_none() && !self.agreement.is_vacuous() && self.agreement.is_agreeing()
    }

    /// The law produced no evidence — either it never ran, or a symbol was
    /// missing. **A vacuous law is not a passing law.**
    pub fn is_vacuous(&self) -> bool {
        self.unavailable.is_some() || self.agreement.is_vacuous()
    }
}

/// A bundle of related laws, run together over one corpus.
#[derive(Clone, Debug)]
pub struct ConformanceReport {
    pub bundle: &'static str,
    pub laws: Vec<LawReport>,
}

impl ConformanceReport {
    pub fn new(bundle: &'static str) -> Self {
        Self {
            bundle,
            laws: Vec::new(),
        }
    }

    pub fn push(&mut self, law: LawReport) {
        self.laws.push(law);
    }

    /// Every law that ran was not falsified, and none was unavailable. Says
    /// nothing about coverage — read [`Self::checked`] alongside it.
    pub fn is_holding(&self) -> bool {
        self.laws
            .iter()
            .all(|law| law.agreement.is_agreeing() && law.unavailable.is_none())
    }

    /// Every law in the bundle ran on at least one sample and held.
    pub fn is_holding_nonvacuously(&self) -> bool {
        !self.laws.is_empty() && self.laws.iter().all(LawReport::is_holding)
    }

    /// Samples on which some law actually ran. **Only laws that ran are counted**,
    /// so a bundle whose symbols were all absent reports zero rather than green.
    pub fn checked(&self) -> usize {
        self.laws.iter().map(|law| law.agreement.checked).sum()
    }

    pub fn inconclusive(&self) -> usize {
        self.laws.iter().map(|law| law.agreement.inconclusive).sum()
    }

    /// `(law, needed symbol)` for every law that could not run.
    pub fn unavailable(&self) -> Vec<(&'static str, &'static str)> {
        self.laws
            .iter()
            .filter_map(|law| law.unavailable.map(|needs| (law.law(), needs)))
            .collect()
    }

    pub fn failures(&self) -> Vec<(&'static str, usize, usize, Disagreement)> {
        self.laws
            .iter()
            .flat_map(|law| {
                law.agreement
                    .failures
                    .iter()
                    .map(move |&(source, start, disagreement)| {
                        (law.law(), source, start, disagreement)
                    })
            })
            .collect()
    }
}

// TODO(cov:lang.combinator-parsing.host-applicative-laws, minor): The host law fixture fixes
// one `Value` type, so `host::partial::Ap` — whose function-carrying parser must have
// `Value: FnOnce(Value) -> B` — is reachable only through boxed function values. The
// applicative bundle is therefore checked in full for the syntax encoding, where the value
// universe is single-sorted and application goes through the environment, and only for
// identity and interchange in the host encoding. Closing the gap wants a second fixture
// trait carrying a distinct function-value type.

#[cfg(test)]
mod tests {
    use super::*;

    /// A bundle whose laws could not run is not a passing bundle. This is the
    /// distinction that keeps `Unavailable` from behaving as a silent skip.
    #[test]
    fn an_unavailable_law_is_not_a_holding_law() {
        let mut report = ConformanceReport::new("bundle");
        report.push(LawReport::unavailable("identity", "identity_value"));
        assert!(!report.is_holding());
        assert_eq!(report.checked(), 0);
        assert_eq!(report.unavailable(), vec![("identity", "identity_value")]);
    }

    /// ...and neither is one that ran on nothing.
    #[test]
    fn a_law_that_never_ran_is_vacuous_not_holding() {
        let law = LawReport::new("identity");
        assert!(!law.is_holding());
        assert!(law.is_vacuous());
    }
}
