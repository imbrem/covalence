//! The relationship layer: what is, and what is not, a morphism.
//!
//! # Axis 1 — semantic. Refinements, never equalities.
//!
//! Widening a total parser to a partial one is an injective, information
//! preserving embedding: with an uninhabited diagnostic type, "declines" is not
//! merely unused on the image, it is impossible. Widening a partial parser to a
//! relational one preserves positive content but discards the diagnostic, so it
//! is non-injective and **has no retraction** — any law of the shape
//! `narrow(widen(p)) == p` is false.
//!
//! Ordered choice *refines* relational union. The positive direction is a
//! one-way implication and must never be written as an equation: membership in
//! the union does not imply ordered choice selects it, because when both
//! alternatives match the union has two members and ordered choice yields only
//! the first. The two agree exactly on emptiness, and even that relates *two
//! evaluators* to each other — it is not a claim that nothing matches.
//!
//! There is no canonical narrowing from relational back to partial. Enumeration
//! order is deterministic in-house but deterministic is not canonical, so the
//! only surface offered is a policy-forcing three-way outcome in which ambiguity
//! is a distinguished answer rather than an error.
//!
//! The refinement chain lives in the adapters and **never in the trait
//! hierarchy**. Making the total prefix trait a supertrait of the partial one
//! would hand every total parser a non-match channel by inheritance and reopen
//! exactly the collapse this crate exists to prevent. The trait graph stays
//! discrete; the absence of a blanket impl *is* the enforcement mechanism.
//!
//! # Axis 2 — representational. A poset, not a groupoid.
//!
//! Compiling a syntax program to a host combinator value preserves the
//! match / no-match / error trichotomy and the positive projection under a
//! caller-supplied agreement. It does **not** preserve diagnostic payload, and it
//! has no inverse: host values contain closures, which are not data. The right
//! word for the relationship is compilation, not equivalence.
//!
//! Every axis-2 claim quantifies over `(program, environment)` pairs, never over
//! programs alone. Rule references and bind continuations resolve through the
//! environment, so two programs equal as data behave differently under different
//! environments, and cross-fragment claims additionally require environment
//! coherence.
//!
//! # What is compared
//!
//! Observations only: the value, the consumed extent, and the remainder. Values
//! are compared by a caller-supplied agreement, never by an assumed host
//! `PartialEq`; extents are compared with host equality, valid only within a
//! single carrier. Error payloads are never compared across encodings — only the
//! trichotomy is. **Witnesses are never compared in any morphism law**: two
//! law-equal programs must record different witnesses, so a law demanding witness
//! equality is false. The one sound witness-level statement is a span projection,
//! offered only as an optional law gated on a caller-supplied projection.

//! # The morphism table
//!
//! Axis 1 — semantic. Each row names an adapter or the deliberate absence of one; the
//! exact law and its status live on the item itself.
//!
//! | id | claim | status |
//! |---|---|---|
//! | **M1** | [`WidenTotalToPartial`]: the partial observation is `Match` of the total one | iso onto its image; `Diagnostic = Infallible` makes non-match *uninhabited* there |
//! | **M2** | [`WidenPartialToRelational`]: `Match(m) ↦ [m]`, `NoMatch(_) ↦ []`, cardinality ≤ 1 | one-way refinement; lossy, non-injective, **no retraction** |
//! | **M5** | [`WidenTotalToRelational`]: cardinality **exactly** 1 | one-way refinement, strictly stronger than M1 ∘ M2, hence its own type |
//! | **M3⁺** | ordered choice **refines** union: a match of `oc(p,q)` agrees with *some* member of `union(widen p, widen q)` | one-way **implication**; the converse is false |
//! | **M3⁻** | `oc(p,q)` declines **⟺** the union enumerates nothing | biconditional, exact — and only because it relates two *evaluators* |
//! | **M4** | `oc(p,q)` agrees with the *first* union result | true **only** on the image of M2; there is no `take_first` in this API |
//! | **M6** | relational → partial | **not a morphism**; [`narrow_relational`] classifies and never picks |
//! | **M7** | the chain lives in the adapters | enforced by the empty trait graph and pinned by `compile_fail` doctests |
//!
//! Axis 2 — representational. [`compile_deterministic`], [`compile_ordered`] and
//! [`compile_relational`] are **N1**: semantics-preserving translations that are
//! non-surjective and have no inverse. There is no axis-2 counterpart to the mode-generic
//! encoding, because that encoding was evaluated and dropped; see the marker in `host`.
//!
//! # §e.1 — the refinement does not commute with `bind`
//!
//! This is the single most important qualification on the table above, and it is the
//! reason M3 is phrased as a statement about **whole observations** rather than as a
//! rewrite rule on programs.
//!
//! Take `p` and `q` both matching at `i` with *different* values, and a continuation `k`
//! that declines after `p`'s value and succeeds after `q`'s. Then:
//!
//! - `bind(oc(p, q), k)` — ordered choice commits to `p`, `k` declines, and the ordered
//!   bind never retries the head, because backtracking enters only through ordered choice.
//!   The whole program **declines**.
//! - the first result of `bind(union(widen p, widen q), k)` — relational bind continues
//!   *every* head result, `p`'s branch contributes nothing, `q`'s contributes a result.
//!   The whole program **matches**.
//!
//! So M3 and M4 hold at the top of a program and fail under any context with a `bind`
//! above the choice. Consequently this crate exposes no `simplify`, no `normalize`, and no
//! `to_relational` operation on programs: any such operation would have to be sound in
//! arbitrary contexts, and none of these laws is.
//!
//! # §e.2 — how these laws go vacuously green
//!
//! A corpus built only from widened partial parsers confirms M4 *everywhere*, because on
//! that image it is genuinely true. Any suite checking these laws therefore owes two
//! generator obligations: a relational corpus containing parsers that produce **two or
//! more results at the same offset**, and an ordered corpus containing a **`bind` above a
//! choice whose continuation declines on the first alternative's value**. Without both,
//! the entire non-collapse suite is vacuous while appearing to pass.

pub mod agreement;
pub mod check;
mod compile;
mod narrow;
mod observe;
mod widen;

pub use agreement::{
    AgreeBy, AgreementOutcome, AgreementReport, CollectionPolicy, Corpus, Disagreement, Duplicates,
    PartialObserver, RelationalObserver, ResultOrdering, ScopeReport, Side, TotalObserver,
    ValueAgreement, mutually_contained_by, same_collection_by, same_multiset_by,
    same_observation_by, same_sequence_by,
};
pub use check::{
    AmbiguityAudit, WithoutFailureInhabitant, audit_relational_ambiguity,
    check_choice_and_union_agree_on_emptiness, check_choice_refines_union,
    check_encodings_agree_partial, check_encodings_agree_relational, check_encodings_agree_total,
    check_partial_embeds_in_relational, check_take_first_agreement_is_scoped,
    check_total_embeds_in_partial, check_total_embeds_in_relational,
};
pub use compile::{
    CompiledOrderedParser, CompiledRelational, CompiledTotalParser, compile_deterministic,
    compile_ordered, compile_relational,
};
pub use narrow::{Narrowed, narrow_relational};
pub use observe::{
    Observation, PartialObserved, RelationalObserved, TotalObserved, observe_partial,
    observe_relational, observe_span, observe_total, partial_as_relational, total_as_partial,
    total_as_relational,
};
pub use widen::{WidenPartialToRelational, WidenTotalToPartial, WidenTotalToRelational};

// TODO(cov:lang.combinator-parsing.collapse-agreeing-ignores-order, minor): Under
// `Duplicates::CollapseAgreeing` the collection comparison is mutual containment, so
// `ResultOrdering` is not consulted and cardinality is not compared. Collapsing *within* one
// side would need an agreement between that side and itself, which `ValueAgreement<A, B>`
// does not supply. A same-side agreement parameter would let dedup-then-compare be offered
// as a distinct, sharper policy.

// TODO(cov:lang.combinator-parsing.bind-associativity-only-up-to-observation, minor): §e.14
// — bind associativity is not statable on the nose in either encoding, because the two
// sides carry different witness *types* (`Seq<Seq<A,B>,C>` against `Seq<A,Seq<B,C>>`). At
// host level it is checkable only under the observation projection, or up to
// `host::reassociate_*`, whose round trip is tested but whose iso-hood is not proved. The
// on-the-nose statement needs the witness types related in the object language, so it
// belongs at the logic level with the other `theory::CombinatorMorphismLaws` capabilities.

// TODO(cov:lang.combinator-parsing.refinement-inequation-unproved, minor): M3⁺ is a
// one-way inequation and M3⁻ a biconditional between two evaluators. Both are statable
// exactly as written above, and at host level are checkable only by failure to falsify over
// a finite corpus. Their universal forms quantify over sources *and* environments, which
// needs the environment reflected into the object language; they belong at the logic level
// as `theory::CombinatorMorphismLaws` capabilities and must never be mintable by
// evaluation.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::budget::{CombinatorBudget, RelationalLimits};
    use crate::host::RelationalPrefixParser;
    use crate::syntax::{
        Core, Ordered, OrderedEnv, PartialEvaluator, PrimitiveMatch, Relational, RelationalEnv,
        RelationalEvaluator, Signature, SignatureEnv,
    };
    use covalence_parsing_api::{ParseAttempt, PartialPrefixParser};

    /// A signature whose primitives *overlap*: every one of them matches any single atom
    /// and yields its own tag as the value. Overlap is what makes both alternatives of a
    /// choice succeed at the same offset with different values, which is the precondition
    /// of §e.2's generator obligation. A corpus of non-overlapping primitives confirms
    /// every law here and proves nothing.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Tags;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Never;

    impl Signature for Tags {
        type Atom = u8;
        type Value = u8;
        /// The tag this primitive yields when it consumes an atom.
        type Primitive = u8;
        type Function = ();
        type Continuation = ();
        type PrimitiveWitness = ();
    }

    struct Env;

    impl SignatureEnv<Tags> for Env {
        type Error = Never;

        fn apply_function(&self, _function: &(), argument: u8) -> Result<u8, Never> {
            Ok(argument)
        }

        fn apply_value(&self, _function: u8, argument: u8) -> Result<u8, Never> {
            Ok(argument)
        }

        fn step(
            &self,
            primitive: &u8,
            source: &[u8],
            at: usize,
        ) -> Result<Option<PrimitiveMatch<Tags>>, Never> {
            Ok(source.get(at).map(|_| PrimitiveMatch {
                value: *primitive,
                witness: (),
                end: at + 1,
            }))
        }
    }

    impl OrderedEnv<Tags> for Env {
        fn ordered_rule(&self, _rule: usize) -> Option<&Ordered<Tags>> {
            None
        }

        /// Declines on tag 1 and succeeds on anything else. That asymmetry is the whole
        /// counterexample.
        fn ordered_resolve(&self, _continuation: &(), value: &u8) -> Result<Ordered<Tags>, Never> {
            Ok(match value {
                1 => Ordered::Fail,
                other => Ordered::Core(Core::Pure(*other)),
            })
        }
    }

    impl RelationalEnv<Tags> for Env {
        fn relational_rule(&self, _rule: usize) -> Option<&Relational<Tags>> {
            None
        }

        fn relational_resolve(
            &self,
            _continuation: &(),
            value: &u8,
        ) -> Result<Relational<Tags>, Never> {
            Ok(match value {
                1 => Relational::Void,
                other => Relational::Core(Core::Pure(*other)),
            })
        }
    }

    const BUDGET: CombinatorBudget = CombinatorBudget::new(64, 512, 32, 512, 64);
    const LIMITS: RelationalLimits = RelationalLimits::new(64, 64);

    fn ordered_choice() -> Ordered<Tags> {
        Ordered::OrderedChoice(vec![
            Ordered::Core(Core::Prim(1)),
            Ordered::Core(Core::Prim(2)),
        ])
    }

    fn union() -> Relational<Tags> {
        Relational::Union(vec![
            Relational::Core(Core::Prim(1)),
            Relational::Core(Core::Prim(2)),
        ])
    }

    /// M3⁺ and M4 at the top of a program, where they do hold.
    ///
    /// Both alternatives match at offset 0 with different values. Ordered choice yields
    /// the first; the union yields both. Membership holds — but note that it is an
    /// *implication*, and the converse plainly fails here: tag 2 is in the union and
    /// ordered choice will never produce it.
    #[test]
    fn ordered_choice_refines_union_at_the_top_of_a_program() {
        let ordered = ordered_choice();
        let relational = union();
        let partial = PartialEvaluator::new(&ordered, &Env, BUDGET);
        let enumerated = RelationalEvaluator::new(&relational, &Env, BUDGET, LIMITS)
            .parse_prefixes(b"x", 0)
            .expect("no failure");

        let ParseAttempt::Match(matched) = partial.parse_prefix(b"x", 0).expect("no failure")
        else {
            panic!("expected a match");
        };
        assert!(
            enumerated.iter().any(
                |member| (member.value, member.remainder) == (matched.value, matched.remainder)
            ),
            "M3+ membership"
        );
        // The converse is false, and this is what makes it false.
        assert_eq!(enumerated.len(), 2);
        assert!(enumerated.iter().any(|member| member.value == 2));
    }

    /// **§e.1 — the counterexample, executed.**
    ///
    /// With a `bind` above the choice the refinement stops holding. Ordered choice commits
    /// to the first alternative's value, the continuation declines on it, and ordered bind
    /// never retries the head — so the whole program declines. Relational bind continues
    /// *every* head result, so the second alternative's value reaches a continuation that
    /// accepts it and the union-side program enumerates a result.
    ///
    /// This is why M3 is a statement about whole observations and never a rewrite rule, and
    /// why no `take_first` ships: taking the first result of the relational side here would
    /// produce a match where the ordered program declines.
    #[test]
    fn the_refinement_does_not_commute_with_bind() {
        let ordered = Ordered::Core(Core::Bind(Box::new(ordered_choice()), ()));
        let relational = Relational::Core(Core::Bind(Box::new(union()), ()));

        let partial = PartialEvaluator::new(&ordered, &Env, BUDGET);
        let enumerated = RelationalEvaluator::new(&relational, &Env, BUDGET, LIMITS)
            .parse_prefixes(b"x", 0)
            .expect("no failure");

        assert!(matches!(
            partial.parse_prefix(b"x", 0).expect("no failure"),
            ParseAttempt::NoMatch(_)
        ));
        assert_eq!(enumerated.len(), 1);
        assert_eq!(enumerated[0].value, 2);
    }

    /// M6: the enumeration above is classified, never collapsed to the ordered answer.
    #[test]
    fn narrowing_reports_ambiguity_rather_than_choosing() {
        let relational = union();
        let enumerated = RelationalEvaluator::new(&relational, &Env, BUDGET, LIMITS)
            .parse_prefixes(b"x", 0)
            .expect("no failure");
        assert!(matches!(
            narrow_relational(enumerated),
            Narrowed::Ambiguous(members) if members.len() == 2
        ));
    }
}
