//! A reference signature, environment and corpus that satisfy the generator
//! obligations.
//!
//! This is shipped rather than kept in `#[cfg(test)]` because the obligations it
//! satisfies are the difficult part of using this crate's conformance suite, and
//! a caller assembling their own corpus needs something to compare against.
//!
//! # The three obligations, and how this corpus meets them
//!
//! 1. **Genuine ambiguity.** [`Primitive::Atom`] is *overlapping*: distinct
//!    primitives all consume exactly one atom and yield distinct values, so
//!    `union(atom(1), atom(2))` produces two results **at the same extent**. A
//!    corpus of non-overlapping primitives confirms every law here and proves
//!    nothing, because the scoped take-first agreement is then true everywhere.
//! 2. **A bind above a choice that separates.** [`Continuation::RejectOne`]
//!    declines on the value `atom(1)` produces and succeeds on the value
//!    `atom(2)` produces. With `p = atom(1)` and `q = atom(2)`, ordered choice
//!    commits to `p`, the continuation declines, and the whole program declines —
//!    while pushing the bind under the choice matches through `q`. That is the
//!    counterexample separating ordered choice from union, and without it the
//!    entire non-collapse suite is vacuous while appearing green.
//! 3. **No distinguished failure inhabitant.** [`Value`] is a tag-or-function
//!    universe with no `None`, no `Err` and no sentinel meaning "did not match".
//!    A total parser over a value type that could encode failure has smuggled the
//!    non-match channel inside the value, and every totality law then holds by
//!    construction while measuring nothing. The obligation is enforced by the
//!    [`crate::morphism::WithoutFailureInhabitant`] bound, which this type
//!    implements and `Option<_>` deliberately cannot.
//!
//! # The deterministic rule table
//!
//! [`TotalEnv::total_rule`] is backed by a real table — see [`RULE_PURE_ADDER`],
//! [`RULE_ATOM`] and [`RULE_LEFT_RECURSIVE`] — rather than returning `None`. An
//! environment with no rules makes the `Core::Rule` arm of *both* total
//! evaluators unreachable, including its left-recursion guard, so breaking either
//! arm leaves the suite green: the same vacuity as obligations 1 and 2 above,
//! one axis over. The two well-founded rules differ in both observable
//! coordinates (one contributes a value and no extent, the other the reverse) so
//! that resolving the wrong body is distinguishable from dropping a body's value
//! or its extent.
//!
//! # Data equality here is the caller's choice, not the harness's
//!
//! [`Value`] derives `PartialEq`, and [`agreement`] uses it. That is a *caller*
//! decision made at one call site, not an assumption baked into any signature: no
//! function in `conformance` or `morphism::agreement` bounds a value type on
//! `PartialEq`.

use crate::budget::{CombinatorBudget, RelationalLimits};
use crate::conformance::syntax::{
    ApplicativeLawInputs, ChoiceLawInputs, FunctorLawInputs, MonadLawInputs, UnionLawInputs,
};
use crate::morphism::WithoutFailureInhabitant;
use crate::morphism::agreement::{AgreeBy, Corpus};
use crate::syntax::{
    Core, Deterministic, Ordered, OrderedEnv, PrimitiveMatch, Relational, RelationalEnv, Signature,
    SignatureEnv, TotalEnv,
};

/// The reference signature: tags and first-order function symbols over bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reference;

/// The value universe. Single-sorted, as it must be without GADTs: an ill-typed
/// application surfaces as an environment error at run time, never as a non-match.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Tag(u8),
    Fun(Fun),
}

impl WithoutFailureInhabitant for Value {}

/// Defunctionalized *value-level* functions, so `Ap` has something to apply.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fun {
    Identity,
    /// `\Tag(t) -> Tag(t + n)`, wrapping.
    Add(u8),
    /// `($ y)` — applies its argument to `y`.
    Section(Box<Value>),
    /// `(.)`, awaiting both operands.
    Compose,
    /// `(f .)`, awaiting the second operand.
    ComposeWith(Box<Fun>),
    /// `f . g`.
    Composed(Box<Fun>, Box<Fun>),
}

/// Input-consuming leaves. **Deliberately overlapping**: every [`Primitive::Atom`]
/// matches any single atom, which is what makes two alternatives succeed at the
/// same offset with different values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Primitive {
    /// Consumes one atom, yields `Tag(tag)`.
    Atom(u8),
    /// Consumes one atom, yields `Fun(Add(n))` — a *consuming* parser whose value
    /// is a function, which the applicative laws need.
    AtomAsAdder(u8),
    /// **Fails the evaluator when reached.** Not a non-match — an `Err`. This is
    /// how "was this alternative evaluated at all?" becomes observable: ordered
    /// choice must never reach a poisoned second alternative after the first
    /// matched, and relational union must always reach it.
    Poison,
}

/// Map symbols. `Twice` exists as the caller's claim about `Succ ∘ Succ`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Function {
    Identity,
    Succ,
    Twice,
}

/// Defunctionalized continuation symbols.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Continuation {
    /// The monadic unit: resolves to `Pure(x)`.
    Yield,
    /// **The separator.** Declines on `Tag(1)` and yields on anything else.
    RejectOne,
    /// Consumes one further atom, yielding `Tag(9)`.
    ThenAtom,
    /// The caller's claim about `RejectOne >=> ThenAtom`.
    RejectOneThenAtom,
}

impl Signature for Reference {
    type Atom = u8;
    type Value = Value;
    type Primitive = Primitive;
    type Function = Function;
    type Continuation = Continuation;
    type PrimitiveWitness = u8;
}

/// The reference environment's failure channel. **Evaluator failure only** — an
/// ill-typed application, or a symbol this environment cannot interpret. Ordinary
/// non-match never travels here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceError {
    /// A value was applied that is not a function, or applied to the wrong shape.
    NotApplicable,
    /// A continuation symbol this fragment cannot express.
    UnsupportedContinuation(Continuation),
    /// [`Primitive::Poison`] was evaluated.
    Poisoned,
}

/// The reference environment.
#[derive(Clone, Copy, Debug, Default)]
pub struct Env;

fn apply_fun(function: &Fun, argument: Value) -> Result<Value, ReferenceError> {
    match function {
        Fun::Identity => Ok(argument),
        Fun::Add(n) => match argument {
            Value::Tag(tag) => Ok(Value::Tag(tag.wrapping_add(*n))),
            Value::Fun(_) => Err(ReferenceError::NotApplicable),
        },
        Fun::Section(y) => match argument {
            Value::Fun(inner) => apply_fun(&inner, (**y).clone()),
            Value::Tag(_) => Err(ReferenceError::NotApplicable),
        },
        Fun::Compose => match argument {
            Value::Fun(inner) => Ok(Value::Fun(Fun::ComposeWith(Box::new(inner)))),
            Value::Tag(_) => Err(ReferenceError::NotApplicable),
        },
        Fun::ComposeWith(first) => match argument {
            Value::Fun(second) => Ok(Value::Fun(Fun::Composed(first.clone(), Box::new(second)))),
            Value::Tag(_) => Err(ReferenceError::NotApplicable),
        },
        Fun::Composed(first, second) => apply_fun(first, apply_fun(second, argument)?),
    }
}

impl SignatureEnv<Reference> for Env {
    type Error = ReferenceError;

    fn apply_function(
        &self,
        function: &Function,
        argument: Value,
    ) -> Result<Value, ReferenceError> {
        match (function, argument) {
            (Function::Identity, argument) => Ok(argument),
            (Function::Succ, Value::Tag(tag)) => Ok(Value::Tag(tag.wrapping_add(1))),
            (Function::Twice, Value::Tag(tag)) => Ok(Value::Tag(tag.wrapping_add(2))),
            _ => Err(ReferenceError::NotApplicable),
        }
    }

    /// Applying a non-function is an **ill-formed program**, hence evaluator
    /// failure — never a non-match. That distinction is what keeps `Err` from
    /// becoming a second, silent decline channel.
    fn apply_value(&self, function: Value, argument: Value) -> Result<Value, ReferenceError> {
        match function {
            Value::Fun(function) => apply_fun(&function, argument),
            Value::Tag(_) => Err(ReferenceError::NotApplicable),
        }
    }

    fn step(
        &self,
        primitive: &Primitive,
        source: &[u8],
        at: usize,
    ) -> Result<Option<PrimitiveMatch<Reference>>, ReferenceError> {
        let Some(atom) = source.get(at) else {
            // Ordinary non-match: no atom here.
            return Ok(None);
        };
        let value = match primitive {
            Primitive::Atom(tag) => Value::Tag(*tag),
            Primitive::AtomAsAdder(n) => Value::Fun(Fun::Add(*n)),
            Primitive::Poison => return Err(ReferenceError::Poisoned),
        };
        Ok(Some(PrimitiveMatch {
            value,
            witness: *atom,
            end: at + 1,
        }))
    }
}

impl OrderedEnv<Reference> for Env {
    // TODO(cov:lang.combinator-parsing.reference-ordered-rules, minor): The ordered
    // and relational rule tables are still empty, so `Core::Rule` — and its
    // left-recursion guard — is exercised only in the deterministic fragment, by
    // `TOTAL_RULES`. Mirror that table for `Ordered` and `Relational`: the ordered
    // one wants a rule whose body is an `OrderedChoice`, and the relational one a
    // left-recursive rule under a `Union`, where the guard must fire per alternative
    // rather than once per node.
    fn ordered_rule(&self, _rule: usize) -> Option<&Ordered<Reference>> {
        None
    }

    fn ordered_resolve(
        &self,
        continuation: &Continuation,
        value: &Value,
    ) -> Result<Ordered<Reference>, ReferenceError> {
        let rejected = *value == Value::Tag(1);
        Ok(match continuation {
            Continuation::Yield => Ordered::Core(Core::Pure(value.clone())),
            // A continuation that should not match resolves to `Fail` — a program,
            // not an error. `Err` is reserved for evaluator failure.
            Continuation::RejectOne if rejected => Ordered::Fail,
            Continuation::RejectOne => Ordered::Core(Core::Pure(value.clone())),
            Continuation::ThenAtom => Ordered::Core(Core::Prim(Primitive::Atom(9))),
            Continuation::RejectOneThenAtom if rejected => Ordered::Fail,
            Continuation::RejectOneThenAtom => Ordered::Core(Core::Prim(Primitive::Atom(9))),
        })
    }
}

impl RelationalEnv<Reference> for Env {
    fn relational_rule(&self, _rule: usize) -> Option<&Relational<Reference>> {
        None
    }

    fn relational_resolve(
        &self,
        continuation: &Continuation,
        value: &Value,
    ) -> Result<Relational<Reference>, ReferenceError> {
        let rejected = *value == Value::Tag(1);
        Ok(match continuation {
            Continuation::Yield => Relational::Core(Core::Pure(value.clone())),
            Continuation::RejectOne if rejected => Relational::Void,
            Continuation::RejectOne => Relational::Core(Core::Pure(value.clone())),
            Continuation::ThenAtom => Relational::Core(Core::Prim(Primitive::Atom(9))),
            Continuation::RejectOneThenAtom if rejected => Relational::Void,
            Continuation::RejectOneThenAtom => Relational::Core(Core::Prim(Primitive::Atom(9))),
        })
    }
}

impl TotalEnv<Reference> for Env {
    /// No `Option`: this environment **cannot** report non-match, which is the
    /// structural content of "total". At end of input the step consumes nothing
    /// and still produces, because a total parser has no channel in which to
    /// decline.
    fn total_step(
        &self,
        primitive: &Primitive,
        source: &[u8],
        at: usize,
    ) -> Result<PrimitiveMatch<Reference>, ReferenceError> {
        let value = match primitive {
            Primitive::Atom(tag) => Value::Tag(*tag),
            Primitive::AtomAsAdder(n) => Value::Fun(Fun::Add(*n)),
            Primitive::Poison => return Err(ReferenceError::Poisoned),
        };
        Ok(PrimitiveMatch {
            value,
            witness: source.get(at).copied().unwrap_or_default(),
            end: (at + 1).min(source.len()).max(at),
        })
    }

    /// Indexes [`TOTAL_RULES`]. An index outside it is `None` — the
    /// [`crate::budget::CombinatorEvalError::UndefinedRule`] path, which is a
    /// reachable outcome of a well-formed program rather than a corpus defect,
    /// since nothing checks rule indices before evaluation.
    fn total_rule(&self, rule: usize) -> Option<&Deterministic<Reference>> {
        TOTAL_RULES.get(rule)
    }

    /// `RejectOne` and its composite are **not expressible** in the deterministic
    /// fragment, which has no failure operator — so they are an environment error
    /// here rather than being silently reinterpreted as something that succeeds.
    /// That honesty is the point: the fragment axis and the capability axis are
    /// different axes, and the totality of this fragment lives in this signature.
    fn total_resolve(
        &self,
        continuation: &Continuation,
        value: &Value,
    ) -> Result<Deterministic<Reference>, ReferenceError> {
        match continuation {
            Continuation::Yield => Ok(Deterministic(Core::Pure(value.clone()))),
            Continuation::ThenAtom => Ok(Deterministic(Core::Prim(Primitive::Atom(9)))),
            other => Err(ReferenceError::UnsupportedContinuation(*other)),
        }
    }
}

// ---------------------------------------------------------------------------
// The deterministic rule table
// ---------------------------------------------------------------------------

/// A rule whose body is [`Core::Pure`]: yields `Fun(Add(4))`, **consumes
/// nothing**.
///
/// Carries two obligations at once. It is the only `Core::Pure` the deterministic
/// fragment's corpus reaches, and it is a rule body that contributes a *value*
/// without contributing an extent — so a compiled `Core::Rule` arm that dropped
/// the body's value and one that dropped the body's extent are separately
/// detectable, against [`RULE_ATOM`], which does the opposite.
pub const RULE_PURE_ADDER: usize = 0;

/// A rule whose body consumes: yields `Tag(3)` and advances one atom.
pub const RULE_ATOM: usize = 1;

/// **A directly left-recursive rule**: its body is a reference to itself, at the
/// same offset.
///
/// The point is not that it parses anything — it cannot — but that both
/// encodings must *report* [`crate::budget::CombinatorEvalError::LeftRecursion`]
/// rather than recursing until some unrelated resource runs out. The two are
/// distinguishable only by the error payload, which no agreement law compares
/// (both sides failing is [`crate::morphism::AgreementOutcome::Inconclusive`],
/// deliberately), so the guard is pinned by a direct assertion on the error
/// instead. Without such a rule in this table the left-recursion check is dead
/// code in both evaluators.
pub const RULE_LEFT_RECURSIVE: usize = 2;

/// The deterministic rule table, indexed by [`TotalEnv::total_rule`].
///
/// A `LazyLock` rather than a `const`, because rule bodies are `Box`ed and a
/// `&self`-borrowed return needs storage that outlives the environment — [`Env`]
/// stays a unit struct so every existing `&Env` call site is unaffected.
static TOTAL_RULES: std::sync::LazyLock<Vec<Deterministic<Reference>>> =
    std::sync::LazyLock::new(|| {
        vec![
            Deterministic(Core::Pure(Value::Fun(Fun::Add(4)))),
            Deterministic(Core::Prim(Primitive::Atom(3))),
            Deterministic(Core::Rule(RULE_LEFT_RECURSIVE)),
        ]
    });

// ---------------------------------------------------------------------------
// The corpus and its budgets
// ---------------------------------------------------------------------------

const SOURCES: &[&[u8]] = &[b"abc", b"ab", b"z", b""];
const STARTS: &[usize] = &[0, 1];

/// Sources crossed with start offsets. Finite, as every corpus in this crate is.
pub fn corpus() -> Corpus<'static, [u8]> {
    Corpus::new(SOURCES, STARTS)
}

/// Generous enough that no reference law is decided by exhaustion.
pub const BUDGET: CombinatorBudget = CombinatorBudget::new(64, 4096, 64, 4096, 256);

pub const LIMITS: RelationalLimits = RelationalLimits::new(256, 256);

/// The caller's agreement. Host `==` on values is used *here*, at one call site,
/// by the caller's choice — never assumed by a signature.
pub fn agreement() -> AgreeBy<fn(&Value, &Value) -> bool> {
    AgreeBy(|left, right| left == right)
}

/// `atom(t)` consumes one atom and yields `Tag(t)`. Overlapping by construction.
pub fn atom(tag: u8) -> Ordered<Reference> {
    Ordered::Core(Core::Prim(Primitive::Atom(tag)))
}

pub fn relational_atom(tag: u8) -> Relational<Reference> {
    Relational::Core(Core::Prim(Primitive::Atom(tag)))
}

/// A consuming parser whose *value is a function*, which the applicative laws need.
pub fn adder(n: u8) -> Ordered<Reference> {
    Ordered::Core(Core::Prim(Primitive::AtomAsAdder(n)))
}

pub fn deterministic_atom(tag: u8) -> Deterministic<Reference> {
    Deterministic(Core::Prim(Primitive::Atom(tag)))
}

pub fn functor_inputs() -> FunctorLawInputs<Reference> {
    FunctorLawInputs {
        subject: atom(3),
        identity: Function::Identity,
        f: Function::Succ,
        g: Function::Succ,
        g_after_f: Function::Twice,
    }
}

pub fn applicative_inputs() -> ApplicativeLawInputs<Reference> {
    ApplicativeLawInputs {
        subject: adder(1),
        argument: adder(2),
        final_argument: atom(5),
        identity_value: Some(Value::Fun(Fun::Identity)),
        section_of: Some(Value::Fun(Fun::Section(Box::new(Value::Tag(4))))),
        compose_value: Some(Value::Fun(Fun::Compose)),
        function_value: Some(Value::Fun(Fun::Add(3))),
        y: Value::Tag(4),
        f_of_x: Some(Value::Tag(7)),
    }
}

/// The **accepting** path: `subject` yields `Tag(3)`, which [`Continuation::RejectOne`]
/// accepts, so `k_then_h` is exercised on the branch where both halves of the
/// composite run.
///
/// This is only half the claim. The caller asserts `RejectOneThenAtom` *is*
/// `RejectOne >=> ThenAtom`, and a composite that got the *rejecting* branch
/// wrong — resolving to something that matches where `RejectOne` declines —
/// agrees with the claim everywhere on this subject. See
/// [`rejecting_monad_inputs`].
pub fn monad_inputs() -> MonadLawInputs<Reference> {
    MonadLawInputs {
        subject: atom(3),
        value: Value::Tag(3),
        k: Continuation::RejectOne,
        h: Continuation::ThenAtom,
        k_then_h: Continuation::RejectOneThenAtom,
        pure_continuation: Continuation::Yield,
    }
}

/// The **rejecting** path of the same composite claim: `subject` yields `Tag(1)`,
/// the one value [`Continuation::RejectOne`] declines on.
///
/// Associativity here compares `bind (bind atom(1) RejectOne) ThenAtom` — which
/// declines, because the inner bind does — against `bind atom(1) RejectOneThenAtom`.
/// The law holds only if the composite *also* declines on `Tag(1)`. Under
/// [`monad_inputs`] alone that branch of `ordered_resolve` is never reached, and
/// a composite that resolved to `Pure` instead of `Fail` when rejected would
/// still be reported as `RejectOne >=> ThenAtom`.
pub fn rejecting_monad_inputs() -> MonadLawInputs<Reference> {
    MonadLawInputs {
        subject: atom(1),
        value: Value::Tag(1),
        k: Continuation::RejectOne,
        h: Continuation::ThenAtom,
        k_then_h: Continuation::RejectOneThenAtom,
        pure_continuation: Continuation::Yield,
    }
}

pub fn choice_inputs() -> ChoiceLawInputs<Reference> {
    ChoiceLawInputs {
        p: atom(1),
        q: atom(2),
        r: atom(3),
        f: Function::Succ,
        k: Continuation::Yield,
    }
}

pub fn union_inputs() -> UnionLawInputs<Reference> {
    UnionLawInputs {
        p: relational_atom(1),
        q: relational_atom(2),
        r: relational_atom(3),
        f: Function::Succ,
        k: Continuation::Yield,
    }
}

/// The ambiguous relational program required by obligation 1: two results at the
/// **same extent** with different values.
pub fn ambiguous_union() -> Relational<Reference> {
    Relational::Union(vec![relational_atom(1), relational_atom(2)])
}

/// The ordered counterpart of [`ambiguous_union`].
pub fn overlapping_choice() -> Ordered<Reference> {
    Ordered::OrderedChoice(vec![atom(1), atom(2)])
}

/// A program that makes the evaluator fail if it is ever reached.
pub fn poison() -> Ordered<Reference> {
    Ordered::Core(Core::Prim(Primitive::Poison))
}

pub fn relational_poison() -> Relational<Reference> {
    Relational::Core(Core::Prim(Primitive::Poison))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conformance::syntax::{
        check_applicative_laws, check_functor_laws, check_monad_laws,
        check_ordered_choice_does_not_distribute_over_bind,
        check_ordered_choice_is_not_commutative, check_ordered_choice_laws,
        check_union_distributes_over_bind, check_union_is_not_idempotent, check_union_laws,
    };
    use crate::morphism::CollectionPolicy;

    fn report_holds(report: &crate::conformance::ConformanceReport) {
        assert!(
            report.is_holding(),
            "{}: failures {:?}, unavailable {:?}",
            report.bundle,
            report.failures(),
            report.unavailable()
        );
        assert!(
            report.checked() > 0,
            "{} ran on no samples; a vacuous bundle is not a passing bundle",
            report.bundle
        );
    }

    #[test]
    fn functor_laws_hold() {
        let report =
            check_functor_laws(&Env, &functor_inputs(), &corpus(), BUDGET, &mut agreement());
        report_holds(&report);
        assert!(report.laws.iter().all(|law| law.is_holding()));
    }

    #[test]
    fn applicative_laws_hold() {
        let report = check_applicative_laws(
            &Env,
            &applicative_inputs(),
            &corpus(),
            BUDGET,
            &mut agreement(),
        );
        report_holds(&report);
        // All four laws ran: no symbol was missing from the reference signature.
        assert_eq!(report.laws.len(), 4);
        assert!(report.laws.iter().all(|law| law.is_holding()));
    }

    /// The `Unavailable` channel is not decoration: withholding a symbol must
    /// name it rather than silently passing.
    #[test]
    fn a_withheld_symbol_is_reported_by_name_not_skipped() {
        let mut inputs = applicative_inputs();
        inputs.compose_value = None;
        let report = check_applicative_laws(&Env, &inputs, &corpus(), BUDGET, &mut agreement());
        assert_eq!(
            report.unavailable(),
            vec![(
                "applicative composition: ap (ap (ap (pure (.)) u) v) w == ap u (ap v w)",
                "compose_value"
            )]
        );
        assert!(!report.is_holding());
    }

    #[test]
    fn monad_laws_hold() {
        let report = check_monad_laws(&Env, &monad_inputs(), &corpus(), BUDGET, &mut agreement());
        report_holds(&report);
    }

    /// The same laws on the branch [`monad_inputs`] cannot reach.
    ///
    /// `subject` yields `Tag(1)`, so `RejectOne` declines and associativity
    /// pins the *rejecting* half of the caller's `RejectOneThenAtom` claim.
    /// Make `Continuation::RejectOneThenAtom` resolve to `Pure(value)` rather
    /// than `Fail` when rejected and this must go red — while `monad_laws_hold`
    /// stays green, which is precisely why both exist.
    #[test]
    fn monad_laws_hold_on_the_rejecting_path() {
        let report = check_monad_laws(
            &Env,
            &rejecting_monad_inputs(),
            &corpus(),
            BUDGET,
            &mut agreement(),
        );
        report_holds(&report);
    }

    #[test]
    fn ordered_choice_laws_hold() {
        let report =
            check_ordered_choice_laws(&Env, &choice_inputs(), &corpus(), BUDGET, &mut agreement());
        report_holds(&report);
    }

    #[test]
    fn union_laws_hold_as_enumerated() {
        let report = check_union_laws(
            &Env,
            &union_inputs(),
            &corpus(),
            BUDGET,
            LIMITS,
            &mut agreement(),
            &CollectionPolicy::AS_ENUMERATED,
        );
        // Commutativity and idempotence are unavailable under the default policy,
        // and that is the correct report: both are false on the nose.
        assert_eq!(
            report.unavailable(),
            vec![
                (
                    "union commutativity (up to permutation only)",
                    "ResultOrdering::UpToPermutation"
                ),
                (
                    "union idempotence (relative to caller dedup only)",
                    "Duplicates::CollapseAgreeing"
                ),
            ]
        );
        assert!(report.failures().is_empty(), "{:?}", report.failures());
    }

    /// Commutativity becomes checkable only once the caller opts into comparing
    /// up to permutation — and idempotence only once they opt into dedup.
    #[test]
    fn union_commutativity_and_idempotence_need_their_policies() {
        let report = check_union_laws(
            &Env,
            &union_inputs(),
            &corpus(),
            BUDGET,
            LIMITS,
            &mut agreement(),
            &CollectionPolicy::UP_TO_DEDUPLICATION,
        );
        assert!(report.unavailable().is_empty());
        assert!(report.failures().is_empty(), "{:?}", report.failures());
        assert!(report.checked() > 0);
    }

    /// **Corpus obligation 1**, asserted as a test: the reference relational
    /// program produces two results at the same extent. Without this the scoped
    /// take-first agreement is confirmed everywhere and proves nothing.
    #[test]
    fn corpus_contains_a_genuinely_ambiguous_parser() {
        let program = ambiguous_union();
        let mut observe = |source: &[u8], start: usize| {
            crate::morphism::observe_relational(
                crate::host::RelationalPrefixParser::parse_prefixes(
                    &crate::syntax::RelationalEvaluator::new(&program, &Env, BUDGET, LIMITS),
                    source,
                    start,
                ),
            )
        };
        let audit = crate::morphism::audit_relational_ambiguity(&mut observe, &corpus());
        assert!(
            audit.is_genuinely_ambiguous(),
            "the relational corpus must contain >= 2 results at one extent: {audit:?}"
        );
    }

    /// **Corpus obligation 2**, asserted as a test: a bind above a choice whose
    /// continuation declines on the first alternative's value and succeeds on the
    /// second's. This is the counterexample separating ordered choice from union,
    /// and without it the entire non-collapse suite is vacuous while green.
    #[test]
    fn corpus_contains_a_bind_above_a_choice_that_separates() {
        let report = check_ordered_choice_does_not_distribute_over_bind(
            &Env,
            &atom(1),
            &atom(2),
            &Continuation::RejectOne,
            &corpus(),
            BUDGET,
            &mut agreement(),
        );
        assert!(
            report.exhibited(),
            "no divergence found; the corpus lacks the separating shape: {report:?}"
        );
    }

    /// ...and the relational operator *does* distribute, which is what makes the
    /// two genuinely different operators rather than two spellings of one.
    #[test]
    fn union_distributes_over_bind_where_ordered_choice_does_not() {
        let mut inputs = union_inputs();
        inputs.k = Continuation::RejectOne;
        let law = check_union_distributes_over_bind(
            &Env,
            &inputs,
            &corpus(),
            BUDGET,
            LIMITS,
            &mut agreement(),
            &CollectionPolicy::AS_ENUMERATED,
        );
        assert!(law.is_holding(), "{:?}", law.agreement.failures);
    }

    #[test]
    fn ordered_choice_is_not_commutative() {
        let report = check_ordered_choice_is_not_commutative(
            &Env,
            &atom(1),
            &atom(2),
            &corpus(),
            BUDGET,
            &mut agreement(),
        );
        assert!(report.exhibited(), "{report:?}");
    }

    #[test]
    fn union_is_not_idempotent() {
        let report =
            check_union_is_not_idempotent(&Env, &relational_atom(1), &corpus(), BUDGET, LIMITS);
        assert!(
            report.exhibited(),
            "union(p, p) did not double the result count anywhere: {report:?}"
        );
    }
}
