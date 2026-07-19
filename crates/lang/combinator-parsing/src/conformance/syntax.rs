//! Tier (i) for encoding F — the syntax encoding, where programs are data.
//!
//! This is the tier that can actually be property-tested at the program level,
//! and it is the second load-bearing justification for keeping the syntax
//! encoding at all: `Ordered<S>` and `Relational<S>` are *values*, so laws can be
//! stated by building both sides as data and evaluating them. Arbitrary Rust
//! closures cannot be generated, so the host encoding admits nothing comparable.
//!
//! # Composite symbols are caller input, never constructed here
//!
//! A law like `map g (map f p) ≡ map (g ∘ f) p` mentions `g ∘ f`, and a
//! defunctionalized symbol set need not be closed under composition. So the
//! composite is supplied by the caller as a *claim*, and conformance verifies the
//! claim rather than constructing a symbol it has no right to construct. An
//! absent symbol yields [`LawReport::unavailable`] naming what was needed.
//!
//! # Every law here quantifies over `(program, environment)` pairs
//!
//! Never over programs alone. `Core::Rule` and `Core::Bind` resolve through the
//! environment, so two programs equal as data denote different parsers under
//! different environments. The environment is a parameter of every function
//! below, and no result transfers to a different one.

use crate::budget::{CombinatorBudget, CombinatorEvalError, RelationalLimits};
use crate::conformance::{ConformanceReport, LawReport};
use crate::host::RelationalPrefixParser;
use crate::morphism::agreement::{
    AgreementOutcome, CollectionPolicy, Corpus, Duplicates, ScopeReport, Side, ValueAgreement,
};
use crate::morphism::check::{compare_partial, compare_relational};
use crate::morphism::{PartialObserved, RelationalObserved, observe_partial, observe_relational};
use crate::syntax::{
    Core, Ordered, OrderedEnv, PartialEvaluator, Relational, RelationalEnv, RelationalEvaluator,
    Signature,
};
use covalence_parsing_api::PartialPrefixParser;

// ---------------------------------------------------------------------------
// Program builders — public, because callers assemble their own corpora
// ---------------------------------------------------------------------------

pub fn ordered_pure<S: Signature>(value: S::Value) -> Ordered<S> {
    Ordered::Core(Core::Pure(value))
}

pub fn ordered_map<S: Signature>(function: S::Function, inner: Ordered<S>) -> Ordered<S> {
    Ordered::Core(Core::Map(function, Box::new(inner)))
}

/// `functions` is parsed first, then `arguments`, left to right in the source.
pub fn ordered_ap<S: Signature>(functions: Ordered<S>, arguments: Ordered<S>) -> Ordered<S> {
    Ordered::Core(Core::Ap(Box::new(functions), Box::new(arguments)))
}

pub fn ordered_bind<S: Signature>(head: Ordered<S>, continuation: S::Continuation) -> Ordered<S> {
    Ordered::Core(Core::Bind(Box::new(head), continuation))
}

pub fn relational_pure<S: Signature>(value: S::Value) -> Relational<S> {
    Relational::Core(Core::Pure(value))
}

pub fn relational_map<S: Signature>(function: S::Function, inner: Relational<S>) -> Relational<S> {
    Relational::Core(Core::Map(function, Box::new(inner)))
}

pub fn relational_ap<S: Signature>(
    functions: Relational<S>,
    arguments: Relational<S>,
) -> Relational<S> {
    Relational::Core(Core::Ap(Box::new(functions), Box::new(arguments)))
}

pub fn relational_bind<S: Signature>(
    head: Relational<S>,
    continuation: S::Continuation,
) -> Relational<S> {
    Relational::Core(Core::Bind(Box::new(head), continuation))
}

// ---------------------------------------------------------------------------
// Observation
// ---------------------------------------------------------------------------

type OrderedObserved<S, E> = PartialObserved<
    <S as Signature>::Value,
    CombinatorEvalError<<E as crate::syntax::SignatureEnv<S>>::Error>,
>;

fn observe_ordered<S, E>(
    program: &Ordered<S>,
    env: &E,
    budget: CombinatorBudget,
    source: &[S::Atom],
    start: usize,
) -> OrderedObserved<S, E>
where
    S: Signature,
    E: OrderedEnv<S> + ?Sized,
{
    observe_partial(PartialEvaluator::new(program, env, budget).parse_prefix(source, start))
}

type RelationalObserved_<S, E> = RelationalObserved<
    <S as Signature>::Value,
    CombinatorEvalError<<E as crate::syntax::SignatureEnv<S>>::Error>,
>;

fn observe_relational_program<S, E>(
    program: &Relational<S>,
    env: &E,
    budget: CombinatorBudget,
    limits: RelationalLimits,
    source: &[S::Atom],
    start: usize,
) -> RelationalObserved_<S, E>
where
    S: Signature,
    E: RelationalEnv<S> + ?Sized,
{
    observe_relational(
        RelationalEvaluator::new(program, env, budget, limits).parse_prefixes(source, start),
    )
}

/// Run one two-sided ordered law over a corpus.
fn run_ordered_law<S, E, G>(
    law: &'static str,
    left: &Ordered<S>,
    right: &Ordered<S>,
    env: &E,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    agreement: &mut G,
) -> LawReport
where
    S: Signature,
    E: OrderedEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let mut report = LawReport::new(law);
    for (index, source, start) in corpus.samples() {
        let outcome = compare_partial(
            observe_ordered(left, env, budget, source, start),
            observe_ordered(right, env, budget, source, start),
            agreement,
        );
        report.record(index, start, outcome);
    }
    report
}

/// Run one two-sided relational law over a corpus.
#[allow(clippy::too_many_arguments)] // A private two-sided runner: every argument is a
// distinct policy knob the caller chose, and bundling them would hide which is which.
fn run_relational_law<S, E, G>(
    law: &'static str,
    left: &Relational<S>,
    right: &Relational<S>,
    env: &E,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    limits: RelationalLimits,
    agreement: &mut G,
    policy: &CollectionPolicy,
) -> LawReport
where
    S: Signature,
    E: RelationalEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let mut report = LawReport::new(law);
    for (index, source, start) in corpus.samples() {
        let outcome = compare_relational(
            observe_relational_program(left, env, budget, limits, source, start),
            observe_relational_program(right, env, budget, limits, source, start),
            agreement,
            policy,
        );
        report.record(index, start, outcome);
    }
    report
}

// ---------------------------------------------------------------------------
// Functor
// ---------------------------------------------------------------------------

pub struct FunctorLawInputs<S: Signature> {
    pub subject: Ordered<S>,
    pub identity: S::Function,
    pub f: S::Function,
    pub g: S::Function,
    /// The caller's claim about `g ∘ f`. Not constructed here: the symbol set
    /// need not be closed under composition.
    pub g_after_f: S::Function,
}

/// > **identity** `map id p ≡ p`
/// > **composition** `map g (map f p) ≡ map g_after_f p`
///
/// Both up to the observation projection. Witnesses differ on the two sides of
/// composition by construction — that is the point of the law, not a defect —
/// and a check demanding witness equality would be checking a false law.
pub fn check_functor_laws<S, E, G>(
    env: &E,
    inputs: &FunctorLawInputs<S>,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    agreement: &mut G,
) -> ConformanceReport
where
    S: Signature,
    E: OrderedEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let mut report = ConformanceReport::new("functor");
    report.push(run_ordered_law(
        "functor identity: map id p == p",
        &ordered_map(inputs.identity.clone(), inputs.subject.clone()),
        &inputs.subject,
        env,
        corpus,
        budget,
        agreement,
    ));
    report.push(run_ordered_law(
        "functor composition: map g (map f p) == map (g . f) p",
        &ordered_map(
            inputs.g.clone(),
            ordered_map(inputs.f.clone(), inputs.subject.clone()),
        ),
        &ordered_map(inputs.g_after_f.clone(), inputs.subject.clone()),
        env,
        corpus,
        budget,
        agreement,
    ));
    report
}

// ---------------------------------------------------------------------------
// Applicative
// ---------------------------------------------------------------------------

/// Inputs for the applicative bundle.
///
/// `subject`, `argument` and `final_argument` play the roles of `u`, `v` and `w`
/// in the composition law, so `subject` and `argument` must be parsers producing
/// **function** values in the caller's value universe. The identity law is the
/// one exception: it holds for any subject.
///
/// **Deviation from the brief**, minimal: `argument`, `final_argument` and
/// `function_value` are added. Composition mentions three parsers and the
/// homomorphism law mentions a function *value*; a bundle carrying only `subject`
/// could state neither.
pub struct ApplicativeLawInputs<S: Signature> {
    pub subject: Ordered<S>,
    pub argument: Ordered<S>,
    pub final_argument: Ordered<S>,
    /// A value that `apply_value` honours as the identity function.
    pub identity_value: Option<S::Value>,
    /// The section `($ y)` for the chosen `y`.
    pub section_of: Option<S::Value>,
    /// A composition combinator value.
    pub compose_value: Option<S::Value>,
    /// A function value, for the homomorphism law.
    pub function_value: Option<S::Value>,
    pub y: S::Value,
    /// The caller's claim about `function_value y`.
    pub f_of_x: Option<S::Value>,
}

/// > **identity** `ap (pure id) u ≡ u`
/// > **homomorphism** `ap (pure f) (pure y) ≡ pure (f y)`
/// > **interchange** `ap u (pure y) ≡ ap (pure ($ y)) u`
/// > **composition** `ap (ap (ap (pure (.)) u) v) w ≡ ap u (ap v w)`
///
/// Each **only up to the positive projection**: the two sides visit the
/// sub-parsers in different orders and record different witnesses and different
/// split offsets. Any law demanding witness equality here is false.
///
/// Every law whose caller-supplied symbol is absent reports
/// [`LawReport::unavailable`] naming the missing field, rather than being skipped.
pub fn check_applicative_laws<S, E, G>(
    env: &E,
    inputs: &ApplicativeLawInputs<S>,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    agreement: &mut G,
) -> ConformanceReport
where
    S: Signature,
    E: OrderedEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let mut report = ConformanceReport::new("applicative");

    const IDENTITY: &str = "applicative identity: ap (pure id) u == u";
    match &inputs.identity_value {
        None => report.push(LawReport::unavailable(IDENTITY, "identity_value")),
        Some(identity) => report.push(run_ordered_law(
            IDENTITY,
            &ordered_ap(ordered_pure(identity.clone()), inputs.subject.clone()),
            &inputs.subject,
            env,
            corpus,
            budget,
            agreement,
        )),
    }

    const HOMOMORPHISM: &str = "applicative homomorphism: ap (pure f) (pure y) == pure (f y)";
    match (&inputs.function_value, &inputs.f_of_x) {
        (Some(function), Some(applied)) => report.push(run_ordered_law(
            HOMOMORPHISM,
            &ordered_ap(
                ordered_pure(function.clone()),
                ordered_pure(inputs.y.clone()),
            ),
            &ordered_pure(applied.clone()),
            env,
            corpus,
            budget,
            agreement,
        )),
        (None, _) => report.push(LawReport::unavailable(HOMOMORPHISM, "function_value")),
        (_, None) => report.push(LawReport::unavailable(HOMOMORPHISM, "f_of_x")),
    }

    const INTERCHANGE: &str = "applicative interchange: ap u (pure y) == ap (pure ($ y)) u";
    match &inputs.section_of {
        None => report.push(LawReport::unavailable(INTERCHANGE, "section_of")),
        Some(section) => report.push(run_ordered_law(
            INTERCHANGE,
            &ordered_ap(inputs.subject.clone(), ordered_pure(inputs.y.clone())),
            &ordered_ap(ordered_pure(section.clone()), inputs.subject.clone()),
            env,
            corpus,
            budget,
            agreement,
        )),
    }

    const COMPOSITION: &str =
        "applicative composition: ap (ap (ap (pure (.)) u) v) w == ap u (ap v w)";
    match &inputs.compose_value {
        None => report.push(LawReport::unavailable(COMPOSITION, "compose_value")),
        Some(compose) => report.push(run_ordered_law(
            COMPOSITION,
            &ordered_ap(
                ordered_ap(
                    ordered_ap(ordered_pure(compose.clone()), inputs.subject.clone()),
                    inputs.argument.clone(),
                ),
                inputs.final_argument.clone(),
            ),
            &ordered_ap(
                inputs.subject.clone(),
                ordered_ap(inputs.argument.clone(), inputs.final_argument.clone()),
            ),
            env,
            corpus,
            budget,
            agreement,
        )),
    }

    report
}

// ---------------------------------------------------------------------------
// Monad
// ---------------------------------------------------------------------------

pub struct MonadLawInputs<S: Signature> {
    pub subject: Ordered<S>,
    pub value: S::Value,
    pub k: S::Continuation,
    pub h: S::Continuation,
    /// The caller's claim about `\x -> k x >>= h`.
    pub k_then_h: S::Continuation,
    /// A continuation resolving to `Pure(x)` for its argument `x`.
    pub pure_continuation: S::Continuation,
}

/// > **left identity** `bind (pure v) k ≡ resolve(k, v)`
/// > **right identity** `bind p pure_continuation ≡ p`
/// > **associativity** `bind (bind p k) h ≡ bind p k_then_h`
///
/// Associativity holds **only up to the positive projection**: the two sides
/// carry different witness *types* — a left-nested sequence against a
/// right-nested one — so the on-the-nose statement is not expressible in this
/// encoding at all. A reassociation relating them exists at the host level, but
/// its iso-hood is unproved, so the observation projection is the honest check.
///
/// Two *distinct, non-trivial* continuations are required, and the fixture
/// obligation is real: associativity with `k = h` survives argument-ordering and
/// offset-threading bugs routinely.
pub fn check_monad_laws<S, E, G>(
    env: &E,
    inputs: &MonadLawInputs<S>,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    agreement: &mut G,
) -> ConformanceReport
where
    S: Signature,
    E: OrderedEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let mut report = ConformanceReport::new("monad");

    const LEFT: &str = "monad left identity: bind (pure v) k == resolve(k, v)";
    match env.ordered_resolve(&inputs.k, &inputs.value) {
        Ok(resolved) => report.push(run_ordered_law(
            LEFT,
            &ordered_bind(ordered_pure(inputs.value.clone()), inputs.k.clone()),
            &resolved,
            env,
            corpus,
            budget,
            agreement,
        )),
        // The environment itself failed to resolve the symbol. That is evaluator
        // failure on the right-hand side of the law, not a violation of it.
        Err(_) => {
            let mut law = LawReport::new(LEFT);
            for (index, _, start) in corpus.samples() {
                law.record(
                    index,
                    start,
                    AgreementOutcome::Inconclusive { side: Side::Right },
                );
            }
            report.push(law);
        }
    }

    report.push(run_ordered_law(
        "monad right identity: bind p pure == p",
        &ordered_bind(inputs.subject.clone(), inputs.pure_continuation.clone()),
        &inputs.subject,
        env,
        corpus,
        budget,
        agreement,
    ));

    report.push(run_ordered_law(
        "monad associativity: bind (bind p k) h == bind p (k >=> h)",
        &ordered_bind(
            ordered_bind(inputs.subject.clone(), inputs.k.clone()),
            inputs.h.clone(),
        ),
        &ordered_bind(inputs.subject.clone(), inputs.k_then_h.clone()),
        env,
        corpus,
        budget,
        agreement,
    ));

    report
}

// ---------------------------------------------------------------------------
// Ordered choice
// ---------------------------------------------------------------------------

pub struct ChoiceLawInputs<S: Signature> {
    pub p: Ordered<S>,
    pub q: Ordered<S>,
    pub r: Ordered<S>,
    /// A function symbol, for the annihilation law `map f Fail ≡ Fail`.
    pub f: S::Function,
    /// A continuation symbol, for `bind Fail k ≡ Fail`.
    pub k: S::Continuation,
}

/// The left-biased monoid laws, **and the ones that are not laws**.
///
/// > `Fail` is a two-sided unit; `OrderedChoice(vec![]) ≡ Fail`; choice is
/// > associative and **idempotent**; `map f Fail ≡ Fail`; `bind Fail k ≡ Fail`.
///
/// # Associativity holds only in the diagnostic-forgetting quotient
///
/// The two associations agree on positive content but fold diagnostics
/// differently: `merge(merge(dp, dq), dr)` against `merge(dp, merge(dq, dr))`.
/// They are equal only when the caller's merge is itself associative.
/// Observations carry no diagnostic, so this check runs *inside* that quotient —
/// it cannot see the difference, and reporting the law as holding here does not
/// establish the unquotiented statement. Three of four source designs asserted it
/// flat.
///
/// # Commutativity is not checked here, because it is false
///
/// See [`check_ordered_choice_is_not_commutative`], which actively looks for a
/// witnessing sample rather than leaving the non-law merely unmentioned.
pub fn check_ordered_choice_laws<S, E, G>(
    env: &E,
    inputs: &ChoiceLawInputs<S>,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    agreement: &mut G,
) -> ConformanceReport
where
    S: Signature,
    E: OrderedEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let mut report = ConformanceReport::new("ordered choice");
    let choice = |alternatives: Vec<Ordered<S>>| Ordered::OrderedChoice(alternatives);

    report.push(run_ordered_law(
        "choice left unit: oc(Fail, p) == p",
        &choice(vec![Ordered::Fail, inputs.p.clone()]),
        &inputs.p,
        env,
        corpus,
        budget,
        agreement,
    ));
    report.push(run_ordered_law(
        "choice right unit: oc(p, Fail) == p",
        &choice(vec![inputs.p.clone(), Ordered::Fail]),
        &inputs.p,
        env,
        corpus,
        budget,
        agreement,
    ));
    report.push(run_ordered_law(
        "choice empty is Fail: oc([]) == Fail",
        &choice(Vec::new()),
        &Ordered::Fail,
        env,
        corpus,
        budget,
        agreement,
    ));
    report.push(run_ordered_law(
        "choice associativity (diagnostic-forgetting quotient only)",
        &choice(vec![
            choice(vec![inputs.p.clone(), inputs.q.clone()]),
            inputs.r.clone(),
        ]),
        &choice(vec![
            inputs.p.clone(),
            choice(vec![inputs.q.clone(), inputs.r.clone()]),
        ]),
        env,
        corpus,
        budget,
        agreement,
    ));
    report.push(run_ordered_law(
        "choice idempotence: oc(p, p) == p",
        &choice(vec![inputs.p.clone(), inputs.p.clone()]),
        &inputs.p,
        env,
        corpus,
        budget,
        agreement,
    ));
    report.push(run_ordered_law(
        "choice annihilation: map f Fail == Fail",
        &ordered_map(inputs.f.clone(), Ordered::Fail),
        &Ordered::Fail,
        env,
        corpus,
        budget,
        agreement,
    ));
    report.push(run_ordered_law(
        "choice annihilation: bind Fail k == Fail",
        &ordered_bind(Ordered::Fail, inputs.k.clone()),
        &Ordered::Fail,
        env,
        corpus,
        budget,
        agreement,
    ));
    report
}

/// **Ordered choice is not commutative**, asserted as a positive claim.
///
/// Looks for a sample where `oc(p, q)` and `oc(q, p)` disagree, which exists
/// whenever both alternatives can match at one offset with different values.
///
/// The success condition is [`ScopeReport::exhibited`]: a run finding no
/// divergence means the corpus is too weak — `p` and `q` never both matched — not
/// that ordered choice is commutative. A corpus of non-overlapping alternatives
/// confirms every choice law above and never reaches this one.
pub fn check_ordered_choice_is_not_commutative<S, E, G>(
    env: &E,
    p: &Ordered<S>,
    q: &Ordered<S>,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    agreement: &mut G,
) -> ScopeReport
where
    S: Signature,
    E: OrderedEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let forward = Ordered::OrderedChoice(vec![p.clone(), q.clone()]);
    let backward = Ordered::OrderedChoice(vec![q.clone(), p.clone()]);
    let mut report = ScopeReport::new("ordered choice is not commutative");
    for (index, source, start) in corpus.samples() {
        match compare_partial(
            observe_ordered(&forward, env, budget, source, start),
            observe_ordered(&backward, env, budget, source, start),
            agreement,
        ) {
            AgreementOutcome::Agreed => report.record_agreement(),
            AgreementOutcome::Disagreed(_) => report.record_divergence(index, start),
            AgreementOutcome::Inconclusive { .. } => report.record_inconclusive(),
        }
    }
    report
}

// ---------------------------------------------------------------------------
// Relational union
// ---------------------------------------------------------------------------

pub struct UnionLawInputs<S: Signature> {
    pub p: Relational<S>,
    pub q: Relational<S>,
    pub r: Relational<S>,
    pub f: S::Function,
    pub k: S::Continuation,
}

/// The commutative-monoid laws of union, each with its actual side condition.
///
/// > `Void` is a two-sided unit; `Union(vec![]) ≡ Void`; union is associative,
/// > and commutative **up to permutation**; `map f Void ≡ Void`;
/// > `bind Void k ≡ Void`; `ap Void p ≡ Void`.
///
/// # Commutativity needs a policy, and so does idempotence
///
/// Commutativity is **false on the nose** — enumeration order is meaningful data
/// in this family, and in-house relational parsers sort their results and assert
/// the stability of that order. It is checked only when the caller's policy is
/// [`crate::morphism::ResultOrdering::UpToPermutation`], and reports
/// `Unavailable` otherwise.
///
/// Idempotence is **false outright**: union is a free/multiset union, so
/// `union(p, p)` enumerates twice as many results. It becomes statable only
/// relative to a caller-supplied dedup, i.e. under
/// [`crate::morphism::Duplicates::CollapseAgreeing`], whose well-definedness
/// requires the agreement be an equivalence — an unchecked caller obligation.
/// Under any other policy it reports `Unavailable`, never a failure: reporting it
/// as a failure is what tempts an implementer to "fix" it by deduplicating inside
/// the evaluator, destroying the ambiguity retention this fragment exists for.
/// See also [`check_union_is_not_idempotent`].
pub fn check_union_laws<S, E, G>(
    env: &E,
    inputs: &UnionLawInputs<S>,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    limits: RelationalLimits,
    agreement: &mut G,
    policy: &CollectionPolicy,
) -> ConformanceReport
where
    S: Signature,
    E: RelationalEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let mut report = ConformanceReport::new("union");
    let union = |alternatives: Vec<Relational<S>>| Relational::Union(alternatives);
    let law = |name, left: Relational<S>, right: Relational<S>, agreement: &mut G| {
        run_relational_law(
            name, &left, &right, env, corpus, budget, limits, agreement, policy,
        )
    };

    report.push(law(
        "union left unit: union(Void, p) == p",
        union(vec![Relational::Void, inputs.p.clone()]),
        inputs.p.clone(),
        agreement,
    ));
    report.push(law(
        "union right unit: union(p, Void) == p",
        union(vec![inputs.p.clone(), Relational::Void]),
        inputs.p.clone(),
        agreement,
    ));
    report.push(law(
        "union empty is Void: union([]) == Void",
        union(Vec::new()),
        Relational::Void,
        agreement,
    ));
    report.push(law(
        "union associativity",
        union(vec![
            union(vec![inputs.p.clone(), inputs.q.clone()]),
            inputs.r.clone(),
        ]),
        union(vec![
            inputs.p.clone(),
            union(vec![inputs.q.clone(), inputs.r.clone()]),
        ]),
        agreement,
    ));
    report.push(law(
        "union annihilation: map f Void == Void",
        relational_map(inputs.f.clone(), Relational::Void),
        Relational::Void,
        agreement,
    ));
    report.push(law(
        "union annihilation: bind Void k == Void",
        relational_bind(Relational::Void, inputs.k.clone()),
        Relational::Void,
        agreement,
    ));
    report.push(law(
        "union annihilation: ap Void p == Void",
        relational_ap(Relational::Void, inputs.p.clone()),
        Relational::Void,
        agreement,
    ));

    const COMMUTATIVITY: &str = "union commutativity (up to permutation only)";
    if policy.ordering == crate::morphism::ResultOrdering::UpToPermutation {
        report.push(law(
            COMMUTATIVITY,
            union(vec![inputs.p.clone(), inputs.q.clone()]),
            union(vec![inputs.q.clone(), inputs.p.clone()]),
            agreement,
        ));
    } else {
        report.push(LawReport::unavailable(
            COMMUTATIVITY,
            "ResultOrdering::UpToPermutation",
        ));
    }

    const IDEMPOTENCE: &str = "union idempotence (relative to caller dedup only)";
    if policy.duplicates == Duplicates::CollapseAgreeing {
        report.push(law(
            IDEMPOTENCE,
            union(vec![inputs.p.clone(), inputs.p.clone()]),
            inputs.p.clone(),
            agreement,
        ));
    } else {
        report.push(LawReport::unavailable(
            IDEMPOTENCE,
            "Duplicates::CollapseAgreeing",
        ));
    }

    report
}

/// **Union is not idempotent**, asserted as a positive claim about cardinality.
///
/// `union(p, p)` enumerates `2n` results where `p` enumerates `n`. This is
/// checked so that nobody "fixes" the failing idempotence law by deduplicating
/// inside the evaluator — which would silently destroy the ambiguity retention
/// the relational capability exists to provide.
///
/// Success is [`ScopeReport::exhibited`]: a corpus on which `p` never produces a
/// result cannot exhibit the doubling, and reports so rather than passing.
pub fn check_union_is_not_idempotent<S, E>(
    env: &E,
    p: &Relational<S>,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    limits: RelationalLimits,
) -> ScopeReport
where
    S: Signature,
    E: RelationalEnv<S> + ?Sized,
{
    let doubled = Relational::Union(vec![p.clone(), p.clone()]);
    let mut report = ScopeReport::new("union is not idempotent");
    for (index, source, start) in corpus.samples() {
        let single = observe_relational_program(p, env, budget, limits, source, start);
        let twice = observe_relational_program(&doubled, env, budget, limits, source, start);
        match (single, twice) {
            (RelationalObserved::Enumerated(single), RelationalObserved::Enumerated(twice)) => {
                if !single.is_empty() && twice.len() == 2 * single.len() {
                    report.record_divergence(index, start);
                } else if twice.len() == single.len() {
                    // Cardinality unchanged: something deduplicated.
                    report.record_agreement();
                } else {
                    report.record_inconclusive();
                }
            }
            _ => report.record_inconclusive(),
        }
    }
    report
}

// ---------------------------------------------------------------------------
// The separating law: distribution over bind
// ---------------------------------------------------------------------------

/// **Union distributes over bind.**
///
/// > `bind (union(p, q)) k ≡ union(bind p k, bind q k)`
///
/// Relational bind continues *every* head result, so splitting the union above or
/// below the bind enumerates the same things in the same order. This is the law
/// that its ordered counterpart fails, and two operators that disagree on
/// left-distributivity are two operators.
///
/// `p`, `q` and `k` are taken from [`UnionLawInputs`]; `r` and `f` are unused here.
pub fn check_union_distributes_over_bind<S, E, G>(
    env: &E,
    inputs: &UnionLawInputs<S>,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    limits: RelationalLimits,
    agreement: &mut G,
    policy: &CollectionPolicy,
) -> LawReport
where
    S: Signature,
    E: RelationalEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let UnionLawInputs { p, q, k, .. } = inputs;
    run_relational_law(
        "union distributes over bind",
        &relational_bind(Relational::Union(vec![p.clone(), q.clone()]), k.clone()),
        &Relational::Union(vec![
            relational_bind(p.clone(), k.clone()),
            relational_bind(q.clone(), k.clone()),
        ]),
        env,
        corpus,
        budget,
        limits,
        agreement,
        policy,
    )
}

/// **Ordered choice does NOT distribute over bind**, asserted as a positive claim.
///
/// > `bind (oc(p, q)) k` and `oc(bind p k, bind q k)` **disagree.**
///
/// Ordered choice commits to `p`'s match and never retries `q` when `k` declines,
/// so the left side declines where the right side matches through `q`. This is
/// the sharpest separator between the two operators, and it is the reason the
/// refinement between them is stated as a claim about *whole observations* and
/// never as a rewrite rule on programs.
///
/// # This function is the second corpus obligation
///
/// Its success condition is [`ScopeReport::exhibited`]. Finding no divergence
/// means the corpus lacks a **bind above a choice whose continuation declines on
/// the first alternative's value and succeeds on the second's** — the shape
/// without which the entire non-collapse suite is vacuous while appearing green.
/// A run with zero divergences is a statement about the corpus, never about the
/// operators.
pub fn check_ordered_choice_does_not_distribute_over_bind<S, E, G>(
    env: &E,
    p: &Ordered<S>,
    q: &Ordered<S>,
    k: &S::Continuation,
    corpus: &Corpus<'_, [S::Atom]>,
    budget: CombinatorBudget,
    agreement: &mut G,
) -> ScopeReport
where
    S: Signature,
    E: OrderedEnv<S> + ?Sized,
    G: ValueAgreement<S::Value, S::Value>,
{
    let above = ordered_bind(
        Ordered::OrderedChoice(vec![p.clone(), q.clone()]),
        k.clone(),
    );
    let below = Ordered::OrderedChoice(vec![
        ordered_bind(p.clone(), k.clone()),
        ordered_bind(q.clone(), k.clone()),
    ]);
    let mut report = ScopeReport::new("ordered choice does not distribute over bind");
    for (index, source, start) in corpus.samples() {
        match compare_partial(
            observe_ordered(&above, env, budget, source, start),
            observe_ordered(&below, env, budget, source, start),
            agreement,
        ) {
            AgreementOutcome::Agreed => report.record_agreement(),
            AgreementOutcome::Disagreed(_) => report.record_divergence(index, start),
            AgreementOutcome::Inconclusive { .. } => report.record_inconclusive(),
        }
    }
    report
}
