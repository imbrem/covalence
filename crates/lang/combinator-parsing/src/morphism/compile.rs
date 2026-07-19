//! Axis 2 — **N1 · compiling the syntax encoding into host combinator values.**
//!
//! This is a *compilation*, not an equivalence, and the asymmetry is the point.
//!
//! # The law
//!
//! Write `⟦·⟧` for the appropriate evaluation as in [`super::widen`]. For every fragment:
//!
//! > for all `program`, `env`, `budget`, `s`, `i`:
//! > `compile_*(program, env, budget)` and the corresponding syntax evaluator built from
//! > `(program, env, budget)` agree on
//! >   **(i)** the `Match` / `NoMatch` / `Err` trichotomy, and
//! >   **(ii)** the positive projection `obs(m) = (value, consumed, remainder)` under a
//! >           caller-supplied value agreement.
//!
//! # Status: **semantics-preserving translation. Non-surjective. No inverse.**
//!
//! ## §e.12 — there is no `decompile`
//!
//! `decompile: DynPartial -> Ordered<S>` does not exist and cannot be written. A compiled
//! parser is a tree of `Fn` closures; closures are not data, cannot be inspected, cannot
//! be hashed, and cannot be enumerated. Axis 2 is a **poset, not a groupoid**: the arrow
//! goes one way only, and "compilation" rather than "equivalence" is the correct word for
//! the relationship between the two encodings.
//!
//! Two consequences that are easy to state and easy to forget. First, the compiled parser
//! implements no `ParserSyntax`: it has no syntax to hand back, and that absence is
//! exactly the information the compilation destroyed. Second, this is precisely why the
//! syntax encoding is kept — it is the only one of the two that is data, and therefore the
//! only one over which the law above can be *property-generated* rather than exercised on
//! hand-written examples.
//!
//! ## What is *not* claimed
//!
//! **Diagnostic payloads are not compared and agreement on them is not claimed.** These
//! functions build the syntax encoding's flat diagnostic, but a hand-written host
//! expression builds whatever the caller's `merge` builds. Agreement there is neither
//! claimed nor testable.
//!
//! **Witnesses are never compared** by any morphism law. The compiled expression
//! nevertheless builds the *syntax encoding's* witness types rather than the host
//! encoding's shared sequencing witnesses, so that positive projections remain comparable
//! without a witness translation standing between the two sides of the law. That is an
//! honest description of what the compiled parser is: a host expression computing the
//! spine's evidence.
//!
//! ## §e.10 — the law quantifies over pairs, never over programs
//!
//! Every claim above is universally quantified over `(program, env)` **pairs**. Two
//! programs equal as data behave differently under different environments, because
//! `Core::Rule(i)` and `Core::Bind(_, k)` resolve through the environment. Any
//! cross-fragment consequence additionally carries the environment-coherence side
//! condition documented on `syntax::deterministic_into_ordered`.

use crate::budget::{
    CombinatorBudget, CombinatorDiagnostic, CombinatorDiagnosticKind, CombinatorEvalError,
    CombinatorLimit, CombinatorResource, RelationalLimits, check_primitive_extent,
};
use crate::host::partial::DynPartial;
use crate::host::total::DynTotal;
use crate::host::{RelationalPrefixParser, TotalPrefixParser};
use crate::syntax::{
    Core, CoreWitness, Deterministic, DeterministicWitness, Ordered, OrderedEnv, OrderedWitness,
    Relational, RelationalEnv, RelationalWitness, Signature, TotalEnv,
};
use covalence_parsing_api::{
    ParseAttempt, PartialPrefixParser, PrefixInterpretation, PrefixParseResult, Span,
};

// TODO(cov:lang.combinator-parsing.compilation-agreement-unproved, minor): N1 — that a
// compiled program and its syntax evaluator agree on the trichotomy and the positive
// projection — is checked here only by falsification over a finite corpus under a finite
// budget. Its universal form quantifies over all programs, all environments, all sources
// and all start offsets, and is provable only at the logic level through
// `theory::CombinatorMorphismLaws::compilation_preserves_semantics`. No amount of host
// evaluation may mint it.

// PERF(cov:lang.combinator-parsing.compile-rebuilds-rule-bodies, minor): `Core::Rule` and
// `Core::Bind` compile their target on every entry at every offset, because a rule body may
// be recursive and a continuation's program is not known until its value is. The syntax
// encoding's indexed rule table is the in-tree answer for grammars that feel this; measure
// before caching compiled bodies behind an `Rc`.

/// Per-evaluation mutable state, mirroring each syntax evaluator's own local state.
///
/// The parsing API's methods take `&self`, so this is threaded explicitly through the
/// compiled closure tree rather than stored on a node. Storing a bound on a node makes
/// resource behaviour association-dependent, which is exactly what makes union
/// associativity fail as a resource artifact rather than a semantic disagreement.
struct State {
    budget: CombinatorBudget,
    limits: RelationalLimits,
    work: usize,
    depth: usize,
    witness_nodes: usize,
    resolutions: usize,
    results: usize,
    farthest: usize,
    active: Vec<(usize, usize)>,
}

impl State {
    fn new(budget: CombinatorBudget, limits: RelationalLimits, start: usize) -> Self {
        Self {
            budget,
            limits,
            work: 0,
            depth: 0,
            witness_nodes: 0,
            resolutions: 0,
            results: 0,
            farthest: start,
            active: Vec::new(),
        }
    }

    fn charge_witness<X>(&mut self) -> Result<(), CombinatorEvalError<X>> {
        if self.witness_nodes >= self.budget.max_witness_nodes {
            return exhausted(
                CombinatorResource::WitnessNodes,
                self.budget.max_witness_nodes,
            );
        }
        self.witness_nodes += 1;
        Ok(())
    }

    fn charge_resolution<X>(&mut self) -> Result<(), CombinatorEvalError<X>> {
        if self.resolutions >= self.budget.max_continuation_resolutions {
            return exhausted(
                CombinatorResource::ContinuationResolutions,
                self.budget.max_continuation_resolutions,
            );
        }
        self.resolutions += 1;
        Ok(())
    }

    /// Charge one **newly created** relational result about to be pushed into a node holding
    /// `node_results`. Both bounds are checked before the push, never after.
    ///
    /// Mirrors the evaluator's `push_result`: the global bound is charged once per result, by
    /// the node that creates it, so it does not depend on how a union is associated.
    fn charge_result<X>(&mut self, node_results: usize) -> Result<(), CombinatorEvalError<X>> {
        self.relay_result(node_results)?;
        if self.results >= self.limits.max_results {
            return exhausted(CombinatorResource::Results, self.limits.max_results);
        }
        self.results += 1;
        Ok(())
    }

    /// Check the per-node bound for one **already charged** result being relayed.
    fn relay_result<X>(&mut self, node_results: usize) -> Result<(), CombinatorEvalError<X>> {
        if node_results >= self.limits.max_results_per_node {
            return exhausted(
                CombinatorResource::ResultsPerNode,
                self.limits.max_results_per_node,
            );
        }
        Ok(())
    }
}

fn exhausted<T, X>(
    resource: CombinatorResource,
    limit: usize,
) -> Result<T, CombinatorEvalError<X>> {
    Err(CombinatorEvalError::ResourceExhausted(
        CombinatorLimit::new(resource, limit),
    ))
}

/// Charge work and depth before recursing, never after: a post-hoc check is not a bound.
fn enter<X>(st: &mut State) -> Result<(), CombinatorEvalError<X>> {
    if st.work >= st.budget.max_work {
        return exhausted(CombinatorResource::Work, st.budget.max_work);
    }
    st.work += 1;
    if st.depth >= st.budget.max_depth {
        return exhausted(CombinatorResource::Depth, st.budget.max_depth);
    }
    st.depth += 1;
    Ok(())
}

fn source_units_ok<X>(len: usize, budget: CombinatorBudget) -> Result<(), CombinatorEvalError<X>> {
    if len > budget.max_source_units {
        return exhausted(CombinatorResource::SourceUnits, budget.max_source_units);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Deterministic fragment -> total host parser
// ---------------------------------------------------------------------------

/// A compiled step: a closure over the source, an offset, and the evaluation state.
///
/// The three capabilities differ only in `T` — the shape of what a step yields — which is
/// exactly where their semantics live. Sharing the closure shape relates nothing: the
/// aliases below stay distinct types, and no value inhabits two of them.
/// Parameterised by the atom type rather than by `S`, because `<S as Signature>::Atom` is a
/// projection and inference cannot solve back through it to recover `S`.
type Step<'e, A, T, X> =
    Box<dyn Fn(&[A], usize, &mut State) -> Result<T, CombinatorEvalError<X>> + 'e>;

/// Wrap a compiled step so entering it charges depth and leaving it releases depth.
///
/// Depth is charged in one place for all three capabilities, so the bound cannot drift
/// between them.
fn bounded<'e, A: 'e, T: 'e, X: 'e>(body: Step<'e, A, T, X>) -> Step<'e, A, T, X> {
    Box::new(move |source, at, st| {
        enter(st)?;
        let out = body(source, at, st);
        st.depth -= 1;
        out
    })
}

/// A compiled deterministic step. No `Option`: the total environment cannot decline.
type TotalStep<'e, S, X> =
    Step<'e, <S as Signature>::Atom, (<S as Signature>::Value, DeterministicWitness<S>, usize), X>;

fn total_step<'e, S, E>(node: &Deterministic<S>, env: &'e E) -> TotalStep<'e, S, E::Error>
where
    S: Signature + 'e,
    E: TotalEnv<S> + ?Sized + 'e,
{
    let body: TotalStep<'e, S, E::Error> = match &node.0 {
        Core::Pure(value) => {
            let value = value.clone();
            Box::new(move |_source, at, st| {
                st.charge_witness()?;
                Ok((
                    value.clone(),
                    DeterministicWitness(CoreWitness::Pure { at }),
                    at,
                ))
            })
        }

        Core::Prim(primitive) => {
            let primitive = primitive.clone();
            Box::new(move |source, at, st| {
                let matched = env
                    .total_step(&primitive, source, at)
                    .map_err(CombinatorEvalError::Environment)?;
                let span = check_primitive_extent(at, matched.end, source.len())?;
                st.charge_witness()?;
                Ok((
                    matched.value,
                    DeterministicWitness(CoreWitness::Prim {
                        span,
                        witness: matched.witness,
                    }),
                    matched.end,
                ))
            })
        }

        Core::Map(function, inner) => {
            let function = function.clone();
            let inner = total_step(inner, env);
            Box::new(move |source, at, st| {
                let (value, witness, end) = inner(source, at, st)?;
                let value = env
                    .apply_function(&function, value)
                    .map_err(CombinatorEvalError::Environment)?;
                st.charge_witness()?;
                let span = Span::new(at, end).expect("forward step");
                Ok((
                    value,
                    DeterministicWitness(CoreWitness::Map {
                        span,
                        inner: Box::new(witness),
                    }),
                    end,
                ))
            })
        }

        Core::Ap(functions, arguments) => {
            let functions = total_step(functions, env);
            let arguments = total_step(arguments, env);
            Box::new(move |source, at, st| {
                let (f, wf, mid) = functions(source, at, st)?;
                let (x, wx, end) = arguments(source, mid, st)?;
                let value = env
                    .apply_value(f, x)
                    .map_err(CombinatorEvalError::Environment)?;
                st.charge_witness()?;
                let span = Span::new(at, end).expect("forward step");
                Ok((
                    value,
                    DeterministicWitness(CoreWitness::Ap {
                        span,
                        function: Box::new(wf),
                        argument: Box::new(wx),
                        split: mid,
                    }),
                    end,
                ))
            })
        }

        Core::Bind(head, continuation) => {
            let head = total_step(head, env);
            let continuation = continuation.clone();
            Box::new(move |source, at, st| {
                let (value, wh, mid) = head(source, at, st)?;
                st.charge_resolution()?;
                let next = env
                    .total_resolve(&continuation, &value)
                    .map_err(CombinatorEvalError::Environment)?;
                // The continuation's program is not known until its argument is, so it is
                // compiled here rather than at compile time. This is the concrete reason
                // there is no inverse: a closure that builds a parser per value cannot be
                // read back as a term.
                let (value, wc, end) = total_step(&next, env)(source, mid, st)?;
                st.charge_witness()?;
                let span = Span::new(at, end).expect("forward step");
                Ok((
                    value,
                    DeterministicWitness(CoreWitness::Bind {
                        span,
                        head: Box::new(wh),
                        continuation: Box::new(wc),
                        split: mid,
                    }),
                    end,
                ))
            })
        }

        Core::Rule(rule) => {
            let rule = *rule;
            Box::new(move |source, at, st| {
                if st.active.contains(&(rule, at)) {
                    return Err(CombinatorEvalError::LeftRecursion { rule, offset: at });
                }
                let body = env
                    .total_rule(rule)
                    .ok_or(CombinatorEvalError::UndefinedRule { rule })?;
                let body = total_step(body, env);
                st.active.push((rule, at));
                let out = body(source, at, st);
                st.active.pop();
                let (value, inner, end) = out?;
                st.charge_witness()?;
                let span = Span::new(at, end).expect("forward step");
                Ok((
                    value,
                    DeterministicWitness(CoreWitness::Rule {
                        rule,
                        span,
                        inner: Box::new(inner),
                    }),
                    end,
                ))
            })
        }
    };

    bounded(body)
}

/// A compiled deterministic program, evaluated as a total prefix parser.
struct CompiledTotal<'e, S: Signature, X> {
    step: TotalStep<'e, S, X>,
    budget: CombinatorBudget,
}

impl<S: Signature, X> TotalPrefixParser for CompiledTotal<'_, S, X> {
    type Source = [S::Atom];
    type Value = S::Value;
    type Witness = DeterministicWitness<S>;
    type Error = CombinatorEvalError<X>;

    fn parse_prefix_total(
        &self,
        source: &[S::Atom],
        start: usize,
    ) -> Result<PrefixInterpretation<S::Value, DeterministicWitness<S>>, Self::Error> {
        source_units_ok(source.len(), self.budget)?;
        let mut st = State::new(self.budget, RelationalLimits::new(0, 0), start);
        let (value, witness, end) = (self.step)(source, start, &mut st)?;
        Ok(PrefixInterpretation {
            value,
            witness,
            consumed: Span::new(start, end).expect("forward step"),
            remainder: end,
        })
    }
}

/// A compiled deterministic program, erased behind the host encoding's boxed total type.
pub type CompiledTotalParser<'e, S, X> = DynTotal<
    'e,
    [<S as Signature>::Atom],
    <S as Signature>::Value,
    DeterministicWitness<S>,
    CombinatorEvalError<X>,
>;

/// A compiled ordered program, erased behind the host encoding's boxed partial type.
pub type CompiledOrderedParser<'e, S, X> = DynPartial<
    'e,
    [<S as Signature>::Atom],
    <S as Signature>::Value,
    OrderedWitness<S>,
    CombinatorDiagnostic,
    CombinatorEvalError<X>,
>;

/// **N1 (deterministic fragment).** Compile a deterministic program against a total
/// environment into a host total prefix parser.
///
/// # Law
///
/// > `compile_deterministic(program, env, budget)` and
/// > `TotalEvaluator::new(program, env, budget)` agree on the `Ok` / `Err` dichotomy and,
/// > on `Ok`, on the positive projection.
///
/// # Status: semantics-preserving translation, no inverse.
///
/// **Caller precondition `start <= source.len()`**, inherited from `TotalPrefixParser`,
/// which has no non-match channel in which to report a start out of range.
pub fn compile_deterministic<'e, S, E>(
    program: &Deterministic<S>,
    env: &'e E,
    budget: CombinatorBudget,
) -> CompiledTotalParser<'e, S, E::Error>
where
    S: Signature + 'e,
    E: TotalEnv<S> + ?Sized + 'e,
{
    DynTotal::new(CompiledTotal {
        step: total_step(program, env),
        budget,
    })
}

// ---------------------------------------------------------------------------
// Ordered fragment -> partial host parser
// ---------------------------------------------------------------------------

/// A compiled ordered step. `Ok(None)` is ordinary non-match; `Err` is evaluator failure.
type OrderedStep<'e, S, X> = Step<
    'e,
    <S as Signature>::Atom,
    Option<(<S as Signature>::Value, OrderedWitness<S>, usize)>,
    X,
>;

fn ordered_step<'e, S, E>(node: &Ordered<S>, env: &'e E) -> OrderedStep<'e, S, E::Error>
where
    S: Signature + 'e,
    E: OrderedEnv<S> + ?Sized + 'e,
{
    let body: OrderedStep<'e, S, E::Error> = match node {
        Ordered::Fail => Box::new(move |_source, at, st| {
            st.farthest = st.farthest.max(at);
            Ok(None)
        }),

        Ordered::OrderedChoice(alternatives) => {
            let alternatives: Vec<OrderedStep<'e, S, E::Error>> = alternatives
                .iter()
                .map(|alternative| ordered_step(alternative, env))
                .collect();
            Box::new(move |source, at, st| {
                for (chosen, alternative) in alternatives.iter().enumerate() {
                    // Committing and left-biased: the loop *returns* on the first match,
                    // so later alternatives are never evaluated. That early return is the
                    // operational content of the distinction from relational union.
                    if let Some((value, inner, end)) = alternative(source, at, st)? {
                        st.charge_witness()?;
                        let span = Span::new(at, end).expect("forward step");
                        return Ok(Some((
                            value,
                            OrderedWitness::OrderedChoice {
                                chosen,
                                span,
                                inner: Box::new(inner),
                            },
                            end,
                        )));
                    }
                }
                st.farthest = st.farthest.max(at);
                Ok(None)
            })
        }

        Ordered::Core(core) => match core {
            Core::Pure(value) => {
                let value = value.clone();
                Box::new(move |_source, at, st| {
                    st.charge_witness()?;
                    Ok(Some((
                        value.clone(),
                        OrderedWitness::Core(CoreWitness::Pure { at }),
                        at,
                    )))
                })
            }

            Core::Prim(primitive) => {
                let primitive = primitive.clone();
                Box::new(move |source, at, st| {
                    match env
                        .step(&primitive, source, at)
                        .map_err(CombinatorEvalError::Environment)?
                    {
                        None => {
                            st.farthest = st.farthest.max(at);
                            Ok(None)
                        }
                        Some(matched) => {
                            let span = check_primitive_extent(at, matched.end, source.len())?;
                            st.charge_witness()?;
                            st.farthest = st.farthest.max(matched.end);
                            Ok(Some((
                                matched.value,
                                OrderedWitness::Core(CoreWitness::Prim {
                                    span,
                                    witness: matched.witness,
                                }),
                                matched.end,
                            )))
                        }
                    }
                })
            }

            Core::Map(function, inner) => {
                let function = function.clone();
                let inner = ordered_step(inner, env);
                Box::new(move |source, at, st| {
                    let Some((value, witness, end)) = inner(source, at, st)? else {
                        return Ok(None);
                    };
                    let value = env
                        .apply_function(&function, value)
                        .map_err(CombinatorEvalError::Environment)?;
                    st.charge_witness()?;
                    let span = Span::new(at, end).expect("forward step");
                    Ok(Some((
                        value,
                        OrderedWitness::Core(CoreWitness::Map {
                            span,
                            inner: Box::new(witness),
                        }),
                        end,
                    )))
                })
            }

            Core::Ap(functions, arguments) => {
                let functions = ordered_step(functions, env);
                let arguments = ordered_step(arguments, env);
                Box::new(move |source, at, st| {
                    let Some((f, wf, mid)) = functions(source, at, st)? else {
                        return Ok(None);
                    };
                    let Some((x, wx, end)) = arguments(source, mid, st)? else {
                        return Ok(None);
                    };
                    let value = env
                        .apply_value(f, x)
                        .map_err(CombinatorEvalError::Environment)?;
                    st.charge_witness()?;
                    let span = Span::new(at, end).expect("forward step");
                    Ok(Some((
                        value,
                        OrderedWitness::Core(CoreWitness::Ap {
                            span,
                            function: Box::new(wf),
                            argument: Box::new(wx),
                            split: mid,
                        }),
                        end,
                    )))
                })
            }

            Core::Bind(head, continuation) => {
                let head = ordered_step(head, env);
                let continuation = continuation.clone();
                Box::new(move |source, at, st| {
                    let Some((value, wh, mid)) = head(source, at, st)? else {
                        return Ok(None);
                    };
                    st.charge_resolution()?;
                    let next = env
                        .ordered_resolve(&continuation, &value)
                        .map_err(CombinatorEvalError::Environment)?;
                    // Ordered bind does NOT retry the head: the head is a partial function
                    // with exactly one result, and backtracking enters only through ordered
                    // choice. This is the semantic difference from relational bind that
                    // makes ordered choice fail to distribute over bind.
                    let Some((value, wc, end)) = ordered_step(&next, env)(source, mid, st)? else {
                        return Ok(None);
                    };
                    st.charge_witness()?;
                    let span = Span::new(at, end).expect("forward step");
                    Ok(Some((
                        value,
                        OrderedWitness::Core(CoreWitness::Bind {
                            span,
                            head: Box::new(wh),
                            continuation: Box::new(wc),
                            split: mid,
                        }),
                        end,
                    )))
                })
            }

            Core::Rule(rule) => {
                let rule = *rule;
                Box::new(move |source, at, st| {
                    if st.active.contains(&(rule, at)) {
                        return Err(CombinatorEvalError::LeftRecursion { rule, offset: at });
                    }
                    let body = env
                        .ordered_rule(rule)
                        .ok_or(CombinatorEvalError::UndefinedRule { rule })?;
                    let body = ordered_step(body, env);
                    st.active.push((rule, at));
                    let out = body(source, at, st);
                    st.active.pop();
                    let Some((value, inner, end)) = out? else {
                        return Ok(None);
                    };
                    st.charge_witness()?;
                    let span = Span::new(at, end).expect("forward step");
                    Ok(Some((
                        value,
                        OrderedWitness::Core(CoreWitness::Rule {
                            rule,
                            span,
                            inner: Box::new(inner),
                        }),
                        end,
                    )))
                })
            }
        },
    };

    bounded(body)
}

/// A compiled ordered program, evaluated as a partial prefix parser.
struct CompiledOrdered<'e, S: Signature, X> {
    step: OrderedStep<'e, S, X>,
    budget: CombinatorBudget,
}

impl<S: Signature, X> PartialPrefixParser for CompiledOrdered<'_, S, X> {
    type Source = [S::Atom];
    type Value = S::Value;
    type Witness = OrderedWitness<S>;
    type Diagnostic = CombinatorDiagnostic;
    type Error = CombinatorEvalError<X>;

    fn parse_prefix(
        &self,
        source: &[S::Atom],
        start: usize,
    ) -> PrefixParseResult<S::Value, OrderedWitness<S>, CombinatorDiagnostic, Self::Error> {
        source_units_ok(source.len(), self.budget)?;
        if start > source.len() {
            return Ok(ParseAttempt::NoMatch(CombinatorDiagnostic::new(
                start,
                CombinatorDiagnosticKind::StartOutOfBounds,
            )));
        }
        let mut st = State::new(self.budget, RelationalLimits::new(0, 0), start);
        Ok(match (self.step)(source, start, &mut st)? {
            None => ParseAttempt::NoMatch(CombinatorDiagnostic::new(
                st.farthest,
                CombinatorDiagnosticKind::NoMatch,
            )),
            Some((value, witness, end)) => ParseAttempt::Match(PrefixInterpretation {
                value,
                witness,
                consumed: Span::new(start, end).expect("forward step"),
                remainder: end,
            }),
        })
    }
}

/// **N1 (ordered fragment).** Compile an ordered program against an ordered environment
/// into a host partial prefix parser.
///
/// # Law
///
/// > `compile_ordered(program, env, budget)` and
/// > `PartialEvaluator::new(program, env, budget)` agree on the `Match` / `NoMatch` / `Err`
/// > trichotomy and, on `Match`, on the positive projection under a caller agreement.
///
/// # Status: semantics-preserving translation, non-surjective, **no inverse**.
///
/// Diagnostic payloads are outside the law. The returned parser reports the syntax
/// encoding's flat diagnostic, and a hand-written host expression reports whatever its
/// caller-supplied merge builds; that is the whole reason the host encoding is kept, and
/// it is why agreement on diagnostics is neither claimed nor testable.
pub fn compile_ordered<'e, S, E>(
    program: &Ordered<S>,
    env: &'e E,
    budget: CombinatorBudget,
) -> CompiledOrderedParser<'e, S, E::Error>
where
    S: Signature + 'e,
    E: OrderedEnv<S> + ?Sized + 'e,
{
    DynPartial::new(CompiledOrdered {
        step: ordered_step(program, env),
        budget,
    })
}

// ---------------------------------------------------------------------------
// Relational fragment -> relational host parser
// ---------------------------------------------------------------------------

/// A compiled relational step: an enumeration, with no early return anywhere.
type RelationalStep<'e, S, X> = Step<
    'e,
    <S as Signature>::Atom,
    Vec<(<S as Signature>::Value, RelationalWitness<S>, usize)>,
    X,
>;

/// One enumerated result: value, evidence, and the offset after it.
type Enumerated<S> = (<S as Signature>::Value, RelationalWitness<S>, usize);

/// Push a newly created result, charging the global and per-node bounds.
fn push<S: Signature, X>(
    out: &mut Vec<Enumerated<S>>,
    st: &mut State,
    result: Enumerated<S>,
) -> Result<(), CombinatorEvalError<X>> {
    st.charge_result(out.len())?;
    out.push(result);
    Ok(())
}

/// Push a result the node was handed rather than created, checking only the per-node bound.
fn relay<S: Signature, X>(
    out: &mut Vec<Enumerated<S>>,
    st: &mut State,
    result: Enumerated<S>,
) -> Result<(), CombinatorEvalError<X>> {
    st.relay_result(out.len())?;
    out.push(result);
    Ok(())
}

fn relational_step<'e, S, E>(node: &Relational<S>, env: &'e E) -> RelationalStep<'e, S, E::Error>
where
    S: Signature + 'e,
    E: RelationalEnv<S> + ?Sized + 'e,
{
    let body: RelationalStep<'e, S, E::Error> = match node {
        Relational::Void => Box::new(move |_source, _at, _st| Ok(Vec::new())),

        Relational::Union(alternatives) => {
            let alternatives: Vec<RelationalStep<'e, S, E::Error>> = alternatives
                .iter()
                .map(|alternative| relational_step(alternative, env))
                .collect();
            Box::new(move |source, at, st| {
                let mut out = Vec::new();
                for (alternative, branch) in alternatives.iter().enumerate() {
                    // Every alternative is explored and every result retained. There is no
                    // early return and no deduplication: union is a free/multiset union,
                    // so `union(p, p)` enumerates twice as many results.
                    for (value, inner, end) in branch(source, at, st)? {
                        st.charge_witness()?;
                        let span = Span::new(at, end).expect("forward step");
                        // Union relays: its outputs are in bijection with its branches'.
                        relay(
                            &mut out,
                            st,
                            (
                                value,
                                RelationalWitness::Union {
                                    alternative,
                                    span,
                                    inner: Box::new(inner),
                                },
                                end,
                            ),
                        )?;
                    }
                }
                Ok(out)
            })
        }

        Relational::Core(core) => match core {
            Core::Pure(value) => {
                let value = value.clone();
                Box::new(move |_source, at, st| {
                    st.charge_witness()?;
                    let mut out = Vec::new();
                    push(
                        &mut out,
                        st,
                        (
                            value.clone(),
                            RelationalWitness::Core(CoreWitness::Pure { at }),
                            at,
                        ),
                    )?;
                    Ok(out)
                })
            }

            Core::Prim(primitive) => {
                let primitive = primitive.clone();
                Box::new(move |source, at, st| {
                    let mut out = Vec::new();
                    // Primitives are deterministic: all nondeterminism in this algebra is
                    // explicit syntax, so a primitive contributes zero or one result.
                    if let Some(matched) = env
                        .step(&primitive, source, at)
                        .map_err(CombinatorEvalError::Environment)?
                    {
                        let span = check_primitive_extent(at, matched.end, source.len())?;
                        st.charge_witness()?;
                        push(
                            &mut out,
                            st,
                            (
                                matched.value,
                                RelationalWitness::Core(CoreWitness::Prim {
                                    span,
                                    witness: matched.witness,
                                }),
                                matched.end,
                            ),
                        )?;
                    }
                    Ok(out)
                })
            }

            Core::Map(function, inner) => {
                let function = function.clone();
                let inner = relational_step(inner, env);
                Box::new(move |source, at, st| {
                    let mut out = Vec::new();
                    for (value, witness, end) in inner(source, at, st)? {
                        let value = env
                            .apply_function(&function, value)
                            .map_err(CombinatorEvalError::Environment)?;
                        st.charge_witness()?;
                        let span = Span::new(at, end).expect("forward step");
                        // Mapping creates no results: it rewrites the values it was handed.
                        relay(
                            &mut out,
                            st,
                            (
                                value,
                                RelationalWitness::Core(CoreWitness::Map {
                                    span,
                                    inner: Box::new(witness),
                                }),
                                end,
                            ),
                        )?;
                    }
                    Ok(out)
                })
            }

            Core::Ap(functions, arguments) => {
                let functions = relational_step(functions, env);
                let arguments = relational_step(arguments, env);
                Box::new(move |source, at, st| {
                    let mut out = Vec::new();
                    for (f, wf, mid) in functions(source, at, st)? {
                        for (x, wx, end) in arguments(source, mid, st)? {
                            let value = env
                                .apply_value(f.clone(), x)
                                .map_err(CombinatorEvalError::Environment)?;
                            st.charge_witness()?;
                            let span = Span::new(at, end).expect("forward step");
                            push(
                                &mut out,
                                st,
                                (
                                    value,
                                    RelationalWitness::Core(CoreWitness::Ap {
                                        span,
                                        function: Box::new(wf.clone()),
                                        argument: Box::new(wx),
                                        split: mid,
                                    }),
                                    end,
                                ),
                            )?;
                        }
                    }
                    Ok(out)
                })
            }

            Core::Bind(head, continuation) => {
                let head = relational_step(head, env);
                let continuation = continuation.clone();
                Box::new(move |source, at, st| {
                    let mut out = Vec::new();
                    // Relational bind continues *every* head result. That is the semantic
                    // difference from ordered bind, and it is why union left-distributes
                    // over bind while ordered choice does not.
                    for (value, wh, mid) in head(source, at, st)? {
                        st.charge_resolution()?;
                        let next = env
                            .relational_resolve(&continuation, &value)
                            .map_err(CombinatorEvalError::Environment)?;
                        for (value, wc, end) in relational_step(&next, env)(source, mid, st)? {
                            st.charge_witness()?;
                            let span = Span::new(at, end).expect("forward step");
                            push(
                                &mut out,
                                st,
                                (
                                    value,
                                    RelationalWitness::Core(CoreWitness::Bind {
                                        span,
                                        head: Box::new(wh.clone()),
                                        continuation: Box::new(wc),
                                        split: mid,
                                    }),
                                    end,
                                ),
                            )?;
                        }
                    }
                    Ok(out)
                })
            }

            Core::Rule(rule) => {
                let rule = *rule;
                Box::new(move |source, at, st| {
                    if st.active.contains(&(rule, at)) {
                        return Err(CombinatorEvalError::LeftRecursion { rule, offset: at });
                    }
                    let body = env
                        .relational_rule(rule)
                        .ok_or(CombinatorEvalError::UndefinedRule { rule })?;
                    let body = relational_step(body, env);
                    st.active.push((rule, at));
                    let inner = body(source, at, st);
                    st.active.pop();
                    let mut out = Vec::new();
                    for (value, witness, end) in inner? {
                        st.charge_witness()?;
                        let span = Span::new(at, end).expect("forward step");
                        // A rule reference relays its body's results unchanged.
                        relay(
                            &mut out,
                            st,
                            (
                                value,
                                RelationalWitness::Core(CoreWitness::Rule {
                                    rule,
                                    span,
                                    inner: Box::new(witness),
                                }),
                                end,
                            ),
                        )?;
                    }
                    Ok(out)
                })
            }
        },
    };

    bounded(body)
}

/// A compiled relational program, evaluated as a relational prefix parser.
///
/// This holds its [`RelationalLimits`] at the evaluation boundary and threads them through
/// the whole compiled tree in the per-evaluation state, so no node owns a bound and
/// reassociating a union does not change which node trips which limit.
pub struct CompiledRelational<'e, S: Signature, X> {
    step: RelationalStep<'e, S, X>,
    budget: CombinatorBudget,
    limits: RelationalLimits,
}

impl<S: Signature, X> RelationalPrefixParser for CompiledRelational<'_, S, X> {
    type Source = [S::Atom];
    type Value = S::Value;
    type Witness = RelationalWitness<S>;
    type Error = CombinatorEvalError<X>;

    fn parse_prefixes(
        &self,
        source: &[S::Atom],
        start: usize,
    ) -> Result<Vec<PrefixInterpretation<S::Value, RelationalWitness<S>>>, Self::Error> {
        source_units_ok(source.len(), self.budget)?;
        let mut st = State::new(self.budget, self.limits, start);
        Ok((self.step)(source, start, &mut st)?
            .into_iter()
            .map(|(value, witness, end)| PrefixInterpretation {
                value,
                witness,
                consumed: Span::new(start, end).expect("forward step"),
                remainder: end,
            })
            .collect())
    }
}

/// **N1 (relational fragment).** Compile a relational program against a relational
/// environment into a host relational prefix parser.
///
/// # Law
///
/// > `compile_relational(program, env, budget, limits)` and
/// > `RelationalEvaluator::new(program, env, budget, limits)` agree on the `Ok` / `Err`
/// > dichotomy and, on `Ok`, on the enumerated sequence up to the positive projection —
/// > **in enumeration order**, since order is meaningful data in this family and comparing
/// > up to permutation is an explicit caller policy rather than a default.
///
/// # Status: semantics-preserving translation, no inverse.
///
/// There is no diagnostic on either side, permanently. An empty enumeration on either side
/// proves no negative fact, and the two agreeing on emptiness relates *two evaluators*, not
/// an evaluator to truth.
pub fn compile_relational<'e, S, E>(
    program: &Relational<S>,
    env: &'e E,
    budget: CombinatorBudget,
    limits: RelationalLimits,
) -> CompiledRelational<'e, S, E::Error>
where
    S: Signature + 'e,
    E: RelationalEnv<S> + ?Sized + 'e,
{
    CompiledRelational {
        step: relational_step(program, env),
        budget,
        limits,
    }
}

// TODO(cov:lang.combinator-parsing.compiled-relational-not-erasable, minor): A compiled
// relational program cannot be lifted into `host::relational::Leaf` and hence not into
// `DynRelational`, because `Leaf` requires `Error = CombinatorError<E>` and this parser
// reports `CombinatorEvalError<E>`. Bridging needs a relational `MapErr`, which the host
// encoding does not have (only the partial capability has one). Until then a compiled
// relational program is usable at the top of an expression but not as a foreign leaf
// inside one.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{PartialEvaluator, PrimitiveMatch, RelationalEvaluator, SignatureEnv};

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Bytes;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Never;

    impl Signature for Bytes {
        type Atom = u8;
        type Value = u8;
        type Primitive = u8;
        type Function = ();
        type Continuation = ();
        type PrimitiveWitness = ();
    }

    struct Env;

    impl SignatureEnv<Bytes> for Env {
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
        ) -> Result<Option<PrimitiveMatch<Bytes>>, Never> {
            Ok(match source.get(at) {
                Some(byte) if byte == primitive => Some(PrimitiveMatch {
                    value: *byte,
                    witness: (),
                    end: at + 1,
                }),
                _ => None,
            })
        }
    }

    impl OrderedEnv<Bytes> for Env {
        fn ordered_rule(&self, _rule: usize) -> Option<&Ordered<Bytes>> {
            None
        }

        fn ordered_resolve(&self, _continuation: &(), value: &u8) -> Result<Ordered<Bytes>, Never> {
            Ok(Ordered::Core(Core::Prim(*value)))
        }
    }

    impl RelationalEnv<Bytes> for Env {
        fn relational_rule(&self, _rule: usize) -> Option<&Relational<Bytes>> {
            None
        }

        fn relational_resolve(
            &self,
            _continuation: &(),
            value: &u8,
        ) -> Result<Relational<Bytes>, Never> {
            Ok(Relational::Core(Core::Prim(*value)))
        }
    }

    const BUDGET: CombinatorBudget = CombinatorBudget::new(64, 512, 32, 512, 64);
    const LIMITS: RelationalLimits = RelationalLimits::new(64, 64);

    fn ordered_program() -> Ordered<Bytes> {
        // `bind(oc(prim 'a', prim 'b'), k)` where `k` expects the byte just parsed again.
        Ordered::Core(Core::Bind(
            Box::new(Ordered::OrderedChoice(vec![
                Ordered::Core(Core::Prim(b'a')),
                Ordered::Core(Core::Prim(b'b')),
            ])),
            (),
        ))
    }

    /// N1 on the ordered fragment: trichotomy and positive projection agree.
    #[test]
    fn compiled_ordered_agrees_with_the_evaluator() {
        let program = ordered_program();
        let evaluator = PartialEvaluator::new(&program, &Env, BUDGET);
        let compiled = compile_ordered(&program, &Env, BUDGET);

        for source in [&b""[..], b"a", b"aa", b"ab", b"bb", b"ba", b"aab"] {
            for start in 0..=source.len() + 1 {
                let left = evaluator.parse_prefix(source, start).expect("no failure");
                let right = compiled.parse_prefix(source, start).expect("no failure");
                match (left, right) {
                    (ParseAttempt::Match(l), ParseAttempt::Match(r)) => {
                        // Positive projection only: witnesses are never compared.
                        assert_eq!(
                            (l.value, l.consumed, l.remainder),
                            (r.value, r.consumed, r.remainder)
                        );
                    }
                    (ParseAttempt::NoMatch(_), ParseAttempt::NoMatch(_)) => {}
                    (l, r) => panic!("trichotomy disagreement at {start}: {l:?} vs {r:?}"),
                }
            }
        }
    }

    /// N1 on the relational fragment, compared in enumeration order.
    #[test]
    fn compiled_relational_agrees_with_the_evaluator() {
        let program = Relational::Union(vec![
            Relational::Core(Core::Prim(b'a')),
            Relational::Core(Core::Prim(b'a')),
            Relational::Core(Core::Prim(b'b')),
        ]);
        let evaluator = RelationalEvaluator::new(&program, &Env, BUDGET, LIMITS);
        let compiled = compile_relational(&program, &Env, BUDGET, LIMITS);

        for source in [&b""[..], b"a", b"b", b"ab"] {
            for start in 0..=source.len() {
                let left = evaluator.parse_prefixes(source, start).expect("no failure");
                let right = compiled.parse_prefixes(source, start).expect("no failure");
                assert_eq!(left.len(), right.len());
                for (l, r) in left.into_iter().zip(right) {
                    assert_eq!(
                        (l.value, l.consumed, l.remainder),
                        (r.value, r.consumed, r.remainder)
                    );
                }
            }
        }
        // Union is a free union: `a` twice really is two results, not one.
        assert_eq!(
            compiled.parse_prefixes(b"a", 0).expect("no failure").len(),
            2
        );
    }

    /// An environment that reports an extent outside the source, exactly as
    /// `syntax::env`'s own fixture does. Repeated here because that fixture is private to
    /// the `syntax` module tree.
    struct HostileEnv;

    impl SignatureEnv<Bytes> for HostileEnv {
        type Error = Never;

        fn apply_function(&self, _function: &(), argument: u8) -> Result<u8, Never> {
            Ok(argument)
        }

        fn apply_value(&self, _function: u8, argument: u8) -> Result<u8, Never> {
            Ok(argument)
        }

        fn step(
            &self,
            _primitive: &u8,
            source: &[u8],
            _at: usize,
        ) -> Result<Option<PrimitiveMatch<Bytes>>, Never> {
            Ok(Some(PrimitiveMatch {
                value: 0,
                witness: (),
                end: source.len() + 100,
            }))
        }
    }

    impl OrderedEnv<Bytes> for HostileEnv {
        fn ordered_rule(&self, _rule: usize) -> Option<&Ordered<Bytes>> {
            None
        }

        fn ordered_resolve(&self, _continuation: &(), value: &u8) -> Result<Ordered<Bytes>, Never> {
            Ok(Ordered::Core(Core::Pure(*value)))
        }
    }

    /// **The two encodings agree on the trichotomy for an over-running leaf.**
    ///
    /// This used to be a genuine N1 disagreement rather than a payload difference: the
    /// syntax encoding returned `Ok(Match)` carrying a span outside the source, while the
    /// host encoding's [`check_step`] rejected the identical extent as a cursor violation.
    /// Both now report evaluator failure.
    #[test]
    fn both_encodings_reject_a_leaf_that_over_runs_the_source() {
        use crate::host::cursor::check_step;

        let program = Ordered::Core(Core::Prim(0));
        let evaluator = PartialEvaluator::new(&program, &HostileEnv, BUDGET);
        let compiled = compile_ordered(&program, &HostileEnv, BUDGET);
        let expected = Err(CombinatorEvalError::PrimitiveExtent {
            at: 0,
            end: 103,
            source_len: 3,
        });

        // The syntax encoding and its compilation: same trichotomy branch, same payload.
        assert_eq!(evaluator.parse_prefix(b"abc", 0), expected);
        assert_eq!(compiled.parse_prefix(b"abc", 0), expected);

        // The host encoding, on the identical extent, through its own check.
        assert!(
            check_step(
                0,
                3,
                PrefixInterpretation {
                    value: 0u8,
                    witness: (),
                    consumed: Span { start: 0, end: 103 },
                    remainder: 103,
                },
            )
            .is_err()
        );
    }

    /// The compiled relational program charges results where they are created, so its
    /// global bound — like the evaluator's — does not depend on how a union is associated.
    /// Branch result counts are deliberately unequal (2, 2, 1); see the evaluator's twin
    /// test for why an equal-count fixture cannot falsify this.
    #[test]
    fn compiled_relational_global_bound_does_not_depend_on_association() {
        let fan =
            |n: usize| Relational::Union((0..n).map(|_| Relational::Core(Core::Pure(0))).collect());
        let left_nested = Relational::Union(vec![
            Relational::Union(vec![fan(2), fan(2)]),
            Relational::Core(Core::Pure(0)),
        ]);
        let right_nested = Relational::Union(vec![
            fan(2),
            Relational::Union(vec![fan(2), Relational::Core(Core::Pure(0))]),
        ]);

        let outcome = |program: &Relational<Bytes>, max_results: usize| {
            compile_relational(
                program,
                &Env,
                BUDGET,
                RelationalLimits::new(max_results, 1024),
            )
            .parse_prefixes(b"", 0)
            .map(|results| results.len())
        };

        for max_results in 0..=24 {
            assert_eq!(
                outcome(&left_nested, max_results),
                outcome(&right_nested, max_results),
                "associations disagree at max_results = {max_results}"
            );
        }
        assert_eq!(outcome(&left_nested, 5), Ok(5));
    }

    /// The compiled parser is charged the same way the evaluator is, so exhaustion is a
    /// shared outcome rather than a source of spurious disagreement.
    #[test]
    fn compiled_ordered_is_bounded_like_the_evaluator() {
        let program = ordered_program();
        let starved = CombinatorBudget::new(64, 1, 32, 512, 64);
        let evaluator = PartialEvaluator::new(&program, &Env, starved);
        let compiled = compile_ordered(&program, &Env, starved);
        assert_eq!(
            evaluator.parse_prefix(b"aa", 0).unwrap_err(),
            compiled.parse_prefix(b"aa", 0).unwrap_err()
        );
    }
}
