//! Bounded evaluation of the relational fragment as an **enumeration**.

use crate::budget::{
    CombinatorBudget, CombinatorEvalError, CombinatorLimit, CombinatorResource, RelationalLimits,
    check_primitive_extent,
};
use crate::host::RelationalPrefixParser;
use crate::sharing::clone_unless_last;
use crate::syntax::{Core, CoreWitness, Relational, RelationalEnv, RelationalWitness, Signature};
use covalence_parsing_api::{
    ParserSyntax, PrefixInterpretation, RelationalParseResult, RelationalParser, Span,
};

/// Whether enumeration retains prefix matches or only whole-source matches.
///
/// Exactness is an explicit policy rather than a convention about remainders, mirroring
/// `PegMode`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelationalMode {
    Prefix,
    Exact,
}

/// Bounded evaluation of the relational fragment.
///
/// Every alternative of a union is explored and every result is retained: there is no early
/// return anywhere and no deduplication. Union is a **free/multiset** union — `union(p, p)`
/// enumerates twice as many results — and collapsing duplicates inside the evaluator would
/// destroy exactly the ambiguity retention this fragment exists to provide. Deduplication is
/// a caller policy applied to observations, never an evaluator behaviour.
///
/// An empty enumeration proves no negative fact. This evaluator has no diagnostic channel,
/// permanently: granting one would reintroduce the material ordered choice needs.
pub struct RelationalEvaluator<'p, 'e, S: Signature, E: ?Sized> {
    program: &'p Relational<S>,
    env: &'e E,
    budget: CombinatorBudget,
    limits: RelationalLimits,
}

// PERF(cov:lang.combinator-parsing.relational-sharing, major): No derivation sharing, and
// the two halves have different answers. Value-level sharing — a packed forest as in
// cfg-parsing — needs more than the untyped universe provides. *Witness*-level sharing does
// not: `CoreWitness<S, R>` is already generic in its recursion knot, so tying the relational
// witness through `Rc` instead of `Box` would drop witness allocation from
// O(results x depth) to O(results) while leaving Deterministic and Ordered untouched, and
// `Rc` preserves the derived Clone/Debug/PartialEq/Eq that witness comparison relies on.
// The deterministic half of this is already paid off: not cloning on an inner loop's final
// iteration (`sharing::clone_unless_last`) took an unambiguous left-nested Ap chain at depth
// 128 from 16770 allocations to 514, i.e. from quadratic to linear. What is left is the
// genuinely ambiguous case, where each retained alternative still deep-copies a witness of
// its own depth: measured on a 2^k-result Ap chain, allocations per result still climb about
// +3 per level (12.5 at k=3 to 33.1 at k=10), so the total is O(2^k x k) where retention
// alone requires O(2^k). Only `Rc` removes that; until then max_results and max_work are the
// only defence, and truncation is always reported as `ResourceExhausted` rather than silently
// dropping results.

// PERF(cov:lang.combinator-parsing.relational-recomputation, major): `st.active` is cycle
// detection, not memoization, so a rule reachable by p distinct paths at one offset
// re-evaluates its whole subtree p times — the classic backtracking blow-up, whose failure
// mode here is a *truncated* answer reported as `ResourceExhausted` rather than merely a slow
// one. A `(rule, offset)` memo is type-feasible since `Signature` already requires
// `Value: Clone`, but every hit clones each cached value and witness, so it is only clearly a
// win after the witness sharing above. Needs an ambiguous-grammar corpus to measure; the
// crate has none.

/// Per-call mutable state. A0015's methods take `&self`, so this is a local, never a field
/// and never interior mutability.
struct EvalState {
    work: usize,
    depth: usize,
    witness_nodes: usize,
    resolutions: usize,
    results: usize,
    active: Vec<(usize, usize)>,
}

/// One enumerated result: value, evidence, and the offset after it.
type Result3<S> = (<S as Signature>::Value, RelationalWitness<S>, usize);

/// A completed enumeration of prefix interpretations.
type Enumeration<S, E> = Result<
    Vec<PrefixInterpretation<<S as Signature>::Value, RelationalWitness<S>>>,
    CombinatorEvalError<E>,
>;

impl<'p, 'e, S: Signature, E: RelationalEnv<S> + ?Sized> RelationalEvaluator<'p, 'e, S, E> {
    pub fn new(
        program: &'p Relational<S>,
        env: &'e E,
        budget: CombinatorBudget,
        limits: RelationalLimits,
    ) -> Self {
        Self {
            program,
            env,
            budget,
            limits,
        }
    }

    fn exhausted<T>(
        resource: CombinatorResource,
        limit: usize,
    ) -> Result<T, CombinatorEvalError<E::Error>> {
        Err(CombinatorEvalError::ResourceExhausted(CombinatorLimit {
            resource,
            limit,
        }))
    }

    /// Charge and append one **newly created** result: the global bound and the per-node
    /// bound both apply.
    ///
    /// The global counter is charged exactly once per result, by the node that creates it —
    /// `Pure` and `Prim`, and the cross-product operators `Ap` and `Bind`, each of whose
    /// outputs is a new combination rather than one of its inputs. A node that merely relays
    /// what it was handed uses [`Self::relay_result`] instead, which is what keeps the global
    /// bound independent of how a union is associated: re-charging on pass-through costs
    /// `3a + 3b + 2c` for branches of `a`, `b`, `c` results left-associated against
    /// `2a + 3b + 3c` right-associated, equal only when `a == c`.
    ///
    /// Both bounds are checked **before** the push, never after. Draining both arms of a
    /// union and checking afterwards is not a bound, it is a post-hoc assertion that an
    /// adversarial grammar has already defeated.
    fn push_result(
        &self,
        out: &mut Vec<Result3<S>>,
        st: &mut EvalState,
        result: Result3<S>,
    ) -> Result<(), CombinatorEvalError<E::Error>> {
        // Per-node before global, so a node at both limits reports the same resource it did
        // before results were split into created and relayed.
        if out.len() >= self.limits.max_results_per_node {
            return Self::exhausted(
                CombinatorResource::ResultsPerNode,
                self.limits.max_results_per_node,
            );
        }
        if st.results >= self.limits.max_results {
            return Self::exhausted(CombinatorResource::Results, self.limits.max_results);
        }
        st.results += 1;
        out.push(result);
        Ok(())
    }

    /// Append one **already charged** result, checking only the per-node bound.
    ///
    /// The per-node bound is deliberately per node and so applies to relays too: bounding a
    /// single node's fan-out is exactly what it is for. The global bound does not, because
    /// the result was charged where it was created.
    fn relay_result(
        &self,
        out: &mut Vec<Result3<S>>,
        result: Result3<S>,
    ) -> Result<(), CombinatorEvalError<E::Error>> {
        if out.len() >= self.limits.max_results_per_node {
            return Self::exhausted(
                CombinatorResource::ResultsPerNode,
                self.limits.max_results_per_node,
            );
        }
        out.push(result);
        Ok(())
    }

    fn eval(
        &self,
        node: &Relational<S>,
        source: &[S::Atom],
        at: usize,
        st: &mut EvalState,
    ) -> Result<Vec<Result3<S>>, CombinatorEvalError<E::Error>> {
        // Charge before recursing, never after: a post-hoc check is not a bound.
        if st.work >= self.budget.max_work {
            return Self::exhausted(CombinatorResource::Work, self.budget.max_work);
        }
        st.work += 1;
        if st.depth >= self.budget.max_depth {
            return Self::exhausted(CombinatorResource::Depth, self.budget.max_depth);
        }
        st.depth += 1;
        let out = self.eval_inner(node, source, at, st);
        st.depth -= 1;
        out
    }

    fn charge_witness(&self, st: &mut EvalState) -> Result<(), CombinatorEvalError<E::Error>> {
        if st.witness_nodes >= self.budget.max_witness_nodes {
            return Self::exhausted(
                CombinatorResource::WitnessNodes,
                self.budget.max_witness_nodes,
            );
        }
        st.witness_nodes += 1;
        Ok(())
    }

    fn eval_inner(
        &self,
        node: &Relational<S>,
        source: &[S::Atom],
        at: usize,
        st: &mut EvalState,
    ) -> Result<Vec<Result3<S>>, CombinatorEvalError<E::Error>> {
        match node {
            Relational::Void => Ok(Vec::new()),

            Relational::Union(alternatives) => {
                let mut out = Vec::new();
                for (alternative, branch) in alternatives.iter().enumerate() {
                    // Every alternative is explored. No early return: that line-by-line
                    // difference from ordered choice is the operational content of the
                    // distinction between the two operators.
                    for (value, inner, end) in self.eval(branch, source, at, st)? {
                        self.charge_witness(st)?;
                        let span = Span::new(at, end).expect("forward step");
                        // Union relays: its outputs are in bijection with its branches',
                        // which were charged where they were created.
                        self.relay_result(
                            &mut out,
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
            }

            Relational::Core(core) => match core {
                Core::Pure(value) => {
                    self.charge_witness(st)?;
                    let mut out = Vec::new();
                    self.push_result(
                        &mut out,
                        st,
                        (
                            value.clone(),
                            RelationalWitness::Core(CoreWitness::Pure { at }),
                            at,
                        ),
                    )?;
                    Ok(out)
                }

                Core::Prim(primitive) => {
                    let mut out = Vec::new();
                    // Primitives are deterministic: all nondeterminism in this algebra is
                    // explicit syntax, so a primitive contributes zero or one result.
                    if let Some(matched) = self
                        .env
                        .step(primitive, source, at)
                        .map_err(CombinatorEvalError::Environment)?
                    {
                        // The environment is caller-supplied, so its forward-step
                        // precondition is validated, never assumed.
                        let span = check_primitive_extent(at, matched.end, source.len())?;
                        self.charge_witness(st)?;
                        self.push_result(
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
                }

                Core::Map(function, inner) => {
                    let mut out = Vec::new();
                    for (value, witness, end) in self.eval(inner, source, at, st)? {
                        let value = self
                            .env
                            .apply_function(function, value)
                            .map_err(CombinatorEvalError::Environment)?;
                        self.charge_witness(st)?;
                        let span = Span::new(at, end).expect("forward step");
                        // Mapping creates no results: it rewrites the values it was handed.
                        self.relay_result(
                            &mut out,
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
                }

                Core::Ap(functions, arguments) => {
                    let mut out = Vec::new();
                    for (f, wf, mid) in self.eval(functions, source, at, st)? {
                        // One function value and one function witness are consumed once per
                        // argument result, so each is cloned per continuation — except on
                        // the last, which nothing follows and can therefore move them.
                        let argument_results = self.eval(arguments, source, mid, st)?;
                        let steps = argument_results.len();
                        let mut f = Some(f);
                        let mut wf = Some(wf);
                        for (step, (x, wx, end)) in argument_results.into_iter().enumerate() {
                            let last = step + 1 == steps;
                            let value = self
                                .env
                                .apply_value(clone_unless_last(&mut f, last), x)
                                .map_err(CombinatorEvalError::Environment)?;
                            self.charge_witness(st)?;
                            let span = Span::new(at, end).expect("forward step");
                            self.push_result(
                                &mut out,
                                st,
                                (
                                    value,
                                    RelationalWitness::Core(CoreWitness::Ap {
                                        span,
                                        function: Box::new(clone_unless_last(&mut wf, last)),
                                        argument: Box::new(wx),
                                        split: mid,
                                    }),
                                    end,
                                ),
                            )?;
                        }
                    }
                    Ok(out)
                }

                Core::Bind(head, continuation) => {
                    let mut out = Vec::new();
                    // Relational bind continues *every* head result. That is the semantic
                    // difference from the ordered fragment's bind, which commits to the
                    // head's single result and never retries it.
                    for (value, wh, mid) in self.eval(head, source, at, st)? {
                        if st.resolutions >= self.budget.max_continuation_resolutions {
                            return Self::exhausted(
                                CombinatorResource::ContinuationResolutions,
                                self.budget.max_continuation_resolutions,
                            );
                        }
                        st.resolutions += 1;
                        let next = self
                            .env
                            .relational_resolve(continuation, &value)
                            .map_err(CombinatorEvalError::Environment)?;
                        // The head witness is consumed once per continuation result, so it
                        // is cloned per result — except on the last, which can move it.
                        let continuation_results = self.eval(&next, source, mid, st)?;
                        let steps = continuation_results.len();
                        let mut wh = Some(wh);
                        for (step, (value, wc, end)) in continuation_results.into_iter().enumerate()
                        {
                            let last = step + 1 == steps;
                            self.charge_witness(st)?;
                            let span = Span::new(at, end).expect("forward step");
                            self.push_result(
                                &mut out,
                                st,
                                (
                                    value,
                                    RelationalWitness::Core(CoreWitness::Bind {
                                        span,
                                        head: Box::new(clone_unless_last(&mut wh, last)),
                                        continuation: Box::new(wc),
                                        split: mid,
                                    }),
                                    end,
                                ),
                            )?;
                        }
                    }
                    Ok(out)
                }

                Core::Rule(rule) => {
                    if st.active.contains(&(*rule, at)) {
                        return Err(CombinatorEvalError::LeftRecursion {
                            rule: *rule,
                            offset: at,
                        });
                    }
                    let body = self
                        .env
                        .relational_rule(*rule)
                        .ok_or(CombinatorEvalError::UndefinedRule { rule: *rule })?;
                    st.active.push((*rule, at));
                    let inner = self.eval(body, source, at, st);
                    st.active.pop();
                    let mut out = Vec::new();
                    for (value, witness, end) in inner? {
                        self.charge_witness(st)?;
                        let span = Span::new(at, end).expect("forward step");
                        // A rule reference relays its body's results unchanged.
                        self.relay_result(
                            &mut out,
                            (
                                value,
                                RelationalWitness::Core(CoreWitness::Rule {
                                    rule: *rule,
                                    span,
                                    inner: Box::new(witness),
                                }),
                                end,
                            ),
                        )?;
                    }
                    Ok(out)
                }
            },
        }
    }

    /// Enumerate interpretations from `start`, retaining prefixes or only whole-source
    /// matches according to `mode`.
    ///
    /// A `start` past the end of the source is not an error and not a diagnostic — this
    /// capability has neither channel. It simply enumerates whatever the program does
    /// there, which for an input-consuming program is nothing.
    pub fn eval_prefixes(
        &self,
        source: &[S::Atom],
        start: usize,
        mode: RelationalMode,
    ) -> Enumeration<S, E::Error> {
        if source.len() > self.budget.max_source_units {
            return Self::exhausted(
                CombinatorResource::SourceUnits,
                self.budget.max_source_units,
            );
        }
        let mut st = EvalState {
            work: 0,
            depth: 0,
            witness_nodes: 0,
            resolutions: 0,
            results: 0,
            active: Vec::new(),
        };
        let results = self.eval(self.program, source, start, &mut st)?;
        Ok(results
            .into_iter()
            .map(|(value, witness, end)| PrefixInterpretation {
                value,
                witness,
                consumed: Span::new(start, end).expect("forward step"),
                remainder: end,
            })
            .filter(|parsed| match mode {
                RelationalMode::Prefix => true,
                RelationalMode::Exact => parsed.is_complete(source.len()),
            })
            .collect())
    }
}

impl<S: Signature, E: RelationalEnv<S> + ?Sized> RelationalPrefixParser
    for RelationalEvaluator<'_, '_, S, E>
{
    type Source = [S::Atom];
    type Value = S::Value;
    type Witness = RelationalWitness<S>;
    type Error = CombinatorEvalError<E::Error>;

    fn parse_prefixes(
        &self,
        source: &[S::Atom],
        start: usize,
    ) -> Result<Vec<PrefixInterpretation<S::Value, RelationalWitness<S>>>, Self::Error> {
        self.eval_prefixes(source, start, RelationalMode::Prefix)
    }
}

impl<S: Signature, E: RelationalEnv<S> + ?Sized> RelationalParser
    for RelationalEvaluator<'_, '_, S, E>
{
    type Source = [S::Atom];
    type Value = S::Value;
    type Witness = RelationalWitness<S>;
    type Error = CombinatorEvalError<E::Error>;

    /// Whole-source enumeration: only results consuming the entire input are retained.
    ///
    /// Completeness is not implied. An empty result proves no negative fact.
    fn parses(
        &self,
        source: &[S::Atom],
    ) -> RelationalParseResult<S::Value, RelationalWitness<S>, Self::Error> {
        Ok(self
            .eval_prefixes(source, 0, RelationalMode::Exact)?
            .into_iter()
            .map(|parsed| (parsed.value, parsed.witness))
            .collect())
    }
}

impl<S: Signature, E: ?Sized> ParserSyntax for RelationalEvaluator<'_, '_, S, E> {
    type Syntax = Relational<S>;

    fn syntax(&self) -> &Relational<S> {
        self.program
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::env::fixtures::{Bytes, Extent, HostileEnv, Never, PureEnv};

    const BUDGET: CombinatorBudget = CombinatorBudget::new(64, 512, 32, 512, 64);

    fn evaluate_hostile(
        extent: Extent,
        source: &[u8],
        start: usize,
    ) -> Result<Vec<PrefixInterpretation<u8, RelationalWitness<Bytes>>>, CombinatorEvalError<Never>>
    {
        let program = Relational::Core(Core::Prim(0));
        let env = HostileEnv(extent);
        RelationalEvaluator::new(&program, &env, BUDGET, RelationalLimits::new(64, 64))
            .parse_prefixes(source, start)
    }

    #[test]
    fn a_backwards_primitive_step_is_an_evaluator_failure_not_a_panic() {
        assert_eq!(
            evaluate_hostile(Extent::Backwards, b"abc", 2),
            Err(CombinatorEvalError::PrimitiveExtent {
                at: 2,
                end: 1,
                source_len: 3
            })
        );
    }

    #[test]
    fn a_primitive_extent_past_the_end_of_the_source_is_an_evaluator_failure() {
        assert_eq!(
            evaluate_hostile(Extent::PastEnd, b"abc", 0),
            Err(CombinatorEvalError::PrimitiveExtent {
                at: 0,
                end: 103,
                source_len: 3
            })
        );
    }

    /// A subtree enumerating `n` zero-width results, built without any node that itself
    /// creates results beyond the `Pure`s at the leaves.
    fn fan(n: usize) -> Relational<Bytes> {
        Relational::Union((0..n).map(|_| Relational::Core(Core::Pure(0))).collect())
    }

    /// The global result bound counts results, not the nodes they pass through, so it must
    /// not depend on how a union is associated.
    ///
    /// The branch result counts are deliberately **unequal** (2, 2, 1). With equal counts
    /// the two associations charge the same total by arithmetic accident — the old
    /// pass-through charging gave `3a + 3b + 2c` against `2a + 3b + 3c`, which differ only
    /// by `a - c` — so an equal-count fixture is structurally incapable of falsifying this.
    #[test]
    fn the_global_bound_does_not_depend_on_association() {
        let left_nested = Relational::Union(vec![
            Relational::Union(vec![fan(2), fan(2)]),
            Relational::Core(Core::Pure(0)),
        ]);
        let right_nested = Relational::Union(vec![
            fan(2),
            Relational::Union(vec![fan(2), Relational::Core(Core::Pure(0))]),
        ]);

        let outcome = |program: &Relational<Bytes>, max_results: usize| {
            RelationalEvaluator::new(
                program,
                &PureEnv,
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
        // And the bound genuinely counts the five results, not the nodes they cross.
        assert_eq!(outcome(&left_nested, 5), Ok(5));
        assert_eq!(
            outcome(&left_nested, 4),
            Err(CombinatorEvalError::ResourceExhausted(
                CombinatorLimit::new(CombinatorResource::Results, 4)
            ))
        );
    }
}
