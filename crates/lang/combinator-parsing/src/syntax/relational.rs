//! Bounded evaluation of the relational fragment as an **enumeration**.

use crate::budget::{
    CombinatorBudget, CombinatorEvalError, CombinatorLimit, CombinatorResource, RelationalLimits,
};
use crate::host::RelationalPrefixParser;
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

// PERF(cov:lang.combinator-parsing.relational-sharing, major): No derivation sharing. A
// packed forest as in cfg-parsing needs value-level sharing the untyped universe does not
// provide; max_results and max_work are the only defence and truncation is always reported
// as `ResourceExhausted` rather than silently dropping results.

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

    /// Charge and append one result.
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
                        self.push_result(
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
                        self.charge_witness(st)?;
                        let span =
                            Span::new(at, matched.end).expect("primitive must be a forward step");
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
                        self.push_result(
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
                }

                Core::Ap(functions, arguments) => {
                    let mut out = Vec::new();
                    for (f, wf, mid) in self.eval(functions, source, at, st)? {
                        // One function value is consumed once per argument result, so it
                        // is cloned per continuation rather than moved.
                        for (x, wx, end) in self.eval(arguments, source, mid, st)? {
                            let value = self
                                .env
                                .apply_value(f.clone(), x)
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
                        for (value, wc, end) in self.eval(&next, source, mid, st)? {
                            self.charge_witness(st)?;
                            let span = Span::new(at, end).expect("forward step");
                            self.push_result(
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
                        self.push_result(
                            &mut out,
                            st,
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
