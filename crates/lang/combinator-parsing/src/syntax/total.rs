//! Bounded evaluation of the deterministic fragment as a **total** prefix function.

use crate::budget::{
    CombinatorBudget, CombinatorEvalError, CombinatorLimit, CombinatorResource,
    check_primitive_extent,
};
use crate::host::TotalPrefixParser;
use crate::syntax::{Core, CoreWitness, Deterministic, DeterministicWitness, Signature, TotalEnv};
use covalence_parsing_api::{ParserSyntax, PrefixInterpretation, Span};

/// Bounded evaluation of the deterministic fragment as a total prefix function.
///
/// There is **no `Option` anywhere** in this evaluator: [`TotalEnv::total_step`] cannot
/// report non-match, so neither can this. That is what makes totality a signature property
/// rather than an honour-system marker.
///
/// Totality is still modulo resources: budget exhaustion, an undefined rule, left recursion
/// through a rule reference, and environment failure are all `Err`. That is the same posture
/// as A0015's own `TotalParser`, and it is why no host observation of this evaluator proves
/// genuine totality.
///
/// **Caller precondition: `start <= source.len()`.** See the marker below.
pub struct TotalEvaluator<'p, 'e, S: Signature, E: ?Sized> {
    program: &'p Deterministic<S>,
    env: &'e E,
    budget: CombinatorBudget,
}

// TODO(cov:lang.combinator-parsing.total-start-precondition, minor): `TotalPrefixParser`
// has no non-match channel, so `start > source.len()` is a documented caller precondition
// rather than a reported outcome. Revisit if a total prefix parser ever needs to saturate.

/// One evaluation step. There is no `Option`: the total environment cannot decline.
type StepResult<S, E> =
    Result<(<S as Signature>::Value, DeterministicWitness<S>, usize), CombinatorEvalError<E>>;

/// Per-call mutable state. A0015's methods take `&self`, so this is a local, never a field
/// and never interior mutability.
struct EvalState {
    work: usize,
    depth: usize,
    witness_nodes: usize,
    resolutions: usize,
    active: Vec<(usize, usize)>,
}

impl<'p, 'e, S: Signature, E: TotalEnv<S> + ?Sized> TotalEvaluator<'p, 'e, S, E> {
    pub fn new(program: &'p Deterministic<S>, env: &'e E, budget: CombinatorBudget) -> Self {
        Self {
            program,
            env,
            budget,
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

    fn eval(
        &self,
        node: &Deterministic<S>,
        source: &[S::Atom],
        at: usize,
        st: &mut EvalState,
    ) -> StepResult<S, E::Error> {
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
        node: &Deterministic<S>,
        source: &[S::Atom],
        at: usize,
        st: &mut EvalState,
    ) -> StepResult<S, E::Error> {
        match &node.0 {
            Core::Pure(value) => {
                self.charge_witness(st)?;
                Ok((
                    value.clone(),
                    DeterministicWitness(CoreWitness::Pure { at }),
                    at,
                ))
            }

            Core::Prim(primitive) => {
                let matched = self
                    .env
                    .total_step(primitive, source, at)
                    .map_err(CombinatorEvalError::Environment)?;
                // The environment is caller-supplied, so its forward-step precondition is
                // validated, never assumed. Totality is modulo resources and well-formed
                // environments; it was never a licence to abort the process.
                let span = check_primitive_extent(at, matched.end, source.len())?;
                self.charge_witness(st)?;
                Ok((
                    matched.value,
                    DeterministicWitness(CoreWitness::Prim {
                        span,
                        witness: matched.witness,
                    }),
                    matched.end,
                ))
            }

            Core::Map(function, inner) => {
                let (value, witness, end) = self.eval(inner, source, at, st)?;
                let value = self
                    .env
                    .apply_function(function, value)
                    .map_err(CombinatorEvalError::Environment)?;
                self.charge_witness(st)?;
                let span = Span::new(at, end).expect("forward step");
                Ok((
                    value,
                    DeterministicWitness(CoreWitness::Map {
                        span,
                        inner: Box::new(witness),
                    }),
                    end,
                ))
            }

            Core::Ap(functions, arguments) => {
                let (f, wf, mid) = self.eval(functions, source, at, st)?;
                let (x, wx, end) = self.eval(arguments, source, mid, st)?;
                let value = self
                    .env
                    .apply_value(f, x)
                    .map_err(CombinatorEvalError::Environment)?;
                self.charge_witness(st)?;
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
            }

            Core::Bind(head, continuation) => {
                let (value, wh, mid) = self.eval(head, source, at, st)?;
                if st.resolutions >= self.budget.max_continuation_resolutions {
                    return Self::exhausted(
                        CombinatorResource::ContinuationResolutions,
                        self.budget.max_continuation_resolutions,
                    );
                }
                st.resolutions += 1;
                let next = self
                    .env
                    .total_resolve(continuation, &value)
                    .map_err(CombinatorEvalError::Environment)?;
                let (value, wc, end) = self.eval(&next, source, mid, st)?;
                self.charge_witness(st)?;
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
                    .total_rule(*rule)
                    .ok_or(CombinatorEvalError::UndefinedRule { rule: *rule })?;
                st.active.push((*rule, at));
                let out = self.eval(body, source, at, st);
                st.active.pop();
                let (value, inner, end) = out?;
                self.charge_witness(st)?;
                let span = Span::new(at, end).expect("forward step");
                Ok((
                    value,
                    DeterministicWitness(CoreWitness::Rule {
                        rule: *rule,
                        span,
                        inner: Box::new(inner),
                    }),
                    end,
                ))
            }
        }
    }
}

impl<S: Signature, E: TotalEnv<S> + ?Sized> TotalPrefixParser for TotalEvaluator<'_, '_, S, E> {
    type Source = [S::Atom];
    type Value = S::Value;
    type Witness = DeterministicWitness<S>;
    type Error = CombinatorEvalError<E::Error>;

    fn parse_prefix_total(
        &self,
        source: &[S::Atom],
        start: usize,
    ) -> Result<PrefixInterpretation<S::Value, DeterministicWitness<S>>, Self::Error> {
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
            active: Vec::new(),
        };
        let (value, witness, end) = self.eval(self.program, source, start, &mut st)?;
        Ok(PrefixInterpretation {
            value,
            witness,
            consumed: Span::new(start, end).expect("forward step"),
            remainder: end,
        })
    }
}

impl<S: Signature, E: ?Sized> ParserSyntax for TotalEvaluator<'_, '_, S, E> {
    type Syntax = Deterministic<S>;

    fn syntax(&self) -> &Deterministic<S> {
        self.program
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::env::fixtures::{Bytes, Extent, HostileEnv, Never};

    const BUDGET: CombinatorBudget = CombinatorBudget::new(64, 512, 32, 512, 64);

    fn evaluate(
        extent: Extent,
        source: &[u8],
        start: usize,
    ) -> Result<PrefixInterpretation<u8, DeterministicWitness<Bytes>>, CombinatorEvalError<Never>>
    {
        let program = Deterministic(Core::Prim(0));
        let env = HostileEnv(extent);
        TotalEvaluator::new(&program, &env, BUDGET).parse_prefix_total(source, start)
    }

    /// Totality is modulo resources and well-formed environments, not modulo panics: a
    /// backwards `total_step` used to abort the process through `Span::new(..).expect`.
    #[test]
    fn a_backwards_primitive_step_is_an_evaluator_failure_not_a_panic() {
        assert_eq!(
            evaluate(Extent::Backwards, b"abc", 2),
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
            evaluate(Extent::PastEnd, b"abc", 0),
            Err(CombinatorEvalError::PrimitiveExtent {
                at: 0,
                end: 103,
                source_len: 3
            })
        );
    }
}
