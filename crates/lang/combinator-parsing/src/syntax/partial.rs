//! Bounded evaluation of the ordered fragment as a **partial** prefix function.

use crate::budget::{
    CombinatorBudget, CombinatorDiagnostic, CombinatorDiagnosticKind, CombinatorEvalError,
    CombinatorLimit, CombinatorResource, check_primitive_extent,
};
use crate::syntax::{Core, CoreWitness, Ordered, OrderedEnv, OrderedWitness, Signature};
use covalence_parsing_api::{
    ExactParseResult, ParseAttempt, ParserSyntax, PartialExactParser, PartialPrefixParser,
    PrefixInterpretation, PrefixParseResult, Span,
};

/// Bounded evaluation of the ordered fragment as a partial prefix function.
///
/// `Ok(ParseAttempt::NoMatch(_))` is ordinary non-match; `Err` is evaluator failure.
///
/// `E: ?Sized` is on the struct **and every impl**, so the `&dyn OrderedEnv<S, Error = _>`
/// escape hatch actually works; without it any attempt to use one is E0277.
pub struct PartialEvaluator<'p, 'e, S: Signature, E: ?Sized> {
    program: &'p Ordered<S>,
    env: &'e E,
    budget: CombinatorBudget,
}

/// One evaluation step: `Ok(None)` is ordinary non-match, `Err` is evaluator failure.
type StepResult<S, E> =
    Result<Option<(<S as Signature>::Value, OrderedWitness<S>, usize)>, CombinatorEvalError<E>>;

/// Per-call mutable state. A0015's methods take `&self`, so this is a local, never a field
/// and never interior mutability.
struct EvalState {
    work: usize,
    depth: usize,
    witness_nodes: usize,
    resolutions: usize,
    farthest: usize,
    active: Vec<(usize, usize)>,
}

impl<'p, 'e, S: Signature, E: OrderedEnv<S> + ?Sized> PartialEvaluator<'p, 'e, S, E> {
    pub fn new(program: &'p Ordered<S>, env: &'e E, budget: CombinatorBudget) -> Self {
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

    /// `Ok(None)` is ordinary non-match; `Err` is evaluator failure.
    fn eval(
        &self,
        node: &Ordered<S>,
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
        node: &Ordered<S>,
        source: &[S::Atom],
        at: usize,
        st: &mut EvalState,
    ) -> StepResult<S, E::Error> {
        match node {
            Ordered::Fail => {
                st.farthest = st.farthest.max(at);
                Ok(None)
            }

            Ordered::OrderedChoice(alternatives) => {
                for (chosen, alternative) in alternatives.iter().enumerate() {
                    if let Some((value, inner, end)) = self.eval(alternative, source, at, st)? {
                        self.charge_witness(st)?;
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
                    // Committing: reaching here means alternative `chosen` produced no
                    // match at this offset. Later alternatives are explored only now.
                }
                st.farthest = st.farthest.max(at);
                Ok(None)
            }

            Ordered::Core(core) => match core {
                Core::Pure(value) => {
                    self.charge_witness(st)?;
                    Ok(Some((
                        value.clone(),
                        OrderedWitness::Core(CoreWitness::Pure { at }),
                        at,
                    )))
                }

                Core::Prim(primitive) => {
                    match self
                        .env
                        .step(primitive, source, at)
                        .map_err(CombinatorEvalError::Environment)?
                    {
                        None => {
                            st.farthest = st.farthest.max(at);
                            Ok(None)
                        }
                        Some(matched) => {
                            // The environment is caller-supplied, so its forward-step
                            // precondition is validated, never assumed.
                            let span = check_primitive_extent(at, matched.end, source.len())?;
                            self.charge_witness(st)?;
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
                }

                Core::Map(function, inner) => {
                    let Some((value, witness, end)) = self.eval(inner, source, at, st)? else {
                        return Ok(None);
                    };
                    let value = self
                        .env
                        .apply_function(function, value)
                        .map_err(CombinatorEvalError::Environment)?;
                    self.charge_witness(st)?;
                    let span = Span::new(at, end).expect("forward step");
                    Ok(Some((
                        value,
                        OrderedWitness::Core(CoreWitness::Map {
                            span,
                            inner: Box::new(witness),
                        }),
                        end,
                    )))
                }

                Core::Ap(functions, arguments) => {
                    let Some((f, wf, mid)) = self.eval(functions, source, at, st)? else {
                        return Ok(None);
                    };
                    let Some((x, wx, end)) = self.eval(arguments, source, mid, st)? else {
                        return Ok(None);
                    };
                    let value = self
                        .env
                        .apply_value(f, x)
                        .map_err(CombinatorEvalError::Environment)?;
                    self.charge_witness(st)?;
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
                }

                Core::Bind(head, continuation) => {
                    let Some((value, wh, mid)) = self.eval(head, source, at, st)? else {
                        return Ok(None);
                    };
                    if st.resolutions >= self.budget.max_continuation_resolutions {
                        return Self::exhausted(
                            CombinatorResource::ContinuationResolutions,
                            self.budget.max_continuation_resolutions,
                        );
                    }
                    st.resolutions += 1;
                    let next = self
                        .env
                        .ordered_resolve(continuation, &value)
                        .map_err(CombinatorEvalError::Environment)?;
                    // Ordered bind does NOT retry `head`. The head is a partial function
                    // with exactly one result; backtracking enters only through
                    // OrderedChoice. This is a semantic difference from the relational
                    // fragment's bind, not an implementation detail.
                    let Some((value, wc, end)) = self.eval(&next, source, mid, st)? else {
                        return Ok(None);
                    };
                    self.charge_witness(st)?;
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
                        .ordered_rule(*rule)
                        .ok_or(CombinatorEvalError::UndefinedRule { rule: *rule })?;
                    st.active.push((*rule, at));
                    let out = self.eval(body, source, at, st);
                    st.active.pop();
                    let Some((value, inner, end)) = out? else {
                        return Ok(None);
                    };
                    self.charge_witness(st)?;
                    let span = Span::new(at, end).expect("forward step");
                    Ok(Some((
                        value,
                        OrderedWitness::Core(CoreWitness::Rule {
                            rule: *rule,
                            span,
                            inner: Box::new(inner),
                        }),
                        end,
                    )))
                }
            },
        }
    }
}

impl<S: Signature, E: OrderedEnv<S> + ?Sized> PartialPrefixParser
    for PartialEvaluator<'_, '_, S, E>
{
    type Source = [S::Atom];
    type Value = S::Value;
    type Witness = OrderedWitness<S>;
    type Diagnostic = CombinatorDiagnostic;
    type Error = CombinatorEvalError<E::Error>;

    fn parse_prefix(
        &self,
        source: &[S::Atom],
        start: usize,
    ) -> PrefixParseResult<S::Value, OrderedWitness<S>, CombinatorDiagnostic, Self::Error> {
        if source.len() > self.budget.max_source_units {
            return Self::exhausted(
                CombinatorResource::SourceUnits,
                self.budget.max_source_units,
            );
        }
        if start > source.len() {
            return Ok(ParseAttempt::NoMatch(CombinatorDiagnostic {
                offset: start,
                kind: CombinatorDiagnosticKind::StartOutOfBounds,
            }));
        }
        let mut st = EvalState {
            work: 0,
            depth: 0,
            witness_nodes: 0,
            resolutions: 0,
            farthest: start,
            active: Vec::new(),
        };
        Ok(match self.eval(self.program, source, start, &mut st)? {
            None => ParseAttempt::NoMatch(CombinatorDiagnostic {
                offset: st.farthest,
                kind: CombinatorDiagnosticKind::NoMatch,
            }),
            Some((value, witness, end)) => ParseAttempt::Match(PrefixInterpretation {
                value,
                witness,
                consumed: Span::new(start, end).expect("forward step"),
                remainder: end,
            }),
        })
    }
}

impl<S: Signature, E: OrderedEnv<S> + ?Sized> PartialExactParser
    for PartialEvaluator<'_, '_, S, E>
{
    type Source = [S::Atom];
    type Value = S::Value;
    type Witness = OrderedWitness<S>;
    type Diagnostic = CombinatorDiagnostic;
    type Error = CombinatorEvalError<E::Error>;

    fn parse_exact(
        &self,
        source: &[S::Atom],
    ) -> ExactParseResult<S::Value, OrderedWitness<S>, CombinatorDiagnostic, Self::Error> {
        // Implemented directly rather than through `exact_from_prefix`, so the error type
        // stays `CombinatorEvalError<_>` instead of `PrefixAdapterError<_>`; the extent
        // invariant is guaranteed by construction above.
        Ok(match self.parse_prefix(source, 0)? {
            ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch(diagnostic),
            ParseAttempt::Match(parsed) if parsed.is_complete(source.len()) => {
                ParseAttempt::Match((parsed.value, parsed.witness))
            }
            ParseAttempt::Match(parsed) => ParseAttempt::NoMatch(CombinatorDiagnostic {
                offset: parsed.remainder,
                kind: CombinatorDiagnosticKind::TrailingInput,
            }),
        })
    }
}

impl<S: Signature, E: ?Sized> ParserSyntax for PartialEvaluator<'_, '_, S, E> {
    type Syntax = Ordered<S>;

    fn syntax(&self) -> &Ordered<S> {
        self.program
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::env::fixtures::{Bytes, Extent, HostileEnv};

    const BUDGET: CombinatorBudget = CombinatorBudget::new(64, 512, 32, 512, 64);

    fn evaluate(
        extent: Extent,
        source: &[u8],
        start: usize,
    ) -> PrefixParseResult<
        u8,
        OrderedWitness<Bytes>,
        CombinatorDiagnostic,
        CombinatorEvalError<crate::syntax::env::fixtures::Never>,
    > {
        run(Ordered::Core(Core::Prim(0)), extent, source, start)
    }

    fn run(
        program: Ordered<Bytes>,
        extent: Extent,
        source: &[u8],
        start: usize,
    ) -> PrefixParseResult<
        u8,
        OrderedWitness<Bytes>,
        CombinatorDiagnostic,
        CombinatorEvalError<crate::syntax::env::fixtures::Never>,
    > {
        let env = HostileEnv(extent);
        PartialEvaluator::new(&program, &env, BUDGET).parse_prefix(source, start)
    }

    /// A backwards primitive step used to abort the process through `Span::new(..).expect`.
    /// It is a caller-supplied environment, so it must be evaluator failure.
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

    /// An extent past the end of the source used to be silently accepted, yielding a match
    /// whose `consumed` and `remainder` escaped the source.
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

    /// Every composite node still builds its span with `Span::new(..).expect("forward step")`.
    /// Those are sound only because a leaf can no longer report a backwards extent: the leaf
    /// fails first, so the enclosing node never reaches its own construction. Pin that
    /// reachability argument rather than leaving it as commentary — a future leaf that skips
    /// `check_primitive_extent` would turn each of these back into a process abort.
    #[test]
    fn a_hostile_leaf_under_a_composite_node_fails_before_the_composite_builds_a_span() {
        let prim = || Ordered::Core(Core::Prim(0));
        let expected = Err(CombinatorEvalError::PrimitiveExtent {
            at: 1,
            end: 0,
            source_len: 3,
        });
        for program in [
            Ordered::Core(Core::Map((), Box::new(prim()))),
            Ordered::Core(Core::Ap(Box::new(prim()), Box::new(prim()))),
            Ordered::Core(Core::Bind(Box::new(prim()), ())),
        ] {
            assert_eq!(run(program, Extent::Backwards, b"abc", 1), expected);
        }
    }
}
