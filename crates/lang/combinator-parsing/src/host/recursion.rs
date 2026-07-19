//! Bounded recursion for the **partial** capability.
//!
//! This module is the partial-capability twin of the [`BoundedRelational`] seam in
//! [`relational`](crate::host::relational), and it exists for the same reason, stated there
//! for result limits and here for recursion depth.
//!
//! # Why a second trait, and why it is not a fourth capability
//!
//! `PartialPrefixParser::parse_prefix` takes `(&self, source, start)`. When a combinator
//! calls into an opaque sub-parser, the only channels that survive the call are `&self` and
//! `&Source`; `start` is semantic and the return type carries no state. So a recursion point
//! nested below an opaque sub-parser can learn the current depth in exactly three ways:
//!
//! 1. **Stored on the node** — an `Rc<Cell<usize>>` captured at construction. Rejected: this
//!    crate's bounds are supplied at the evaluation boundary and never stored per combinator
//!    node, because a bound living on a node makes the algebra's laws association-dependent
//!    (see [`budget`](crate::budget)).
//! 2. **Carried in the source** — a `Source` wrapper holding the counter. Rejected: it forks
//!    the source carrier, and every law, conformance harness, and
//!    [`alphabet`](crate::host::alphabet) alias in this crate is stated over `[u8]` and
//!    `[UnicodeScalar]`. A bounded expression would compose with none of them.
//! 3. **Threaded as an explicit parameter** — which needs a method the foreign trait does not
//!    have. That is [`BoundedPartial`], below.
//!
//! [`BoundedPartial`] is *not* a fourth capability and stands in no relation to
//! [`TotalPrefixParser`](crate::host::TotalPrefixParser) or
//! [`RelationalPrefixParser`](crate::host::RelationalPrefixParser). It is the same partial
//! capability with the evaluator's state made visible, exactly as [`BoundedRelational`] is
//! the relational capability with the evaluation's result limits made visible. The empty
//! graph between the three capabilities is untouched.
//!
//! [`BoundedRelational`]: crate::host::relational::BoundedRelational
//!
//! # Depth counts recursion points, not nodes
//!
//! [`RecursionCtx`] is charged in exactly one place: [`Recurse`], the operator that ties a
//! knot. Sequencing and choice thread the context without charging it.
//!
//! This is a deliberate difference from the syntax encoding, whose evaluator charges depth on
//! every node and whose depth bound is therefore sensitive to how an expression is
//! associated. Charging only at recursion points makes this bound
//! **association-independent**: reassociating a chain of [`OrderedChoice`] or [`Bind`] does
//! not change the depth any input reaches. What the bound measures is the number of nested
//! knot traversals, which is the quantity a left-recursive grammar actually diverges in.
//!
//! # What this does and does not bound
//!
//! It bounds recursion tied through [`Recurse`] within a bounded expression. It does **not**
//! bound a [`Leaf`]'s own internals: a foreign leaf that recurses inside itself is opaque
//! here, exactly as a foreign relational leaf cannot be bounded from the inside. Nor does it
//! bound [`partial::Lazy`](crate::host::partial::Lazy), which ties its knot through
//! `parse_prefix` and has no context to consult; that is the residue recorded on the marker
//! in [`partial`](crate::host::partial).

use covalence_parsing_api::{
    ParseAttempt, PartialPrefixParser, PrefixInterpretation, PrefixParseResult,
};

use crate::budget::{CombinatorLimit, CombinatorResource};
use crate::host::cursor::{CombinatorError, SourceExtent, check_step, join_steps};
use crate::host::witness::{ChoiceWitness, SeqWitness};

/// Per-evaluation recursion state.
///
/// `depth` is a **per-evaluation** counter, not a per-node one, which is what keeps the bound
/// independent of how the expression is associated.
#[derive(Clone, Copy, Debug)]
pub struct RecursionCtx {
    max_depth: usize,
    depth: usize,
}

impl RecursionCtx {
    /// Start a fresh evaluation admitting at most `max_depth` nested recursion points.
    pub const fn new(max_depth: usize) -> Self {
        Self {
            max_depth,
            depth: 0,
        }
    }

    /// The bound this evaluation is running under.
    pub const fn max_depth(&self) -> usize {
        self.max_depth
    }

    /// Recursion points currently entered.
    pub const fn depth(&self) -> usize {
        self.depth
    }

    /// Charge one recursion point about to be entered.
    ///
    /// Checked **before** descending, never after: recursing first and asserting a bound on
    /// the way back out is not a bound, because the stack is already gone.
    pub fn enter(&mut self) -> Result<(), CombinatorLimit> {
        if self.depth >= self.max_depth {
            return Err(CombinatorLimit::new(
                CombinatorResource::Depth,
                self.max_depth,
            ));
        }
        self.depth += 1;
        Ok(())
    }

    /// Release a recursion point entered by [`enter`](Self::enter).
    pub fn leave(&mut self) {
        self.depth -= 1;
    }
}

/// A partial combinator that can see the evaluation's recursion state.
///
/// This is the seam that makes the depth bound reach inner nodes without any node storing a
/// bound. It is deliberately *not* `PartialPrefixParser`: an unbounded entry point on a
/// recursion-capable expression would let a caller sidestep the bound entirely, which is the
/// whole failure this module exists to close. The only bridge is [`PartialEvaluation`].
pub trait BoundedPartial {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Diagnostic;
    type Error;

    fn parse_prefix_within(
        &self,
        source: &Self::Source,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<Self::Value, Self::Witness, Self::Diagnostic, Self::Error>;
}

/// The single bridge from a bounded combinator expression to the partial prefix trait.
///
/// The caller's bound lives here and nowhere else. Reassociating the expression inside does
/// not move a bound from one node to another.
///
/// ```
/// use covalence_combinator_parsing::host::recursion::{
///     Leaf, OrderedChoice, PartialEvaluation, Recurse, recurse,
/// };
/// # use covalence_parsing_api::PartialPrefixParser;
/// // A bounded expression becomes an ordinary partial prefix parser only through here.
/// fn is_partial<P: PartialPrefixParser>(_: &P) {}
/// ```
pub struct PartialEvaluation<P> {
    pub parser: P,
    pub max_depth: usize,
}

impl<P> PartialEvaluation<P> {
    /// Bound `parser` to at most `max_depth` nested recursion points per evaluation.
    pub const fn new(parser: P, max_depth: usize) -> Self {
        Self { parser, max_depth }
    }
}

impl<P: BoundedPartial> PartialPrefixParser for PartialEvaluation<P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = P::Error;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<P::Value, P::Witness, P::Diagnostic, P::Error> {
        // Fresh per call: the context is a local, never a field and never interior
        // mutability, exactly as in the syntax encoding's evaluators.
        let mut ctx = RecursionCtx::new(self.max_depth);
        self.parser.parse_prefix_within(source, start, &mut ctx)
    }
}

/// Lift an existing partial parser into a bounded expression as a leaf.
///
/// The leaf is treated as non-recursive: it is forwarded to unchanged and charged nothing.
/// A leaf that recurses inside itself is opaque from here and stays unbounded, which is the
/// same honest weaker guarantee `relational::Leaf` gives for result limits.
pub struct Leaf<P>(pub P);

impl<P: PartialPrefixParser> BoundedPartial for Leaf<P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = P::Error;

    fn parse_prefix_within(
        &self,
        source: &P::Source,
        start: usize,
        _ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<P::Value, P::Witness, P::Diagnostic, P::Error> {
        self.0.parse_prefix(source, start)
    }
}

/// Type erasure for bounded expressions.
///
/// Required for the same reason [`DynPartial`](crate::host::partial::DynPartial) is: a boxed
/// trait object of a foreign-or-local trait cannot itself implement the trait from a
/// downstream crate without a local forwarding newtype. Every recursion knot passes through
/// one of these.
pub struct DynBounded<'p, S: ?Sized, V, W, D, E>(
    pub Box<dyn BoundedPartial<Source = S, Value = V, Witness = W, Diagnostic = D, Error = E> + 'p>,
);

impl<'p, S: ?Sized, V, W, D, E> DynBounded<'p, S, V, W, D, E> {
    /// Erase a concrete bounded parser.
    pub fn new<P>(parser: P) -> Self
    where
        P: BoundedPartial<Source = S, Value = V, Witness = W, Diagnostic = D, Error = E> + 'p,
    {
        Self(Box::new(parser))
    }
}

impl<S: ?Sized, V, W, D, E> BoundedPartial for DynBounded<'_, S, V, W, D, E> {
    type Source = S;
    type Value = V;
    type Witness = W;
    type Diagnostic = D;
    type Error = E;

    fn parse_prefix_within(
        &self,
        source: &S,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<V, W, D, E> {
        self.0.parse_prefix_within(source, start, ctx)
    }
}

/// A recursion point: rebuilds its sub-expression on entry, under the depth bound.
///
/// This is the bounded counterpart of [`partial::Lazy`](crate::host::partial::Lazy), and the
/// **only** operator in this module that charges [`RecursionCtx`]. A grammar that ties its
/// knot here gets a [`CombinatorError::Limit`] naming
/// [`CombinatorResource::Depth`](crate::budget::CombinatorResource::Depth) where the
/// unbounded encoding overflows the native stack.
pub struct Recurse<F> {
    pub make: F,
}

/// Construct a [`Recurse`].
pub fn recurse<F>(make: F) -> Recurse<F> {
    Recurse { make }
}

impl<F, P, E> BoundedPartial for Recurse<F>
where
    F: Fn() -> P,
    P: BoundedPartial<Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = CombinatorError<E>;

    fn parse_prefix_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<P::Value, P::Witness, P::Diagnostic, CombinatorError<E>> {
        // Charge before descending, never after.
        ctx.enter().map_err(CombinatorError::Limit)?;
        // Not `?`: the release runs on the failure path too, so `enter`/`leave` stay balanced
        // locally rather than relying on who catches the error. No current combinator recovers
        // from an `Err`, and `PartialEvaluation` builds a fresh context per call, so a leak
        // here is not observable today — which is exactly why it is worth closing at the
        // source instead of resting on two facts that hold elsewhere.
        let out = (self.make)().parse_prefix_within(source, start, ctx);
        ctx.leave();
        out
    }
}

/// Value mapping. Threads the context; charges nothing.
pub struct Map<P, F> {
    pub parser: P,
    pub function: F,
}

impl<P, F, B> BoundedPartial for Map<P, F>
where
    P: BoundedPartial,
    F: Fn(P::Value) -> B,
{
    type Source = P::Source;
    type Value = B;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = P::Error;

    fn parse_prefix_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<B, P::Witness, P::Diagnostic, P::Error> {
        Ok(match self.parser.parse_prefix_within(source, start, ctx)? {
            ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch(diagnostic),
            ParseAttempt::Match(matched) => ParseAttempt::Match(PrefixInterpretation {
                value: (self.function)(matched.value),
                witness: matched.witness,
                consumed: matched.consumed,
                remainder: matched.remainder,
            }),
        })
    }
}

/// Bring a foreign leaf's error type to the expression's convention. Threads the context.
pub struct MapErr<P, F> {
    pub parser: P,
    pub function: F,
}

impl<P, F, E2> BoundedPartial for MapErr<P, F>
where
    P: BoundedPartial,
    F: Fn(P::Error) -> E2,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = E2;

    fn parse_prefix_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<P::Value, P::Witness, P::Diagnostic, E2> {
        self.parser
            .parse_prefix_within(source, start, ctx)
            .map_err(&self.function)
    }
}

/// Bring a foreign leaf's diagnostic to the expression's unified diagnostic.
pub struct MapDiagnostic<P, F> {
    pub parser: P,
    pub function: F,
}

impl<P, F, D2> BoundedPartial for MapDiagnostic<P, F>
where
    P: BoundedPartial,
    F: Fn(P::Diagnostic) -> D2,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = D2;
    type Error = P::Error;

    fn parse_prefix_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<P::Value, P::Witness, D2, P::Error> {
        Ok(match self.parser.parse_prefix_within(source, start, ctx)? {
            ParseAttempt::Match(matched) => ParseAttempt::Match(matched),
            ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch((self.function)(diagnostic)),
        })
    }
}

/// Value-independent sequencing with application. Mirrors
/// [`partial::Ap`](crate::host::partial::Ap), threading the context through both sides.
pub struct Ap<P, Q> {
    pub functions: P,
    pub arguments: Q,
}

impl<P, Q, B, E> BoundedPartial for Ap<P, Q>
where
    P: BoundedPartial<Error = CombinatorError<E>>,
    P::Source: SourceExtent,
    P::Value: FnOnce(Q::Value) -> B,
    Q: BoundedPartial<Source = P::Source, Diagnostic = P::Diagnostic, Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = B;
    type Witness = SeqWitness<P::Witness, Q::Witness>;
    type Diagnostic = P::Diagnostic;
    type Error = CombinatorError<E>;

    fn parse_prefix_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<B, Self::Witness, P::Diagnostic, CombinatorError<E>> {
        let source_len = source.extent();
        let function = match self.functions.parse_prefix_within(source, start, ctx)? {
            ParseAttempt::NoMatch(diagnostic) => return Ok(ParseAttempt::NoMatch(diagnostic)),
            ParseAttempt::Match(matched) => {
                check_step(start, source_len, matched).map_err(CombinatorError::Cursor)?
            }
        };
        let split = function.remainder;
        let argument = match self.arguments.parse_prefix_within(source, split, ctx)? {
            ParseAttempt::NoMatch(diagnostic) => return Ok(ParseAttempt::NoMatch(diagnostic)),
            ParseAttempt::Match(matched) => {
                check_step(split, source_len, matched).map_err(CombinatorError::Cursor)?
            }
        };
        let consumed = join_steps(start, source_len, function.consumed, &argument)?;
        Ok(ParseAttempt::Match(PrefixInterpretation {
            value: (function.value)(argument.value),
            witness: SeqWitness {
                first: function.witness,
                second: argument.witness,
                split,
            },
            consumed,
            remainder: argument.remainder,
        }))
    }
}

/// Value-dependent sequencing. Mirrors [`partial::Bind`](crate::host::partial::Bind),
/// including its commitment not to retry its head when the continuation declines.
pub struct Bind<P, F> {
    pub parser: P,
    pub continuation: F,
}

impl<P, F, Q, E> BoundedPartial for Bind<P, F>
where
    P: BoundedPartial<Error = CombinatorError<E>>,
    P::Source: SourceExtent,
    F: Fn(P::Value) -> Q,
    Q: BoundedPartial<Source = P::Source, Diagnostic = P::Diagnostic, Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = Q::Value;
    type Witness = SeqWitness<P::Witness, Q::Witness>;
    type Diagnostic = P::Diagnostic;
    type Error = CombinatorError<E>;

    fn parse_prefix_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<Q::Value, Self::Witness, P::Diagnostic, CombinatorError<E>> {
        let source_len = source.extent();
        let head = match self.parser.parse_prefix_within(source, start, ctx)? {
            ParseAttempt::NoMatch(diagnostic) => return Ok(ParseAttempt::NoMatch(diagnostic)),
            ParseAttempt::Match(matched) => {
                check_step(start, source_len, matched).map_err(CombinatorError::Cursor)?
            }
        };
        let split = head.remainder;
        let next = (self.continuation)(head.value);
        // The head is not retried: a partial parser has exactly one result at this offset.
        let tail = match next.parse_prefix_within(source, split, ctx)? {
            ParseAttempt::NoMatch(diagnostic) => return Ok(ParseAttempt::NoMatch(diagnostic)),
            ParseAttempt::Match(matched) => {
                check_step(split, source_len, matched).map_err(CombinatorError::Cursor)?
            }
        };
        let consumed = join_steps(start, source_len, head.consumed, &tail)?;
        Ok(ParseAttempt::Match(PrefixInterpretation {
            value: tail.value,
            witness: SeqWitness {
                first: head.witness,
                second: tail.witness,
                split,
            },
            consumed,
            remainder: tail.remainder,
        }))
    }
}

/// Ordered, committing choice. Mirrors
/// [`partial::OrderedChoice`](crate::host::partial::OrderedChoice), including its commitment
/// not to evaluate the second alternative once the first matched.
///
/// ```compile_fail,E0277
/// use covalence_combinator_parsing::host::RelationalPrefixParser;
/// use covalence_combinator_parsing::host::recursion::OrderedChoice;
/// fn assert_relational<P: RelationalPrefixParser>(_: P) {}
/// // Still a partial-capability operator: bounding recursion grants no relational reading.
/// fn use_it<P, Q, M>(choice: OrderedChoice<P, Q, M>) { assert_relational(choice); }
/// ```
///
/// ```compile_fail,E0277
/// use covalence_combinator_parsing::host::recursion::{BoundedPartial, Recurse};
/// use covalence_parsing_api::PartialPrefixParser;
/// fn assert_partial<P: PartialPrefixParser>(_: P) {}
/// // A bounded expression is not itself a partial prefix parser: the only bridge that
/// // constructs the recursion context is `PartialEvaluation`.
/// fn use_it<F>(node: Recurse<F>) where Recurse<F>: BoundedPartial { assert_partial(node); }
/// ```
pub struct OrderedChoice<P, Q, M> {
    pub first: P,
    pub second: Q,
    pub merge: M,
}

impl<P, Q, M, E> BoundedPartial for OrderedChoice<P, Q, M>
where
    P: BoundedPartial<Error = CombinatorError<E>>,
    Q: BoundedPartial<
            Source = P::Source,
            Value = P::Value,
            Diagnostic = P::Diagnostic,
            Error = CombinatorError<E>,
        >,
    M: Fn(P::Diagnostic, P::Diagnostic) -> P::Diagnostic,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = ChoiceWitness<P::Witness, Q::Witness, P::Diagnostic>;
    type Diagnostic = P::Diagnostic;
    type Error = CombinatorError<E>;

    fn parse_prefix_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RecursionCtx,
    ) -> PrefixParseResult<P::Value, Self::Witness, P::Diagnostic, CombinatorError<E>> {
        // The early return is the operational content of "committing": on a first match the
        // second alternative is never evaluated at all.
        let first_diagnostic = match self.first.parse_prefix_within(source, start, ctx)? {
            ParseAttempt::Match(matched) => {
                return Ok(ParseAttempt::Match(PrefixInterpretation {
                    value: matched.value,
                    witness: ChoiceWitness::First(matched.witness),
                    consumed: matched.consumed,
                    remainder: matched.remainder,
                }));
            }
            ParseAttempt::NoMatch(diagnostic) => diagnostic,
        };
        Ok(match self.second.parse_prefix_within(source, start, ctx)? {
            ParseAttempt::Match(matched) => ParseAttempt::Match(PrefixInterpretation {
                value: matched.value,
                witness: ChoiceWitness::Second {
                    first_diagnostic,
                    witness: matched.witness,
                },
                consumed: matched.consumed,
                remainder: matched.remainder,
            }),
            ParseAttempt::NoMatch(second_diagnostic) => {
                ParseAttempt::NoMatch((self.merge)(first_diagnostic, second_diagnostic))
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_parsing_api::Span;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Missing(u8);

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct ForeignError;

    type Err0 = CombinatorError<ForeignError>;

    /// A leaf matching one specific byte.
    struct Byte(u8);

    impl PartialPrefixParser for Byte {
        type Source = [u8];
        type Value = u8;
        type Witness = ();
        type Diagnostic = Missing;
        type Error = Err0;

        fn parse_prefix(
            &self,
            source: &[u8],
            start: usize,
        ) -> PrefixParseResult<u8, (), Missing, Err0> {
            match source.get(start) {
                Some(&byte) if byte == self.0 => Ok(ParseAttempt::Match(PrefixInterpretation {
                    value: byte,
                    witness: (),
                    consumed: Span {
                        start,
                        end: start + 1,
                    },
                    remainder: start + 1,
                })),
                _ => Ok(ParseAttempt::NoMatch(Missing(self.0))),
            }
        }
    }

    fn last(_left: Missing, right: Missing) -> Missing {
        right
    }

    type Erased = DynBounded<'static, [u8], u8, (), Missing, Err0>;

    /// Erases any witness to `()` so a recursion knot can close on one type.
    struct ForgetWitness<P>(P);

    impl<P: BoundedPartial> BoundedPartial for ForgetWitness<P> {
        type Source = P::Source;
        type Value = P::Value;
        type Witness = ();
        type Diagnostic = P::Diagnostic;
        type Error = P::Error;

        fn parse_prefix_within(
            &self,
            source: &P::Source,
            start: usize,
            ctx: &mut RecursionCtx,
        ) -> PrefixParseResult<P::Value, (), P::Diagnostic, P::Error> {
            Ok(match self.0.parse_prefix_within(source, start, ctx)? {
                ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch(diagnostic),
                ParseAttempt::Match(matched) => ParseAttempt::Match(PrefixInterpretation {
                    value: matched.value,
                    witness: (),
                    consumed: matched.consumed,
                    remainder: matched.remainder,
                }),
            })
        }
    }

    /// `expr := expr | 'b'` — directly left recursive. The first alternative re-enters at the
    /// same offset having consumed nothing, so nothing but the depth bound ever stops it.
    fn left_recursive() -> Erased {
        DynBounded::new(ForgetWitness(OrderedChoice {
            first: recurse(left_recursive),
            second: Leaf(Byte(b'b')),
            merge: last as fn(Missing, Missing) -> Missing,
        }))
    }

    /// The headline test: a left-recursive bounded grammar reports a bounded error where the
    /// unbounded encoding overflows the native stack.
    ///
    /// Disable the check — `RecursionCtx::enter` returning `Ok(())` unconditionally, or
    /// `Recurse` not calling it — and this must go red by *aborting the test process with a
    /// stack overflow*, not by failing an assertion.
    #[test]
    fn left_recursion_reports_a_depth_bound_instead_of_overflowing() {
        let parser = PartialEvaluation::new(left_recursive(), 64);
        let outcome = parser.parse_prefix(b"b", 0);
        assert_eq!(
            outcome,
            Err(CombinatorError::Limit(CombinatorLimit::new(
                CombinatorResource::Depth,
                64
            )))
        );
    }

    /// The bound is a property of the evaluation, not of the grammar value: the same
    /// expression under a different bound reports that bound.
    #[test]
    fn the_reported_limit_is_the_one_the_caller_supplied() {
        let parser = PartialEvaluation::new(left_recursive(), 7);
        assert_eq!(
            parser.parse_prefix(b"b", 0),
            Err(CombinatorError::Limit(CombinatorLimit::new(
                CombinatorResource::Depth,
                7
            )))
        );
    }

    /// `digits := 'a' digits | 'b'` — right recursive, so it consumes before re-entering and
    /// terminates on its own. Recursion that makes progress must not be penalised.
    fn right_recursive() -> Erased {
        DynBounded::new(ForgetWitness(OrderedChoice {
            first: ForgetWitness(Bind {
                parser: Leaf(Byte(b'a')),
                continuation: |_| recurse(right_recursive),
            }),
            second: Leaf(Byte(b'b')),
            merge: last as fn(Missing, Missing) -> Missing,
        }))
    }

    #[test]
    fn productive_recursion_is_not_penalised() {
        let parser = PartialEvaluation::new(right_recursive(), 64);
        let ParseAttempt::Match(matched) = parser
            .parse_prefix(b"aaaab", 0)
            .expect("productive recursion stays inside the bound")
        else {
            panic!("expected a match");
        };
        assert_eq!(matched.remainder, 5);
    }

    /// `max_depth` counts *nested* recursion points, so it trips on nesting and not on the
    /// number of times a knot is traversed overall.
    #[test]
    fn the_bound_counts_nested_recursion_points() {
        let parser = PartialEvaluation::new(right_recursive(), 4);
        // Three nested `recurse` traversals plus the final one that matches `'b'`.
        let outcome = parser.parse_prefix(b"aaab", 0);
        assert!(outcome.is_ok(), "expected a match, got {outcome:?}");
        // One more level of nesting than the bound admits.
        let parser = PartialEvaluation::new(right_recursive(), 2);
        assert_eq!(
            parser.parse_prefix(b"aaab", 0),
            Err(CombinatorError::Limit(CombinatorLimit::new(
                CombinatorResource::Depth,
                2
            )))
        );
    }

    /// Depth is *released* when a recursion point returns, so two knots traversed in sequence
    /// each get the full bound rather than sharing it.
    ///
    /// Each half of `"aabaab"` nests two recursion points, four across the whole input. Under
    /// `max_depth = 2` this matches only because the first half's depth is given back before
    /// the second half is entered. Delete the `ctx.leave()` in `Recurse` and this goes red
    /// with a `Depth` limit — it is the test that makes that line load-bearing.
    #[test]
    fn depth_is_released_when_a_recursion_point_returns() {
        let parser = PartialEvaluation::new(
            Bind {
                parser: right_recursive(),
                continuation: |_| right_recursive(),
            },
            2,
        );
        let ParseAttempt::Match(matched) = parser
            .parse_prefix(b"aabaab", 0)
            .expect("sequential knots each get the full bound")
        else {
            panic!("expected a match");
        };
        assert_eq!(matched.remainder, 6);
    }

    /// Charging only at recursion points is what makes the bound association-independent: the
    /// two associations of a choice chain reach the same depth on the same input.
    #[test]
    fn reassociating_choice_does_not_move_the_bound() {
        let left = PartialEvaluation::new(
            ForgetWitness(OrderedChoice {
                first: ForgetWitness(OrderedChoice {
                    first: Leaf(Byte(b'x')),
                    second: Leaf(Byte(b'y')),
                    merge: last as fn(Missing, Missing) -> Missing,
                }),
                second: recurse(left_recursive),
                merge: last as fn(Missing, Missing) -> Missing,
            }),
            3,
        );
        let right = PartialEvaluation::new(
            ForgetWitness(OrderedChoice {
                first: Leaf(Byte(b'x')),
                second: ForgetWitness(OrderedChoice {
                    first: Leaf(Byte(b'y')),
                    second: recurse(left_recursive),
                    merge: last as fn(Missing, Missing) -> Missing,
                }),
                merge: last as fn(Missing, Missing) -> Missing,
            }),
            3,
        );
        let expected = Err(CombinatorError::Limit(CombinatorLimit::new(
            CombinatorResource::Depth,
            3,
        )));
        assert_eq!(left.parse_prefix(b"b", 0), expected);
        assert_eq!(right.parse_prefix(b"b", 0), expected);
    }

    /// Ordered choice still commits: the second alternative is not evaluated after a match,
    /// and threading a recursion context did not change that.
    #[test]
    fn bounded_ordered_choice_still_does_not_evaluate_its_second_arm() {
        struct Poisoned;

        impl BoundedPartial for Poisoned {
            type Source = [u8];
            type Value = u8;
            type Witness = ();
            type Diagnostic = Missing;
            type Error = Err0;

            fn parse_prefix_within(
                &self,
                _source: &[u8],
                _start: usize,
                _ctx: &mut RecursionCtx,
            ) -> PrefixParseResult<u8, (), Missing, Err0> {
                Err(CombinatorError::Parser(ForeignError))
            }
        }

        let parser = PartialEvaluation::new(
            OrderedChoice {
                first: Leaf(Byte(b'a')),
                second: Poisoned,
                merge: last as fn(Missing, Missing) -> Missing,
            },
            8,
        );
        let ParseAttempt::Match(matched) = parser
            .parse_prefix(b"abc", 0)
            .expect("the second arm must not be consulted")
        else {
            panic!("expected a match from the first alternative");
        };
        assert!(matches!(matched.witness, ChoiceWitness::First(())));
    }
}
