//! Executable host-data realization of the common Lisp core.
//!
//! This backend is deliberately proof-free. It is useful for frontend tests,
//! trace discovery, differential testing, and as an executable specification
//! for proof-producing backends.

use core::convert::Infallible;
use core::fmt::{Debug, Display, Formatter};
use core::marker::PhantomData;
use std::sync::{Arc, OnceLock};

use crate::relation::{DeterministicStep, StepRelation, TerminalValue};
use crate::runtime::{
    ClosureRecord, LispClosure, LispEnvironment, LispMachineValue, LispRecursiveEnvironment,
    LispRuntime, LispValue, PrimitiveSemantics, RecursiveAllocation, RuntimeBinding,
    RuntimeDatumError, RuntimeValueLayer, RuntimeValueView, inject_datum,
};
use crate::syntax::{
    Binding, CoreExpr, CoreExprLayer, EvaluationOrder, LispExpression, LispSyntax, Parameter,
    Strategy,
};

/// The direct inductive S-expression reference backend.
///
/// This alias keeps the Lisp syntax vocabulary concise while ensuring quoted
/// data is literally the shared A0005 representation rather than a duplicate
/// host-only enum.
pub use covalence_sexpr_api::FreeSExpr as Datum;

/// Persistent lexical environment, represented directly for the host backend.
#[derive(Clone, Debug)]
pub struct HostEnvironment<S, V> {
    bindings: Arc<Vec<(S, HostBindingCell<V>)>>,
}

/// One persistent environment cell.
///
/// Ordinary bindings are initialized before insertion. Recursive binding
/// groups allocate all cells first, build closures over the resulting
/// environment, and initialize each cell exactly once.
#[derive(Clone, Debug)]
pub struct HostBindingCell<V> {
    value: Arc<OnceLock<V>>,
}

/// Single-use initialization capability for one reserved recursive binding.
#[derive(Debug)]
pub struct HostRecursiveCell<V>(HostBindingCell<V>);

impl<V> HostBindingCell<V> {
    fn uninitialized() -> Self {
        Self {
            value: Arc::new(OnceLock::new()),
        }
    }

    fn initialized(value: V) -> Self {
        let cell = Self::uninitialized();
        let _ = cell.value.set(value);
        cell
    }

    pub fn get(&self) -> Option<&V> {
        self.value.get()
    }

    fn initialize(&self, value: V) -> Result<(), V> {
        self.value.set(value)
    }
}

impl<V> PartialEq for HostBindingCell<V> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.value, &other.value)
    }
}

impl<V> Eq for HostBindingCell<V> {}

impl<S: PartialEq, V> PartialEq for HostEnvironment<S, V> {
    fn eq(&self, other: &Self) -> bool {
        self.bindings == other.bindings
    }
}

impl<S: Eq, V> Eq for HostEnvironment<S, V> {}

impl<S, V> Default for HostEnvironment<S, V> {
    fn default() -> Self {
        Self {
            bindings: Arc::new(Vec::new()),
        }
    }
}

impl<S: Clone + PartialEq, V: Clone> HostEnvironment<S, V> {
    pub fn lookup(&self, symbol: &S) -> Option<V> {
        self.bindings
            .iter()
            .rev()
            .find(|(name, _)| name == symbol)
            .and_then(|(_, cell)| cell.get().cloned())
    }

    pub fn extend(&self, bindings: impl IntoIterator<Item = (S, V)>) -> Self {
        let mut extended = self.bindings.as_ref().clone();
        extended.extend(
            bindings
                .into_iter()
                .map(|(name, value)| (name, HostBindingCell::initialized(value))),
        );
        Self {
            bindings: Arc::new(extended),
        }
    }

    fn extend_cells(&self, bindings: Vec<(S, HostBindingCell<V>)>) -> Self {
        let mut extended = self.bindings.as_ref().clone();
        extended.extend(bindings);
        Self {
            bindings: Arc::new(extended),
        }
    }

    pub fn bindings(&self) -> impl DoubleEndedIterator<Item = (&S, &V)> {
        self.bindings
            .iter()
            .filter_map(|(name, cell)| cell.get().map(|value| (name, value)))
    }
}

/// Host-machine vocabulary metadata.
///
/// The operation meanings themselves live in backend-parametric
/// [`PrimitiveSemantics`]; this trait only selects the types used by the
/// direct Rust CEK realization.
pub trait CorePrimitive:
    PrimitiveSemantics<HostValues<Self::Symbol, Self::Atom, Self::Primitive>>
{
    type Symbol: Clone + PartialEq + Debug;
    type Atom: Clone + PartialEq + Debug;
    type Primitive: Clone + PartialEq + Debug;
}

type RuntimePrimitiveError<R, P> = <P as PrimitiveSemantics<<R as LispRuntime>::Values>>::Error;

type Expr<S, A, P> = CoreExpr<S, Datum<A>, P>;
type Value<S, A, P> = HostValue<S, A, P>;
type Environment<S, A, P> = HostEnvironment<S, Value<S, A, P>>;

/// A lexical closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostClosure<S, A, P> {
    pub name: Option<S>,
    pub parameters: Vec<Parameter<S>>,
    pub rest: Option<Parameter<S>>,
    pub body: Expr<S, A, P>,
    pub environment: Environment<S, A, P>,
}

/// Closure-resource capability backed by [`HostClosure`].
#[derive(Clone, Copy, Debug)]
pub struct HostClosures<S, A, P>(PhantomData<(S, A, P)>);

impl<S, A, P> Default for HostClosures<S, A, P> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<S: Clone, A: Clone, P: Clone> LispClosure for HostClosures<S, A, P> {
    type Symbol = S;
    type Expr = Expr<S, A, P>;
    type Environment = Environment<S, A, P>;
    type Closure = Arc<HostClosure<S, A, P>>;
    type Error = Infallible;

    fn close(
        &self,
        record: ClosureRecord<Self::Symbol, Self::Expr, Self::Environment>,
    ) -> Result<Self::Closure, Self::Error> {
        Ok(Arc::new(HostClosure {
            name: record.name,
            parameters: record.parameters.into_iter().map(Parameter::new).collect(),
            rest: record.rest.map(Parameter::new),
            body: record.body,
            environment: record.environment,
        }))
    }

    fn open(
        &self,
        closure: &Self::Closure,
    ) -> Result<ClosureRecord<Self::Symbol, Self::Expr, Self::Environment>, Self::Error> {
        Ok(ClosureRecord {
            name: closure.name.clone(),
            parameters: closure
                .parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect(),
            rest: closure
                .rest
                .as_ref()
                .map(|parameter| parameter.name.clone()),
            body: closure.body.clone(),
            environment: closure.environment.clone(),
        })
    }
}

/// Direct Rust realization of [`crate::runtime_value_fixpoint`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostValue<S, A, P> {
    Atom(A),
    Nil,
    Cons(Box<Self>, Box<Self>),
    Closure(Arc<HostClosure<S, A, P>>),
    Primitive(P),
    ApplyListProcedure,
}

impl<S, A, P> HostValue<S, A, P> {
    pub fn cons(head: Self, tail: Self) -> Self {
        Self::Cons(Box::new(head), Box::new(tail))
    }

    pub fn list(values: impl IntoIterator<Item = Self>) -> Self {
        let values: Vec<_> = values.into_iter().collect();
        values
            .into_iter()
            .rev()
            .fold(Self::Nil, |tail, head| Self::cons(head, tail))
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Self::Nil)
    }
}

impl<S, A: Clone, P> HostValue<S, A, P> {
    pub fn datum(datum: Datum<A>) -> Self {
        match datum {
            Datum::Atom(atom) => Self::Atom(atom),
            Datum::Nil => Self::Nil,
            Datum::Cons(head, tail) => Self::cons(Self::datum(*head), Self::datum(*tail)),
        }
    }

    /// Project a runtime value back to quoted data when it contains no
    /// procedures.
    pub fn as_datum(&self) -> Option<Datum<A>> {
        match self {
            Self::Atom(atom) => Some(Datum::Atom(atom.clone())),
            Self::Nil => Some(Datum::Nil),
            Self::Cons(head, tail) => Some(Datum::cons(head.as_datum()?, tail.as_datum()?)),
            Self::Closure(_) | Self::Primitive(_) | Self::ApplyListProcedure => None,
        }
    }
}

/// Runtime-value capability backed by the direct Rust [`HostValue`] domain.
#[derive(Clone, Copy, Debug)]
pub struct HostValues<S, A, P>(PhantomData<(S, A, P)>);

impl<S, A, P> Default for HostValues<S, A, P> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<S: Clone, A: Clone, P: Clone> LispValue for HostValues<S, A, P> {
    type Atom = A;
    type Primitive = P;
    type Value = HostValue<S, A, P>;
    type Error = Infallible;

    fn atom(&self, atom: A) -> Result<Self::Value, Self::Error> {
        Ok(HostValue::Atom(atom))
    }

    fn nil(&self) -> Self::Value {
        HostValue::Nil
    }

    fn cons(&self, head: Self::Value, tail: Self::Value) -> Result<Self::Value, Self::Error> {
        Ok(HostValue::cons(head, tail))
    }

    fn primitive(&self, primitive: P) -> Result<Self::Value, Self::Error> {
        Ok(HostValue::Primitive(primitive))
    }

    fn apply_list_procedure(&self) -> Self::Value {
        HostValue::ApplyListProcedure
    }

    fn view(
        &self,
        value: &Self::Value,
    ) -> Result<RuntimeValueView<A, P, Self::Value>, Self::Error> {
        Ok(match value {
            HostValue::Atom(atom) => RuntimeValueView::Atom(atom.clone()),
            HostValue::Nil => RuntimeValueView::Nil,
            HostValue::Cons(head, tail) => RuntimeValueView::Cons {
                head: (**head).clone(),
                tail: (**tail).clone(),
            },
            HostValue::Closure(_) => RuntimeValueView::Closure,
            HostValue::Primitive(primitive) => RuntimeValueView::Primitive(primitive.clone()),
            HostValue::ApplyListProcedure => RuntimeValueView::ApplyListProcedure,
        })
    }
}

impl<S: Clone, A: Clone, P: Clone> LispMachineValue for HostValues<S, A, P> {
    type Closure = Arc<HostClosure<S, A, P>>;

    fn roll(
        &self,
        layer: RuntimeValueLayer<A, Self::Closure, P, Self::Value>,
    ) -> Result<Self::Value, Self::Error> {
        Ok(match layer {
            RuntimeValueLayer::Atom(atom) => HostValue::Atom(atom),
            RuntimeValueLayer::Nil => HostValue::Nil,
            RuntimeValueLayer::Cons { head, tail } => HostValue::cons(head, tail),
            RuntimeValueLayer::Closure(closure) => HostValue::Closure(closure),
            RuntimeValueLayer::Primitive(primitive) => HostValue::Primitive(primitive),
            RuntimeValueLayer::ApplyListProcedure => HostValue::ApplyListProcedure,
        })
    }

    fn unroll(
        &self,
        value: &Self::Value,
    ) -> Result<RuntimeValueLayer<A, Self::Closure, P, Self::Value>, Self::Error> {
        Ok(match value {
            HostValue::Atom(atom) => RuntimeValueLayer::Atom(atom.clone()),
            HostValue::Nil => RuntimeValueLayer::Nil,
            HostValue::Cons(head, tail) => RuntimeValueLayer::Cons {
                head: (**head).clone(),
                tail: (**tail).clone(),
            },
            HostValue::Closure(closure) => RuntimeValueLayer::Closure(Arc::clone(closure)),
            HostValue::Primitive(primitive) => RuntimeValueLayer::Primitive(primitive.clone()),
            HostValue::ApplyListProcedure => RuntimeValueLayer::ApplyListProcedure,
        })
    }
}

/// Persistent-environment capability backed by [`HostEnvironment`].
#[derive(Clone, Copy, Debug)]
pub struct HostEnvironments<S, V>(PhantomData<(S, V)>);

impl<S, V> Default for HostEnvironments<S, V> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<S: Clone + PartialEq, V: Clone> LispEnvironment for HostEnvironments<S, V> {
    type Symbol = S;
    type Value = V;
    type Environment = HostEnvironment<S, V>;
    type Error = Infallible;

    fn empty(&self) -> Self::Environment {
        HostEnvironment::default()
    }

    fn lookup(
        &self,
        environment: &Self::Environment,
        symbol: &S,
    ) -> Result<Option<V>, Self::Error> {
        Ok(environment.lookup(symbol))
    }

    fn extend(
        &self,
        environment: &Self::Environment,
        bindings: Vec<RuntimeBinding<S, V>>,
    ) -> Result<Self::Environment, Self::Error> {
        Ok(environment.extend(
            bindings
                .into_iter()
                .map(|binding| (binding.symbol, binding.value)),
        ))
    }
}

impl<S: Clone + PartialEq, V: Clone> LispRecursiveEnvironment for HostEnvironments<S, V> {
    type Cell = HostRecursiveCell<V>;

    fn reserve_recursive(
        &self,
        environment: &Self::Environment,
        symbols: Vec<Self::Symbol>,
    ) -> Result<RecursiveAllocation<Self::Environment, Self::Cell>, Self::Error> {
        let cells: Vec<_> = symbols
            .iter()
            .map(|_| HostBindingCell::uninitialized())
            .collect();
        let environment =
            environment.extend_cells(symbols.into_iter().zip(cells.iter().cloned()).collect());
        Ok(RecursiveAllocation {
            environment,
            cells: cells.into_iter().map(HostRecursiveCell).collect(),
        })
    }

    fn initialize_recursive(
        &self,
        cell: Self::Cell,
        value: Self::Value,
    ) -> Result<(), Self::Error> {
        cell.0
            .initialize(value)
            .unwrap_or_else(|_| unreachable!("single-use recursive cell was already initialized"));
        Ok(())
    }
}

/// Coherent direct-Rust runtime bundle for the common Lisp machine.
#[derive(Clone, Debug)]
pub struct HostRuntime<S, A, P> {
    data: covalence_sexpr_api::Free<A>,
    values: HostValues<S, A, P>,
    expressions: CoreSyntax<S, A, P>,
    closures: HostClosures<S, A, P>,
    environments: HostEnvironments<S, HostValue<S, A, P>>,
}

impl<S, A, P> Default for HostRuntime<S, A, P> {
    fn default() -> Self {
        Self {
            data: covalence_sexpr_api::Free::new(),
            values: HostValues::default(),
            expressions: CoreSyntax::default(),
            closures: HostClosures::default(),
            environments: HostEnvironments::default(),
        }
    }
}

impl<S, A, P> LispRuntime for HostRuntime<S, A, P>
where
    S: Clone + PartialEq,
    A: Clone,
    P: Clone,
{
    type Symbol = S;
    type Atom = A;
    type Datum = Datum<A>;
    type Primitive = P;
    type Expr = Expr<S, A, P>;
    type Value = Value<S, A, P>;
    type Closure = Arc<HostClosure<S, A, P>>;
    type Environment = Environment<S, A, P>;
    type Error = Infallible;
    type Data = covalence_sexpr_api::Free<A>;
    type Values = HostValues<S, A, P>;
    type Expressions = CoreSyntax<S, A, P>;
    type Closures = HostClosures<S, A, P>;
    type Environments = HostEnvironments<S, HostValue<S, A, P>>;

    fn values(&self) -> &Self::Values {
        &self.values
    }

    fn data(&self) -> &Self::Data {
        &self.data
    }

    fn expressions(&self) -> &Self::Expressions {
        &self.expressions
    }

    fn closures(&self) -> &Self::Closures {
        &self.closures
    }

    fn environments(&self) -> &Self::Environments {
        &self.environments
    }
}

/// The active expression or computed value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineControl<E, V> {
    Expression(E),
    Value(V),
}

/// Evaluation-context frames for a strict lexical CEK-style machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineFrame<E, V, N, P> {
    If {
        consequent: E,
        alternative: E,
        environment: N,
    },
    Sequence {
        remaining: Vec<E>,
        environment: N,
    },
    ApplyParts {
        function: Option<V>,
        evaluated: Vec<Option<V>>,
        splice_tail: bool,
        current: MachineApplicationPosition,
        remaining: Vec<MachineApplicationPart<E>>,
        environment: N,
    },
    PrimitiveArguments {
        primitive: P,
        evaluated: Vec<Option<V>>,
        current: usize,
        remaining: Vec<(usize, E)>,
        environment: N,
    },
}

/// Position currently being evaluated in an application.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineApplicationPosition {
    Operator,
    Argument(usize),
}

/// One unevaluated part of an application.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineApplicationPart<E> {
    Operator(E),
    Argument { index: usize, expression: E },
}

/// A complete machine configuration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineConfiguration<E, V, N, P> {
    pub control: MachineControl<E, V>,
    pub environment: N,
    pub continuation: Vec<MachineFrame<E, V, N, P>>,
}

impl<E, V, N: Default, P> MachineConfiguration<E, V, N, P> {
    pub fn initial(expression: E) -> Self {
        Self::with_environment(expression, N::default())
    }
}

impl<E, V, N, P> MachineConfiguration<E, V, N, P> {
    pub fn with_environment(expression: E, environment: N) -> Self {
        Self {
            control: MachineControl::Expression(expression),
            environment,
            continuation: Vec::new(),
        }
    }

    pub fn terminal_value(&self) -> Option<&V> {
        if self.continuation.is_empty()
            && let MachineControl::Value(value) = &self.control
        {
            Some(value)
        } else {
            None
        }
    }
}

pub type HostControl<S, A, P> = MachineControl<Expr<S, A, P>, Value<S, A, P>>;
pub type HostFrame<S, A, P> = MachineFrame<Expr<S, A, P>, Value<S, A, P>, Environment<S, A, P>, P>;
pub type HostApplicationPosition = MachineApplicationPosition;
pub type HostApplicationPart<S, A, P> = MachineApplicationPart<Expr<S, A, P>>;
pub type HostConfiguration<S, A, P> =
    MachineConfiguration<Expr<S, A, P>, Value<S, A, P>, Environment<S, A, P>, P>;

/// Errors from the executable host machine.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArityExpectation {
    Exactly(usize),
    AtLeast(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreMachineError<S, E, R = Infallible> {
    UnboundVariable(S),
    DuplicateRecursiveBinding(S),
    InvalidRecursiveInitializer(S),
    NondeterministicSuccessors {
        count: usize,
    },
    NotCallable,
    Arity {
        expected: ArityExpectation,
        actual: usize,
    },
    ImproperArgumentList,
    Primitive(E),
    Runtime(R),
}

impl<S: Debug, E: Debug, R: Debug> Display for CoreMachineError<S, E, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnboundVariable(symbol) => write!(f, "unbound variable: {symbol:?}"),
            Self::DuplicateRecursiveBinding(symbol) => {
                write!(f, "duplicate recursive binding: {symbol:?}")
            }
            Self::InvalidRecursiveInitializer(symbol) => {
                write!(f, "recursive binding must initialize a lambda: {symbol:?}")
            }
            Self::NondeterministicSuccessors { count } => write!(
                f,
                "deterministic execution requested for a state with {count} legal successors"
            ),
            Self::NotCallable => f.write_str("attempted to apply a non-closure value"),
            Self::Arity { expected, actual } => match expected {
                ArityExpectation::Exactly(expected) => {
                    write!(f, "arity mismatch: expected {expected}, got {actual}")
                }
                ArityExpectation::AtLeast(expected) => {
                    write!(
                        f,
                        "arity mismatch: expected at least {expected}, got {actual}"
                    )
                }
            },
            Self::ImproperArgumentList => {
                f.write_str("apply-list tail did not evaluate to a proper list")
            }
            Self::Primitive(error) => write!(f, "primitive operation failed: {error:?}"),
            Self::Runtime(error) => write!(f, "runtime representation failed: {error:?}"),
        }
    }
}

impl<S: Debug, E: Debug, R: Debug> core::error::Error for CoreMachineError<S, E, R> {}

/// Strategy-parameterized evaluator over a coherent Lisp runtime.
///
/// The representation bundle is explicit even though the current transition
/// implementation is provided first for [`HostRuntime`]. This keeps ownership
/// and policy independent: subsequent backends can reuse the same machine
/// state and transition algorithm without impersonating the direct Rust
/// representation.
#[derive(Clone, Debug)]
pub struct LispMachine<R, P> {
    primitives: P,
    strategy: Strategy,
    runtime: R,
}

impl<R, P> LispMachine<R, P> {
    pub fn with_runtime(runtime: R, primitives: P, strategy: Strategy) -> Self {
        Self {
            primitives,
            strategy,
            runtime,
        }
    }

    pub fn runtime(&self) -> &R {
        &self.runtime
    }

    pub fn primitives(&self) -> &P {
        &self.primitives
    }

    pub fn strategy(&self) -> Strategy {
        self.strategy
    }
}

/// Compatibility name for the direct-Rust realization of [`LispMachine`].
pub type CoreMachine<P> = LispMachine<
    HostRuntime<
        <P as CorePrimitive>::Symbol,
        <P as CorePrimitive>::Atom,
        <P as CorePrimitive>::Primitive,
    >,
    P,
>;

impl<P: CorePrimitive> LispMachine<HostRuntime<P::Symbol, P::Atom, P::Primitive>, P> {
    pub fn new(primitives: P) -> Self {
        Self::with_strategy(primitives, Strategy::STRICT_LEXICAL)
    }

    pub fn with_strategy(primitives: P, strategy: Strategy) -> Self {
        Self::with_runtime(HostRuntime::default(), primitives, strategy)
    }
}

type RuntimeConfiguration<R> = MachineConfiguration<
    <R as LispRuntime>::Expr,
    <R as LispRuntime>::Value,
    <R as LispRuntime>::Environment,
    <R as LispRuntime>::Primitive,
>;

type RuntimeMachineError<R, P> = CoreMachineError<
    <R as LispRuntime>::Symbol,
    RuntimePrimitiveError<R, P>,
    <R as LispRuntime>::Error,
>;

impl<R, P> LispMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    fn values(&self) -> &R::Values {
        self.runtime.values()
    }

    fn closures(&self) -> &R::Closures {
        self.runtime.closures()
    }

    fn environments(&self) -> &R::Environments {
        self.runtime.environments()
    }

    /// Extend an environment with an atomic mutually recursive lambda group.
    ///
    /// All names and cells are allocated before any closure is built, so
    /// forward and mutual references observe the same lexical generation.
    pub fn bind_recursive(
        &self,
        parent: &R::Environment,
        bindings: Vec<(R::Symbol, R::Expr)>,
    ) -> Result<R::Environment, RuntimeMachineError<R, P>> {
        for (index, (name, expression)) in bindings.iter().enumerate() {
            if bindings[..index].iter().any(|(earlier, _)| earlier == name) {
                return Err(CoreMachineError::DuplicateRecursiveBinding(name.clone()));
            }
            if !matches!(
                self.runtime
                    .expressions()
                    .view(expression)
                    .map_err(CoreMachineError::Runtime)?,
                CoreExprLayer::Lambda { .. }
            ) {
                return Err(CoreMachineError::InvalidRecursiveInitializer(name.clone()));
            }
        }
        let environments = self.environments();
        let allocation = environments
            .reserve_recursive(
                parent,
                bindings.iter().map(|(name, _)| name.clone()).collect(),
            )
            .map_err(CoreMachineError::Runtime)?;
        let environment = allocation.environment;
        for ((_, expression), cell) in bindings.into_iter().zip(allocation.cells) {
            let CoreExprLayer::Lambda {
                name,
                parameters,
                rest,
                body,
            } = self
                .runtime
                .expressions()
                .view(&expression)
                .map_err(CoreMachineError::Runtime)?
            else {
                unreachable!("recursive initializers validated above")
            };
            let closure = self
                .closures()
                .close(ClosureRecord {
                    name,
                    parameters: parameters
                        .into_iter()
                        .map(|parameter| parameter.name)
                        .collect(),
                    rest: rest.map(|parameter| parameter.name),
                    body,
                    environment: environment.clone(),
                })
                .map_err(CoreMachineError::Runtime)?;
            let closure = self
                .values()
                .roll(RuntimeValueLayer::Closure(closure))
                .map_err(CoreMachineError::Runtime)?;
            environments
                .initialize_recursive(cell, closure)
                .map_err(CoreMachineError::Runtime)?;
        }
        Ok(environment)
    }

    fn argument_choices(&self, count: usize) -> Vec<usize> {
        match self.strategy.order {
            EvaluationOrder::ApplicativeLeftToRight => vec![0],
            EvaluationOrder::ApplicativeRightToLeft => vec![count - 1],
            EvaluationOrder::Relational => (0..count).collect(),
        }
    }

    fn schedule_application_part(
        &self,
        configuration: RuntimeConfiguration<R>,
        function: Option<R::Value>,
        evaluated: Vec<Option<R::Value>>,
        splice_tail: bool,
        remaining: Vec<MachineApplicationPart<R::Expr>>,
        environment: R::Environment,
    ) -> Vec<RuntimeConfiguration<R>> {
        self.argument_choices(remaining.len())
            .into_iter()
            .map(|choice| {
                let mut next = configuration.clone();
                let mut pending = remaining.clone();
                let (current, expression) = match pending.remove(choice) {
                    MachineApplicationPart::Operator(expression) => {
                        (MachineApplicationPosition::Operator, expression)
                    }
                    MachineApplicationPart::Argument { index, expression } => {
                        (MachineApplicationPosition::Argument(index), expression)
                    }
                };
                next.continuation.push(MachineFrame::ApplyParts {
                    function: function.clone(),
                    evaluated: evaluated.clone(),
                    splice_tail,
                    current,
                    remaining: pending,
                    environment: environment.clone(),
                });
                next.control = MachineControl::Expression(expression);
                next.environment = environment.clone();
                next
            })
            .collect()
    }

    fn schedule_primitive_argument(
        &self,
        configuration: RuntimeConfiguration<R>,
        primitive: R::Primitive,
        evaluated: Vec<Option<R::Value>>,
        remaining: Vec<(usize, R::Expr)>,
        environment: R::Environment,
    ) -> Vec<RuntimeConfiguration<R>> {
        self.argument_choices(remaining.len())
            .into_iter()
            .map(|choice| {
                let mut next = configuration.clone();
                let mut pending = remaining.clone();
                let (current, expression) = pending.remove(choice);
                next.continuation.push(MachineFrame::PrimitiveArguments {
                    primitive: primitive.clone(),
                    evaluated: evaluated.clone(),
                    current,
                    remaining: pending,
                    environment: environment.clone(),
                });
                next.control = MachineControl::Expression(expression);
                next.environment = environment.clone();
                next
            })
            .collect()
    }

    fn completed_arguments(evaluated: Vec<Option<R::Value>>) -> Vec<R::Value> {
        evaluated
            .into_iter()
            .map(|value| value.expect("every argument position was evaluated"))
            .collect()
    }

    fn continue_with(
        &self,
        mut configuration: RuntimeConfiguration<R>,
        value: R::Value,
    ) -> Result<Vec<RuntimeConfiguration<R>>, RuntimeMachineError<R, P>> {
        let Some(frame) = configuration.continuation.pop() else {
            return Ok(Vec::new());
        };
        match frame {
            MachineFrame::If {
                consequent,
                alternative,
                environment,
            } => {
                configuration.control = MachineControl::Expression(
                    if self
                        .primitives
                        .is_false(self.values(), &value)
                        .map_err(CoreMachineError::Primitive)?
                    {
                        alternative
                    } else {
                        consequent
                    },
                );
                configuration.environment = environment;
            }
            MachineFrame::Sequence {
                mut remaining,
                environment,
            } => {
                let expression = remaining
                    .pop()
                    .expect("sequence frames always contain a next expression");
                if !remaining.is_empty() {
                    configuration.continuation.push(MachineFrame::Sequence {
                        remaining,
                        environment: environment.clone(),
                    });
                }
                configuration.control = MachineControl::Expression(expression);
                configuration.environment = environment;
            }
            MachineFrame::ApplyParts {
                mut function,
                mut evaluated,
                splice_tail,
                current,
                remaining,
                environment,
            } => {
                match current {
                    MachineApplicationPosition::Operator => function = Some(value),
                    MachineApplicationPosition::Argument(index) => evaluated[index] = Some(value),
                }
                if remaining.is_empty() {
                    let function = function.expect("the application operator was evaluated");
                    let mut arguments = Self::completed_arguments(evaluated);
                    if splice_tail {
                        let tail = arguments
                            .pop()
                            .expect("apply-list always schedules its tail");
                        arguments.extend(self.proper_list(tail)?);
                    }
                    return Ok(self
                        .apply(configuration, function, arguments)?
                        .into_iter()
                        .collect());
                }
                return Ok(self.schedule_application_part(
                    configuration,
                    function,
                    evaluated,
                    splice_tail,
                    remaining,
                    environment,
                ));
            }
            MachineFrame::PrimitiveArguments {
                primitive,
                mut evaluated,
                current,
                remaining,
                environment,
            } => {
                evaluated[current] = Some(value);
                if remaining.is_empty() {
                    let arguments = Self::completed_arguments(evaluated);
                    let value = self
                        .primitives
                        .apply(self.values(), &primitive, &arguments)
                        .map_err(CoreMachineError::Primitive)?;
                    configuration.control = MachineControl::Value(value);
                } else {
                    return Ok(self.schedule_primitive_argument(
                        configuration,
                        primitive,
                        evaluated,
                        remaining,
                        environment,
                    ));
                }
            }
        }
        Ok(vec![configuration])
    }

    fn apply(
        &self,
        mut configuration: RuntimeConfiguration<R>,
        function: R::Value,
        arguments: Vec<R::Value>,
    ) -> Result<Option<RuntimeConfiguration<R>>, RuntimeMachineError<R, P>> {
        let closure = match self
            .values()
            .unroll(&function)
            .map_err(CoreMachineError::Runtime)?
        {
            RuntimeValueLayer::Closure(closure) => closure,
            RuntimeValueLayer::Primitive(primitive) => {
                let value = self
                    .primitives
                    .apply(self.values(), &primitive, &arguments)
                    .map_err(CoreMachineError::Primitive)?;
                configuration.control = MachineControl::Value(value);
                return Ok(Some(configuration));
            }
            RuntimeValueLayer::ApplyListProcedure => {
                if arguments.len() < 2 {
                    return Err(CoreMachineError::Arity {
                        expected: ArityExpectation::AtLeast(2),
                        actual: arguments.len(),
                    });
                }
                let mut arguments = arguments;
                let function = arguments.remove(0);
                let tail = arguments.pop().expect("at least two apply arguments");
                arguments.extend(self.proper_list(tail)?);
                return self.apply(configuration, function, arguments);
            }
            RuntimeValueLayer::Atom(_)
            | RuntimeValueLayer::Nil
            | RuntimeValueLayer::Cons { .. } => return Err(CoreMachineError::NotCallable),
        };
        let closure = self
            .closures()
            .open(&closure)
            .map_err(CoreMachineError::Runtime)?;
        if closure.rest.is_none() && closure.parameters.len() != arguments.len() {
            return Err(CoreMachineError::Arity {
                expected: ArityExpectation::Exactly(closure.parameters.len()),
                actual: arguments.len(),
            });
        }
        if closure.rest.is_some() && arguments.len() < closure.parameters.len() {
            return Err(CoreMachineError::Arity {
                expected: ArityExpectation::AtLeast(closure.parameters.len()),
                actual: arguments.len(),
            });
        }
        let mut bindings =
            Vec::with_capacity(arguments.len() + usize::from(closure.name.is_some()));
        if let Some(name) = &closure.name {
            bindings.push((name.clone(), function));
        }
        bindings.extend(
            closure
                .parameters
                .iter()
                .cloned()
                .zip(arguments.iter().cloned()),
        );
        if let Some(rest) = &closure.rest {
            bindings.push((
                rest.clone(),
                self.values()
                    .list(arguments.into_iter().skip(closure.parameters.len()))
                    .map_err(CoreMachineError::Runtime)?,
            ));
        }
        let parent = if self.strategy.lexical_scope {
            &closure.environment
        } else {
            &configuration.environment
        };
        configuration.environment = self
            .environments()
            .extend(
                parent,
                bindings
                    .into_iter()
                    .map(|(symbol, value)| RuntimeBinding::new(symbol, value))
                    .collect(),
            )
            .map_err(CoreMachineError::Runtime)?;
        configuration.control = MachineControl::Expression(closure.body);
        Ok(Some(configuration))
    }

    fn proper_list(&self, value: R::Value) -> Result<Vec<R::Value>, RuntimeMachineError<R, P>> {
        self.values()
            .as_list(&value)
            .map_err(CoreMachineError::Runtime)?
            .ok_or(CoreMachineError::ImproperArgumentList)
    }
}

impl<R, P> LispMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    fn step_successors(
        &self,
        configuration: &RuntimeConfiguration<R>,
    ) -> Result<Vec<RuntimeConfiguration<R>>, RuntimeMachineError<R, P>> {
        let mut next = configuration.clone();
        let control = next.control.clone();
        match control {
            MachineControl::Value(value) => self.continue_with(next, value),
            MachineControl::Expression(expression) => {
                match self
                    .runtime
                    .expressions()
                    .view(&expression)
                    .map_err(CoreMachineError::Runtime)?
                {
                    CoreExprLayer::Literal(datum) | CoreExprLayer::Quote(datum) => {
                        let value = inject_datum(self.runtime.data(), self.values(), &datum)
                            .map_err(|error| match error {
                                RuntimeDatumError::Datum(error)
                                | RuntimeDatumError::Value(error) => {
                                    CoreMachineError::Runtime(error)
                                }
                            });
                        next.control = MachineControl::Value(value?);
                    }
                    CoreExprLayer::Truth(value) => {
                        next.control = MachineControl::Value(
                            self.primitives
                                .truth(self.values(), value)
                                .map_err(CoreMachineError::Primitive)?,
                        );
                    }
                    CoreExprLayer::Variable(symbol) => {
                        let value = self
                            .environments()
                            .lookup(&next.environment, &symbol)
                            .map_err(CoreMachineError::Runtime)?
                            .ok_or(CoreMachineError::UnboundVariable(symbol))?;
                        next.control = MachineControl::Value(value);
                    }
                    CoreExprLayer::If {
                        condition,
                        consequent,
                        alternative,
                    } => {
                        next.continuation.push(MachineFrame::If {
                            consequent,
                            alternative,
                            environment: next.environment.clone(),
                        });
                        next.control = MachineControl::Expression(condition);
                    }
                    CoreExprLayer::Cond { clauses } => {
                        let syntax = self.runtime.expressions();
                        let mut expression =
                            syntax.truth(false).map_err(CoreMachineError::Runtime)?;
                        for (condition, consequent) in clauses.into_iter().rev() {
                            expression = syntax
                                .if_then_else(condition, consequent, expression)
                                .map_err(CoreMachineError::Runtime)?;
                        }
                        next.control = MachineControl::Expression(expression);
                    }
                    CoreExprLayer::Sequence { first, rest } => {
                        if !rest.is_empty() {
                            let mut remaining = rest;
                            remaining.reverse();
                            next.continuation.push(MachineFrame::Sequence {
                                remaining,
                                environment: next.environment.clone(),
                            });
                        }
                        next.control = MachineControl::Expression(first);
                    }
                    CoreExprLayer::Lambda {
                        name,
                        parameters,
                        rest,
                        body,
                    } => {
                        let closure = self
                            .closures()
                            .close(ClosureRecord {
                                name,
                                parameters: parameters
                                    .into_iter()
                                    .map(|parameter| parameter.name)
                                    .collect(),
                                rest: rest.map(|parameter| parameter.name),
                                body,
                                environment: next.environment.clone(),
                            })
                            .map_err(CoreMachineError::Runtime)?;
                        next.control = MachineControl::Value(
                            self.values()
                                .roll(RuntimeValueLayer::Closure(closure))
                                .map_err(CoreMachineError::Runtime)?,
                        );
                    }
                    CoreExprLayer::Apply {
                        operator,
                        arguments,
                    } => {
                        let argument_count = arguments.len();
                        let mut parts = Vec::with_capacity(argument_count + 1);
                        parts.push(MachineApplicationPart::Operator(operator));
                        parts.extend(arguments.into_iter().enumerate().map(
                            |(index, expression)| MachineApplicationPart::Argument {
                                index,
                                expression,
                            },
                        ));
                        return Ok(self.schedule_application_part(
                            next.clone(),
                            None,
                            vec![None; argument_count],
                            false,
                            parts,
                            next.environment,
                        ));
                    }
                    CoreExprLayer::ApplyList {
                        operator,
                        mut arguments,
                        tail,
                    } => {
                        arguments.push(tail);
                        let argument_count = arguments.len();
                        let mut parts = Vec::with_capacity(argument_count + 1);
                        parts.push(MachineApplicationPart::Operator(operator));
                        parts.extend(arguments.into_iter().enumerate().map(
                            |(index, expression)| MachineApplicationPart::Argument {
                                index,
                                expression,
                            },
                        ));
                        return Ok(self.schedule_application_part(
                            next.clone(),
                            None,
                            vec![None; argument_count],
                            true,
                            parts,
                            next.environment,
                        ));
                    }
                    CoreExprLayer::Let { bindings, body } => {
                        let parameters = bindings
                            .iter()
                            .map(|binding| binding.name.clone())
                            .collect();
                        let arguments = bindings.into_iter().map(|binding| binding.value).collect();
                        let syntax = self.runtime.expressions();
                        let operator = syntax
                            .lambda(None, parameters, None, body)
                            .map_err(CoreMachineError::Runtime)?;
                        next.control = MachineControl::Expression(
                            syntax
                                .apply(operator, arguments)
                                .map_err(CoreMachineError::Runtime)?,
                        );
                    }
                    CoreExprLayer::LetRec { bindings, body } => {
                        let environment = self.bind_recursive(
                            &next.environment,
                            bindings
                                .into_iter()
                                .map(|binding| (binding.name, binding.value))
                                .collect(),
                        )?;
                        next.environment = environment;
                        next.control = MachineControl::Expression(body);
                    }
                    CoreExprLayer::Primitive {
                        operator,
                        arguments,
                    } => {
                        if arguments.is_empty() {
                            let value = self
                                .primitives
                                .apply(self.values(), &operator, &[])
                                .map_err(CoreMachineError::Primitive)?;
                            next.control = MachineControl::Value(value);
                        } else {
                            let count = arguments.len();
                            return Ok(self.schedule_primitive_argument(
                                next.clone(),
                                operator,
                                vec![None; count],
                                arguments.into_iter().enumerate().collect(),
                                next.environment,
                            ));
                        }
                    }
                    CoreExprLayer::PrimitiveValue(primitive) => {
                        next.control = MachineControl::Value(
                            self.values()
                                .roll(RuntimeValueLayer::Primitive(primitive))
                                .map_err(CoreMachineError::Runtime)?,
                        );
                    }
                    CoreExprLayer::ApplyListProcedure => {
                        next.control = MachineControl::Value(
                            self.values()
                                .roll(RuntimeValueLayer::ApplyListProcedure)
                                .map_err(CoreMachineError::Runtime)?,
                        );
                    }
                }
                Ok(vec![next])
            }
        }
    }
}

impl<R, P> DeterministicStep for LispMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    R::Expr: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    R::Primitive: Debug + PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    fn next(
        &self,
        configuration: &RuntimeConfiguration<R>,
    ) -> Result<Option<RuntimeConfiguration<R>>, Self::Error> {
        let mut successors = self.step_successors(configuration)?;
        match successors.len() {
            0 => Ok(None),
            1 => Ok(successors.pop()),
            count => Err(CoreMachineError::NondeterministicSuccessors { count }),
        }
    }
}

impl<R, P> StepRelation for LispMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    R::Expr: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    R::Primitive: Debug + PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    type Configuration = RuntimeConfiguration<R>;
    type Error = RuntimeMachineError<R, P>;

    fn successors(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        self.step_successors(configuration)
    }
}

impl<R, P> TerminalValue for LispMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    R::Expr: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    R::Primitive: Debug + PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    type Value = R::Value;

    fn terminal_value(&self, configuration: &Self::Configuration) -> Option<Self::Value> {
        configuration.terminal_value().cloned()
    }
}

/// Direct construction and observation of [`CoreExpr`].
#[derive(Clone, Copy, Debug)]
pub struct CoreSyntax<S, A, P>(PhantomData<(S, A, P)>);

impl<S, A, P> Default for CoreSyntax<S, A, P> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<S: Clone, A: Clone, P: Clone> LispExpression for CoreSyntax<S, A, P> {
    type Symbol = S;
    type Datum = Datum<A>;
    type Primitive = P;
    type Expr = CoreExpr<S, Datum<A>, P>;
    type Error = Infallible;

    fn view(
        &self,
        expression: &Self::Expr,
    ) -> Result<CoreExprLayer<S, Self::Datum, P, Self::Expr>, Self::Error> {
        Ok(expression.clone().into_layer())
    }
}

impl<S: Clone, A: Clone, P: Clone> LispSyntax for CoreSyntax<S, A, P> {
    type Symbol = S;
    type Datum = Datum<A>;
    type Primitive = P;
    type Expr = CoreExpr<S, Datum<A>, P>;
    type Error = core::convert::Infallible;

    fn literal(&self, datum: Self::Datum) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Literal(datum))
    }

    fn truth(&self, value: bool) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Truth(value))
    }

    fn variable(&self, symbol: Self::Symbol) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Variable(symbol))
    }

    fn quote(&self, datum: Self::Datum) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Quote(datum))
    }

    fn if_then_else(
        &self,
        condition: Self::Expr,
        consequent: Self::Expr,
        alternative: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::If {
            condition: Box::new(condition),
            consequent: Box::new(consequent),
            alternative: Box::new(alternative),
        })
    }

    fn cond(&self, clauses: Vec<(Self::Expr, Self::Expr)>) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Cond { clauses })
    }

    fn sequence(
        &self,
        first: Self::Expr,
        rest: Vec<Self::Expr>,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Sequence {
            first: Box::new(first),
            rest,
        })
    }

    fn lambda(
        &self,
        name: Option<Self::Symbol>,
        parameters: Vec<Self::Symbol>,
        rest: Option<Self::Symbol>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Lambda {
            name,
            parameters: parameters.into_iter().map(Parameter::new).collect(),
            rest: rest.map(Parameter::new),
            body: Box::new(body),
        })
    }

    fn apply(
        &self,
        operator: Self::Expr,
        arguments: Vec<Self::Expr>,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Apply {
            operator: Box::new(operator),
            arguments,
        })
    }

    fn apply_list(
        &self,
        operator: Self::Expr,
        arguments: Vec<Self::Expr>,
        tail: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::ApplyList {
            operator: Box::new(operator),
            arguments,
            tail: Box::new(tail),
        })
    }

    fn let_bind(
        &self,
        bindings: Vec<(Self::Symbol, Self::Expr)>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Let {
            bindings: bindings
                .into_iter()
                .map(|(name, value)| Binding::new(name, value))
                .collect(),
            body: Box::new(body),
        })
    }

    fn let_rec(
        &self,
        bindings: Vec<(Self::Symbol, Self::Expr)>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::LetRec {
            bindings: bindings
                .into_iter()
                .map(|(name, value)| Binding::new(name, value))
                .collect(),
            body: Box::new(body),
        })
    }

    fn primitive(
        &self,
        operator: Self::Primitive,
        arguments: Vec<Self::Expr>,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Primitive {
            operator,
            arguments,
        })
    }

    fn primitive_value(&self, operator: Self::Primitive) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::PrimitiveValue(operator))
    }

    fn apply_list_procedure(&self) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::ApplyListProcedure)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::relation::{
        Evaluation, ExecutionError, ExplorationBounds, evaluate, execute, explore,
    };

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Primitive {
        Cons,
        Car,
        Cdr,
        Null,
    }

    #[derive(Clone, Debug)]
    struct Sector;

    impl CorePrimitive for Sector {
        type Symbol = &'static str;
        type Atom = &'static str;
        type Primitive = Primitive;
    }

    impl PrimitiveSemantics<HostValues<&'static str, &'static str, Primitive>> for Sector {
        type Error = &'static str;

        fn apply(
            &self,
            values: &HostValues<&'static str, &'static str, Primitive>,
            primitive: &Primitive,
            arguments: &[HostValue<&'static str, &'static str, Primitive>],
        ) -> Result<HostValue<&'static str, &'static str, Primitive>, Self::Error> {
            match (primitive, arguments) {
                (Primitive::Cons, [head, tail]) => values
                    .cons(head.clone(), tail.clone())
                    .map_err(|never| match never {}),
                (Primitive::Car, [HostValue::Cons(head, _)]) => Ok((**head).clone()),
                (Primitive::Cdr, [HostValue::Cons(_, tail)]) => Ok((**tail).clone()),
                (Primitive::Null, [value]) => self.truth(values, matches!(value, HostValue::Nil)),
                _ => Err("bad primitive application"),
            }
        }

        fn truth(
            &self,
            values: &HostValues<&'static str, &'static str, Primitive>,
            value: bool,
        ) -> Result<HostValue<&'static str, &'static str, Primitive>, Self::Error> {
            Ok(if value {
                values.atom("t").map_err(|never| match never {})?
            } else {
                values.nil()
            })
        }

        fn is_false(
            &self,
            values: &HostValues<&'static str, &'static str, Primitive>,
            value: &HostValue<&'static str, &'static str, Primitive>,
        ) -> Result<bool, Self::Error> {
            Ok(matches!(
                values.view(value).map_err(|never| match never {})?,
                RuntimeValueView::Nil
            ))
        }
    }

    /// A deliberately distinct runtime owner that delegates to the direct
    /// representation. This is a conformance harness: if the evaluator
    /// accidentally specializes itself to `HostRuntime`, this backend stops
    /// implementing `StepRelation` even though every carrier is compatible.
    #[derive(Clone, Debug, Default)]
    struct DelegatingRuntime(HostRuntime<&'static str, &'static str, Primitive>);

    impl LispRuntime for DelegatingRuntime {
        type Symbol = &'static str;
        type Atom = &'static str;
        type Datum = Datum<&'static str>;
        type Primitive = Primitive;
        type Expr = Expr<Self::Symbol, Self::Atom, Self::Primitive>;
        type Value = Value<Self::Symbol, Self::Atom, Self::Primitive>;
        type Closure = Arc<HostClosure<Self::Symbol, Self::Atom, Self::Primitive>>;
        type Environment = Environment<Self::Symbol, Self::Atom, Self::Primitive>;
        type Error = Infallible;
        type Data = covalence_sexpr_api::Free<Self::Atom>;
        type Values = HostValues<Self::Symbol, Self::Atom, Self::Primitive>;
        type Expressions = CoreSyntax<Self::Symbol, Self::Atom, Self::Primitive>;
        type Closures = HostClosures<Self::Symbol, Self::Atom, Self::Primitive>;
        type Environments = HostEnvironments<Self::Symbol, Self::Value>;

        fn values(&self) -> &Self::Values {
            self.0.values()
        }

        fn data(&self) -> &Self::Data {
            self.0.data()
        }

        fn expressions(&self) -> &Self::Expressions {
            self.0.expressions()
        }

        fn closures(&self) -> &Self::Closures {
            self.0.closures()
        }

        fn environments(&self) -> &Self::Environments {
            self.0.environments()
        }
    }

    #[test]
    fn machine_state_is_independent_of_host_runtime_representations() {
        type Alternate = MachineConfiguration<&'static str, u8, Vec<(&'static str, u8)>, ()>;

        let mut configuration = Alternate::initial("expression");
        assert!(matches!(
            configuration.control,
            MachineControl::Expression("expression")
        ));
        configuration.control = MachineControl::Value(42);
        assert_eq!(configuration.terminal_value(), Some(&42));
    }

    #[test]
    fn host_machine_values_satisfy_runtime_fixpoint_round_trips() {
        type TestValue = HostValue<&'static str, &'static str, Primitive>;

        let runtime = HostRuntime::<&str, &str, Primitive>::default();
        let values = runtime.values();
        let closures = runtime.closures();
        let expression = CoreExpr::Variable("value");
        assert_eq!(
            CoreExpr::from_layer(
                runtime
                    .expressions()
                    .view(&expression)
                    .unwrap_or_else(|never| match never {})
            ),
            expression
        );
        let closure_record = ClosureRecord {
            name: Some("identity"),
            parameters: vec!["value"],
            rest: None,
            body: CoreExpr::Variable("value"),
            environment: HostEnvironment::<&str, TestValue>::default(),
        };
        let closure = closures
            .close(closure_record.clone())
            .unwrap_or_else(|never| match never {});
        assert_eq!(
            closures
                .open(&closure)
                .unwrap_or_else(|never| match never {}),
            closure_record
        );
        let layers = [
            RuntimeValueLayer::Atom("atom"),
            RuntimeValueLayer::Nil,
            RuntimeValueLayer::Cons {
                head: HostValue::Atom("head"),
                tail: HostValue::Nil,
            },
            RuntimeValueLayer::Closure(closure),
            RuntimeValueLayer::Primitive(Primitive::Car),
            RuntimeValueLayer::ApplyListProcedure,
        ];

        for layer in layers {
            let value = values
                .roll(layer.clone())
                .unwrap_or_else(|never| match never {});
            if layer.case() == crate::RuntimeValueCase::Closure {
                assert!(matches!(
                    values.view(&value).unwrap_or_else(|never| match never {}),
                    RuntimeValueView::Closure
                ));
            }
            assert_eq!(
                values.unroll(&value).unwrap_or_else(|never| match never {}),
                layer
            );
        }
    }

    #[test]
    fn sector_primitives_run_through_auditable_small_steps() {
        let expression = CoreExpr::Primitive {
            operator: Primitive::Car,
            arguments: vec![CoreExpr::Primitive {
                operator: Primitive::Cons,
                arguments: vec![
                    CoreExpr::Literal(Datum::Atom("head")),
                    CoreExpr::Literal(Datum::Nil),
                ],
            }],
        };
        let machine = CoreMachine::new(Sector);
        let trace = execute(&machine, HostConfiguration::initial(expression), 16).unwrap();
        assert_eq!(trace.end().terminal_value(), Some(&HostValue::Atom("head")));
    }

    #[test]
    fn transition_algorithm_is_generic_over_the_runtime_bundle() {
        let expression = CoreExpr::Primitive {
            operator: Primitive::Car,
            arguments: vec![CoreExpr::Primitive {
                operator: Primitive::Cons,
                arguments: vec![
                    CoreExpr::Literal(Datum::Atom("generic")),
                    CoreExpr::Literal(Datum::Nil),
                ],
            }],
        };
        let runtime = DelegatingRuntime::default();
        let environment = runtime.environments().empty();
        let machine = LispMachine::with_runtime(runtime, Sector, Strategy::STRICT_LEXICAL);
        let trace = execute(
            &machine,
            MachineConfiguration::with_environment(expression, environment),
            16,
        )
        .unwrap();

        assert_eq!(
            trace.end().terminal_value(),
            Some(&HostValue::Atom("generic"))
        );
    }

    fn pair_expression() -> Expr<&'static str, &'static str, Primitive> {
        CoreExpr::Primitive {
            operator: Primitive::Cons,
            arguments: vec![
                CoreExpr::Literal(Datum::Atom("left")),
                CoreExpr::Literal(Datum::Atom("right")),
            ],
        }
    }

    fn application_expression() -> Expr<&'static str, &'static str, Primitive> {
        CoreExpr::Apply {
            operator: Box::new(CoreExpr::Lambda {
                name: None,
                parameters: vec![Parameter::new("x"), Parameter::new("y")],
                rest: None,
                body: Box::new(CoreExpr::Variable("x")),
            }),
            arguments: vec![
                CoreExpr::Literal(Datum::Atom("left")),
                CoreExpr::Literal(Datum::Atom("right")),
            ],
        }
    }

    #[test]
    fn deterministic_strategies_choose_opposite_operand_orders() {
        let initial = HostConfiguration::initial(pair_expression());
        let left = CoreMachine::new(Sector)
            .next(&initial)
            .unwrap()
            .expect("left successor");
        let right = CoreMachine::with_strategy(
            Sector,
            Strategy {
                order: EvaluationOrder::ApplicativeRightToLeft,
                lexical_scope: true,
            },
        )
        .next(&initial)
        .unwrap()
        .expect("right successor");
        assert!(matches!(
            left.control,
            HostControl::Expression(CoreExpr::Literal(Datum::Atom("left")))
        ));
        assert!(matches!(
            right.control,
            HostControl::Expression(CoreExpr::Literal(Datum::Atom("right")))
        ));

        let trace = execute(
            &CoreMachine::with_strategy(
                Sector,
                Strategy {
                    order: EvaluationOrder::ApplicativeRightToLeft,
                    lexical_scope: true,
                },
            ),
            initial,
            16,
        )
        .unwrap();
        assert_eq!(
            trace.end().terminal_value(),
            Some(&HostValue::cons(
                HostValue::Atom("left"),
                HostValue::Atom("right")
            )),
            "evaluation order must not permute argument positions"
        );
    }

    #[test]
    fn relational_strategy_exposes_each_pending_operand_choice() {
        let machine = CoreMachine::with_strategy(
            Sector,
            Strategy {
                order: EvaluationOrder::Relational,
                lexical_scope: true,
            },
        );
        let initial = HostConfiguration::initial(pair_expression());
        let successors = machine.successors(&initial).unwrap();
        assert_eq!(successors.len(), 2);
        assert!(successors.iter().any(|state| matches!(
            state.control,
            HostControl::Expression(CoreExpr::Literal(Datum::Atom("left")))
        )));
        assert!(successors.iter().any(|state| matches!(
            state.control,
            HostControl::Expression(CoreExpr::Literal(Datum::Atom("right")))
        )));
        assert!(matches!(
            machine.next(&initial),
            Err(CoreMachineError::NondeterministicSuccessors { count: 2 })
        ));

        let exploration = explore(
            &machine,
            initial,
            ExplorationBounds {
                max_steps: 16,
                max_traces: 64,
            },
        )
        .unwrap();
        assert!(!exploration.truncated);
        assert!(exploration.stuck.is_empty());
        assert_eq!(
            exploration.values.len(),
            2,
            "both legal operand orders retain distinct trace provenance"
        );
        assert!(exploration.values.iter().all(|result| {
            result.value == HostValue::cons(HostValue::Atom("left"), HostValue::Atom("right"))
        }));
    }

    #[test]
    fn application_order_includes_the_operator() {
        let initial = HostConfiguration::initial(application_expression());
        let left_machine = CoreMachine::new(Sector);
        let left = left_machine.next(&initial).unwrap().unwrap();
        assert!(matches!(
            left.control,
            HostControl::Expression(CoreExpr::Lambda { .. })
        ));

        let right_machine = CoreMachine::with_strategy(
            Sector,
            Strategy {
                order: EvaluationOrder::ApplicativeRightToLeft,
                lexical_scope: true,
            },
        );
        let right = right_machine.next(&initial).unwrap().unwrap();
        assert!(matches!(
            right.control,
            HostControl::Expression(CoreExpr::Literal(Datum::Atom("right")))
        ));
        let result = evaluate(&right_machine, initial.clone(), 32).unwrap();
        let Evaluation::Value(result) = result else {
            panic!("right-to-left application must return")
        };
        assert_eq!(result.value, HostValue::Atom("left"));

        let relational = CoreMachine::with_strategy(
            Sector,
            Strategy {
                order: EvaluationOrder::Relational,
                lexical_scope: true,
            },
        );
        assert_eq!(relational.successors(&initial).unwrap().len(), 3);
    }

    #[test]
    fn scope_strategy_distinguishes_lexical_and_dynamic_lisp() {
        let call_f = CoreExpr::Apply {
            operator: Box::new(CoreExpr::Variable("f")),
            arguments: Vec::new(),
        };
        let expression = CoreExpr::Let {
            bindings: vec![Binding::new("x", CoreExpr::Literal(Datum::Atom("lexical")))],
            body: Box::new(CoreExpr::Let {
                bindings: vec![Binding::new(
                    "f",
                    CoreExpr::Lambda {
                        name: None,
                        parameters: Vec::new(),
                        rest: None,
                        body: Box::new(CoreExpr::Variable("x")),
                    },
                )],
                body: Box::new(CoreExpr::Let {
                    bindings: vec![Binding::new("x", CoreExpr::Literal(Datum::Atom("dynamic")))],
                    body: Box::new(call_f),
                }),
            }),
        };
        let lexical = evaluate(
            &CoreMachine::new(Sector),
            HostConfiguration::initial(expression.clone()),
            64,
        )
        .unwrap();
        let dynamic = evaluate(
            &CoreMachine::with_strategy(
                Sector,
                Strategy {
                    order: EvaluationOrder::ApplicativeLeftToRight,
                    lexical_scope: false,
                },
            ),
            HostConfiguration::initial(expression),
            64,
        )
        .unwrap();
        let Evaluation::Value(lexical) = lexical else {
            panic!("lexical program must return")
        };
        let Evaluation::Value(dynamic) = dynamic else {
            panic!("dynamic program must return")
        };
        assert_eq!(lexical.value, HostValue::Atom("lexical"));
        assert_eq!(dynamic.value, HostValue::Atom("dynamic"));
    }

    #[test]
    fn host_evaluation_constructs_may_eval_evidence() {
        let expression = CoreExpr::Quote(Datum::Atom("answer"));
        let initial = HostConfiguration::initial(expression);
        let Evaluation::Value(result) = evaluate(&CoreMachine::new(Sector), initial, 1).unwrap()
        else {
            panic!("quotation must evaluate to a value")
        };
        assert_eq!(
            result.value,
            HostValue::Atom("answer"),
            "the observed value comes from the terminal machine configuration"
        );
        assert_eq!(result.trace.steps(), 1);
    }

    #[test]
    fn sequence_evaluates_every_expression_in_order_and_returns_the_last() {
        let expression = CoreExpr::Sequence {
            first: Box::new(CoreExpr::Literal(Datum::Atom("discarded"))),
            rest: vec![
                CoreExpr::Literal(Datum::Atom("also-discarded")),
                CoreExpr::Literal(Datum::Atom("answer")),
            ],
        };
        let Evaluation::Value(result) = evaluate(
            &CoreMachine::new(Sector),
            HostConfiguration::initial(expression),
            8,
        )
        .unwrap() else {
            panic!("finite sequence must return")
        };
        assert_eq!(result.value, HostValue::Atom("answer"));
        assert_eq!(result.trace.steps(), 6);
    }

    #[test]
    fn named_closure_supports_partial_recursive_semantics() {
        let identity = CoreExpr::Lambda {
            name: Some("self"),
            parameters: vec![Parameter::new("x")],
            rest: None,
            body: Box::new(CoreExpr::Variable("x")),
        };
        let expression = CoreExpr::Apply {
            operator: Box::new(identity),
            arguments: vec![CoreExpr::Literal(Datum::Atom("value"))],
        };
        let machine = CoreMachine::new(Sector);
        let trace = execute(&machine, HostConfiguration::initial(expression), 16).unwrap();
        assert_eq!(
            trace.end().terminal_value(),
            Some(&HostValue::Atom("value"))
        );
    }

    #[test]
    fn rest_binding_is_a_runtime_list_that_can_contain_closures() {
        let identity = CoreExpr::Lambda {
            name: None,
            parameters: vec![Parameter::new("x")],
            rest: None,
            body: Box::new(CoreExpr::Variable("x")),
        };
        let choose_rest_procedure = CoreExpr::Lambda {
            name: None,
            parameters: Vec::new(),
            rest: Some(Parameter::new("procedures")),
            body: Box::new(CoreExpr::Primitive {
                operator: Primitive::Car,
                arguments: vec![CoreExpr::Variable("procedures")],
            }),
        };
        let expression = CoreExpr::Apply {
            operator: Box::new(CoreExpr::Apply {
                operator: Box::new(choose_rest_procedure),
                arguments: vec![identity],
            }),
            arguments: vec![CoreExpr::Literal(Datum::Atom("answer"))],
        };
        let result = evaluate(
            &CoreMachine::new(Sector),
            HostConfiguration::initial(expression),
            32,
        )
        .unwrap();
        let Evaluation::Value(result) = result else {
            panic!("rest-list procedure must be callable")
        };
        assert_eq!(result.value, HostValue::Atom("answer"));
    }

    #[test]
    fn apply_list_rejects_an_improper_tail() {
        let expression = CoreExpr::ApplyList {
            operator: Box::new(CoreExpr::Lambda {
                name: None,
                parameters: Vec::new(),
                rest: Some(Parameter::new("arguments")),
                body: Box::new(CoreExpr::Variable("arguments")),
            }),
            arguments: Vec::new(),
            tail: Box::new(CoreExpr::Literal(Datum::Atom("not-a-list"))),
        };
        assert!(matches!(
            execute(
                &CoreMachine::new(Sector),
                HostConfiguration::initial(expression),
                16
            ),
            Err(ExecutionError::Relation(
                CoreMachineError::ImproperArgumentList
            ))
        ));
    }

    #[test]
    fn letrec_supports_lexical_mutual_recursion() {
        let call = |name, argument| CoreExpr::Apply {
            operator: Box::new(CoreExpr::Variable(name)),
            arguments: vec![argument],
        };
        let null = |argument| CoreExpr::Primitive {
            operator: Primitive::Null,
            arguments: vec![argument],
        };
        let cdr = |argument| CoreExpr::Primitive {
            operator: Primitive::Cdr,
            arguments: vec![argument],
        };
        let even = CoreExpr::Lambda {
            name: None,
            parameters: vec![Parameter::new("xs")],
            rest: None,
            body: Box::new(CoreExpr::If {
                condition: Box::new(null(CoreExpr::Variable("xs"))),
                consequent: Box::new(CoreExpr::Truth(true)),
                alternative: Box::new(call("odd", cdr(CoreExpr::Variable("xs")))),
            }),
        };
        let odd = CoreExpr::Lambda {
            name: None,
            parameters: vec![Parameter::new("xs")],
            rest: None,
            body: Box::new(CoreExpr::If {
                condition: Box::new(null(CoreExpr::Variable("xs"))),
                consequent: Box::new(CoreExpr::Truth(false)),
                alternative: Box::new(call("even", cdr(CoreExpr::Variable("xs")))),
            }),
        };
        let input = Datum::list([Datum::Atom("a"), Datum::Atom("b")]);
        let expression = CoreExpr::LetRec {
            bindings: vec![Binding::new("even", even), Binding::new("odd", odd)],
            body: Box::new(call("even", CoreExpr::Literal(input))),
        };

        let Evaluation::Value(result) = evaluate(
            &CoreMachine::new(Sector),
            HostConfiguration::initial(expression),
            128,
        )
        .unwrap() else {
            panic!("mutually recursive parity program must return")
        };
        assert_eq!(result.value, HostValue::Atom("t"));
    }

    #[test]
    fn letrec_rejects_non_lambda_initializers_before_execution() {
        let expression = CoreExpr::LetRec {
            bindings: vec![Binding::new("x", CoreExpr::Truth(true))],
            body: Box::new(CoreExpr::Variable("x")),
        };
        let error = execute(
            &CoreMachine::new(Sector),
            HostConfiguration::initial(expression),
            8,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            crate::relation::ExecutionError::Relation(
                CoreMachineError::InvalidRecursiveInitializer("x")
            )
        ));
    }
}
