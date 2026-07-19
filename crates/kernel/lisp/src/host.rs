//! Executable host-data realization of the common Lisp core.
//!
//! This backend is deliberately proof-free. It is useful for frontend tests,
//! trace discovery, differential testing, and as an executable specification
//! for proof-producing backends.

use core::fmt::{Debug, Display, Formatter};
use core::marker::PhantomData;
use std::sync::{Arc, OnceLock};

use crate::relation::{DeterministicStep, StepRelation, TerminalValue};
use crate::syntax::{Binding, CoreExpr, EvaluationOrder, LispSyntax, Parameter, Strategy};

/// The direct inductive S-expression representation
/// `μX. Atom(P) + 1 + X×X`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Datum<P> {
    Atom(P),
    Nil,
    Cons(Box<Self>, Box<Self>),
}

impl<P> Datum<P> {
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
}

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

/// Semantics for a dialect's primitive operations.
pub trait CorePrimitive {
    type Symbol: Clone + PartialEq + Debug;
    type Atom: Clone + PartialEq + Debug;
    type Primitive: Clone + PartialEq + Debug;
    type Error: Debug;

    fn apply(
        &self,
        primitive: &Self::Primitive,
        arguments: &[HostValue<Self::Symbol, Self::Atom, Self::Primitive>],
    ) -> Result<HostValue<Self::Symbol, Self::Atom, Self::Primitive>, Self::Error>;

    fn truth(&self, value: bool) -> HostValue<Self::Symbol, Self::Atom, Self::Primitive>;

    /// Dialect-specific truth observation. The default is McCarthy/ACL2
    /// truthiness: only the empty list is false.
    fn is_false(&self, value: &HostValue<Self::Symbol, Self::Atom, Self::Primitive>) -> bool {
        value.is_false()
    }
}

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

/// Runtime values of the host realization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostValue<S, A, P> {
    Atom(A),
    Nil,
    Cons(Box<Self>, Box<Self>),
    Closure(Arc<HostClosure<S, A, P>>),
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
            Self::Closure(_) => None,
        }
    }
}

/// The active expression or computed value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostControl<S, A, P> {
    Expression(Expr<S, A, P>),
    Value(Value<S, A, P>),
}

/// Evaluation-context frames for a strict lexical CEK-style machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostFrame<S, A, P> {
    If {
        consequent: Expr<S, A, P>,
        alternative: Expr<S, A, P>,
        environment: Environment<S, A, P>,
    },
    Sequence {
        remaining: Vec<Expr<S, A, P>>,
        environment: Environment<S, A, P>,
    },
    ApplyParts {
        function: Option<Value<S, A, P>>,
        evaluated: Vec<Option<Value<S, A, P>>>,
        splice_tail: bool,
        current: HostApplicationPosition,
        remaining: Vec<HostApplicationPart<S, A, P>>,
        environment: Environment<S, A, P>,
    },
    PrimitiveArguments {
        primitive: P,
        evaluated: Vec<Option<Value<S, A, P>>>,
        current: usize,
        remaining: Vec<(usize, Expr<S, A, P>)>,
        environment: Environment<S, A, P>,
    },
}

/// Position currently being evaluated in an application.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HostApplicationPosition {
    Operator,
    Argument(usize),
}

/// One unevaluated part of an application.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostApplicationPart<S, A, P> {
    Operator(Expr<S, A, P>),
    Argument {
        index: usize,
        expression: Expr<S, A, P>,
    },
}

/// A complete machine configuration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostConfiguration<S, A, P> {
    pub control: HostControl<S, A, P>,
    pub environment: Environment<S, A, P>,
    pub continuation: Vec<HostFrame<S, A, P>>,
}

impl<S, A, P> HostConfiguration<S, A, P> {
    pub fn initial(expression: Expr<S, A, P>) -> Self {
        Self::with_environment(expression, HostEnvironment::default())
    }

    pub fn with_environment(expression: Expr<S, A, P>, environment: Environment<S, A, P>) -> Self {
        Self {
            control: HostControl::Expression(expression),
            environment,
            continuation: Vec::new(),
        }
    }

    pub fn terminal_value(&self) -> Option<&Value<S, A, P>> {
        if self.continuation.is_empty()
            && let HostControl::Value(value) = &self.control
        {
            Some(value)
        } else {
            None
        }
    }
}

/// Errors from the executable host machine.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArityExpectation {
    Exactly(usize),
    AtLeast(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreMachineError<S, E> {
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
}

impl<S: Debug, E: Debug> Display for CoreMachineError<S, E> {
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
        }
    }
}

impl<S: Debug, E: Debug> core::error::Error for CoreMachineError<S, E> {}

/// Strategy-parameterized host realization of the common Lisp core.
#[derive(Clone, Debug)]
pub struct CoreMachine<P> {
    primitives: P,
    strategy: Strategy,
}

impl<P> CoreMachine<P> {
    pub fn new(primitives: P) -> Self {
        Self::with_strategy(primitives, Strategy::STRICT_LEXICAL)
    }

    pub fn with_strategy(primitives: P, strategy: Strategy) -> Self {
        Self {
            primitives,
            strategy,
        }
    }

    pub fn primitives(&self) -> &P {
        &self.primitives
    }

    pub fn strategy(&self) -> Strategy {
        self.strategy
    }
}

type ConfigOf<P> = HostConfiguration<
    <P as CorePrimitive>::Symbol,
    <P as CorePrimitive>::Atom,
    <P as CorePrimitive>::Primitive,
>;

impl<P: CorePrimitive> CoreMachine<P> {
    /// Extend an environment with an atomic mutually recursive lambda group.
    ///
    /// All names and cells are allocated before any closure is built, so
    /// forward and mutual references observe the same lexical generation.
    pub fn bind_recursive(
        &self,
        parent: &Environment<P::Symbol, P::Atom, P::Primitive>,
        bindings: Vec<(P::Symbol, Expr<P::Symbol, P::Atom, P::Primitive>)>,
    ) -> Result<Environment<P::Symbol, P::Atom, P::Primitive>, CoreMachineError<P::Symbol, P::Error>>
    {
        for (index, (name, expression)) in bindings.iter().enumerate() {
            if bindings[..index].iter().any(|(earlier, _)| earlier == name) {
                return Err(CoreMachineError::DuplicateRecursiveBinding(name.clone()));
            }
            if !matches!(expression, CoreExpr::Lambda { .. }) {
                return Err(CoreMachineError::InvalidRecursiveInitializer(name.clone()));
            }
        }
        let cells: Vec<_> = bindings
            .iter()
            .map(|(name, _)| (name.clone(), HostBindingCell::uninitialized()))
            .collect();
        let environment = parent.extend_cells(cells.clone());
        for ((_, expression), (_, cell)) in bindings.into_iter().zip(cells) {
            let CoreExpr::Lambda {
                name,
                parameters,
                rest,
                body,
            } = expression
            else {
                unreachable!("recursive initializers validated above")
            };
            let closure = HostValue::Closure(Arc::new(HostClosure {
                name,
                parameters,
                rest,
                body: *body,
                environment: environment.clone(),
            }));
            cell.initialize(closure)
                .expect("fresh recursive binding cell");
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
        configuration: ConfigOf<P>,
        function: Option<Value<P::Symbol, P::Atom, P::Primitive>>,
        evaluated: Vec<Option<Value<P::Symbol, P::Atom, P::Primitive>>>,
        splice_tail: bool,
        remaining: Vec<HostApplicationPart<P::Symbol, P::Atom, P::Primitive>>,
        environment: Environment<P::Symbol, P::Atom, P::Primitive>,
    ) -> Vec<ConfigOf<P>> {
        self.argument_choices(remaining.len())
            .into_iter()
            .map(|choice| {
                let mut next = configuration.clone();
                let mut pending = remaining.clone();
                let (current, expression) = match pending.remove(choice) {
                    HostApplicationPart::Operator(expression) => {
                        (HostApplicationPosition::Operator, expression)
                    }
                    HostApplicationPart::Argument { index, expression } => {
                        (HostApplicationPosition::Argument(index), expression)
                    }
                };
                next.continuation.push(HostFrame::ApplyParts {
                    function: function.clone(),
                    evaluated: evaluated.clone(),
                    splice_tail,
                    current,
                    remaining: pending,
                    environment: environment.clone(),
                });
                next.control = HostControl::Expression(expression);
                next.environment = environment.clone();
                next
            })
            .collect()
    }

    fn schedule_primitive_argument(
        &self,
        configuration: ConfigOf<P>,
        primitive: P::Primitive,
        evaluated: Vec<Option<Value<P::Symbol, P::Atom, P::Primitive>>>,
        remaining: Vec<(usize, Expr<P::Symbol, P::Atom, P::Primitive>)>,
        environment: Environment<P::Symbol, P::Atom, P::Primitive>,
    ) -> Vec<ConfigOf<P>> {
        self.argument_choices(remaining.len())
            .into_iter()
            .map(|choice| {
                let mut next = configuration.clone();
                let mut pending = remaining.clone();
                let (current, expression) = pending.remove(choice);
                next.continuation.push(HostFrame::PrimitiveArguments {
                    primitive: primitive.clone(),
                    evaluated: evaluated.clone(),
                    current,
                    remaining: pending,
                    environment: environment.clone(),
                });
                next.control = HostControl::Expression(expression);
                next.environment = environment.clone();
                next
            })
            .collect()
    }

    fn completed_arguments(
        evaluated: Vec<Option<Value<P::Symbol, P::Atom, P::Primitive>>>,
    ) -> Vec<Value<P::Symbol, P::Atom, P::Primitive>> {
        evaluated
            .into_iter()
            .map(|value| value.expect("every argument position was evaluated"))
            .collect()
    }

    fn continue_with(
        &self,
        mut configuration: ConfigOf<P>,
        value: Value<P::Symbol, P::Atom, P::Primitive>,
    ) -> Result<Vec<ConfigOf<P>>, CoreMachineError<P::Symbol, P::Error>> {
        let Some(frame) = configuration.continuation.pop() else {
            return Ok(Vec::new());
        };
        match frame {
            HostFrame::If {
                consequent,
                alternative,
                environment,
            } => {
                configuration.control =
                    HostControl::Expression(if self.primitives.is_false(&value) {
                        alternative
                    } else {
                        consequent
                    });
                configuration.environment = environment;
            }
            HostFrame::Sequence {
                mut remaining,
                environment,
            } => {
                let expression = remaining
                    .pop()
                    .expect("sequence frames always contain a next expression");
                if !remaining.is_empty() {
                    configuration.continuation.push(HostFrame::Sequence {
                        remaining,
                        environment: environment.clone(),
                    });
                }
                configuration.control = HostControl::Expression(expression);
                configuration.environment = environment;
            }
            HostFrame::ApplyParts {
                mut function,
                mut evaluated,
                splice_tail,
                current,
                remaining,
                environment,
            } => {
                match current {
                    HostApplicationPosition::Operator => function = Some(value),
                    HostApplicationPosition::Argument(index) => evaluated[index] = Some(value),
                }
                if remaining.is_empty() {
                    let function = function.expect("the application operator was evaluated");
                    let mut arguments = Self::completed_arguments(evaluated);
                    if splice_tail {
                        let tail = arguments
                            .pop()
                            .expect("apply-list always schedules its tail");
                        arguments.extend(Self::proper_list(tail)?);
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
            HostFrame::PrimitiveArguments {
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
                        .apply(&primitive, &arguments)
                        .map_err(CoreMachineError::Primitive)?;
                    configuration.control = HostControl::Value(value);
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
        mut configuration: ConfigOf<P>,
        function: Value<P::Symbol, P::Atom, P::Primitive>,
        arguments: Vec<Value<P::Symbol, P::Atom, P::Primitive>>,
    ) -> Result<Option<ConfigOf<P>>, CoreMachineError<P::Symbol, P::Error>> {
        let HostValue::Closure(closure) = function.clone() else {
            return Err(CoreMachineError::NotCallable);
        };
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
                .map(|parameter| parameter.name.clone())
                .zip(arguments.iter().cloned()),
        );
        if let Some(rest) = &closure.rest {
            bindings.push((
                rest.name.clone(),
                HostValue::list(arguments.into_iter().skip(closure.parameters.len())),
            ));
        }
        let parent = if self.strategy.lexical_scope {
            &closure.environment
        } else {
            &configuration.environment
        };
        configuration.environment = parent.extend(bindings);
        configuration.control = HostControl::Expression(closure.body.clone());
        Ok(Some(configuration))
    }

    fn proper_list(
        mut value: Value<P::Symbol, P::Atom, P::Primitive>,
    ) -> Result<Vec<Value<P::Symbol, P::Atom, P::Primitive>>, CoreMachineError<P::Symbol, P::Error>>
    {
        let mut values = Vec::new();
        loop {
            match value {
                HostValue::Nil => return Ok(values),
                HostValue::Cons(head, tail) => {
                    values.push(*head);
                    value = *tail;
                }
                HostValue::Atom(_) | HostValue::Closure(_) => {
                    return Err(CoreMachineError::ImproperArgumentList);
                }
            }
        }
    }
}

impl<P: CorePrimitive> CoreMachine<P> {
    fn step_successors(
        &self,
        configuration: &ConfigOf<P>,
    ) -> Result<Vec<ConfigOf<P>>, CoreMachineError<P::Symbol, P::Error>> {
        let mut next = configuration.clone();
        let control = next.control.clone();
        match control {
            HostControl::Value(value) => self.continue_with(next, value),
            HostControl::Expression(expression) => {
                match expression {
                    CoreExpr::Literal(datum) | CoreExpr::Quote(datum) => {
                        next.control = HostControl::Value(HostValue::datum(datum));
                    }
                    CoreExpr::Truth(value) => {
                        next.control = HostControl::Value(self.primitives.truth(value));
                    }
                    CoreExpr::Variable(symbol) => {
                        let value = next
                            .environment
                            .lookup(&symbol)
                            .ok_or(CoreMachineError::UnboundVariable(symbol))?;
                        next.control = HostControl::Value(value);
                    }
                    CoreExpr::If {
                        condition,
                        consequent,
                        alternative,
                    } => {
                        next.continuation.push(HostFrame::If {
                            consequent: *consequent,
                            alternative: *alternative,
                            environment: next.environment.clone(),
                        });
                        next.control = HostControl::Expression(*condition);
                    }
                    CoreExpr::Cond { clauses } => {
                        let expression = clauses.into_iter().rev().fold(
                            CoreExpr::Literal(Datum::Nil),
                            |alternative, (condition, consequent)| CoreExpr::If {
                                condition: Box::new(condition),
                                consequent: Box::new(consequent),
                                alternative: Box::new(alternative),
                            },
                        );
                        next.control = HostControl::Expression(expression);
                    }
                    CoreExpr::Sequence { first, rest } => {
                        if !rest.is_empty() {
                            let mut remaining = rest;
                            remaining.reverse();
                            next.continuation.push(HostFrame::Sequence {
                                remaining,
                                environment: next.environment.clone(),
                            });
                        }
                        next.control = HostControl::Expression(*first);
                    }
                    CoreExpr::Lambda {
                        name,
                        parameters,
                        rest,
                        body,
                    } => {
                        next.control =
                            HostControl::Value(HostValue::Closure(Arc::new(HostClosure {
                                name,
                                parameters,
                                rest,
                                body: *body,
                                environment: next.environment.clone(),
                            })));
                    }
                    CoreExpr::Apply {
                        operator,
                        arguments,
                    } => {
                        let argument_count = arguments.len();
                        let mut parts = Vec::with_capacity(argument_count + 1);
                        parts.push(HostApplicationPart::Operator(*operator));
                        parts.extend(arguments.into_iter().enumerate().map(
                            |(index, expression)| HostApplicationPart::Argument {
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
                    CoreExpr::ApplyList {
                        operator,
                        mut arguments,
                        tail,
                    } => {
                        arguments.push(*tail);
                        let argument_count = arguments.len();
                        let mut parts = Vec::with_capacity(argument_count + 1);
                        parts.push(HostApplicationPart::Operator(*operator));
                        parts.extend(arguments.into_iter().enumerate().map(
                            |(index, expression)| HostApplicationPart::Argument {
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
                    CoreExpr::Let { bindings, body } => {
                        let parameters = bindings
                            .iter()
                            .map(|binding| Parameter::new(binding.name.clone()))
                            .collect();
                        let arguments = bindings.into_iter().map(|binding| binding.value).collect();
                        next.control = HostControl::Expression(CoreExpr::Apply {
                            operator: Box::new(CoreExpr::Lambda {
                                name: None,
                                parameters,
                                rest: None,
                                body,
                            }),
                            arguments,
                        });
                    }
                    CoreExpr::LetRec { bindings, body } => {
                        let environment = self.bind_recursive(
                            &next.environment,
                            bindings
                                .into_iter()
                                .map(|binding| (binding.name, binding.value))
                                .collect(),
                        )?;
                        next.environment = environment;
                        next.control = HostControl::Expression(*body);
                    }
                    CoreExpr::Primitive {
                        operator,
                        arguments,
                    } => {
                        if arguments.is_empty() {
                            let value = self
                                .primitives
                                .apply(&operator, &[])
                                .map_err(CoreMachineError::Primitive)?;
                            next.control = HostControl::Value(value);
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
                }
                Ok(vec![next])
            }
        }
    }
}

impl<P: CorePrimitive> DeterministicStep for CoreMachine<P> {
    fn next(&self, configuration: &ConfigOf<P>) -> Result<Option<ConfigOf<P>>, Self::Error> {
        let mut successors = self.step_successors(configuration)?;
        match successors.len() {
            0 => Ok(None),
            1 => Ok(successors.pop()),
            count => Err(CoreMachineError::NondeterministicSuccessors { count }),
        }
    }
}

impl<P: CorePrimitive> StepRelation for CoreMachine<P> {
    type Configuration = ConfigOf<P>;
    type Error = CoreMachineError<P::Symbol, P::Error>;

    fn successors(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        self.step_successors(configuration)
    }
}

impl<P: CorePrimitive> TerminalValue for CoreMachine<P> {
    type Value = Value<P::Symbol, P::Atom, P::Primitive>;

    fn terminal_value(&self, configuration: &Self::Configuration) -> Option<Self::Value> {
        configuration.terminal_value().cloned()
    }
}

/// Constructor-only implementation of [`LispSyntax`] for [`CoreExpr`].
#[derive(Clone, Copy, Debug, Default)]
pub struct CoreSyntax<S, A, P>(PhantomData<(S, A, P)>);

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
        type Error = &'static str;

        fn apply(
            &self,
            primitive: &Primitive,
            arguments: &[HostValue<&'static str, &'static str, Primitive>],
        ) -> Result<HostValue<&'static str, &'static str, Primitive>, Self::Error> {
            match (primitive, arguments) {
                (Primitive::Cons, [head, tail]) => Ok(HostValue::cons(head.clone(), tail.clone())),
                (Primitive::Car, [HostValue::Cons(head, _)]) => Ok((**head).clone()),
                (Primitive::Cdr, [HostValue::Cons(_, tail)]) => Ok((**tail).clone()),
                (Primitive::Null, [value]) => Ok(self.truth(matches!(value, HostValue::Nil))),
                _ => Err("bad primitive application"),
            }
        }

        fn truth(&self, value: bool) -> HostValue<&'static str, &'static str, Primitive> {
            if value {
                HostValue::Atom("t")
            } else {
                HostValue::Nil
            }
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
