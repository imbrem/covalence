//! Executable host-data realization of the common Lisp core.
//!
//! This backend is deliberately proof-free. It is useful for frontend tests,
//! trace discovery, differential testing, and as an executable specification
//! for proof-producing backends.

use core::fmt::{Debug, Display, Formatter};
use core::marker::PhantomData;
use std::sync::{Arc, OnceLock};

use crate::relation::{DeterministicStep, StepRelation, TerminalValue};
use crate::syntax::{Binding, CoreExpr, LispSyntax, Parameter};

// TODO(cov:lisp.core.relational-strategies, major): Add nondeterministic evaluation-context backends for relational operand order and unspecified choices.

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
    pub body: Expr<S, A, P>,
    pub environment: Environment<S, A, P>,
}

/// Runtime values of the host realization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostValue<S, A, P> {
    Datum(Datum<A>),
    Closure(Arc<HostClosure<S, A, P>>),
}

impl<S, A, P> HostValue<S, A, P> {
    pub fn datum(datum: Datum<A>) -> Self {
        Self::Datum(datum)
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Self::Datum(Datum::Nil))
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
    ApplyOperator {
        arguments: Vec<Expr<S, A, P>>,
        environment: Environment<S, A, P>,
    },
    ApplyArguments {
        function: Value<S, A, P>,
        evaluated: Vec<Value<S, A, P>>,
        remaining: Vec<Expr<S, A, P>>,
        environment: Environment<S, A, P>,
    },
    PrimitiveArguments {
        primitive: P,
        evaluated: Vec<Value<S, A, P>>,
        remaining: Vec<Expr<S, A, P>>,
        environment: Environment<S, A, P>,
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreMachineError<S, E> {
    UnboundVariable(S),
    DuplicateRecursiveBinding(S),
    InvalidRecursiveInitializer(S),
    NotCallable,
    Arity { expected: usize, actual: usize },
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
            Self::NotCallable => f.write_str("attempted to apply a non-closure value"),
            Self::Arity { expected, actual } => {
                write!(f, "arity mismatch: expected {expected}, got {actual}")
            }
            Self::Primitive(error) => write!(f, "primitive operation failed: {error:?}"),
        }
    }
}

impl<S: Debug, E: Debug> core::error::Error for CoreMachineError<S, E> {}

/// Strict, left-to-right host realization of the common Lisp core.
#[derive(Clone, Debug)]
pub struct CoreMachine<P> {
    primitives: P,
}

impl<P> CoreMachine<P> {
    pub fn new(primitives: P) -> Self {
        Self { primitives }
    }

    pub fn primitives(&self) -> &P {
        &self.primitives
    }
}

type ConfigOf<P> = HostConfiguration<
    <P as CorePrimitive>::Symbol,
    <P as CorePrimitive>::Atom,
    <P as CorePrimitive>::Primitive,
>;

impl<P: CorePrimitive> CoreMachine<P> {
    fn continue_with(
        &self,
        mut configuration: ConfigOf<P>,
        value: Value<P::Symbol, P::Atom, P::Primitive>,
    ) -> Result<Option<ConfigOf<P>>, CoreMachineError<P::Symbol, P::Error>> {
        let Some(frame) = configuration.continuation.pop() else {
            return Ok(None);
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
            HostFrame::ApplyOperator {
                mut arguments,
                environment,
            } => {
                if arguments.is_empty() {
                    return self.apply(configuration, value, Vec::new());
                }
                let first = arguments.remove(0);
                configuration.continuation.push(HostFrame::ApplyArguments {
                    function: value,
                    evaluated: Vec::new(),
                    remaining: arguments,
                    environment: environment.clone(),
                });
                configuration.control = HostControl::Expression(first);
                configuration.environment = environment;
            }
            HostFrame::ApplyArguments {
                function,
                mut evaluated,
                mut remaining,
                environment,
            } => {
                evaluated.push(value);
                if remaining.is_empty() {
                    return self.apply(configuration, function, evaluated);
                }
                let first = remaining.remove(0);
                configuration.continuation.push(HostFrame::ApplyArguments {
                    function,
                    evaluated,
                    remaining,
                    environment: environment.clone(),
                });
                configuration.control = HostControl::Expression(first);
                configuration.environment = environment;
            }
            HostFrame::PrimitiveArguments {
                primitive,
                mut evaluated,
                mut remaining,
                environment,
            } => {
                evaluated.push(value);
                if remaining.is_empty() {
                    let value = self
                        .primitives
                        .apply(&primitive, &evaluated)
                        .map_err(CoreMachineError::Primitive)?;
                    configuration.control = HostControl::Value(value);
                } else {
                    let first = remaining.remove(0);
                    configuration
                        .continuation
                        .push(HostFrame::PrimitiveArguments {
                            primitive,
                            evaluated,
                            remaining,
                            environment: environment.clone(),
                        });
                    configuration.control = HostControl::Expression(first);
                    configuration.environment = environment;
                }
            }
        }
        Ok(Some(configuration))
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
        if closure.parameters.len() != arguments.len() {
            return Err(CoreMachineError::Arity {
                expected: closure.parameters.len(),
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
                .zip(arguments),
        );
        configuration.environment = closure.environment.extend(bindings);
        configuration.control = HostControl::Expression(closure.body.clone());
        Ok(Some(configuration))
    }
}

impl<P: CorePrimitive> DeterministicStep for CoreMachine<P> {
    fn next(&self, configuration: &ConfigOf<P>) -> Result<Option<ConfigOf<P>>, Self::Error> {
        let mut next = configuration.clone();
        let control = next.control.clone();
        match control {
            HostControl::Value(value) => self.continue_with(next, value),
            HostControl::Expression(expression) => {
                match expression {
                    CoreExpr::Literal(datum) | CoreExpr::Quote(datum) => {
                        next.control = HostControl::Value(HostValue::Datum(datum));
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
                    CoreExpr::Lambda {
                        name,
                        parameters,
                        body,
                    } => {
                        next.control =
                            HostControl::Value(HostValue::Closure(Arc::new(HostClosure {
                                name,
                                parameters,
                                body: *body,
                                environment: next.environment.clone(),
                            })));
                    }
                    CoreExpr::Apply {
                        operator,
                        arguments,
                    } => {
                        next.continuation.push(HostFrame::ApplyOperator {
                            arguments,
                            environment: next.environment.clone(),
                        });
                        next.control = HostControl::Expression(*operator);
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
                                body,
                            }),
                            arguments,
                        });
                    }
                    CoreExpr::LetRec { bindings, body } => {
                        for (index, binding) in bindings.iter().enumerate() {
                            if bindings[..index]
                                .iter()
                                .any(|earlier| earlier.name == binding.name)
                            {
                                return Err(CoreMachineError::DuplicateRecursiveBinding(
                                    binding.name.clone(),
                                ));
                            }
                            if !matches!(binding.value, CoreExpr::Lambda { .. }) {
                                return Err(CoreMachineError::InvalidRecursiveInitializer(
                                    binding.name.clone(),
                                ));
                            }
                        }
                        let cells: Vec<_> = bindings
                            .iter()
                            .map(|binding| (binding.name.clone(), HostBindingCell::uninitialized()))
                            .collect();
                        let environment = next.environment.extend_cells(cells.clone());
                        for (binding, (_, cell)) in bindings.into_iter().zip(cells) {
                            let CoreExpr::Lambda {
                                name,
                                parameters,
                                body,
                            } = binding.value
                            else {
                                unreachable!("recursive initializers validated above")
                            };
                            let closure = HostValue::Closure(Arc::new(HostClosure {
                                name,
                                parameters,
                                body: *body,
                                environment: environment.clone(),
                            }));
                            cell.initialize(closure)
                                .expect("fresh recursive binding cell");
                        }
                        next.environment = environment;
                        next.control = HostControl::Expression(*body);
                    }
                    CoreExpr::Primitive {
                        operator,
                        mut arguments,
                    } => {
                        if arguments.is_empty() {
                            let value = self
                                .primitives
                                .apply(&operator, &[])
                                .map_err(CoreMachineError::Primitive)?;
                            next.control = HostControl::Value(value);
                        } else {
                            let first = arguments.remove(0);
                            next.continuation.push(HostFrame::PrimitiveArguments {
                                primitive: operator,
                                evaluated: Vec::new(),
                                remaining: arguments,
                                environment: next.environment.clone(),
                            });
                            next.control = HostControl::Expression(first);
                        }
                    }
                }
                Ok(Some(next))
            }
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
        Ok(self.next(configuration)?.into_iter().collect())
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

    fn lambda(
        &self,
        name: Option<Self::Symbol>,
        parameters: Vec<Self::Symbol>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(CoreExpr::Lambda {
            name,
            parameters: parameters.into_iter().map(Parameter::new).collect(),
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
    use crate::relation::{Evaluation, evaluate, execute};

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
                (Primitive::Cons, [HostValue::Datum(head), HostValue::Datum(tail)]) => {
                    Ok(HostValue::Datum(Datum::cons(head.clone(), tail.clone())))
                }
                (Primitive::Car, [HostValue::Datum(Datum::Cons(head, _))]) => {
                    Ok(HostValue::Datum((**head).clone()))
                }
                (Primitive::Cdr, [HostValue::Datum(Datum::Cons(_, tail))]) => {
                    Ok(HostValue::Datum((**tail).clone()))
                }
                (Primitive::Null, [HostValue::Datum(datum)]) => {
                    Ok(self.truth(matches!(datum, Datum::Nil)))
                }
                _ => Err("bad primitive application"),
            }
        }

        fn truth(&self, value: bool) -> HostValue<&'static str, &'static str, Primitive> {
            HostValue::Datum(if value { Datum::Atom("t") } else { Datum::Nil })
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
        assert_eq!(
            trace.end().terminal_value(),
            Some(&HostValue::Datum(Datum::Atom("head")))
        );
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
            HostValue::Datum(Datum::Atom("answer")),
            "the observed value comes from the terminal machine configuration"
        );
        assert_eq!(result.trace.steps(), 1);
    }

    #[test]
    fn named_closure_supports_partial_recursive_semantics() {
        let identity = CoreExpr::Lambda {
            name: Some("self"),
            parameters: vec![Parameter::new("x")],
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
            Some(&HostValue::Datum(Datum::Atom("value")))
        );
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
            body: Box::new(CoreExpr::If {
                condition: Box::new(null(CoreExpr::Variable("xs"))),
                consequent: Box::new(CoreExpr::Truth(true)),
                alternative: Box::new(call("odd", cdr(CoreExpr::Variable("xs")))),
            }),
        };
        let odd = CoreExpr::Lambda {
            name: None,
            parameters: vec![Parameter::new("xs")],
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
        assert_eq!(result.value, HostValue::Datum(Datum::Atom("t")));
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
