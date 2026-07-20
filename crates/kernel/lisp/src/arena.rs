//! Resource-handle realization of the common Lisp runtime.
//!
//! Values, closures, environments, and recursive cells use the shared typed
//! resource tables from [`crate::resource`]. Quoted data remains the free
//! inductive S-expression backend. This combination models the eventual WIT
//! boundary while running the same [`crate::LispMachine`] transition code as
//! the direct Rust backend.

use core::convert::Infallible;
use core::fmt::{Display, Formatter};
use core::marker::PhantomData;

use covalence_sexpr_api::{Free, FreeSExpr};

use crate::host::Datum;
use crate::resource::{Resource, ResourceArena, ResourceError, ResourceTable};
use crate::runtime::{
    ClosureRecord, LispClosure, LispEnvironment, LispMachineValue, LispRecursiveEnvironment,
    LispRuntime, LispRuntimeSnapshot, LispValue, RecursiveAllocation, RuntimeBinding,
    RuntimeValueLayer, RuntimeValueView,
};
use crate::syntax::{CoreExprLayer, LispExpression, LispSyntax};

pub enum ArenaValueKind {}
pub enum ArenaClosureKind {}
pub enum ArenaEnvironmentKind {}
pub enum ArenaCellKind {}
pub enum ArenaExprKind {}

pub type ArenaValue = Resource<ArenaValueKind>;
pub type ArenaClosure = Resource<ArenaClosureKind>;
pub type ArenaEnvironment = Resource<ArenaEnvironmentKind>;
pub type ArenaRecursiveCell = Resource<ArenaCellKind>;
pub type ArenaExpr = Resource<ArenaExprKind>;

type StoredExpr<S, A, P> = CoreExprLayer<S, Datum<A>, P, ArenaExpr>;
type ValueLayer<A, P> = RuntimeValueLayer<A, ArenaClosure, P, ArenaValue>;
type StoredClosure<S> = ClosureRecord<S, ArenaExpr, ArenaEnvironment>;
type ExprTable<S, A, P> = ResourceTable<ArenaExprKind, StoredExpr<S, A, P>>;
type ValueTable<A, P> = ResourceTable<ArenaValueKind, ValueLayer<A, P>>;
type ClosureTable<S> = ResourceTable<ArenaClosureKind, StoredClosure<S>>;
type EnvironmentTable<S> = ResourceTable<ArenaEnvironmentKind, Vec<(S, ArenaRecursiveCell)>>;
type CellTable = ResourceTable<ArenaCellKind, Option<ArenaValue>>;

/// Failure while resolving or mutating an opaque runtime resource.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArenaRuntimeError {
    Resource(ResourceError),
    RecursiveCellAlreadyInitialized,
}

impl From<ResourceError> for ArenaRuntimeError {
    fn from(error: ResourceError) -> Self {
        Self::Resource(error)
    }
}

impl Display for ArenaRuntimeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Resource(error) => Display::fmt(error, f),
            Self::RecursiveCellAlreadyInitialized => {
                f.write_str("recursive environment cell was already initialized")
            }
        }
    }
}

impl core::error::Error for ArenaRuntimeError {}

/// Opaque expression-resource realization of the common Lisp syntax.
#[derive(Clone, Debug)]
pub struct ArenaSyntax<S, A, P> {
    expressions: ExprTable<S, A, P>,
}

impl<S, A, P> ArenaSyntax<S, A, P> {
    fn allocate(&self, layer: StoredExpr<S, A, P>) -> ArenaExpr {
        self.expressions.insert(layer)
    }
}

impl<S, A, P> LispExpression for ArenaSyntax<S, A, P>
where
    S: Clone,
    A: Clone,
    P: Clone,
{
    type Symbol = S;
    type Datum = Datum<A>;
    type Primitive = P;
    type Expr = ArenaExpr;
    type Error = ArenaRuntimeError;

    fn view(&self, expression: &Self::Expr) -> Result<StoredExpr<S, A, P>, Self::Error> {
        self.expressions.get_cloned(*expression).map_err(Into::into)
    }
}

impl<S, A, P> LispSyntax for ArenaSyntax<S, A, P>
where
    S: Clone,
    A: Clone,
    P: Clone,
{
    type Symbol = S;
    type Datum = Datum<A>;
    type Primitive = P;
    type Expr = ArenaExpr;
    type Error = ArenaRuntimeError;

    fn literal(&self, datum: Self::Datum) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Literal(datum)))
    }

    fn truth(&self, value: bool) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Truth(value)))
    }

    fn variable(&self, symbol: Self::Symbol) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Variable(symbol)))
    }

    fn quote(&self, datum: Self::Datum) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Quote(datum)))
    }

    fn if_then_else(
        &self,
        condition: Self::Expr,
        consequent: Self::Expr,
        alternative: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::If {
            condition,
            consequent,
            alternative,
        }))
    }

    fn cond(&self, clauses: Vec<(Self::Expr, Self::Expr)>) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Cond { clauses }))
    }

    fn sequence(
        &self,
        first: Self::Expr,
        rest: Vec<Self::Expr>,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Sequence { first, rest }))
    }

    fn lambda(
        &self,
        name: Option<Self::Symbol>,
        parameters: Vec<Self::Symbol>,
        rest: Option<Self::Symbol>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Lambda {
            name,
            parameters: parameters.into_iter().map(crate::Parameter::new).collect(),
            rest: rest.map(crate::Parameter::new),
            body,
        }))
    }

    fn apply(
        &self,
        operator: Self::Expr,
        arguments: Vec<Self::Expr>,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Apply {
            operator,
            arguments,
        }))
    }

    fn apply_list(
        &self,
        operator: Self::Expr,
        arguments: Vec<Self::Expr>,
        tail: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::ApplyList {
            operator,
            arguments,
            tail,
        }))
    }

    fn let_bind(
        &self,
        bindings: Vec<(Self::Symbol, Self::Expr)>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Let {
            bindings: bindings
                .into_iter()
                .map(|(name, value)| crate::Binding::new(name, value))
                .collect(),
            body,
        }))
    }

    fn let_rec(
        &self,
        bindings: Vec<(Self::Symbol, Self::Expr)>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::LetRec {
            bindings: bindings
                .into_iter()
                .map(|(name, value)| crate::Binding::new(name, value))
                .collect(),
            body,
        }))
    }

    fn primitive(
        &self,
        operator: Self::Primitive,
        arguments: Vec<Self::Expr>,
    ) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::Primitive {
            operator,
            arguments,
        }))
    }

    fn primitive_value(&self, operator: Self::Primitive) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::PrimitiveValue(operator)))
    }

    fn apply_list_procedure(&self) -> Result<Self::Expr, Self::Error> {
        Ok(self.allocate(CoreExprLayer::ApplyListProcedure))
    }
}

/// Arena-backed runtime-value capability.
#[derive(Clone, Debug)]
pub struct ArenaValues<S, A, P> {
    values: ValueTable<A, P>,
    closures: ClosureTable<S>,
}

impl<S, A, P> ArenaValues<S, A, P> {
    fn allocate(&self, layer: ValueLayer<A, P>) -> ArenaValue {
        self.values.insert(layer)
    }

    fn layer(&self, value: &ArenaValue) -> Result<ValueLayer<A, P>, ArenaRuntimeError>
    where
        A: Clone,
        P: Clone,
    {
        self.values.get_cloned(*value).map_err(Into::into)
    }

    fn equivalent_at(
        &self,
        left: &ArenaValue,
        right: &ArenaValue,
    ) -> Result<bool, ArenaRuntimeError>
    where
        A: Clone + PartialEq,
        P: Clone + PartialEq,
    {
        if left == right {
            return Ok(true);
        }
        Ok(match (self.layer(left)?, self.layer(right)?) {
            (RuntimeValueLayer::Atom(left), RuntimeValueLayer::Atom(right)) => left == right,
            (RuntimeValueLayer::Nil, RuntimeValueLayer::Nil)
            | (RuntimeValueLayer::ApplyListProcedure, RuntimeValueLayer::ApplyListProcedure) => {
                true
            }
            (
                RuntimeValueLayer::Cons {
                    head: left_head,
                    tail: left_tail,
                },
                RuntimeValueLayer::Cons {
                    head: right_head,
                    tail: right_tail,
                },
            ) => {
                self.equivalent_at(&left_head, &right_head)?
                    && self.equivalent_at(&left_tail, &right_tail)?
            }
            (RuntimeValueLayer::Closure(left), RuntimeValueLayer::Closure(right)) => left == right,
            (RuntimeValueLayer::Primitive(left), RuntimeValueLayer::Primitive(right)) => {
                left == right
            }
            _ => false,
        })
    }
}

impl<S, A, P> LispValue for ArenaValues<S, A, P>
where
    A: Clone + PartialEq,
    P: Clone + PartialEq,
{
    type Atom = A;
    type Primitive = P;
    type Value = ArenaValue;
    type Error = ArenaRuntimeError;

    fn atom(&self, atom: A) -> Result<Self::Value, Self::Error> {
        Ok(self.allocate(RuntimeValueLayer::Atom(atom)))
    }

    fn nil(&self) -> Self::Value {
        self.allocate(RuntimeValueLayer::Nil)
    }

    fn cons(&self, head: Self::Value, tail: Self::Value) -> Result<Self::Value, Self::Error> {
        self.layer(&head)?;
        self.layer(&tail)?;
        Ok(self.allocate(RuntimeValueLayer::Cons { head, tail }))
    }

    fn primitive(&self, primitive: P) -> Result<Self::Value, Self::Error> {
        Ok(self.allocate(RuntimeValueLayer::Primitive(primitive)))
    }

    fn apply_list_procedure(&self) -> Self::Value {
        self.allocate(RuntimeValueLayer::ApplyListProcedure)
    }

    fn view(
        &self,
        value: &Self::Value,
    ) -> Result<RuntimeValueView<A, P, Self::Value>, Self::Error> {
        Ok(match self.layer(value)? {
            RuntimeValueLayer::Atom(atom) => RuntimeValueView::Atom(atom),
            RuntimeValueLayer::Nil => RuntimeValueView::Nil,
            RuntimeValueLayer::Cons { head, tail } => RuntimeValueView::Cons { head, tail },
            RuntimeValueLayer::Closure(_) => RuntimeValueView::Closure,
            RuntimeValueLayer::Primitive(primitive) => RuntimeValueView::Primitive(primitive),
            RuntimeValueLayer::ApplyListProcedure => RuntimeValueView::ApplyListProcedure,
        })
    }

    fn equivalent(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error> {
        self.equivalent_at(left, right)
    }
}

impl<S, A, P> LispMachineValue for ArenaValues<S, A, P>
where
    A: Clone + PartialEq,
    P: Clone + PartialEq,
{
    type Closure = ArenaClosure;

    fn roll(&self, layer: ValueLayer<A, P>) -> Result<Self::Value, Self::Error> {
        match &layer {
            RuntimeValueLayer::Cons { head, tail } => {
                self.layer(head)?;
                self.layer(tail)?;
            }
            RuntimeValueLayer::Closure(closure) => {
                self.closures.contains(*closure)?;
            }
            _ => {}
        }
        Ok(self.allocate(layer))
    }

    fn unroll(&self, value: &Self::Value) -> Result<ValueLayer<A, P>, Self::Error> {
        self.layer(value)
    }
}

/// Arena-backed opaque closure capability.
#[derive(Clone, Debug)]
pub struct ArenaClosures<S> {
    closures: ClosureTable<S>,
    environments: EnvironmentTable<S>,
}

impl<S> LispClosure for ArenaClosures<S>
where
    S: Clone,
{
    type Symbol = S;
    type Expr = ArenaExpr;
    type Environment = ArenaEnvironment;
    type Closure = ArenaClosure;
    type Error = ArenaRuntimeError;

    fn close(
        &self,
        record: ClosureRecord<S, Self::Expr, Self::Environment>,
    ) -> Result<Self::Closure, Self::Error> {
        self.environments.contains(record.environment)?;
        Ok(self.closures.insert(record))
    }

    fn open(
        &self,
        closure: &Self::Closure,
    ) -> Result<ClosureRecord<S, Self::Expr, Self::Environment>, Self::Error> {
        self.closures.get_cloned(*closure).map_err(Into::into)
    }
}

/// Arena-backed persistent lexical environments.
#[derive(Clone, Debug)]
pub struct ArenaEnvironments<S, A, P> {
    values: ValueTable<A, P>,
    environments: EnvironmentTable<S>,
    cells: CellTable,
    empty: ArenaEnvironment,
}

impl<S, A, P> ArenaEnvironments<S, A, P> {
    fn environment_bindings(
        &self,
        environment: &ArenaEnvironment,
    ) -> Result<Vec<(S, ArenaRecursiveCell)>, ArenaRuntimeError>
    where
        S: Clone,
    {
        self.environments
            .get_cloned(*environment)
            .map_err(Into::into)
    }
}

impl<S, A, P> LispEnvironment for ArenaEnvironments<S, A, P>
where
    S: Clone + PartialEq,
    A: Clone,
    P: Clone,
{
    type Symbol = S;
    type Value = ArenaValue;
    type Environment = ArenaEnvironment;
    type Error = ArenaRuntimeError;

    fn empty(&self) -> Self::Environment {
        self.empty
    }

    fn lookup(
        &self,
        environment: &Self::Environment,
        symbol: &S,
    ) -> Result<Option<Self::Value>, Self::Error> {
        for (name, cell) in self.environment_bindings(environment)?.iter().rev() {
            if name == symbol {
                return self.cells.get_cloned(*cell).map_err(Into::into);
            }
        }
        Ok(None)
    }

    fn extend(
        &self,
        environment: &Self::Environment,
        bindings: Vec<RuntimeBinding<S, Self::Value>>,
    ) -> Result<Self::Environment, Self::Error> {
        let mut extended = self.environment_bindings(environment)?;
        for binding in bindings {
            self.values.contains(binding.value)?;
            let cell = self.cells.insert(Some(binding.value));
            extended.push((binding.symbol, cell));
        }
        Ok(self.environments.insert(extended))
    }
}

impl<S, A, P> LispRecursiveEnvironment for ArenaEnvironments<S, A, P>
where
    S: Clone + PartialEq,
    A: Clone,
    P: Clone,
{
    type Cell = ArenaRecursiveCell;

    fn reserve_recursive(
        &self,
        environment: &Self::Environment,
        symbols: Vec<S>,
    ) -> Result<RecursiveAllocation<Self::Environment, Self::Cell>, Self::Error> {
        let mut extended = self.environment_bindings(environment)?;
        let cells = symbols
            .into_iter()
            .map(|symbol| {
                let cell = self.cells.insert(None);
                extended.push((symbol, cell));
                cell
            })
            .collect();
        Ok(RecursiveAllocation {
            environment: self.environments.insert(extended),
            cells,
        })
    }

    fn initialize_recursive(
        &self,
        cell: Self::Cell,
        value: Self::Value,
    ) -> Result<(), Self::Error> {
        self.values.contains(value)?;
        let initialized = self
            .cells
            .update(cell, |slot| slot.replace(value).is_some())?;
        if initialized {
            return Err(ArenaRuntimeError::RecursiveCellAlreadyInitialized);
        }
        Ok(())
    }
}

/// Coherent resource-handle runtime with inductive S-expression data.
#[derive(Clone, Debug)]
pub struct ArenaRuntime<S, A, P> {
    data: Free<A>,
    values: ArenaValues<S, A, P>,
    expressions: ArenaSyntax<S, A, P>,
    closures: ArenaClosures<S>,
    environments: ArenaEnvironments<S, A, P>,
    _marker: PhantomData<(S, A, P)>,
}

impl<S, A, P> Default for ArenaRuntime<S, A, P> {
    fn default() -> Self {
        let arena = ResourceArena::new();
        let value_layers = arena.table("Lisp value");
        let expressions = arena.table("Lisp expression");
        let closures = arena.table("Lisp closure");
        let environments = arena.table("Lisp environment");
        let cells = arena.table("Lisp recursive cell");
        let empty = environments.insert(Vec::new());
        Self {
            data: Free::new(),
            values: ArenaValues {
                values: value_layers.clone(),
                closures: closures.clone(),
            },
            expressions: ArenaSyntax { expressions },
            closures: ArenaClosures {
                closures,
                environments: environments.clone(),
            },
            environments: ArenaEnvironments {
                values: value_layers.clone(),
                environments,
                cells,
                empty,
            },
            _marker: PhantomData,
        }
    }
}

impl<S, A, P> LispRuntimeSnapshot for ArenaRuntime<S, A, P>
where
    S: Clone + PartialEq,
    A: Clone + PartialEq,
    P: Clone + PartialEq,
{
    fn replay_snapshot(&self) -> Self {
        let values = self.values.values.snapshot();
        let expressions = self.expressions.expressions.snapshot();
        let closures = self.values.closures.snapshot();
        let environments = self.environments.environments.snapshot();
        let cells = self.environments.cells.snapshot();
        Self {
            data: self.data.clone(),
            values: ArenaValues {
                values: values.clone(),
                closures: closures.clone(),
            },
            expressions: ArenaSyntax { expressions },
            closures: ArenaClosures {
                closures,
                environments: environments.clone(),
            },
            environments: ArenaEnvironments {
                values,
                environments,
                cells,
                empty: self.environments.empty,
            },
            _marker: PhantomData,
        }
    }
}

impl<S, A, P> LispRuntime for ArenaRuntime<S, A, P>
where
    S: Clone + PartialEq,
    A: Clone + PartialEq,
    P: Clone + PartialEq,
{
    type Symbol = S;
    type Atom = A;
    type Datum = FreeSExpr<A>;
    type Primitive = P;
    type Expr = ArenaExpr;
    type Value = ArenaValue;
    type Closure = ArenaClosure;
    type Environment = ArenaEnvironment;
    type Error = ArenaRuntimeError;
    type Data = Free<A>;
    type Values = ArenaValues<S, A, P>;
    type Expressions = ArenaSyntax<S, A, P>;
    type Closures = ArenaClosures<S>;
    type Environments = ArenaEnvironments<S, A, P>;

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

    fn data_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn value_error(&self, error: ArenaRuntimeError) -> Self::Error {
        error
    }

    fn expression_error(&self, error: ArenaRuntimeError) -> Self::Error {
        error
    }

    fn syntax_error(&self, error: ArenaRuntimeError) -> Self::Error {
        error
    }

    fn closure_error(&self, error: ArenaRuntimeError) -> Self::Error {
        error
    }

    fn environment_error(&self, error: ArenaRuntimeError) -> Self::Error {
        error
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CoreExpr, LispRuntime, LispRuntimeSnapshot, import_core};

    type TestRuntime = ArenaRuntime<&'static str, &'static str, &'static str>;

    #[test]
    fn expression_resources_import_observe_snapshot_and_reject_foreign_handles() {
        let runtime = TestRuntime::default();
        let expression = CoreExpr::Apply {
            operator: Box::new(CoreExpr::Lambda {
                name: None,
                parameters: vec![crate::Parameter::new("x")],
                rest: None,
                body: Box::new(CoreExpr::Variable("x")),
            }),
            arguments: vec![CoreExpr::Quote(Datum::Atom("value"))],
        };
        let handle = import_core(runtime.expressions(), &expression).unwrap();
        assert!(matches!(
            runtime.expressions().view(&handle).unwrap(),
            CoreExprLayer::Apply { arguments, .. } if arguments.len() == 1
        ));

        let snapshot = runtime.replay_snapshot();
        assert!(matches!(
            snapshot.expressions().view(&handle).unwrap(),
            CoreExprLayer::Apply { arguments, .. } if arguments.len() == 1
        ));

        let foreign = TestRuntime::default();
        assert!(matches!(
            foreign.expressions().view(&handle),
            Err(ArenaRuntimeError::Resource(ResourceError::Foreign { .. }))
        ));
    }
}
