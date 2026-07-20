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

use crate::host::{CoreSyntax, Datum};
use crate::resource::{Resource, ResourceArena, ResourceError, ResourceTable};
use crate::runtime::{
    ClosureRecord, LispClosure, LispEnvironment, LispMachineValue, LispRecursiveEnvironment,
    LispRuntime, LispRuntimeSnapshot, LispValue, RecursiveAllocation, RuntimeBinding,
    RuntimeValueLayer, RuntimeValueView,
};
use crate::syntax::CoreExpr;

pub enum ArenaValueKind {}
pub enum ArenaClosureKind {}
pub enum ArenaEnvironmentKind {}
pub enum ArenaCellKind {}

pub type ArenaValue = Resource<ArenaValueKind>;
pub type ArenaClosure = Resource<ArenaClosureKind>;
pub type ArenaEnvironment = Resource<ArenaEnvironmentKind>;
pub type ArenaRecursiveCell = Resource<ArenaCellKind>;

type ArenaExpr<S, A, P> = CoreExpr<S, Datum<A>, P>;
type ValueLayer<A, P> = RuntimeValueLayer<A, ArenaClosure, P, ArenaValue>;
type StoredClosure<S, A, P> = ClosureRecord<S, ArenaExpr<S, A, P>, ArenaEnvironment>;
type ValueTable<A, P> = ResourceTable<ArenaValueKind, ValueLayer<A, P>>;
type ClosureTable<S, A, P> = ResourceTable<ArenaClosureKind, StoredClosure<S, A, P>>;
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

/// Arena-backed runtime-value capability.
#[derive(Clone, Debug)]
pub struct ArenaValues<S, A, P> {
    values: ValueTable<A, P>,
    closures: ClosureTable<S, A, P>,
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
pub struct ArenaClosures<S, A, P> {
    closures: ClosureTable<S, A, P>,
    environments: EnvironmentTable<S>,
}

impl<S, A, P> LispClosure for ArenaClosures<S, A, P>
where
    S: Clone,
    A: Clone,
    P: Clone,
{
    type Symbol = S;
    type Expr = ArenaExpr<S, A, P>;
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
    expressions: CoreSyntax<S, A, P>,
    closures: ArenaClosures<S, A, P>,
    environments: ArenaEnvironments<S, A, P>,
    _marker: PhantomData<(S, A, P)>,
}

impl<S, A, P> Default for ArenaRuntime<S, A, P> {
    fn default() -> Self {
        let arena = ResourceArena::new();
        let value_layers = arena.table("Lisp value");
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
            expressions: CoreSyntax::default(),
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
        let closures = self.values.closures.snapshot();
        let environments = self.environments.environments.snapshot();
        let cells = self.environments.cells.snapshot();
        Self {
            data: self.data.clone(),
            values: ArenaValues {
                values: values.clone(),
                closures: closures.clone(),
            },
            expressions: self.expressions.clone(),
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
    type Expr = ArenaExpr<S, A, P>;
    type Value = ArenaValue;
    type Closure = ArenaClosure;
    type Environment = ArenaEnvironment;
    type Error = ArenaRuntimeError;
    type Data = Free<A>;
    type Values = ArenaValues<S, A, P>;
    type Expressions = CoreSyntax<S, A, P>;
    type Closures = ArenaClosures<S, A, P>;
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

    fn expression_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn syntax_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn closure_error(&self, error: ArenaRuntimeError) -> Self::Error {
        error
    }

    fn environment_error(&self, error: ArenaRuntimeError) -> Self::Error {
        error
    }
}
