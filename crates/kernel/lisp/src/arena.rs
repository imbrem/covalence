//! Resource-handle realization of the common Lisp runtime.
//!
//! Unlike [`crate::HostRuntime`], recursive values, closures, environments,
//! and recursive cells are stored in arenas and exposed only as small opaque
//! handles. This is the reference shape for a future WIT component boundary:
//! the evaluator uses exactly the same [`crate::LispMachine`] transition
//! algorithm while every recursive machine object crosses the boundary by
//! identity.

use core::convert::Infallible;
use core::fmt::{Debug, Display, Formatter};
use core::marker::PhantomData;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use covalence_sexpr_api::{Free, FreeSExpr};

use crate::host::{CoreSyntax, Datum};
use crate::runtime::{
    ClosureRecord, LispClosure, LispEnvironment, LispMachineValue, LispRecursiveEnvironment,
    LispRuntime, LispValue, RecursiveAllocation, RuntimeBinding, RuntimeValueLayer,
    RuntimeValueView,
};
use crate::syntax::CoreExpr;

static NEXT_ARENA_ID: AtomicUsize = AtomicUsize::new(1);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ResourceKind {
    Value,
    Closure,
    Environment,
    Cell,
}

/// Failure while resolving or mutating an opaque runtime resource.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArenaRuntimeError {
    ForeignHandle {
        resource: &'static str,
        expected_arena: usize,
        actual_arena: usize,
    },
    StaleHandle {
        resource: &'static str,
        index: usize,
    },
    RecursiveCellAlreadyInitialized,
}

impl Display for ArenaRuntimeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ForeignHandle {
                resource,
                expected_arena,
                actual_arena,
            } => write!(
                f,
                "{resource} handle belongs to arena {actual_arena}, expected {expected_arena}"
            ),
            Self::StaleHandle { resource, index } => {
                write!(f, "stale {resource} handle at index {index}")
            }
            Self::RecursiveCellAlreadyInitialized => {
                f.write_str("recursive environment cell was already initialized")
            }
        }
    }
}

impl core::error::Error for ArenaRuntimeError {}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ResourceHandle {
    arena: usize,
    index: usize,
    kind: ResourceKind,
}

impl Debug for ResourceHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}({}:{})", self.kind, self.arena, self.index)
    }
}

macro_rules! resource_handle {
    ($name:ident, $kind:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(ResourceHandle);

        impl Debug for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                self.0.fmt(f)
            }
        }

        impl $name {
            fn new(arena: usize, index: usize) -> Self {
                Self(ResourceHandle {
                    arena,
                    index,
                    kind: ResourceKind::$kind,
                })
            }
        }
    };
}

resource_handle!(ArenaValue, Value);
resource_handle!(ArenaClosure, Closure);
resource_handle!(ArenaEnvironment, Environment);
resource_handle!(ArenaRecursiveCell, Cell);

type ArenaExpr<S, A, P> = CoreExpr<S, Datum<A>, P>;
type ValueLayer<A, P> = RuntimeValueLayer<A, ArenaClosure, P, ArenaValue>;
type StoredClosure<S, A, P> = ClosureRecord<S, ArenaExpr<S, A, P>, ArenaEnvironment>;

#[derive(Clone, Debug)]
struct StoredCell {
    value: Option<ArenaValue>,
}

#[derive(Clone, Debug)]
struct Storage<S, A, P> {
    arena: usize,
    values: Vec<ValueLayer<A, P>>,
    closures: Vec<StoredClosure<S, A, P>>,
    environments: Vec<Vec<(S, usize)>>,
    cells: Vec<StoredCell>,
}

impl<S, A, P> Storage<S, A, P> {
    fn new() -> Self {
        Self {
            arena: NEXT_ARENA_ID.fetch_add(1, Ordering::Relaxed),
            values: Vec::new(),
            closures: Vec::new(),
            environments: vec![Vec::new()],
            cells: Vec::new(),
        }
    }

    fn check(
        &self,
        handle: ResourceHandle,
        kind: ResourceKind,
        len: usize,
    ) -> Result<usize, ArenaRuntimeError> {
        let resource = match kind {
            ResourceKind::Value => "value",
            ResourceKind::Closure => "closure",
            ResourceKind::Environment => "environment",
            ResourceKind::Cell => "cell",
        };
        if handle.arena != self.arena {
            return Err(ArenaRuntimeError::ForeignHandle {
                resource,
                expected_arena: self.arena,
                actual_arena: handle.arena,
            });
        }
        if handle.kind != kind || handle.index >= len {
            return Err(ArenaRuntimeError::StaleHandle {
                resource,
                index: handle.index,
            });
        }
        Ok(handle.index)
    }
}

type SharedStorage<S, A, P> = Rc<RefCell<Storage<S, A, P>>>;

/// Arena-backed runtime-value capability.
#[derive(Clone, Debug)]
pub struct ArenaValues<S, A, P> {
    storage: SharedStorage<S, A, P>,
}

impl<S, A, P> ArenaValues<S, A, P> {
    fn allocate(&self, layer: ValueLayer<A, P>) -> ArenaValue {
        let mut storage = self.storage.borrow_mut();
        let index = storage.values.len();
        storage.values.push(layer);
        ArenaValue::new(storage.arena, index)
    }

    fn layer(&self, value: &ArenaValue) -> Result<ValueLayer<A, P>, ArenaRuntimeError>
    where
        A: Clone,
        P: Clone,
    {
        let storage = self.storage.borrow();
        let index = storage.check(value.0, ResourceKind::Value, storage.values.len())?;
        Ok(storage.values[index].clone())
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
        if let RuntimeValueLayer::Cons { head, tail } = &layer {
            self.layer(head)?;
            self.layer(tail)?;
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
    storage: SharedStorage<S, A, P>,
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
        let mut storage = self.storage.borrow_mut();
        storage.check(
            record.environment.0,
            ResourceKind::Environment,
            storage.environments.len(),
        )?;
        let index = storage.closures.len();
        storage.closures.push(record);
        Ok(ArenaClosure::new(storage.arena, index))
    }

    fn open(
        &self,
        closure: &Self::Closure,
    ) -> Result<ClosureRecord<S, Self::Expr, Self::Environment>, Self::Error> {
        let storage = self.storage.borrow();
        let index = storage.check(closure.0, ResourceKind::Closure, storage.closures.len())?;
        Ok(storage.closures[index].clone())
    }
}

/// Arena-backed persistent lexical environments.
#[derive(Clone, Debug)]
pub struct ArenaEnvironments<S, A, P> {
    storage: SharedStorage<S, A, P>,
}

impl<S, A, P> ArenaEnvironments<S, A, P> {
    fn environment_bindings(
        &self,
        environment: &ArenaEnvironment,
    ) -> Result<Vec<(S, usize)>, ArenaRuntimeError>
    where
        S: Clone,
    {
        let storage = self.storage.borrow();
        let index = storage.check(
            environment.0,
            ResourceKind::Environment,
            storage.environments.len(),
        )?;
        Ok(storage.environments[index].clone())
    }
}

impl<S, A, P> LispEnvironment for ArenaEnvironments<S, A, P>
where
    S: Clone + PartialEq,
{
    type Symbol = S;
    type Value = ArenaValue;
    type Environment = ArenaEnvironment;
    type Error = ArenaRuntimeError;

    fn empty(&self) -> Self::Environment {
        let storage = self.storage.borrow();
        ArenaEnvironment::new(storage.arena, 0)
    }

    fn lookup(
        &self,
        environment: &Self::Environment,
        symbol: &S,
    ) -> Result<Option<Self::Value>, Self::Error> {
        let bindings = self.environment_bindings(environment)?;
        let storage = self.storage.borrow();
        for (name, cell) in bindings.iter().rev() {
            if name == symbol {
                return Ok(storage.cells[*cell].value);
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
        let mut storage = self.storage.borrow_mut();
        for binding in bindings {
            storage.check(binding.value.0, ResourceKind::Value, storage.values.len())?;
            let cell = storage.cells.len();
            storage.cells.push(StoredCell {
                value: Some(binding.value),
            });
            extended.push((binding.symbol, cell));
        }
        let index = storage.environments.len();
        storage.environments.push(extended);
        Ok(ArenaEnvironment::new(storage.arena, index))
    }
}

impl<S, A, P> LispRecursiveEnvironment for ArenaEnvironments<S, A, P>
where
    S: Clone + PartialEq,
{
    type Cell = ArenaRecursiveCell;

    fn reserve_recursive(
        &self,
        environment: &Self::Environment,
        symbols: Vec<S>,
    ) -> Result<RecursiveAllocation<Self::Environment, Self::Cell>, Self::Error> {
        let mut extended = self.environment_bindings(environment)?;
        let mut storage = self.storage.borrow_mut();
        let mut cells = Vec::with_capacity(symbols.len());
        for symbol in symbols {
            let index = storage.cells.len();
            storage.cells.push(StoredCell { value: None });
            extended.push((symbol, index));
            cells.push(ArenaRecursiveCell::new(storage.arena, index));
        }
        let environment_index = storage.environments.len();
        storage.environments.push(extended);
        Ok(RecursiveAllocation {
            environment: ArenaEnvironment::new(storage.arena, environment_index),
            cells,
        })
    }

    fn initialize_recursive(
        &self,
        cell: Self::Cell,
        value: Self::Value,
    ) -> Result<(), Self::Error> {
        let mut storage = self.storage.borrow_mut();
        let cell_index = storage.check(cell.0, ResourceKind::Cell, storage.cells.len())?;
        storage.check(value.0, ResourceKind::Value, storage.values.len())?;
        if storage.cells[cell_index].value.replace(value).is_some() {
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
        let storage = Rc::new(RefCell::new(Storage::new()));
        Self {
            data: Free::new(),
            values: ArenaValues {
                storage: Rc::clone(&storage),
            },
            expressions: CoreSyntax::default(),
            closures: ArenaClosures {
                storage: Rc::clone(&storage),
            },
            environments: ArenaEnvironments { storage },
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
