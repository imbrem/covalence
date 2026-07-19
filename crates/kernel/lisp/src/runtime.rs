//! Backend-neutral runtime values and lexical environments.
//!
//! Quoted data uses the inductive S-expression API. Runtime values add
//! procedures and permit pairs containing procedures, so they form a distinct
//! recursive domain. These capabilities expose that domain without requiring
//! a backend to use the Rust [`crate::HostValue`] representation.
//!
//! The signatures deliberately use owned handles and finite vectors so a
//! monomorphized version can project to WIT resources.
//!
//! @covalence-api {"id":"A0026","title":"Lisp runtime values and environments","status":"experimental","dependsOn":["A0005","A0022"]}

use covalence_kernel_data::inductive::{
    FieldSpec, FixpointSpec, PolynomialSpec, Position, Validated, VariantCase,
};
use covalence_sexpr_api::{SExprF, SExprSyntax, SExprView};

/// External parameter sorts of the canonical Lisp runtime-value functor.
///
/// A backend supplies representations for these three leaves, while recursive
/// pair fields refer to the runtime-value carrier itself. Closures remain
/// opaque machine resources; the datatype schema does not grant clients a way
/// to forge their captured code or environment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuntimeValueParameter {
    Atom,
    Closure,
    Primitive,
}

/// Constructor tags of the canonical runtime-value fixpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuntimeValueCase {
    Atom,
    Nil,
    Cons,
    Closure,
    Primitive,
    ApplyListProcedure,
}

impl RuntimeValueCase {
    pub const ALL: [Self; 6] = [
        Self::Atom,
        Self::Nil,
        Self::Cons,
        Self::Closure,
        Self::Primitive,
        Self::ApplyListProcedure,
    ];

    pub const fn name(self) -> &'static str {
        match self {
            Self::Atom => "atom",
            Self::Nil => "nil",
            Self::Cons => "cons",
            Self::Closure => "closure",
            Self::Primitive => "primitive",
            Self::ApplyListProcedure => "apply-list-procedure",
        }
    }
}

/// The canonical polynomial declaration of Lisp runtime values.
///
/// In functor notation:
///
/// `ValueF X = Atom + 1 + X×X + Closure + Primitive + 1`.
///
/// Taking its least fixpoint permits procedures inside pairs while keeping
/// ordinary quoted S-expressions as the procedure-free subobject. Backends can
/// realize this declaration through `data/inductive`; [`LispValue`] is the
/// capability-sized constructor/observer interface over such a realization.
pub fn runtime_value_fixpoint() -> Validated<FixpointSpec<RuntimeValueParameter>> {
    use RuntimeValueParameter::{Atom, Closure, Primitive};

    Validated::try_from(FixpointSpec::new(
        "lisp-value",
        PolynomialSpec::new(
            "lisp-value-f",
            vec![
                VariantCase::new(
                    RuntimeValueCase::Atom.name(),
                    vec![FieldSpec::new("value", Position::Param(Atom))],
                ),
                VariantCase::nullary(RuntimeValueCase::Nil.name()),
                VariantCase::new(
                    RuntimeValueCase::Cons.name(),
                    vec![
                        FieldSpec::new("head", Position::Var),
                        FieldSpec::new("tail", Position::Var),
                    ],
                ),
                VariantCase::new(
                    RuntimeValueCase::Closure.name(),
                    vec![FieldSpec::new("value", Position::Param(Closure))],
                ),
                VariantCase::new(
                    RuntimeValueCase::Primitive.name(),
                    vec![FieldSpec::new("value", Position::Param(Primitive))],
                ),
                VariantCase::nullary(RuntimeValueCase::ApplyListProcedure.name()),
            ],
        ),
    ))
    .expect("the fixed Lisp runtime-value declaration is valid")
}

/// One observable layer of a Lisp runtime value.
///
/// Closures are opaque: their captured environment and code are machine
/// internals. A caller may retain or apply the original `Value` handle but
/// cannot forge a closure from this view.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeValueView<A, P, V> {
    Atom(A),
    Nil,
    Cons { head: V, tail: V },
    Closure,
    Primitive(P),
    ApplyListProcedure,
}

impl<A, P, V> RuntimeValueView<A, P, V> {
    pub const fn case(&self) -> RuntimeValueCase {
        match self {
            Self::Atom(_) => RuntimeValueCase::Atom,
            Self::Nil => RuntimeValueCase::Nil,
            Self::Cons { .. } => RuntimeValueCase::Cons,
            Self::Closure => RuntimeValueCase::Closure,
            Self::Primitive(_) => RuntimeValueCase::Primitive,
            Self::ApplyListProcedure => RuntimeValueCase::ApplyListProcedure,
        }
    }
}

/// Construction and one-layer observation of runtime values.
pub trait LispValue {
    type Atom: Clone;
    type Primitive: Clone;
    type Value: Clone;
    type Error;

    fn atom(&self, atom: Self::Atom) -> Result<Self::Value, Self::Error>;
    fn nil(&self) -> Self::Value;
    fn cons(&self, head: Self::Value, tail: Self::Value) -> Result<Self::Value, Self::Error>;
    fn primitive(&self, primitive: Self::Primitive) -> Result<Self::Value, Self::Error>;
    fn apply_list_procedure(&self) -> Self::Value;
    fn view(
        &self,
        value: &Self::Value,
    ) -> Result<RuntimeValueView<Self::Atom, Self::Primitive, Self::Value>, Self::Error>;

    fn list(
        &self,
        values: impl IntoIterator<Item = Self::Value>,
    ) -> Result<Self::Value, Self::Error> {
        let values: Vec<_> = values.into_iter().collect();
        let mut result = self.nil();
        for value in values.into_iter().rev() {
            result = self.cons(value, result)?;
        }
        Ok(result)
    }

    /// Observe a finite proper list, rejecting atoms, procedures, closures,
    /// and dotted tails.
    fn as_list(&self, value: &Self::Value) -> Result<Option<Vec<Self::Value>>, Self::Error> {
        let mut values = Vec::new();
        let mut cursor = value.clone();
        loop {
            match self.view(&cursor)? {
                RuntimeValueView::Nil => return Ok(Some(values)),
                RuntimeValueView::Cons { head, tail } => {
                    values.push(head);
                    cursor = tail;
                }
                RuntimeValueView::Atom(_)
                | RuntimeValueView::Closure
                | RuntimeValueView::Primitive(_)
                | RuntimeValueView::ApplyListProcedure => return Ok(None),
            }
        }
    }
}

/// Meaning of a primitive vocabulary over an abstract runtime-value backend.
///
/// Primitive semantics receives the value capability explicitly. It therefore
/// cannot rely on a concrete Rust enum and can be reused by handle-based HOL
/// or WIT realizations.
pub trait PrimitiveSemantics<V: LispValue> {
    type Error;

    fn apply(
        &self,
        values: &V,
        primitive: &V::Primitive,
        arguments: &[V::Value],
    ) -> Result<V::Value, Self::Error>;

    fn truth(&self, values: &V, value: bool) -> Result<V::Value, Self::Error>;

    fn is_false(&self, values: &V, value: &V::Value) -> Result<bool, Self::Error>;
}

/// Error while transporting between inductive data and runtime values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeDatumError<D, V> {
    Datum(D),
    Value(V),
}

/// Inject an abstract inductive S-expression into a runtime-value backend.
pub fn inject_datum<D, V>(
    data: &D,
    values: &V,
    datum: &D::Value,
) -> Result<V::Value, RuntimeDatumError<D::Error, V::Error>>
where
    D: SExprView,
    V: LispValue<Atom = D::Payload>,
{
    match data.view(datum).map_err(RuntimeDatumError::Datum)? {
        SExprF::Atom(atom) => values.atom(atom).map_err(RuntimeDatumError::Value),
        SExprF::Nil => Ok(values.nil()),
        SExprF::Cons { head, tail } => {
            let head = inject_datum(data, values, &head)?;
            let tail = inject_datum(data, values, &tail)?;
            values.cons(head, tail).map_err(RuntimeDatumError::Value)
        }
    }
}

/// Project a runtime value to an abstract inductive S-expression.
///
/// Returns `None` exactly when a closure or primitive procedure occurs
/// anywhere in the value.
pub fn project_datum<D, V>(
    data: &D,
    values: &V,
    value: &V::Value,
) -> Result<Option<D::Value>, RuntimeDatumError<D::Error, V::Error>>
where
    D: SExprSyntax<Payload = V::Atom>,
    V: LispValue,
{
    Ok(
        match values.view(value).map_err(RuntimeDatumError::Value)? {
            RuntimeValueView::Atom(atom) => {
                Some(data.atom(atom).map_err(RuntimeDatumError::Datum)?)
            }
            RuntimeValueView::Nil => Some(data.nil()),
            RuntimeValueView::Cons { head, tail } => {
                let Some(head) = project_datum(data, values, &head)? else {
                    return Ok(None);
                };
                let Some(tail) = project_datum(data, values, &tail)? else {
                    return Ok(None);
                };
                Some(data.cons(head, tail).map_err(RuntimeDatumError::Datum)?)
            }
            RuntimeValueView::Closure
            | RuntimeValueView::Primitive(_)
            | RuntimeValueView::ApplyListProcedure => None,
        },
    )
}

/// One lexical binding used by [`LispEnvironment::extend`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeBinding<S, V> {
    pub symbol: S,
    pub value: V,
}

impl<S, V> RuntimeBinding<S, V> {
    pub fn new(symbol: S, value: V) -> Self {
        Self { symbol, value }
    }
}

/// Persistent lexical-environment construction and lookup.
///
/// Recursive allocation is intentionally a separate machine capability:
/// ordinary consumers cannot forge uninitialized cells.
pub trait LispEnvironment {
    type Symbol: Clone;
    type Value: Clone;
    type Environment: Clone;
    type Error;

    fn empty(&self) -> Self::Environment;
    fn lookup(
        &self,
        environment: &Self::Environment,
        symbol: &Self::Symbol,
    ) -> Result<Option<Self::Value>, Self::Error>;
    fn extend(
        &self,
        environment: &Self::Environment,
        bindings: Vec<RuntimeBinding<Self::Symbol, Self::Value>>,
    ) -> Result<Self::Environment, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HostEnvironments, HostValue, HostValues};
    use covalence_sexpr_api::{Free, FreeSExpr};

    type Value = HostValue<&'static str, &'static str, &'static str>;

    fn pair_through_capability<V>(values: &V, head: V::Value, tail: V::Value) -> V::Value
    where
        V: LispValue,
        V::Error: core::fmt::Debug,
    {
        values.cons(head, tail).unwrap()
    }

    #[test]
    fn host_values_realize_the_abstract_runtime_domain() {
        let values = HostValues::<&str, &str, &str>::default();
        let atom = values.atom("payload").unwrap();
        let primitive = values.primitive("procedure").unwrap();
        let list = values.list([atom.clone(), primitive.clone()]).unwrap();

        assert_eq!(
            values.as_list(&list).unwrap(),
            Some(vec![atom.clone(), primitive])
        );
        assert_eq!(
            pair_through_capability(&values, atom, values.nil()),
            HostValue::cons(HostValue::Atom("payload"), HostValue::Nil)
        );
    }

    #[test]
    fn host_environments_realize_persistent_lexical_extension() {
        let environments = HostEnvironments::<&str, Value>::default();
        let empty = environments.empty();
        let extended = environments
            .extend(
                &empty,
                vec![RuntimeBinding::new("x", HostValue::Atom("value"))],
            )
            .unwrap();

        assert_eq!(environments.lookup(&empty, &"x").unwrap(), None);
        assert_eq!(
            environments.lookup(&extended, &"x").unwrap(),
            Some(HostValue::Atom("value"))
        );
    }

    #[test]
    fn inductive_data_round_trips_through_runtime_values() {
        let data = Free::<&str>::new();
        let values = HostValues::<&str, &str, &str>::default();
        let datum = FreeSExpr::Cons(
            Box::new(FreeSExpr::Atom("head")),
            Box::new(FreeSExpr::Atom("dotted-tail")),
        );

        let runtime = inject_datum(&data, &values, &datum).unwrap();
        assert_eq!(
            project_datum(&data, &values, &runtime).unwrap(),
            Some(datum)
        );

        let procedure = values.primitive("cons").unwrap();
        let contains_procedure = values.list([procedure]).unwrap();
        assert_eq!(
            project_datum(&data, &values, &contains_procedure).unwrap(),
            None
        );
    }

    #[test]
    fn runtime_values_have_one_checked_polynomial_shape() {
        let spec = runtime_value_fixpoint();
        assert_eq!(spec.name.as_str(), "lisp-value");
        assert_eq!(
            spec.functor
                .variants
                .iter()
                .map(|case| case.name.as_str())
                .collect::<Vec<_>>(),
            RuntimeValueCase::ALL.map(RuntimeValueCase::name)
        );
        assert_eq!(
            spec.functor.variants[2]
                .fields
                .iter()
                .map(|field| &field.position)
                .collect::<Vec<_>>(),
            [&Position::Var, &Position::Var]
        );
        assert!(spec.functor.is_recursive());

        let values = HostValues::<&str, &str, &str>::default();
        assert_eq!(
            values.view(&HostValue::Atom("value")).unwrap().case(),
            RuntimeValueCase::Atom
        );
        assert_eq!(
            values
                .view(&HostValue::Primitive("procedure"))
                .unwrap()
                .case(),
            RuntimeValueCase::Primitive
        );
    }
}
