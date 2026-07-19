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
}
