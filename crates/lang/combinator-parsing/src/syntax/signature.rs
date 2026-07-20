//! The caller-supplied first-order symbol bundle a combinator program is written over.

/// The caller-supplied first-order signature a combinator program is written over.
///
/// `Self` is a marker; all content is in the associated types. Requiring the associated
/// types to be plain data is what lets the syntax and witness types use `#[derive]`: the
/// derives emit only `S: Clone`-style bounds on the type parameter, and the associated-type
/// bounds declared here are what discharge the field obligations.
///
/// `Value: PartialEq + Eq` exists for the derives, so that a program is comparable data.
/// It is a *host* equality and no conformance signature in this crate uses it: law checks
/// take a caller-supplied agreement (see `morphism::agreement`). Do not reach for `==` on
/// values in a law.
pub trait Signature: Clone + core::fmt::Debug + PartialEq + Eq {
    /// Source alphabet element.
    type Atom: Clone + core::fmt::Debug + PartialEq + Eq;
    /// The single-sorted value universe. Untyped: without GADTs, `Map`/`Ap` cannot be
    /// type-indexed, so an ill-typed application is an environment error at run time.
    type Value: Clone + core::fmt::Debug + PartialEq + Eq;
    /// Input-consuming primitive symbols. Primitives are deterministic: all nondeterminism
    /// in this algebra is explicit syntax.
    type Primitive: Clone + core::fmt::Debug + PartialEq + Eq;
    /// Defunctionalized value-function symbols, usable by `Core::Map`.
    type Function: Clone + core::fmt::Debug + PartialEq + Eq;
    /// Defunctionalized continuation symbols, usable by `Core::Bind`.
    type Continuation: Clone + core::fmt::Debug + PartialEq + Eq;
    /// Evidence recorded by a primitive match. Data; no theorem authority.
    type PrimitiveWitness: Clone + core::fmt::Debug + PartialEq + Eq;
}
