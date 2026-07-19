//! Combinator programs as data: the deterministic core and the three fragments.
//!
//! # Data equality does not determine semantics
//!
//! These types derive `PartialEq`/`Eq`, and that equality is **structural equality of the
//! program skeleton, not semantic equality of the parser**. Two [`Ordered`] values equal as
//! data denote different parsers under different environments, because [`Core::Rule`] and
//! [`Core::Bind`] resolve through the environment: `Rule(0)` names whatever the environment's
//! rule table has at index 0, and `Bind(_, k)` runs whatever program the environment's
//! resolver returns for the symbol `k`.
//!
//! Two consequences, both load-bearing:
//!
//! - **Content addressing a program addresses the skeleton, not the parser.** The
//!   environment's identity must be part of any content address, and supplying it is the
//!   caller's responsibility. This crate does not do it and does not claim it.
//! - **Every semantic law in this crate quantifies over `(program, environment)` pairs**,
//!   never over programs alone. In particular "a deterministic program is interpreted
//!   identically by all three fragments" is *false as stated* and holds only under the
//!   environment-coherence side condition documented on
//!   [`deterministic_into_ordered`](crate::syntax::deterministic_into_ordered).

use crate::syntax::Signature;

/// The deterministic core shared by all three fragments.
///
/// `R` is the recursive slot. Each fragment ties the knot at its own type, so a core node
/// built for one fragment can never reach another fragment's evaluator by coercion,
/// subtyping, or a blanket impl.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Core<S: Signature, R> {
    /// Succeeds consuming nothing.
    Pure(S::Value),
    /// An input-consuming leaf.
    Prim(S::Primitive),
    Map(S::Function, R),
    /// The function is *parsed*; left-to-right in the source.
    Ap(R, R),
    /// Value-dependent sequencing through a defunctionalized continuation symbol.
    Bind(R, S::Continuation),
    /// Reference to a named rule in the environment; the only structurally analysable
    /// form of recursion in this algebra.
    Rule(usize),
}

// TODO(cov:lang.combinator-parsing.static-well-formedness, major): Check map/ap arity and
// sort over the bind-free skeleton; the bind-crossing case is not decidable here. Until
// then the value universe is single-sorted and an ill-typed `Map`/`Ap` surfaces as
// `CombinatorEvalError::Environment` at run time rather than as a compile error.

/// Deterministic fragment: the core and nothing else. No failure operator.
///
/// This fragment is total or partial depending on *which environment interprets its
/// primitives*, not on its syntax. See the module table in [`crate::syntax`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Deterministic<S: Signature>(pub Core<S, Box<Deterministic<S>>>);

/// The core plus *ordered* choice: deterministic, left-biased, committing.
///
/// Once an alternative matches, later alternatives are never explored. This is a partial-
/// function notion. It is not [`Relational::Union`] and there is no conversion in either
/// direction (see [`crate::syntax::embed`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ordered<S: Signature> {
    Core(Core<S, Box<Ordered<S>>>),
    OrderedChoice(Vec<Ordered<S>>),
    /// The unit of `OrderedChoice`, equivalent to `OrderedChoice(vec![])`; named so that
    /// ordinary non-match is expressible as syntax rather than as an error.
    Fail,
}

/// The core plus *unordered* union: every alternative explored, every result retained.
///
/// Union is a free/multiset union: it is **not** idempotent (`union(p, p)` enumerates
/// `2n` results) and it is commutative only up to permutation. Deduplicating inside the
/// evaluator would destroy exactly the ambiguity retention this fragment exists for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Relational<S: Signature> {
    Core(Core<S, Box<Relational<S>>>),
    Union(Vec<Relational<S>>),
    /// The unit of `Union`, equivalent to `Union(vec![])`.
    Void,
}
