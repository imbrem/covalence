//! Caller-supplied environments: what a program's symbols actually mean.
//!
//! Method names are **distinct per fragment** (`ordered_rule`, `relational_rule`, …) on
//! purpose. A single `rule`/`resolve` name across the three traits makes `env.rule(0)`
//! ambiguous (E0034) under any `where E: OrderedEnv<S> + RelationalEnv<S>` bound, which
//! would force every cross-fragment law into UFCS.

use crate::syntax::{Deterministic, Ordered, Relational, Signature};

/// A successful primitive step. `end` is the offset after the match.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimitiveMatch<S: Signature> {
    pub value: S::Value,
    pub witness: S::PrimitiveWitness,
    pub end: usize,
}

/// Value semantics shared by all fragments. Object safe.
pub trait SignatureEnv<S: Signature> {
    type Error;

    fn apply_function(
        &self,
        function: &S::Function,
        argument: S::Value,
    ) -> Result<S::Value, Self::Error>;

    /// Apply a *parsed* value as a function, for `Ap`. Partial: applying a non-function is
    /// an ill-formed program, i.e. evaluator failure, never a non-match.
    fn apply_value(&self, function: S::Value, argument: S::Value) -> Result<S::Value, Self::Error>;

    /// Run a primitive. `Ok(None)` is ordinary non-match.
    ///
    /// A primitive must be a forward step: the returned `end` must satisfy `end >= at`.
    fn step(
        &self,
        primitive: &S::Primitive,
        source: &[S::Atom],
        at: usize,
    ) -> Result<Option<PrimitiveMatch<S>>, Self::Error>;
}

/// Total interpretation of the deterministic fragment.
///
/// `total_step` has no `Option`: an implementation *cannot* report non-match. That is the
/// structural content of "total", and it is why there is no `TotalPrimitives` marker.
/// Totality is still modulo resources — budget exhaustion and undefined rules are `Err` —
/// exactly the posture of A0015's own `TotalParser`.
pub trait TotalEnv<S: Signature>: SignatureEnv<S> {
    fn total_step(
        &self,
        primitive: &S::Primitive,
        source: &[S::Atom],
        at: usize,
    ) -> Result<PrimitiveMatch<S>, Self::Error>;
    fn total_rule(&self, rule: usize) -> Option<&Deterministic<S>>;
    fn total_resolve(
        &self,
        continuation: &S::Continuation,
        value: &S::Value,
    ) -> Result<Deterministic<S>, Self::Error>;
}

/// Ordered (partial) interpretation.
pub trait OrderedEnv<S: Signature>: SignatureEnv<S> {
    fn ordered_rule(&self, rule: usize) -> Option<&Ordered<S>>;
    /// A symbol the environment does not know is `Err` (evaluator failure). A continuation
    /// that should *not* match resolves to `Ordered::Fail`.
    fn ordered_resolve(
        &self,
        continuation: &S::Continuation,
        value: &S::Value,
    ) -> Result<Ordered<S>, Self::Error>;
}

/// Relational interpretation.
pub trait RelationalEnv<S: Signature>: SignatureEnv<S> {
    fn relational_rule(&self, rule: usize) -> Option<&Relational<S>>;
    /// A continuation that should yield nothing resolves to `Relational::Void`.
    fn relational_resolve(
        &self,
        continuation: &S::Continuation,
        value: &S::Value,
    ) -> Result<Relational<S>, Self::Error>;
}

// PERF(cov:lang.combinator-parsing.continuation-allocation, minor): Environment resolve
// allocates a fresh program per bind step; measure before switching to Rc<Ordered<S>>.
