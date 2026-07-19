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
    /// A primitive must be a forward step inside the source: the returned `end` must satisfy
    /// `at <= end <= source.len()`. This is **checked, not assumed** — every evaluator runs
    /// the extent through
    /// [`check_primitive_extent`](crate::budget::check_primitive_extent) and reports a
    /// violation as `CombinatorEvalError::PrimitiveExtent`, the same way the host encoding's
    /// `check_step` reports a `CursorViolation`. An environment is caller-supplied, so an
    /// unchecked precondition here is a way for a caller to abort the process or to hand a
    /// consumer a span outside the source.
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

#[cfg(test)]
pub(super) mod fixtures {
    //! Environments shared by the three syntax evaluators' own test modules, so the three
    //! cannot drift apart on the things they must agree about.
    //!
    //! [`HostileEnv`] is deliberately ill-behaved: it violates [`SignatureEnv::step`]'s
    //! forward-step precondition, which is a caller-supplied input and therefore something
    //! every evaluator has to survive.

    use super::{OrderedEnv, PrimitiveMatch, RelationalEnv, SignatureEnv, TotalEnv};
    use crate::syntax::{Core, Deterministic, Ordered, Relational, Signature};

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(crate) struct Bytes;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) struct Never;

    impl Signature for Bytes {
        type Atom = u8;
        type Value = u8;
        type Primitive = u8;
        type Function = ();
        type Continuation = ();
        type PrimitiveWitness = ();
    }

    /// The two ways an environment-supplied extent can be impossible.
    #[derive(Clone, Copy, Debug)]
    pub(crate) enum Extent {
        /// A backwards step: `end < at`.
        Backwards,
        /// Past the end of the source: `end > source.len()`.
        PastEnd,
    }

    /// Reports a match at `Extent` from wherever it is invoked, always.
    pub(crate) struct HostileEnv(pub Extent);

    impl HostileEnv {
        fn matched(&self, source: &[u8], at: usize) -> PrimitiveMatch<Bytes> {
            PrimitiveMatch {
                value: 0,
                witness: (),
                end: match self.0 {
                    Extent::Backwards => at.saturating_sub(1),
                    Extent::PastEnd => source.len() + 100,
                },
            }
        }
    }

    impl SignatureEnv<Bytes> for HostileEnv {
        type Error = Never;

        fn apply_function(&self, _function: &(), argument: u8) -> Result<u8, Never> {
            Ok(argument)
        }

        fn apply_value(&self, _function: u8, argument: u8) -> Result<u8, Never> {
            Ok(argument)
        }

        fn step(
            &self,
            _primitive: &u8,
            source: &[u8],
            at: usize,
        ) -> Result<Option<PrimitiveMatch<Bytes>>, Never> {
            Ok(Some(self.matched(source, at)))
        }
    }

    impl TotalEnv<Bytes> for HostileEnv {
        fn total_step(
            &self,
            _primitive: &u8,
            source: &[u8],
            at: usize,
        ) -> Result<PrimitiveMatch<Bytes>, Never> {
            Ok(self.matched(source, at))
        }

        fn total_rule(&self, _rule: usize) -> Option<&Deterministic<Bytes>> {
            None
        }

        fn total_resolve(
            &self,
            _continuation: &(),
            value: &u8,
        ) -> Result<Deterministic<Bytes>, Never> {
            Ok(Deterministic(Core::Pure(*value)))
        }
    }

    impl OrderedEnv<Bytes> for HostileEnv {
        fn ordered_rule(&self, _rule: usize) -> Option<&Ordered<Bytes>> {
            None
        }

        fn ordered_resolve(&self, _continuation: &(), value: &u8) -> Result<Ordered<Bytes>, Never> {
            Ok(Ordered::Core(Core::Pure(*value)))
        }
    }

    impl RelationalEnv<Bytes> for HostileEnv {
        fn relational_rule(&self, _rule: usize) -> Option<&Relational<Bytes>> {
            None
        }

        fn relational_resolve(
            &self,
            _continuation: &(),
            value: &u8,
        ) -> Result<Relational<Bytes>, Never> {
            Ok(Relational::Core(Core::Pure(*value)))
        }
    }

    /// A well-behaved environment whose primitives never match, for programs built only
    /// from `Pure`, `Void` and the operators over them.
    pub(crate) struct PureEnv;

    impl SignatureEnv<Bytes> for PureEnv {
        type Error = Never;

        fn apply_function(&self, _function: &(), argument: u8) -> Result<u8, Never> {
            Ok(argument)
        }

        fn apply_value(&self, _function: u8, argument: u8) -> Result<u8, Never> {
            Ok(argument)
        }

        fn step(
            &self,
            _primitive: &u8,
            _source: &[u8],
            _at: usize,
        ) -> Result<Option<PrimitiveMatch<Bytes>>, Never> {
            Ok(None)
        }
    }

    impl RelationalEnv<Bytes> for PureEnv {
        fn relational_rule(&self, _rule: usize) -> Option<&Relational<Bytes>> {
            None
        }

        fn relational_resolve(
            &self,
            _continuation: &(),
            value: &u8,
        ) -> Result<Relational<Bytes>, Never> {
            Ok(Relational::Core(Core::Pure(*value)))
        }
    }
}
