//! Evidence recorded by the three evaluators.
//!
//! Witnesses are untrusted **data**. They carry no theorem authority: a witness records
//! what an evaluator did, not that the record is correct, and nothing here is checked.
//!
//! The two nondeterminism witnesses are separate variants of separate types on purpose. An
//! ordered-choice witness carries a bounded negative control record (which earlier
//! alternatives were tried); a union witness carries none, because a relation has no notion
//! of "the other alternative failed". A witness therefore cannot be reinterpreted across
//! fragments.

use crate::syntax::Signature;
use covalence_parsing_api::Span;

/// Evidence for a core node. `R` is the recursive slot, tied per fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreWitness<S: Signature, R> {
    Pure {
        at: usize,
    },
    Prim {
        span: Span,
        witness: S::PrimitiveWitness,
    },
    Map {
        span: Span,
        inner: R,
    },
    Ap {
        span: Span,
        function: R,
        argument: R,
        split: usize,
    },
    /// `split` is the offset where the continuation was invoked. It is redundant with the
    /// sub-spans and is retained because the bind-associativity reassociation isomorphism
    /// is not definable without it — a span alone cannot recover the interior boundary.
    Bind {
        span: Span,
        head: R,
        continuation: R,
        split: usize,
    },
    Rule {
        rule: usize,
        span: Span,
        inner: R,
    },
}

impl<S: Signature, R> CoreWitness<S, R> {
    /// The extent this node consumed.
    pub fn span(&self) -> Span {
        match self {
            Self::Pure { at } => Span {
                start: *at,
                end: *at,
            },
            Self::Prim { span, .. }
            | Self::Map { span, .. }
            | Self::Ap { span, .. }
            | Self::Bind { span, .. }
            | Self::Rule { span, .. } => *span,
        }
    }
}

/// Evidence produced by [`TotalEvaluator`](crate::syntax::TotalEvaluator).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeterministicWitness<S: Signature>(pub CoreWitness<S, Box<DeterministicWitness<S>>>);

/// Evidence produced by [`PartialEvaluator`](crate::syntax::PartialEvaluator).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderedWitness<S: Signature> {
    Core(CoreWitness<S, Box<OrderedWitness<S>>>),
    /// `chosen` records that alternatives `0..chosen` were tried at this offset and none
    /// matched. That is a record of control flow, not a proof that they cannot match.
    OrderedChoice {
        chosen: usize,
        span: Span,
        inner: Box<OrderedWitness<S>>,
    },
}

/// Evidence produced by [`RelationalEvaluator`](crate::syntax::RelationalEvaluator).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelationalWitness<S: Signature> {
    Core(CoreWitness<S, Box<RelationalWitness<S>>>),
    /// `alternative` records only which branch produced *this* result. It says nothing
    /// about the others, which may have produced results of their own.
    Union {
        alternative: usize,
        span: Span,
        inner: Box<RelationalWitness<S>>,
    },
}

impl<S: Signature> DeterministicWitness<S> {
    pub fn span(&self) -> Span {
        self.0.span()
    }
}

impl<S: Signature> OrderedWitness<S> {
    pub fn span(&self) -> Span {
        match self {
            Self::Core(core) => core.span(),
            Self::OrderedChoice { span, .. } => *span,
        }
    }
}

impl<S: Signature> RelationalWitness<S> {
    pub fn span(&self) -> Span {
        match self {
            Self::Core(core) => core.span(),
            Self::Union { span, .. } => *span,
        }
    }
}
