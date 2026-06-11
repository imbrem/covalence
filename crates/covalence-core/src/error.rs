use smol_str::SmolStr;

use crate::term::Type;

/// Errors produced by Pure's typing and inference rules.
///
/// Term-shaped fields are carried as `String` (their `Display` form)
/// rather than concrete `Term<O>` values, so `Error` is *not* generic
/// over the observer type. This keeps error handling uniform across
/// kernels with different observer types and avoids leaking
/// observation data through error types.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("expected term of kind prop, got type {0}")]
    NotProp(Type),

    #[error("type mismatch: expected {expected}, got {got}")]
    TypeMismatch { expected: Type, got: Type },

    #[error("expected function type, got {0}")]
    NotFunction(Type),

    #[error("expected meta-implication (φ ⟹ ψ), got {0}")]
    NotMetaImp(String),

    #[error("expected meta-universal (⋀x:τ. body), got {0}")]
    NotMetaAll(String),

    #[error("expected meta-equality (t ≡ u), got {0}")]
    NotMetaEq(String),

    #[error("expected abstraction (λx:τ. body), got {0}")]
    NotAbs(String),

    #[error("expected application (f x), got {0}")]
    NotApp(String),

    #[error("implication antecedent {expected} does not match hypothesis {got}")]
    ImpAntecedentMismatch { expected: String, got: String },

    #[error("transitivity middle term mismatch: {left} vs {right}")]
    TransMiddleMismatch { left: String, right: String },

    #[error("free variable {name:?} occurs in hypotheses; cannot generalise")]
    FreeVarInHyps { name: SmolStr },

    #[error(
        "binder type {expected} for variable {name:?} does not match its \
         declared type {declared} in the theorem"
    )]
    BinderTypeMismatch {
        name: SmolStr,
        declared: Type,
        expected: Type,
    },

    #[error("η-conversion: body must be (app f (bound 0)) with bound 0 not free in f")]
    EtaShape,

    #[error("cannot cast observer type: term contains an Obs leaf")]
    ObsInCast,

    #[error("dynamic downcast failed: observation's runtime type does not match the target")]
    ObsDowncastTypeMismatch,

    #[error("expected an (obs ...) leaf at the head of {0}")]
    NotObsHead(String),

    #[error("observer's obs_eq method refused to equate the expressions")]
    ObsEqRefused,

    #[error("term has a dangling de Bruijn index (term is not closed at the kernel boundary)")]
    NotClosed,

    #[error(
        "free variable {name:?} declared at two different types in the same term \
         (first {first}, then {second})"
    )]
    FreeVarReuse {
        name: SmolStr,
        first: Type,
        second: Type,
    },

    #[error(
        "new_type_definition: witness conclusion must have shape `P x` with \
         P : α → prop and x : α; got {0}"
    )]
    BadTypeDefWitness(String),

    #[error(
        "define: body has free type variable {tvar:?} that does not appear \
         in the body's overall type {body_type} — this would yield a `Def` \
         whose visible instance type cannot pin down the body's interior \
         types under `inst_tfree`"
    )]
    DefPhantomTFree { tvar: SmolStr, body_type: Type },

    #[error("reduce_prim: term is not a primitive applied to literal arguments")]
    NotReducible,

    #[error("weaken: target context is not a superset of the theorem's hypotheses")]
    NotASuperset,

    #[error(
        "unfold_term_spec: term is not a TermKind::Spec applied to type args"
    )]
    NotASpec,

    #[error(
        "unfold_term_spec: spec carries no body (declaration-only), so it \
         cannot be unfolded"
    )]
    SpecHasNoBody,

    #[error(
        "unfold_term_spec: spec is def-style (its `tm` is a `ty → bool` \
         predicate, not the body itself); use a Hilbert-ε unfolding rule \
         instead"
    )]
    SpecIsDefStyle,

    #[error("concl_eq_parts: conclusion is not a Pure-meta equation")]
    NotAnEquation,
}

pub type Result<T> = std::result::Result<T, Error>;
