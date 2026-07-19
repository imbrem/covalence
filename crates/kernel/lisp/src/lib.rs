//! Backend-neutral capabilities for Lisp-family languages.
//!
//! This crate is the stable semantic waist between datatype representations
//! and concrete frontends such as Sector, Scheme, Forsp, and ACL2. It owns no
//! parser, proof search, event system, or theorem authority. A backend may
//! represent syntax and configurations as Rust data, inductive logic terms,
//! WASM resources, or another carrier while exposing the same capability
//! tower.
//!
//! The tower deliberately separates:
//!
//! 1. S-expression-shaped data;
//! 2. Lisp syntax and lexical environments;
//! 3. one-step operational relations and evaluation strategies;
//! 4. finite trace witnesses and their checked replay; and
//! 5. optional proof-producing soundness capabilities.
//!
//! @covalence-api {"id":"A0022","title":"Lisp operational semantics","status":"experimental","dependsOn":["A0001","A0004","A0005","A0014","A0021"]}
// TODO(cov:lisp.frontends.scheme-forsp, major): Add a proof-producing Forsp backend and cross-check it against the host stack machine.
// TODO(cov:lisp.acl2.admission-layer, severe): Prove existence and uniqueness from common partial Lisp execution, replay them into conservative ACL2 HOL definitions, and retire shallow assumed equations.

#![forbid(unsafe_code)]

pub mod admission;
pub mod effect;
pub mod host;
pub mod relation;
pub mod runtime;
pub mod stack;
pub mod syntax;

pub use covalence_kernel_data as data;
pub use covalence_sexpr_api as sexpr;

pub use admission::{
    AdmissionPolicy, AdmissionReplay, AdmittedDefinition, Definition, ExistenceUniqueness,
    RecursiveCall, TerminationCertificate, Totalization,
};
pub use effect::{
    EffectHandler, EffectReplay, EffectRequest, EffectResume, EffectRunError, EffectState,
    EffectSuspension, EffectSyntax, HandledEffect, HandledRun, handle_to_completion,
};
pub use host::{
    ArityExpectation, CoreMachine, CoreMachineError, CorePrimitive, CoreSyntax, Datum,
    HostConfiguration, HostControl, HostEnvironment, HostEnvironments, HostFrame, HostValue,
    HostValues,
};
pub use relation::{
    CheckedTrace, DeterministicStep, Evaluation, EvaluationDeterminacy, ExecutionError,
    Exploration, ExplorationBounds, MayEval, MayEvalReplay, StepRelation, TerminalValue,
    TraceReplay, TraceSoundness, evaluate, execute, explore,
};
pub use runtime::{
    LispEnvironment, LispValue, PrimitiveSemantics, RuntimeBinding, RuntimeDatumError,
    RuntimeValueView, inject_datum, project_datum,
};
pub use stack::{
    StackConfiguration, StackContinuation, StackInstructionSyntax, StackProgramSyntax,
};
pub use syntax::{
    Binding, CoreExpr, EvaluationOrder, LispDialect, LispSyntax, Parameter, Strategy,
};
