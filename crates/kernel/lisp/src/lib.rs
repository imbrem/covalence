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
// TODO(cov:lisp.acl2.admission-layer, severe): Lift the checked pointwise ACL2-carrier APPEND agreement seam to universal existence and uniqueness for admitted definitions, totalize only from those theorems, and retire shallow assumed equations.

#![forbid(unsafe_code)]

pub mod admission;
pub mod arena;
pub mod effect;
pub mod host;
pub mod relation;
pub mod resource;
pub mod runtime;
pub mod stack;
pub mod stack_effect;
pub mod stack_machine;
pub mod syntax;

pub use covalence_kernel_data as data;
pub use covalence_sexpr_api as sexpr;

pub use admission::{
    AdmissionPolicy, AdmissionReplay, AdmittedDefinition, Definition, EvaluationExistence,
    EvaluationUniqueness, ExecutionAdequacyReplay, ExistenceUniqueness, RecursiveCall,
    SourcedDefinition, TerminationCertificate, Totalization,
};
pub use arena::{
    ArenaClosure, ArenaClosures, ArenaEnvironment, ArenaEnvironments, ArenaRecursiveCell,
    ArenaRuntime, ArenaRuntimeError, ArenaValue, ArenaValues,
};
pub use effect::{
    EffectHandler, EffectReplay, EffectRequest, EffectResume, EffectRunError, EffectState,
    EffectSuspension, EffectSyntax, HandledEffect, HandledRun, handle_to_completion,
};
pub use host::{
    ArityExpectation, CoreMachine, CoreMachineError, CorePrimitive, CoreSyntax, Datum,
    HostClosures, HostConfiguration, HostControl, HostEnvironment, HostEnvironments, HostFrame,
    HostRuntime, HostValue, HostValues, LispMachine, MachineApplicationPart,
    MachineApplicationPosition, MachineConfiguration, MachineControl, MachineFrame,
};
pub use relation::{
    CheckedTrace, DeterministicStep, Evaluation, EvaluationDeterminacy, ExecutionError,
    Exploration, ExplorationBounds, MayEval, MayEvalReplay, StepRelation, TerminalValue,
    TraceReplay, TraceSoundness, evaluate, execute, explore,
};
pub use resource::{Resource, ResourceArena, ResourceError, ResourceTable};
pub use runtime::{
    ClosureRecord, LispClosure, LispEnvironment, LispMachineValue, LispRecursiveEnvironment,
    LispRuntime, LispValue, PrimitiveSemantics, RecursiveAllocation, RuntimeBinding,
    RuntimeDatumError, RuntimeValueCase, RuntimeValueLayer, RuntimeValueParameter,
    RuntimeValueView, inject_datum, project_datum, runtime_value_fixpoint,
};
pub use stack::{
    StackClosure, StackClosureRecord, StackConfiguration, StackContinuation, StackInstructionLayer,
    StackInstructionSyntax, StackInstructionView, StackMachineValue, StackPrimitiveSemantics,
    StackProgramSyntax, StackRuntime, StackValue, StackValueLayer, StackValueView,
};
pub use stack_effect::{
    StackEffectMachine, StackEffectMachineError, StackEffectRuntimeError, StackEffectSemantics,
    StackEffectState,
};
pub use stack_machine::{
    StackMachine, StackMachineError, StackRuntimeConfiguration, StackRuntimeInstruction,
    StackRuntimeMachineError,
};
pub use syntax::{
    Binding, CoreExpr, CoreExprLayer, EvaluationOrder, LispDialect, LispExpression, LispSyntax,
    Parameter, Strategy,
};
