//! Models of computation and the vocabulary used to realize them in HOL.
//!
//! @covalence-api {"id":"A0009","title":"Models of computation","status":"experimental","dependsOn":["A0001"]}
//!
//! This crate separates four concerns:
//!
//! - [`encoding`] gives values canonical bit and byte representations with
//!   strict decoders.
//! - the concrete model modules are plain, auditable program/configuration
//!   descriptions. Their evaluators are **proof search only**: a returned run
//!   is not a theorem.
//! - [`execution`] provides fuel-bounded search and trace collection.
//! - [`simulation`] is vocabulary for auditable simulation and equivalence
//!   witnesses. A value called a witness is data supplied by an implementation,
//!   not a theorem minted by this crate.
//!
//! The proof-bearing theory API is the primary consumer surface: a HOL backend
//! represents programs, inputs, states, step relations, and observations as its
//! own `Type`/`Term` carriers and replays search witnesses into kernel-checked
//! theorems.

#![forbid(unsafe_code)]

pub mod automata_theory;
pub mod blc;
pub mod compiler;
pub mod computability;
pub mod encoding;
pub mod execution;
pub mod finite;
pub mod minsky;
pub mod pushdown;
pub mod simulation;
pub mod ski;
pub mod theory;
pub mod turing;

pub use compiler::{
    CompilationArtifact, CompiledTerm, Compiler, CompilerLaws, CompilerReplayBackend,
    CompilerSearchWitness, ComposedArtifact, ComputationalEquivalence, DomainDecision,
    PartialCompilation, PartialCompiler, PartialCompilerLaws, SimulationVocabulary, StepMapping,
};
pub use computability::{
    ComputableEquivalence, ComputablePredicate, ComputablePredicateFacts, ComputableRelation,
    ComputableSet, DecidableSet, DecidableSetFacts, EnumerableSet, EnumerableSetFacts,
    HostComputationWitness, HostPartialFunction, ManyOneReduction, ManyOneReductionFacts,
    PartialCompilerComputabilityFacts, PartialCompilerTransport, PartialComposition,
    PartialCompositionFacts, PartialComputable, PartialComputableFacts, PartialFunction,
    RecognizableSet, RecognizableSetFacts, SymbolicComputability, SymbolicError, SymbolicLogic,
    TotalComposition, TotalCompositionFacts, TotalComputable, TotalComputableFacts,
};
pub use encoding::{
    BitCodec, BitDecode, BitEncode, ByteCodec, ByteDecode, ByteEncode, DecodeError, Decoder,
};
pub use execution::{
    ExecutionError, Machine, RunResult, Trace, TraceResult, TransitionSystem, run, trace,
};
pub use simulation::{
    EquivalenceWitness, Simulation, SimulationStep, SimulationWitness, StateRelation,
};
