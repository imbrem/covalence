//! The stable `AletheBridge` trait — the single boundary between Alethe
//! ingestion and any backend (HOL kernel, null kernel, future redesigns).
//!
//! The trait surface is intentionally **Alethe-shaped**, not kernel-shaped:
//! one method per top-level Alethe command (`assume`, `step`, `anchor`,
//! `define-fun`) plus the SMT-LIB problem-ingestion verbs (`declare-sort`,
//! `declare-fun`, `assert`).
//!
//! Sorts and terms are passed through as raw `SExpr` so the bridge owns the
//! syntax → semantics translation. Step references are passed through as
//! resolved `Self::Thm` values (the driver maintains the id → Thm map).

use covalence_sexp::SExpr;
use covalence_types::Decision;

use crate::error::BridgeError;

/// High-level Alethe ingestion API.
///
/// Each method handles one piece of an SMT-LIB problem + Alethe proof. The
/// driver ([`crate::ingest::ingest_alethe`]) iterates a problem and proof and
/// calls these methods in order. Implementations may stub any rule that hasn't
/// been wired through to the kernel by returning
/// [`BridgeError::NotImplemented`].
pub trait AletheBridge {
    /// Backend representation of a proven theorem (handle/index — must be `Copy`).
    type Thm: Copy + std::fmt::Debug;

    // -----------------------------------------------------------------
    // SMT-LIB problem ingestion
    // -----------------------------------------------------------------

    /// `(set-logic <name>)` — record the logic. Default: ignore.
    fn set_logic(&mut self, _logic: &str) -> Result<(), BridgeError> {
        Ok(())
    }

    /// `(declare-sort <name> <arity>)`.
    fn declare_sort(&mut self, name: &str, arity: u32) -> Result<(), BridgeError>;

    /// `(declare-fun <name> (<params>...) <sort>)`.
    /// `(declare-const <name> <sort>)` is normalised to params = `[]`.
    fn declare_fun(
        &mut self,
        name: &str,
        params: &[SExpr],
        sort: &SExpr,
    ) -> Result<(), BridgeError>;

    /// `(assert <term>)` — adds a problem-level hypothesis.
    fn assert(&mut self, term: &SExpr) -> Result<(), BridgeError>;

    // -----------------------------------------------------------------
    // Alethe proof commands
    // -----------------------------------------------------------------

    /// `(assume <id> <term>)` — introduce a fact as a hypothesis-theorem.
    fn assume(&mut self, id: &str, term: &SExpr) -> Result<Self::Thm, BridgeError>;

    /// `(step <id> (cl <lits>...) :rule <name> :premises (...) :args (...) :discharge (...))`.
    ///
    /// The driver pre-resolves `:premises` and `:discharge` ids into
    /// `Self::Thm` values. The bridge dispatches on `rule`.
    ///
    /// Returns the theorem that justifies the step's clause.
    fn step(
        &mut self,
        id: &str,
        clause: &[SExpr],
        rule: &str,
        premises: &[Self::Thm],
        args: &[SExpr],
        discharge: &[Self::Thm],
    ) -> Result<Self::Thm, BridgeError>;

    /// `(anchor :step <id> :args (<bindings>...))` — open a subproof scope.
    ///
    /// Default: return `NotImplemented("anchor")`. Subproof support is
    /// expected to evolve significantly under the hood.
    fn anchor(&mut self, _step: &str, _args: &[SExpr]) -> Result<(), BridgeError> {
        Err(BridgeError::NotImplemented("anchor".into()))
    }

    /// `(define-fun <name> (<params>...) <sort> <body>)` — definitional expansion.
    ///
    /// Default: return `NotImplemented("define-fun")`.
    fn define_fun(
        &mut self,
        _name: &str,
        _params: &[SExpr],
        _sort: &SExpr,
        _body: &SExpr,
    ) -> Result<(), BridgeError> {
        Err(BridgeError::NotImplemented("define-fun".into()))
    }

    // -----------------------------------------------------------------
    // Result
    // -----------------------------------------------------------------

    /// Final decision after the driver has finished. By convention:
    /// `Unsat` if the proof derived the empty clause; `Unknown` otherwise.
    fn decision(&self) -> Decision;
}
