//! # `covalence-kernel-sat` — generic SAT-proof replay into the kernel
//!
//! Re-derives a propositional refutation (DRAT / LRAT) through a **clause
//! backend** — the proof is untrusted data, and only the backend's kernel-backed
//! inference mints theorems, so this crate adds **zero TCB**. It is the
//! kernel-facing companion to `covalence-sat` (`crates/lib/sat`), which owns the
//! SAT *formats* (DIMACS / DRAT / LRAT parsing + verdict-only checkers), and the
//! propositional substrate that `covalence-kernel-smt` reuses for the Boolean
//! core of an SMT proof.
//!
//! ## The seam
//!
//! [`ClauseBackend`] abstracts "a logic in which a CNF clause is a theorem and
//! resolution is an inference". The native HOL backend reads a clause as a
//! right-associated `∨` of literals and resolves via `covalence_init::init::logic`;
//! a different target logic supplies its own impl. [`replay_lrat`] drives a
//! backend through an LRAT proof, turning each RUP step's antecedent hints into
//! resolution steps and returning the final `⊢ ⊥`.
//!
//! LRAT (not bare DRAT) is the replay entry point because its steps already
//! carry the per-step antecedent list a resolution replay needs; a plain DRAT
//! proof must first be elaborated to LRAT (e.g. by `drat-trim`) or have its
//! propagation recomputed. See `SKELETONS.md`.

pub use covalence_sat::{Clause, Cnf, Lit, Var};

/// Errors from replaying a SAT proof through a [`ClauseBackend`].
#[derive(Debug, thiserror::Error)]
pub enum ReplayError {
    /// A step referenced a clause id that is not active.
    #[error("SAT replay: undefined clause id {0}")]
    UndefinedClause(u64),
    /// The RUP antecedent chain did not reach a unit/conflict as claimed.
    #[error("SAT replay: RUP step {id} did not propagate to a conflict")]
    BadRup { id: u64 },
    /// The backend rejected a resolution the replay constructed (a replay bug,
    /// not a kernel-soundness issue).
    #[error("SAT replay: backend rejected a resolution: {0}")]
    Backend(String),
    /// A part of the replay that is not wired yet.
    #[error("SAT replay: not implemented: {0}")]
    NotImplemented(&'static str),
}

/// A logic in which a propositional clause is a theorem and resolution is an
/// inference — the backend a SAT proof is replayed through.
///
/// The associated `Thm` is a backend theorem whose conclusion is the clause
/// (read as a disjunction of literals; the empty clause is falsity). Every
/// method that mints a `Thm` does so through the backend's trusted kernel API;
/// this trait declares no soundness obligation of its own.
pub trait ClauseBackend {
    /// A proven clause.
    type Thm: Clone;

    /// Introduce an input CNF clause as an assumed disjunction: `⊢ C` with `C`
    /// among the problem's hypotheses. (The refutation is valid exactly when the
    /// final empty clause's hypotheses are a subset of the input clauses.)
    fn assume_clause(&mut self, clause: &Clause) -> Result<Self::Thm, ReplayError>;

    /// Resolve two clause-theorems on their unique complementary literal,
    /// returning the resolvent (the empty clause `⊢ ⊥` when they are a unit and
    /// its negation).
    fn resolve(&mut self, a: &Self::Thm, b: &Self::Thm) -> Result<Self::Thm, ReplayError>;

    /// Does this theorem prove the empty clause (falsity)?
    fn is_empty_clause(&self, thm: &Self::Thm) -> bool;
}

/// Replay an LRAT proof through a clause backend, returning the final `⊢ ⊥`.
///
/// Algorithm (per RUP-with-hints step `id : clause C, antecedents [a₁ … aₖ]`):
/// assume the negation of `C`, unit-propagate through the antecedent clauses in
/// order (each must become unit or falsified under the running assignment),
/// then read off the reverse propagation order as a resolution chain deriving
/// `C` from the antecedents. `Delete` steps retire clause ids. The proof is
/// complete when a step derives the empty clause.
///
/// Not yet wired — the RUP→resolution-chain extraction is the next module (it is
/// pure and backend-independent, mirroring the `farkas` certificate check in
/// `covalence-kernel-smt`). See `SKELETONS.md`.
pub fn replay_lrat<B: ClauseBackend>(
    _backend: &mut B,
    _cnf: &Cnf,
    _proof: &covalence_sat::LratProof,
) -> Result<B::Thm, ReplayError> {
    Err(ReplayError::NotImplemented(
        "LRAT RUP→resolution replay (see SKELETONS.md)",
    ))
}
