//! # `covalence-kernel-sat` — generic SAT-proof replay into the kernel
//!
//! Re-derives a propositional refutation (DRAT / LRAT) through a pluggable
//! backend — the proof is untrusted data, and only the backend's kernel-backed
//! inference mints theorems, so this crate adds **zero TCB**. Companion to
//! `covalence-sat` (`crates/lib/sat`), which owns the SAT *formats*; the
//! propositional substrate `covalence-kernel-smt` reuses for the Boolean core.
//!
//! ## Three plug points
//!
//! The design separates *what a clause is*, *how a clause is proved*, and *how a
//! proof is replayed*, so lowering backends and replay strategies mix freely:
//!
//! - [`SatProblem`] — the **lowering**: SAT syntax (`Lit`/`Clause`) → a `Term` in
//!   some logic. Pure encoding, **no theorem**. The native impl reads a clause as
//!   a right-associated `∨` of boolean vars; a different logic (or a reflected
//!   `Clause` datatype) supplies its own.
//! - [`ClauseBackend`] — the **proof seam** (a `SatProblem` that also produces
//!   `Thm`s): assume an input clause, resolve two clauses, recognise the empty
//!   clause. This is where kernel inference happens.
//! - [`ReplayStrategy`] — **how** a `LratProof` is driven through a backend
//!   ([`RupReplay`] today; RAT-aware / verified-checker strategies plug in the
//!   same way).
//!
//! [`replay_lrat`] is the convenience entry point (`RupReplay` over the native
//! [`HolClauseBackend`]).

pub mod hol;

use std::collections::HashMap;

pub use covalence_sat::{Clause, Cnf, Lit, LratProof, Var};
pub use hol::HolClauseBackend;

/// Errors from replaying a SAT proof.
#[derive(Debug, thiserror::Error)]
pub enum ReplayError {
    /// A step referenced a clause id that is not active.
    #[error("SAT replay: undefined clause id {0}")]
    UndefinedClause(u64),
    /// The RUP antecedent chain did not reach a unit/conflict as claimed.
    #[error("SAT replay: RUP step {id} did not propagate to a conflict")]
    BadRup { id: u64 },
    /// The backend rejected an inference the replay constructed (a replay bug,
    /// not a kernel-soundness issue).
    #[error("SAT replay: backend rejected an inference: {0}")]
    Backend(String),
    /// A part of the replay not wired yet (e.g. RAT steps).
    #[error("SAT replay: not supported: {0}")]
    Unsupported(&'static str),
}

/// **Lowering**: how SAT syntax is rendered as a `Term` in a target logic —
/// pure encoding, producing no theorem. The Boolean vocabulary a proof is
/// stated over.
///
/// Splitting this out (a `Term`, not a `Thm`) lets a consumer render a clause or
/// the whole formula *without* proving anything — e.g. to state a goal, hash a
/// problem, or drive a different proof strategy over the same encoding.
pub trait SatProblem {
    /// The term representation of a proposition in the target logic.
    type Term;

    /// A literal as a term: the variable positively, its negation negatively.
    fn lit(&self, lit: Lit) -> Self::Term;

    /// A clause as a term — the disjunction of its literals. The **empty clause**
    /// is [`SatProblem::falsity`].
    fn clause(&self, clause: &Clause) -> Self::Term;

    /// Falsity `⊥` — the empty clause's term.
    fn falsity(&self) -> Self::Term;
}

/// **Proof seam**: a [`SatProblem`] lowering that also mints theorems through a
/// kernel. `assume_clause` enters an input clause as a hypothesis, `resolve`
/// resolves two proven clauses, and `is_empty_clause` recognises the refutation.
///
/// A backend declares no soundness obligation of its own — every `Thm` it mints
/// goes through the target kernel's trusted inference.
pub trait ClauseBackend: SatProblem {
    /// A proven clause.
    type Thm: Clone;

    /// Introduce an input clause as an assumed disjunction `⊢ C` (`C` among the
    /// problem's hypotheses). The refutation is genuine exactly when the final
    /// empty clause's hypotheses are a subset of the input clauses.
    fn assume_clause(&mut self, clause: &Clause) -> Result<Self::Thm, ReplayError>;

    /// Resolve two clause-theorems on their complementary literal, returning the
    /// resolvent (`⊢ ⊥` when they are a unit and its negation).
    fn resolve(&mut self, a: &Self::Thm, b: &Self::Thm) -> Result<Self::Thm, ReplayError>;

    /// Does this theorem prove the empty clause (falsity)?
    fn is_empty_clause(&self, thm: &Self::Thm) -> bool;
}

/// **Replay strategy**: how a parsed `LratProof` is driven through a
/// [`ClauseBackend`]. Generic over the backend, so any lowering works under any
/// strategy. [`RupReplay`] is the RUP strategy; RAT-aware and verified-checker
/// strategies implement the same trait.
pub trait ReplayStrategy {
    /// Replay `proof` (over `cnf`) through `backend`, returning the refutation
    /// `⊢ ⊥`.
    fn replay<B: ClauseBackend>(
        &self,
        backend: &mut B,
        cnf: &Cnf,
        proof: &LratProof,
    ) -> Result<B::Thm, ReplayError>;
}

/// The **RUP** (reverse-unit-propagation) strategy: seed the clause map with the
/// input CNF (DIMACS clause `k` → id `k+1`), then per `Add` step left-fold
/// [`ClauseBackend::resolve`] over the antecedent theorems in order — CaDiCaL's
/// RUP hints are a resolution chain whose resolvent is the step's clause; the
/// last is empty, giving `⊢ ⊥`. `Delete` retires ids.
///
/// Assumes each successive resolution has a unique complementary pair (so the
/// backend's own pivot-finding suffices) and that the proof is **RUP-only** —
/// RAT steps (negative antecedent hints) are not handled here; see `SKELETONS.md`.
pub struct RupReplay;

impl ReplayStrategy for RupReplay {
    fn replay<B: ClauseBackend>(
        &self,
        backend: &mut B,
        cnf: &Cnf,
        proof: &LratProof,
    ) -> Result<B::Thm, ReplayError> {
        use covalence_sat::LratStep;

        // Seed: DIMACS clause k (0-based) is LRAT id k+1.
        let mut clauses: HashMap<u64, B::Thm> = HashMap::new();
        for (i, clause) in cnf.clauses().enumerate() {
            clauses.insert((i + 1) as u64, backend.assume_clause(clause)?);
        }

        let get = |clauses: &HashMap<u64, B::Thm>, id: u64| -> Result<B::Thm, ReplayError> {
            clauses
                .get(&id)
                .cloned()
                .ok_or(ReplayError::UndefinedClause(id))
        };

        let mut last: Option<B::Thm> = None;
        let mut refutation: Option<B::Thm> = None;

        for step in proof.steps() {
            match step {
                LratStep::Add {
                    id, antecedents, ..
                } => {
                    let mut ants = antecedents.iter();
                    let first = *ants.next().ok_or(ReplayError::BadRup { id: *id })?;
                    let mut acc = get(&clauses, first)?;
                    for &a in ants {
                        let next = get(&clauses, a)?;
                        acc = backend.resolve(&acc, &next)?;
                    }
                    if refutation.is_none() && backend.is_empty_clause(&acc) {
                        refutation = Some(acc.clone());
                    }
                    last = Some(acc.clone());
                    clauses.insert(*id, acc);
                }
                LratStep::Delete { clause_ids, .. } => {
                    for id in clause_ids {
                        clauses.remove(id);
                    }
                }
            }
        }

        refutation
            .or(last)
            .ok_or(ReplayError::Unsupported("empty LRAT proof (no steps)"))
    }
}

/// Replay an LRAT proof through a clause backend with the default [`RupReplay`]
/// strategy, returning the final `⊢ ⊥`. Convenience over
/// `RupReplay.replay(backend, cnf, proof)`.
pub fn replay_lrat<B: ClauseBackend>(
    backend: &mut B,
    cnf: &Cnf,
    proof: &LratProof,
) -> Result<B::Thm, ReplayError> {
    RupReplay.replay(backend, cnf, proof)
}
