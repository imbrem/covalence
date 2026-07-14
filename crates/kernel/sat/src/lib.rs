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

pub mod hol;

use std::collections::HashMap;

pub use covalence_sat::{Clause, Cnf, Lit, Var};
pub use hol::HolClauseBackend;

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
/// LRAT is RUP-*with-hints*: each `Add { id, clause C, antecedents [a₁ … aₖ] }`
/// step's antecedents are a resolution chain (in propagation order) whose
/// combined resolvent is `C`. We build it by seeding a clause map with the input
/// CNF (DIMACS clause `k` → id `k+1`, via [`ClauseBackend::assume_clause`]) and,
/// per step, left-folding [`ClauseBackend::resolve`] over the antecedent
/// theorems in order: `R = clause(a₁); Rⱼ = resolve(Rⱼ₋₁, clause(aⱼ))`. The
/// resolvent is stored under `id`; the last step's `C` is empty, so `R` is
/// `⊢ ⊥`. `Delete` steps retire ids.
///
/// Returns the first empty-clause theorem derived (else the last step's
/// theorem). The caller checks its hypotheses are a subset of the assumed input
/// clauses — that is what makes it a genuine refutation.
///
/// The left-fold assumes each successive resolution has a *unique* complementary
/// pair (so [`ClauseBackend::resolve`]'s own pivot-finding suffices); this holds
/// for the reverse-unit-propagation chains CaDiCaL emits. A chain that needs an
/// explicit pivot (from unit-propagation simulation) is not yet handled — see
/// `SKELETONS.md`.
pub fn replay_lrat<B: ClauseBackend>(
    backend: &mut B,
    cnf: &Cnf,
    proof: &covalence_sat::LratProof,
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
        .ok_or(ReplayError::NotImplemented("empty LRAT proof (no steps)"))
}
