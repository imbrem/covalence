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
pub mod sequent;

use std::collections::{HashMap, HashSet};

pub use covalence_sat::{Clause, Cnf, Lit, LratProof, Var};
pub use hol::HolClauseBackend;
pub use sequent::SequentClauseBackend;

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

    /// Resolve two clause-theorems on their first complementary literal.
    /// Ambiguous when the clauses share several complementary pairs — RUP replay
    /// uses [`ClauseBackend::resolve_on`] with a computed pivot instead.
    fn resolve(&mut self, a: &Self::Thm, b: &Self::Thm) -> Result<Self::Thm, ReplayError>;

    /// Resolve `a` and `b` on an explicit pivot **variable** — one clause carries
    /// it positively, the other negatively. This is what RUP replay drives (the
    /// pivot per resolution step is the literal a unit clause propagates), since
    /// [`ClauseBackend::resolve`]'s first-pair search is ambiguous on real proofs.
    fn resolve_on(
        &mut self,
        a: &Self::Thm,
        b: &Self::Thm,
        pivot: Var,
    ) -> Result<Self::Thm, ReplayError>;

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

/// The **RUP** (reverse-unit-propagation) strategy — proper trace-based
/// reconstruction. For each `Add` step deriving clause `C` with ordered
/// antecedent hints `a₁ … aₖ`: falsify `C` (assign every literal of `C` false),
/// then unit-propagate the antecedents in order, recording the literal each one
/// forces (its pivot), until one antecedent is fully falsified (the conflict).
/// The resolution proof is then read off **backwards** from the conflict clause,
/// resolving against each propagating clause on its pivot variable — a genuine
/// resolution derivation of `C`. The last step's `C` is empty, giving `⊢ ⊥`.
///
/// This is what real CaDiCaL proofs need: their chains have steps with several
/// complementary pairs, so the *pivot must be computed* (via propagation), not
/// guessed by a first-complementary-pair search. Handles **RUP-only** proofs
/// (run CaDiCaL with `--plain`); RAT steps are a separate strategy — see
/// `SKELETONS.md`.
pub struct RupReplay;

impl ReplayStrategy for RupReplay {
    fn replay<B: ClauseBackend>(
        &self,
        backend: &mut B,
        cnf: &Cnf,
        proof: &LratProof,
    ) -> Result<B::Thm, ReplayError> {
        use covalence_sat::LratStep;

        // Each active clause id → (its literals, its proof). Seed with the input
        // CNF (DIMACS clause k, 0-based, is LRAT id k+1).
        let mut clauses: HashMap<u64, (Vec<Lit>, B::Thm)> = HashMap::new();
        for (i, clause) in cnf.clauses().enumerate() {
            let thm = backend.assume_clause(clause)?;
            clauses.insert((i + 1) as u64, (clause.lits().to_vec(), thm));
        }

        let mut last: Option<B::Thm> = None;
        let mut refutation: Option<B::Thm> = None;

        for step in proof.steps() {
            match step {
                LratStep::Add {
                    id,
                    clause,
                    antecedents,
                    ..
                } => {
                    let c_lits = clause.lits().to_vec();
                    let thm = rup_reconstruct(backend, &c_lits, antecedents, &clauses, *id)?;
                    // Backend-agnostic refutation detection: the refutation is the
                    // step whose LRAT clause is *empty*. This is correct for both
                    // the disjunction backend (concl `F`) and the sequent backend
                    // (every clause has concl `F`, so `is_empty_clause` alone would
                    // fire on the first unit-contradiction step, not the empty one).
                    // `backend.is_empty_clause` stays on the trait as the
                    // backend-side check; here `c_lits.is_empty()` is authoritative.
                    if refutation.is_none() && c_lits.is_empty() {
                        refutation = Some(thm.clone());
                    }
                    last = Some(thm.clone());
                    clauses.insert(*id, (c_lits, thm));
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

/// Reconstruct the resolution proof of clause `C` (`c_lits`) from its ordered
/// RUP antecedents, via unit propagation from `¬C`.
fn rup_reconstruct<B: ClauseBackend>(
    backend: &mut B,
    c_lits: &[Lit],
    antecedents: &[u64],
    clauses: &HashMap<u64, (Vec<Lit>, B::Thm)>,
    step_id: u64,
) -> Result<B::Thm, ReplayError> {
    let get = |id: u64| clauses.get(&id).ok_or(ReplayError::UndefinedClause(id));

    // Falsify C: literal `l ∈ C` is false, so `var(l)` takes value `!l.is_pos()`.
    let mut assign: HashMap<Var, bool> = c_lits.iter().map(|l| (l.var(), !l.is_pos())).collect();

    // Propagate the antecedents in order; `trail` records (forced literal, its
    // clause id); `conflict` is the first fully-falsified antecedent.
    let mut trail: Vec<(Lit, u64)> = Vec::new();
    let mut conflict: Option<u64> = None;
    for &aid in antecedents {
        let (lits, _) = get(aid)?;
        let (mut unassigned, mut n_unassigned, mut satisfied) = (None, 0usize, false);
        for &l in lits {
            match assign.get(&l.var()) {
                Some(&v) if v == l.is_pos() => {
                    satisfied = true; // `l` is true → clause already satisfied
                    break;
                }
                Some(_) => {} // `l` is false
                None => {
                    n_unassigned += 1;
                    unassigned = Some(l);
                }
            }
        }
        if satisfied {
            continue; // a redundant hint; propagates nothing
        }
        match n_unassigned {
            0 => {
                conflict = Some(aid);
                break;
            }
            1 => {
                let u = unassigned.expect("exactly one unassigned");
                assign.insert(u.var(), u.is_pos()); // force `u` true
                trail.push((u, aid));
            }
            _ => return Err(ReplayError::BadRup { id: step_id }), // hint not unit
        }
    }
    let conflict_id = conflict.ok_or(ReplayError::BadRup { id: step_id })?;

    // Read the resolution off backwards: start at the conflict clause and resolve
    // against each propagating clause on its pivot, whenever the negated forced
    // literal is still present in the running resolvent.
    let (conf_lits, conf_thm) = get(conflict_id)?;
    let mut r_lits: HashSet<Lit> = conf_lits.iter().copied().collect();
    let mut r_thm = conf_thm.clone();
    for &(u, aid) in trail.iter().rev() {
        if r_lits.contains(&!u) {
            let (a_lits, a_thm) = get(aid)?;
            r_thm = backend.resolve_on(&r_thm, a_thm, u.var())?;
            r_lits.remove(&!u);
            r_lits.remove(&u);
            r_lits.extend(a_lits.iter().copied().filter(|&l| l != u));
        }
    }
    Ok(r_thm)
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
