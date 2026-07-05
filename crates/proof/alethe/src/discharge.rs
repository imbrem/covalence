//! Discharging a HOL goal `⊢ G` through an Alethe refutation.
//!
//! ## The flow
//!
//! Alethe certifies **UNSAT** (a refutation). To prove a HOL goal `⊢ G`
//! we run that machinery on the *negation*:
//!
//! 1. [`crate::goal::goal_to_problem`] builds the SMT problem whose single
//!    assertion is `¬G`.
//! 2. An [`AletheProof`] refuting `¬G` is obtained — replayed from a
//!    **cached** proof if one is supplied, else produced by an injected
//!    [`SmtSolver`].
//! 3. The proof is replayed through [`HolAletheBridge`] /
//!    [`ingest_alethe`]; reaching the empty clause yields the witnessing
//!    refutation `{¬G} ⊢ F` (surfaced by [`HolAletheBridge::refutation`]).
//! 4. **Reductio**: from `{¬G} ⊢ F` the kernel derives `⊢ G` classically
//!    — `lem(G) : ⊢ G ∨ ¬G`, the left disjunct is `G` itself and the right
//!    discharges `¬G` through `false_elim`.
//!
//! Nothing in the Alethe proof is trusted: every step is re-derived by
//! [`HolAletheBridge`], and the final reductio is three kernel rules. A
//! mistranslated or bogus proof simply fails to check.
//!
//! ## Caching (first cut)
//!
//! [`ProofCache`] is the cached-proof source. Today it is an in-memory /
//! on-disk lookup keyed by the goal's printed form: a [`CachedProof`] is
//! parsed-bytes or a file path. Full **content-addressed** caching through
//! `covalence-store` (key = hash of the canonical problem, value = the
//! Alethe blob, shared across a session and persisted) is a follow-up —
//! see `SKELETONS.md`.

use std::collections::HashMap;
use std::path::PathBuf;

use covalence_core::Term;
use covalence_hol_eval::EvalThm as Thm;
use covalence_init::HolLightCtx;
use covalence_smt::{AletheProof, SmtProblem, SmtSolver, parse_alethe};
use covalence_types::Decision;

use crate::error::BridgeError;
use crate::goal::goal_to_problem;
use crate::hol::HolAletheBridge;
use crate::ingest::ingest_alethe;

type R<T> = Result<T, BridgeError>;

/// A cached Alethe proof: raw text, or a path to read it from.
#[derive(Debug, Clone)]
pub enum CachedProof {
    /// The proof commands as Alethe text (already unwrapped of any
    /// `(proof …)` wrapper).
    Text(String),
    /// A filesystem path to an Alethe proof file.
    Path(PathBuf),
}

impl CachedProof {
    /// Parse this cached proof into an [`AletheProof`].
    fn parse(&self) -> R<AletheProof> {
        let text = match self {
            CachedProof::Text(t) => t.clone(),
            CachedProof::Path(p) => std::fs::read_to_string(p).map_err(|e| {
                BridgeError::Malformed(format!("reading cached proof {}: {e}", p.display()))
            })?,
        };
        Ok(parse_alethe(&text)?)
    }
}

/// A goal-keyed store of cached Alethe proofs.
///
/// The key is the goal's printed form (`Term`'s `Display`) — stable for a
/// given kernel term. This is the *first-cut* cache; the content-addressed
/// `covalence-store` version is deferred (see module docs / `SKELETONS.md`).
#[derive(Debug, Default)]
pub struct ProofCache {
    by_goal: HashMap<String, CachedProof>,
}

impl ProofCache {
    /// An empty cache.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a cached proof for `goal`.
    pub fn insert(&mut self, goal: &Term, proof: CachedProof) {
        self.by_goal.insert(goal.to_string(), proof);
    }

    /// Look up a cached proof for `goal`.
    pub fn get(&self, goal: &Term) -> Option<&CachedProof> {
        self.by_goal.get(&goal.to_string())
    }
}

/// Discharges HOL goals via Alethe: cached proof first, else an injected
/// solver.
///
/// Holds an optional [`ProofCache`] (the fast path, needing no solver) and
/// an optional boxed [`SmtSolver`] (the fallback). At least one must be
/// present for a given goal to discharge.
pub struct SmtDischarger {
    cache: ProofCache,
    solver: Option<Box<dyn SmtSolver>>,
}

impl SmtDischarger {
    /// A discharger with neither a cache nor a solver — add them with the
    /// builder methods. (Useless on its own; primarily for tests that set
    /// exactly one path.)
    pub fn new() -> Self {
        Self {
            cache: ProofCache::new(),
            solver: None,
        }
    }

    /// A discharger backed only by a cache (no solver). Discharge fails for
    /// any goal whose proof is not cached.
    pub fn cached(cache: ProofCache) -> Self {
        Self {
            cache,
            solver: None,
        }
    }

    /// A discharger backed only by a live solver (empty cache).
    pub fn with_solver(solver: Box<dyn SmtSolver>) -> Self {
        Self {
            cache: ProofCache::new(),
            solver: Some(solver),
        }
    }

    /// Attach a cache (cached proofs are tried before the solver).
    pub fn set_cache(&mut self, cache: ProofCache) -> &mut Self {
        self.cache = cache;
        self
    }

    /// Attach a solver fallback.
    pub fn set_solver(&mut self, solver: Box<dyn SmtSolver>) -> &mut Self {
        self.solver = Some(solver);
        self
    }

    /// Mutable access to the cache (e.g. to insert a freshly-solved proof).
    pub fn cache_mut(&mut self) -> &mut ProofCache {
        &mut self.cache
    }

    /// Discharge `goal`, returning the kernel theorem `⊢ goal`.
    ///
    /// Tries the cached proof, then the solver. The returned theorem is
    /// genuine — the Alethe proof is re-checked through the kernel, then
    /// the goal is concluded by reductio.
    pub fn discharge(&self, goal: &Term) -> R<Thm> {
        let problem = goal_to_problem(goal)?;

        // 1) Cached proof, if any.
        if let Some(cached) = self.cache.get(goal) {
            let proof = cached.parse()?;
            return discharge_with_proof(goal, &problem, &proof);
        }

        // 2) Solver fallback.
        if let Some(solver) = &self.solver {
            let proof = solver
                .solve(&problem)
                .map_err(|e| BridgeError::NotImplemented(format!("smt solver: {e}")))?;
            return discharge_with_proof(goal, &problem, &proof);
        }

        Err(BridgeError::NotImplemented(format!(
            "smt: no cached proof and no solver available for goal `{goal}`"
        )))
    }
}

impl Default for SmtDischarger {
    fn default() -> Self {
        Self::new()
    }
}

/// Replay `proof` against `problem` (which must assert `¬goal`), and
/// conclude `⊢ goal` by reductio. Shared by the cached and live paths.
///
/// This is the core "negate-the-goal, refute, conclude `⊢ G`" wrapper on
/// top of the refutation checker.
pub fn discharge_with_proof(goal: &Term, problem: &SmtProblem, proof: &AletheProof) -> R<Thm> {
    let mut bridge = HolAletheBridge::new();
    let decision = ingest_alethe(&mut bridge, problem, proof)?;
    if decision != Decision::Unsat {
        return Err(BridgeError::NotImplemented(format!(
            "smt: proof did not refute `¬({goal})` (verdict {decision:?})"
        )));
    }
    let refutation = bridge.refutation().ok_or_else(|| {
        BridgeError::Kernel("smt: Unsat reported but no refutation theorem captured".into())
    })?;
    reductio(goal, refutation)
}

/// From a refutation `{¬G, …} ⊢ F` whose hypotheses are a subset of
/// `{¬G}`, derive `⊢ G` classically.
///
/// `lem(G) : ⊢ G ∨ ¬G` is eliminated with two implication branches
/// (`or_elim` consumes `⊢ G ⟹ R` and `⊢ ¬G ⟹ R`, here `R = G`):
///
/// * left  `⊢ G ⟹ G`  — `assume(G)` discharged over `G`.
/// * right `⊢ ¬G ⟹ G` — the refutation gives `{¬G} ⊢ F`; `false_elim`
///   turns `F` into `G`, then `imp_intro(¬G)` discharges the assumption.
///
/// `or_elim` then yields the hypothesis-free `⊢ G`.
fn reductio(goal: &Term, refutation: &Thm) -> R<Thm> {
    let ctx = HolLightCtx::new();
    let not_goal = ctx.mk_not(goal.clone());

    // The refutation's hypotheses must be drawn only from `{¬G}` — anything
    // else means the negation we asserted is not the one refuted (a
    // translation bug), surfaced rather than trusted.
    for h in refutation.hyps().iter() {
        if *h != not_goal {
            return Err(BridgeError::Kernel(format!(
                "smt: refutation hypothesis `{h}` is not the negated goal `{not_goal}`"
            )));
        }
    }

    // left: ⊢ G ⟹ G.
    let left = Thm::assume(goal.clone())?.imp_intro(goal)?;
    // right: {¬G} ⊢ F  →  {¬G} ⊢ G  →  ⊢ ¬G ⟹ G.
    let right = refutation
        .clone()
        .false_elim(goal.clone())?
        .imp_intro(&not_goal)?;
    // ⊢ G ∨ ¬G  →  ⊢ G.
    Thm::lem(goal.clone())?
        .or_elim(left, right)
        .map_err(Into::into)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::{Term, Type};
    use covalence_init::HolLightCtx;

    #[test]
    fn empty_discharger_has_no_path() {
        // Neither cache nor solver ⟹ every discharge fails (never trusts).
        let ctx = HolLightCtx::new();
        let a = Term::free("a", Type::bool());
        let goal = ctx.mk_not(ctx.mk_and(a.clone(), ctx.mk_not(a)));
        let discharger = SmtDischarger::new();
        assert!(discharger.discharge(&goal).is_err());
    }
}
