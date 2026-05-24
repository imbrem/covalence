//! Trusted/untrusted DRAT verification: [`Verifier`] and [`Advisor`].
//!
//! A [`Verifier`] is a **table** managing multiple formulas by
//! [`FormulaId`].  All methods take a `FormulaId` parameter.
//!
//! An [`Advisor`] handles one proof step at a time via
//! [`Advisor::step`].  The [`check`] free function provides the
//! standard proof loop on top.
//!
//! **Soundness guarantee:** [`Verifier::propagate`] is the only way
//! to assign a variable — it validates every assignment against the
//! actual clause state.  No sequence of calls can fabricate a
//! conflict; a buggy advisor can only _miss_ conflicts (safe).

use crate::drat::{assign_get, assign_set_true, lit_watch_idx};
use crate::{Cnf, Decision, DratProof, DratStep, Lit};

// ---------------------------------------------------------------------------
// FormulaId
// ---------------------------------------------------------------------------

/// Opaque identifier for a formula managed by a [`Verifier`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FormulaId(u32);

// ---------------------------------------------------------------------------
// PropagateResult
// ---------------------------------------------------------------------------

/// Result of inspecting (and potentially propagating) a single clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropagateResult {
    /// All literals are false — conflict detected.
    Conflict,
    /// Exactly one literal was unknown; it has been set to true.
    Propagated(Lit),
    /// At least one literal is true — clause is satisfied.
    Satisfied,
    /// Two or more literals are unknown — clause is not yet unit.
    Open,
    /// Clause index is out of bounds or clause is inactive (deleted).
    Inactive,
}

// ---------------------------------------------------------------------------
// FormulaState (private)
// ---------------------------------------------------------------------------

struct FormulaState {
    original: Cnf,
    clauses: Vec<(Vec<Lit>, bool)>,
    assign: Vec<Decision>,
    trail: Vec<usize>,
    num_vars: u32,
    complete: bool,
}

// ---------------------------------------------------------------------------
// Verifier — multi-formula table
// ---------------------------------------------------------------------------

/// Trusted DRAT verifier managing multiple formulas by [`FormulaId`].
///
/// All methods are safe on invalid `FormulaId` — they return defaults
/// (0, `None`, `false`, [`PropagateResult::Inactive`]), never panic.
pub struct Verifier {
    formulas: Vec<Option<FormulaState>>,
    free_list: Vec<u32>,
}

impl Verifier {
    /// Create an empty verifier with no formulas.
    pub fn new() -> Self {
        Verifier {
            formulas: Vec::new(),
            free_list: Vec::new(),
        }
    }

    // -- Lifecycle -----------------------------------------------------------

    /// Register a CNF formula and return its [`FormulaId`].
    pub fn create(&mut self, cnf: &Cnf) -> FormulaId {
        let clauses = cnf.clauses().map(|c| (c.lits().to_vec(), true)).collect();
        let state = FormulaState {
            original: cnf.clone(),
            clauses,
            assign: vec![Decision::Unknown; cnf.num_vars() as usize],
            trail: Vec::new(),
            num_vars: cnf.num_vars(),
            complete: false,
        };
        let slot = if let Some(idx) = self.free_list.pop() {
            self.formulas[idx as usize] = Some(state);
            idx
        } else {
            let idx = self.formulas.len() as u32;
            self.formulas.push(Some(state));
            idx
        };
        FormulaId(slot)
    }

    /// Delete a formula, freeing its slot for reuse.
    pub fn delete(&mut self, fid: FormulaId) {
        if let Some(slot) = self.formulas.get_mut(fid.0 as usize) {
            if slot.is_some() {
                *slot = None;
                self.free_list.push(fid.0);
            }
        }
    }

    // -- Original formula (read-only) ----------------------------------------

    /// Number of variables in the original formula.
    pub fn original_num_vars(&self, fid: FormulaId) -> u32 {
        self.get_state(fid).map_or(0, |s| s.original.num_vars())
    }

    /// Number of clauses in the original formula.
    pub fn original_num_clauses(&self, fid: FormulaId) -> usize {
        self.get_state(fid).map_or(0, |s| s.original.num_clauses())
    }

    /// Length of original clause `ci`.
    pub fn original_clause_len(&self, fid: FormulaId, ci: usize) -> usize {
        self.get_state(fid)
            .and_then(|s| s.original.clauses().nth(ci))
            .map_or(0, |c| c.len())
    }

    /// Literal at position `pos` in original clause `ci`.
    pub fn original_clause_lit(&self, fid: FormulaId, ci: usize, pos: usize) -> Option<Lit> {
        self.get_state(fid)
            .and_then(|s| s.original.clauses().nth(ci))
            .and_then(|c| c.lits().get(pos).copied())
    }

    // -- Current proof state -------------------------------------------------

    /// Total number of clauses (including inactive) in the proof state.
    pub fn num_clauses(&self, fid: FormulaId) -> usize {
        self.get_state(fid).map_or(0, |s| s.clauses.len())
    }

    /// Number of literals in proof clause `ci`.
    pub fn clause_len(&self, fid: FormulaId, ci: usize) -> usize {
        self.get_state(fid)
            .and_then(|s| s.clauses.get(ci))
            .map_or(0, |c| c.0.len())
    }

    /// Literal at position `pos` in proof clause `ci`.
    pub fn clause_lit(&self, fid: FormulaId, ci: usize, pos: usize) -> Option<Lit> {
        self.get_state(fid)
            .and_then(|s| s.clauses.get(ci))
            .and_then(|(lits, _)| lits.get(pos).copied())
    }

    /// Is proof clause `ci` active (not deleted)?
    pub fn is_active(&self, fid: FormulaId, ci: usize) -> bool {
        self.get_state(fid)
            .and_then(|s| s.clauses.get(ci))
            .is_some_and(|(_, active)| *active)
    }

    /// Look up a literal's truth value under the current assignment.
    pub fn get(&self, fid: FormulaId, lit: Lit) -> Decision {
        match self.get_state(fid) {
            Some(s) => {
                let vi = (lit.var().index() - 1) as usize;
                if vi >= s.assign.len() {
                    Decision::Unknown
                } else {
                    assign_get(&s.assign, lit)
                }
            }
            None => Decision::Unknown,
        }
    }

    /// Has the empty clause been derived for this formula?
    pub fn is_unsat(&self, fid: FormulaId) -> bool {
        self.get_state(fid).is_some_and(|s| s.complete)
    }

    // -- Trusted propagation -------------------------------------------------

    /// Inspect clause `ci` and, if it is unit, propagate the remaining
    /// literal.  This is the **only** way to assign a variable — every
    /// assignment is validated against the actual clause state.
    pub fn propagate(&mut self, fid: FormulaId, ci: usize) -> PropagateResult {
        let s = match self.get_state_mut(fid) {
            Some(s) => s,
            None => return PropagateResult::Inactive,
        };
        let (lits, active) = match s.clauses.get(ci) {
            Some(c) => c,
            None => return PropagateResult::Inactive,
        };
        if !active {
            return PropagateResult::Inactive;
        }

        let mut unset_count = 0u32;
        let mut last_unset = None;

        for &lit in lits {
            match assign_get(&s.assign, lit) {
                Decision::Sat => return PropagateResult::Satisfied,
                Decision::Unknown => {
                    unset_count += 1;
                    last_unset = Some(lit);
                }
                Decision::Unsat => {}
            }
        }

        match unset_count {
            0 => PropagateResult::Conflict,
            1 => {
                let unit_lit = last_unset.unwrap();
                assign_set_true(&mut s.assign, &mut s.trail, unit_lit);
                PropagateResult::Propagated(unit_lit)
            }
            _ => PropagateResult::Open,
        }
    }

    // -- AT-check building blocks --------------------------------------------

    /// Negate candidate literals for an AT check. Extends variable
    /// capacity as needed. Returns `true` if the candidate is a
    /// trivial tautology (complementary literals found in candidate).
    /// If `false`, the caller must drive BCP via `propagate`, then
    /// call `end_at` to reset.
    pub fn begin_at(&mut self, fid: FormulaId, candidate: &[Lit]) -> bool {
        let s = match self.get_state_mut(fid) {
            Some(s) => s,
            None => return false,
        };

        // Extend variable capacity for any new variables in the candidate.
        for &lit in candidate {
            let var = lit.var().index() as u32;
            if var > s.num_vars {
                s.num_vars = var;
                s.assign.resize(var as usize, Decision::Unknown);
            }
        }

        // Negate each literal in the candidate clause.
        for &lit in candidate {
            if assign_get(&s.assign, lit) == Decision::Sat {
                // Complementary literals → tautology. Reset and return.
                for &vi in &s.trail {
                    s.assign[vi] = Decision::Unknown;
                }
                s.trail.clear();
                return true;
            }
            if assign_get(&s.assign, lit) == Decision::Unknown {
                assign_set_true(&mut s.assign, &mut s.trail, !lit);
            }
        }

        false
    }

    /// Reset the assignment trail after an AT check.
    pub fn end_at(&mut self, fid: FormulaId) {
        if let Some(s) = self.get_state_mut(fid) {
            for &vi in &s.trail {
                s.assign[vi] = Decision::Unknown;
            }
            s.trail.clear();
        }
    }

    /// Add a clause to the proof database. Extends variable capacity.
    /// Sets the `complete` flag if the clause is empty.
    /// Returns the clause index.
    pub fn push_clause(&mut self, fid: FormulaId, lits: &[Lit]) -> usize {
        let s = match self.get_state_mut(fid) {
            Some(s) => s,
            None => return 0,
        };

        for &lit in lits {
            let var = lit.var().index() as u32;
            if var > s.num_vars {
                s.num_vars = var;
                s.assign.resize(var as usize, Decision::Unknown);
            }
        }

        if lits.is_empty() {
            s.complete = true;
        }

        let ci = s.clauses.len();
        s.clauses.push((lits.to_vec(), true));
        ci
    }

    /// Deactivate the first active clause matching `lits`.
    /// Returns the clause index if found.
    pub fn deactivate(&mut self, fid: FormulaId, lits: &[Lit]) -> Option<usize> {
        let s = match self.get_state_mut(fid) {
            Some(s) => s,
            None => return None,
        };
        for (i, (cls_lits, active)) in s.clauses.iter_mut().enumerate() {
            if *active && cls_lits.as_slice() == lits {
                *active = false;
                return Some(i);
            }
        }
        None
    }

    // -- private helpers -----------------------------------------------------

    fn get_state(&self, fid: FormulaId) -> Option<&FormulaState> {
        self.formulas.get(fid.0 as usize).and_then(|s| s.as_ref())
    }

    fn get_state_mut(&mut self, fid: FormulaId) -> Option<&mut FormulaState> {
        self.formulas
            .get_mut(fid.0 as usize)
            .and_then(|s| s.as_mut())
    }
}

impl Default for Verifier {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Advisor trait
// ---------------------------------------------------------------------------

/// Untrusted proof-step advisor.
///
/// Handles one [`DratStep`] at a time.  For Add steps, the advisor
/// sets up the AT check (`begin_at`), drives BCP, resets (`end_at`),
/// and pushes the clause on success.  For Delete steps, it deactivates
/// the clause (and updates any internal bookkeeping).
///
/// **Soundness:** any implementation is safe.  An incorrect advisor can
/// only under-propagate (miss conflicts → reject valid proofs), never
/// fabricate a conflict (accept invalid proofs).
pub trait Advisor {
    /// Process one proof step.  Returns `false` if an Add step is not
    /// AT (proof is invalid); the caller should abort.
    fn step(&mut self, verifier: &mut Verifier, fid: FormulaId, step: &DratStep) -> bool;
}

// ---------------------------------------------------------------------------
// check — standard proof loop
// ---------------------------------------------------------------------------

/// Check a DRAT proof for formula `fid` using the given advisor.
///
/// Iterates over proof steps, calling [`Advisor::step`] for each one.
/// Returns `true` iff every Add step is AT and the empty clause is
/// derived (proving UNSAT).
pub fn check(
    verifier: &mut Verifier,
    fid: FormulaId,
    proof: &DratProof,
    advisor: &mut impl Advisor,
) -> bool {
    for step in proof.steps() {
        if !advisor.step(verifier, fid, step) {
            return false;
        }
    }
    verifier.is_unsat(fid)
}

// ---------------------------------------------------------------------------
// FullScanAdvisor
// ---------------------------------------------------------------------------

/// Advisor that scans all clauses each round — equivalent to the naive
/// full-scan approach, driven through the safe verifier API.
pub struct FullScanAdvisor;

impl FullScanAdvisor {
    /// Full-scan BCP: repeatedly scan all clauses until conflict or fixpoint.
    fn full_scan_bcp(&self, verifier: &mut Verifier, fid: FormulaId) -> bool {
        loop {
            let mut progress = false;
            let n = verifier.num_clauses(fid);
            for ci in 0..n {
                match verifier.propagate(fid, ci) {
                    PropagateResult::Conflict => return true,
                    PropagateResult::Propagated(_) => {
                        progress = true;
                        break;
                    }
                    _ => {}
                }
            }
            if !progress {
                return false;
            }
        }
    }
}

impl Advisor for FullScanAdvisor {
    fn step(&mut self, verifier: &mut Verifier, fid: FormulaId, step: &DratStep) -> bool {
        match step {
            DratStep::Add(clause) => {
                let tautology = verifier.begin_at(fid, clause.lits());
                let at = if tautology {
                    true
                } else {
                    let conflict = self.full_scan_bcp(verifier, fid);
                    verifier.end_at(fid);
                    conflict
                };
                if !at {
                    return false;
                }
                verifier.push_clause(fid, clause.lits());
            }
            DratStep::Delete(clause) => {
                verifier.deactivate(fid, clause.lits());
            }
        }
        true
    }
}

// ---------------------------------------------------------------------------
// WatchedAdvisor
// ---------------------------------------------------------------------------

/// Per-formula watch state.
struct WatchState {
    /// For each clause with ≥2 literals: the watched pair.
    watched: Vec<Option<[Lit; 2]>>,
    /// Watch lists indexed by `lit_watch_idx(l)`.
    watch_lists: Vec<Vec<usize>>,
    /// Clause IDs with fewer than 2 literals.
    short: Vec<usize>,
    num_vars: u32,
    /// Whether initial clauses have been read from the verifier.
    initialized: bool,
}

impl WatchState {
    fn ensure_var(&mut self, var: u32) {
        if var > self.num_vars {
            self.num_vars = var;
            self.watch_lists.resize_with(2 * var as usize, Vec::new);
        }
    }

    fn init_watches_for_clause(&mut self, ci: usize, lits: &[Lit]) {
        while self.watched.len() <= ci {
            self.watched.push(None);
        }

        for &lit in lits {
            self.ensure_var(lit.var().index() as u32);
        }

        if lits.len() >= 2 {
            let watches = [lits[0], lits[1]];
            self.watched[ci] = Some(watches);
            self.watch_lists[lit_watch_idx(lits[0])].push(ci);
            self.watch_lists[lit_watch_idx(lits[1])].push(ci);
        } else {
            self.short.push(ci);
        }
    }

    fn watched_bcp(&mut self, verifier: &mut Verifier, fid: FormulaId, falsified: &[Lit]) -> bool {
        let mut queue: Vec<Lit> = Vec::new();

        // Check short (empty/unit) clauses eagerly.
        for &ci in &self.short {
            if !verifier.is_active(fid, ci) {
                continue;
            }
            match verifier.propagate(fid, ci) {
                PropagateResult::Conflict => return true,
                PropagateResult::Propagated(lit) => queue.push(!lit),
                _ => {}
            }
        }

        queue.extend_from_slice(falsified);

        // BCP with watched literals.
        while let Some(false_lit) = queue.pop() {
            let widx = lit_watch_idx(false_lit);
            if widx >= self.watch_lists.len() {
                continue;
            }

            let mut wlist = std::mem::take(&mut self.watch_lists[widx]);
            let mut i = 0;

            while i < wlist.len() {
                let ci = wlist[i];

                if !verifier.is_active(fid, ci) {
                    wlist.swap_remove(i);
                    continue;
                }

                let watches = match self.watched[ci] {
                    Some(w) => w,
                    None => {
                        i += 1;
                        continue;
                    }
                };

                let other = if watches[0] == false_lit {
                    watches[1]
                } else {
                    watches[0]
                };

                if verifier.get(fid, other) == Decision::Sat {
                    i += 1;
                    continue;
                }

                // Search for a non-false replacement via the verifier.
                let len = verifier.clause_len(fid, ci);
                let mut replacement = None;
                for pos in 0..len {
                    if let Some(lit) = verifier.clause_lit(fid, ci, pos) {
                        if lit != watches[0] && lit != watches[1] {
                            if verifier.get(fid, lit) != Decision::Unsat {
                                replacement = Some(lit);
                                break;
                            }
                        }
                    }
                }

                if let Some(new_watch) = replacement {
                    let new_watches = if watches[0] == false_lit {
                        [new_watch, watches[1]]
                    } else {
                        [watches[0], new_watch]
                    };
                    self.watched[ci] = Some(new_watches);
                    self.ensure_var(new_watch.var().index() as u32);
                    self.watch_lists[lit_watch_idx(new_watch)].push(ci);
                    wlist.swap_remove(i);
                    continue;
                }

                match verifier.propagate(fid, ci) {
                    PropagateResult::Conflict => {
                        self.watch_lists[widx] = wlist;
                        return true;
                    }
                    PropagateResult::Propagated(lit) => queue.push(!lit),
                    _ => {}
                }
                i += 1;
            }

            self.watch_lists[widx] = wlist;
        }

        false
    }
}

/// Advisor using two-watched-literal bookkeeping.
///
/// Maintains per-formula watch state lazily. Reads clause literals and
/// assignment state through the [`Verifier`] during BCP — no clause
/// data is duplicated.
pub struct WatchedAdvisor {
    states: Vec<Option<WatchState>>,
}

impl WatchedAdvisor {
    /// Create an advisor with no per-formula state (created lazily).
    pub fn new() -> Self {
        WatchedAdvisor { states: Vec::new() }
    }

    fn get_or_create(&mut self, fid: FormulaId) -> &mut WatchState {
        let idx = fid.0 as usize;
        if self.states.len() <= idx {
            self.states.resize_with(idx + 1, || None);
        }
        self.states[idx].get_or_insert_with(|| WatchState {
            watched: Vec::new(),
            watch_lists: Vec::new(),
            short: Vec::new(),
            num_vars: 0,
            initialized: false,
        })
    }
}

impl Default for WatchedAdvisor {
    fn default() -> Self {
        Self::new()
    }
}

impl Advisor for WatchedAdvisor {
    fn step(&mut self, verifier: &mut Verifier, fid: FormulaId, step: &DratStep) -> bool {
        // Lazy init: read initial clauses from verifier on first step.
        let ws = self.get_or_create(fid);
        if !ws.initialized {
            ws.initialized = true;
            let n = verifier.num_clauses(fid);
            for ci in 0..n {
                let lits: Vec<Lit> = (0..verifier.clause_len(fid, ci))
                    .filter_map(|pos| verifier.clause_lit(fid, ci, pos))
                    .collect();
                ws.init_watches_for_clause(ci, &lits);
            }
        }

        match step {
            DratStep::Add(clause) => {
                let tautology = verifier.begin_at(fid, clause.lits());
                let at = if tautology {
                    true
                } else {
                    let ws = self.get_or_create(fid);
                    let falsified: Vec<Lit> = clause.lits().to_vec();
                    let conflict = ws.watched_bcp(verifier, fid, &falsified);
                    verifier.end_at(fid);
                    conflict
                };
                if !at {
                    return false;
                }
                let ci = verifier.push_clause(fid, clause.lits());
                let ws = self.get_or_create(fid);
                ws.init_watches_for_clause(ci, clause.lits());
            }
            DratStep::Delete(clause) => {
                if let Some(ci) = verifier.deactivate(fid, clause.lits()) {
                    let ws = self.get_or_create(fid);
                    if ci < ws.watched.len() {
                        ws.watched[ci] = None;
                    }
                }
            }
        }
        true
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Clause, Cnf, DratProof, DratStep, NaiveDratChecker, WatchedDratChecker, check_proof,
    };

    /// Run a proof through the old checkers and both advised variants.
    fn check_all(cnf: &Cnf, proof: &DratProof) -> [bool; 4] {
        let mut naive = NaiveDratChecker::new(cnf);
        let r0 = check_proof(&mut naive, proof);

        let mut watched = WatchedDratChecker::new(cnf);
        let r1 = check_proof(&mut watched, proof);

        let mut v2 = Verifier::new();
        let fid2 = v2.create(cnf);
        let r2 = check(&mut v2, fid2, proof, &mut FullScanAdvisor);

        let mut v3 = Verifier::new();
        let fid3 = v3.create(cnf);
        let r3 = check(&mut v3, fid3, proof, &mut WatchedAdvisor::new());

        [r0, r1, r2, r3]
    }

    fn assert_all_accept(cnf: &Cnf, proof: &DratProof) {
        let r = check_all(cnf, proof);
        assert!(r.iter().all(|&v| v), "expected all accept, got {r:?}");
    }

    fn assert_all_reject(cnf: &Cnf, proof: &DratProof) {
        let r = check_all(cnf, proof);
        assert!(r.iter().all(|&v| !v), "expected all reject, got {r:?}");
    }

    // -- acceptance --

    #[test]
    fn trivial_unsat() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);
        let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
        assert_all_accept(&cnf, &proof);
    }

    #[test]
    fn four_clause_full_proof() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([x, !y]);
        cnf.clause([!x, y]);
        cnf.clause([!x, !y]);
        let proof = DratProof::new([
            DratStep::Add(Clause::new([x])),
            DratStep::Add(Clause::new([!x])),
            DratStep::Add(Clause::new([])),
        ]);
        assert_all_accept(&cnf, &proof);
    }

    #[test]
    fn three_clause_unsat() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([x, !y]);
        cnf.clause([!x]);
        let proof = DratProof::new([
            DratStep::Add(Clause::new([x])),
            DratStep::Add(Clause::new([])),
        ]);
        assert_all_accept(&cnf, &proof);
    }

    #[test]
    fn proof_with_deletion() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);
        let proof = DratProof::new([
            DratStep::Add(Clause::new([])),
            DratStep::Delete(Clause::new([])),
            DratStep::Add(Clause::new([])),
        ]);
        assert_all_accept(&cnf, &proof);
    }

    #[test]
    fn three_var_proof() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        let z = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([x, !y]);
        cnf.clause([!x, z]);
        cnf.clause([!x, !z]);
        let proof = DratProof::new([
            DratStep::Add(Clause::new([x])),
            DratStep::Add(Clause::new([!x])),
            DratStep::Add(Clause::new([])),
        ]);
        assert_all_accept(&cnf, &proof);
    }

    // -- rejection --

    #[test]
    fn empty_proof_rejected() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);
        assert_all_reject(&cnf, &DratProof::new([]));
    }

    #[test]
    fn skip_intermediate_steps() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([x, !y]);
        cnf.clause([!x, y]);
        cnf.clause([!x, !y]);
        assert_all_reject(&cnf, &DratProof::new([DratStep::Add(Clause::new([]))]));
    }

    #[test]
    fn incomplete_proof() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([x, !y]);
        cnf.clause([!x, y]);
        cnf.clause([!x, !y]);
        let proof = DratProof::new([
            DratStep::Add(Clause::new([x])),
            DratStep::Add(Clause::new([!x])),
        ]);
        assert_all_reject(&cnf, &proof);
    }

    #[test]
    fn non_at_clause() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([!x, y]);
        assert_all_reject(&cnf, &DratProof::new([DratStep::Add(Clause::new([!y]))]));
    }

    #[test]
    fn sat_formula_rejected() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        assert_all_reject(&cnf, &DratProof::new([DratStep::Add(Clause::new([]))]));
    }

    #[test]
    fn delete_then_add_empty() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);
        let proof = DratProof::new([
            DratStep::Delete(Clause::new([x])),
            DratStep::Delete(Clause::new([!x])),
            DratStep::Add(Clause::new([])),
        ]);
        assert_all_reject(&cnf, &proof);
    }

    #[test]
    fn wrong_variable() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        let z = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([x, !y]);
        cnf.clause([!x, y]);
        cnf.clause([!x, !y]);
        let proof = DratProof::new([
            DratStep::Add(Clause::new([z])),
            DratStep::Add(Clause::new([])),
        ]);
        assert_all_reject(&cnf, &proof);
    }

    // -- Verifier methods with FormulaId --

    #[test]
    fn propagate_empty_clause_is_conflict() {
        let cnf = Cnf::from_parts(0, vec![Clause::new([])]);
        let mut v = Verifier::new();
        let fid = v.create(&cnf);
        assert_eq!(v.propagate(fid, 0), PropagateResult::Conflict);
    }

    #[test]
    fn propagate_unit_clause() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        let mut v = Verifier::new();
        let fid = v.create(&cnf);
        assert_eq!(v.propagate(fid, 0), PropagateResult::Propagated(x));
        assert_eq!(v.get(fid, x), Decision::Sat);
    }

    #[test]
    fn propagate_satisfied_open_inactive_oob() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, y]);

        // Satisfied: set x=Sat via a unit clause, then check the binary clause
        let mut cnf_sat = Cnf::new();
        let xs = cnf_sat.fresh();
        let ys = cnf_sat.fresh();
        cnf_sat.clause([xs]); // clause 0: unit
        cnf_sat.clause([xs, ys]); // clause 1: binary
        let mut v = Verifier::new();
        let fid = v.create(&cnf_sat);
        assert_eq!(v.propagate(fid, 0), PropagateResult::Propagated(xs));
        assert_eq!(v.propagate(fid, 1), PropagateResult::Satisfied);

        // Open
        let mut v = Verifier::new();
        let fid = v.create(&cnf);
        assert_eq!(v.propagate(fid, 0), PropagateResult::Open);

        // Inactive
        let cnf_empty = Cnf::from_parts(0, vec![Clause::new([])]);
        let mut v = Verifier::new();
        let fid = v.create(&cnf_empty);
        // Deactivate clause 0 to make it inactive
        v.deactivate(fid, &[]);
        assert_eq!(v.propagate(fid, 0), PropagateResult::Inactive);

        // Out of bounds
        let mut v = Verifier::new();
        let fid = v.create(&Cnf::new());
        assert_eq!(v.propagate(fid, 0), PropagateResult::Inactive);
    }

    #[test]
    fn propagate_idempotent() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        let mut v = Verifier::new();
        let fid = v.create(&cnf);
        assert_eq!(v.propagate(fid, 0), PropagateResult::Propagated(x));
        assert_eq!(v.propagate(fid, 0), PropagateResult::Satisfied);
    }

    #[test]
    fn is_unsat_after_check() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);
        let proof = DratProof::new([DratStep::Add(Clause::new([]))]);

        let mut v = Verifier::new();
        let fid = v.create(&cnf);
        assert!(!v.is_unsat(fid));
        assert!(check(&mut v, fid, &proof, &mut FullScanAdvisor));
        assert!(v.is_unsat(fid));
    }

    // -- multi-formula tests --

    #[test]
    fn multiple_formulas_in_one_verifier() {
        let mut cnf1 = Cnf::new();
        let x = cnf1.fresh();
        cnf1.clause([x]);
        cnf1.clause([!x]);
        let proof1 = DratProof::new([DratStep::Add(Clause::new([]))]);

        let mut cnf2 = Cnf::new();
        let a = cnf2.fresh();
        let b = cnf2.fresh();
        cnf2.clause([a, b]);
        cnf2.clause([a, !b]);
        cnf2.clause([!a, b]);
        cnf2.clause([!a, !b]);
        let proof2 = DratProof::new([
            DratStep::Add(Clause::new([a])),
            DratStep::Add(Clause::new([!a])),
            DratStep::Add(Clause::new([])),
        ]);

        let mut v = Verifier::new();
        let fid1 = v.create(&cnf1);
        let fid2 = v.create(&cnf2);

        assert_ne!(fid1, fid2);

        // Check both independently
        assert!(check(&mut v, fid1, &proof1, &mut FullScanAdvisor));
        assert!(check(&mut v, fid2, &proof2, &mut WatchedAdvisor::new()));

        assert!(v.is_unsat(fid1));
        assert!(v.is_unsat(fid2));
    }

    #[test]
    fn delete_formula_returns_defaults() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);

        let mut v = Verifier::new();
        let fid = v.create(&cnf);
        assert_eq!(v.num_clauses(fid), 1);
        assert_eq!(v.original_num_vars(fid), 1);

        v.delete(fid);

        // All accessors return defaults
        assert_eq!(v.num_clauses(fid), 0);
        assert_eq!(v.original_num_vars(fid), 0);
        assert_eq!(v.original_num_clauses(fid), 0);
        assert_eq!(v.original_clause_len(fid, 0), 0);
        assert_eq!(v.original_clause_lit(fid, 0, 0), None);
        assert_eq!(v.clause_len(fid, 0), 0);
        assert_eq!(v.clause_lit(fid, 0, 0), None);
        assert!(!v.is_active(fid, 0));
        assert_eq!(v.get(fid, x), Decision::Unknown);
        assert!(!v.is_unsat(fid));
        assert_eq!(v.propagate(fid, 0), PropagateResult::Inactive);
    }

    #[test]
    fn deleted_slot_reused() {
        let mut v = Verifier::new();
        let fid1 = v.create(&Cnf::new());
        let fid2 = v.create(&Cnf::new());
        assert_eq!(fid1, FormulaId(0));
        assert_eq!(fid2, FormulaId(1));

        v.delete(fid1);
        let fid3 = v.create(&Cnf::new());
        // Slot 0 should be reused
        assert_eq!(fid3, FormulaId(0));
    }

    #[test]
    fn invalid_formula_id_returns_defaults() {
        let v = Verifier::new();
        let bad = FormulaId(99);
        assert_eq!(v.num_clauses(bad), 0);
        assert_eq!(v.original_num_vars(bad), 0);
        assert!(!v.is_unsat(bad));
    }

    #[test]
    fn original_formula_accessors() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, !y]);
        cnf.clause([!x]);

        let mut v = Verifier::new();
        let fid = v.create(&cnf);

        assert_eq!(v.original_num_vars(fid), 2);
        assert_eq!(v.original_num_clauses(fid), 2);
        assert_eq!(v.original_clause_len(fid, 0), 2);
        assert_eq!(v.original_clause_len(fid, 1), 1);
        assert_eq!(v.original_clause_lit(fid, 0, 0), Some(x));
        assert_eq!(v.original_clause_lit(fid, 0, 1), Some(!y));
        assert_eq!(v.original_clause_lit(fid, 1, 0), Some(!x));
        assert_eq!(v.original_clause_lit(fid, 0, 5), None);
        assert_eq!(v.original_clause_lit(fid, 5, 0), None);
    }
}
