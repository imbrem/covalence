//! Multi-formula DRAT proof checker with full RAT support.
//!
//! [`DratChecker`] is a trait for multi-formula DRAT checkers.
//! [`NaiveMultiDratChecker`] is the naive O(n²) implementation that
//! supports both AT (asymmetric tautology) and RAT (resolution
//! asymmetric tautology) steps.
//!
//! The [`check`] free function drives a checker through all steps of
//! a proof.

use crate::{Cnf, Decision, DratProof, DratStep, Lit, Model};

// ---------------------------------------------------------------------------
// FormulaId
// ---------------------------------------------------------------------------

/// Opaque identifier for a formula managed by a [`DratChecker`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FormulaId(u32);

// ---------------------------------------------------------------------------
// DratChecker trait
// ---------------------------------------------------------------------------

/// Multi-formula DRAT proof checker.
pub trait DratChecker {
    /// Register a CNF formula, return its ID.
    fn create(&mut self, cnf: &Cnf) -> FormulaId;
    /// Delete a formula, freeing its slot.
    fn delete(&mut self, fid: FormulaId);
    /// Apply one DRAT step. Returns false if an Add step is not
    /// AT or RAT (proof invalid).
    fn step(&mut self, fid: FormulaId, step: &DratStep) -> bool;
    /// Has the empty clause been derived?
    fn is_unsat(&self, fid: FormulaId) -> bool;
}

// ---------------------------------------------------------------------------
// check — standard proof loop
// ---------------------------------------------------------------------------

/// Drive a checker through all steps of a proof.
///
/// Returns `true` iff every Add step is AT or RAT and the empty clause
/// is derived (proving UNSAT).
pub fn check(checker: &mut impl DratChecker, fid: FormulaId, proof: &DratProof) -> bool {
    for step in proof.steps() {
        if !checker.step(fid, step) {
            return false;
        }
    }
    checker.is_unsat(fid)
}

// ---------------------------------------------------------------------------
// FormulaState (private)
// ---------------------------------------------------------------------------

struct FormulaState {
    clauses: Vec<(Vec<Lit>, bool)>,
    num_vars: u32,
    complete: bool,
}

// ---------------------------------------------------------------------------
// NaiveMultiDratChecker
// ---------------------------------------------------------------------------

/// Naive O(n²) multi-formula DRAT checker with full RAT support.
///
/// Each formula gets its own clause database. AT checks use full-scan
/// BCP. When AT fails, RAT is attempted with pivot = first literal of
/// the candidate clause.
pub struct NaiveMultiDratChecker {
    formulas: Vec<Option<FormulaState>>,
    free_list: Vec<u32>,
}

impl NaiveMultiDratChecker {
    /// Create an empty checker with no formulas.
    pub fn new() -> Self {
        NaiveMultiDratChecker {
            formulas: Vec::new(),
            free_list: Vec::new(),
        }
    }

    fn get_state(&self, fid: FormulaId) -> Option<&FormulaState> {
        self.formulas.get(fid.0 as usize).and_then(|s| s.as_ref())
    }

    fn get_state_mut(&mut self, fid: FormulaId) -> Option<&mut FormulaState> {
        self.formulas
            .get_mut(fid.0 as usize)
            .and_then(|s| s.as_mut())
    }
}

impl Default for NaiveMultiDratChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl DratChecker for NaiveMultiDratChecker {
    fn create(&mut self, cnf: &Cnf) -> FormulaId {
        let clauses = cnf.clauses().map(|c| (c.lits().to_vec(), true)).collect();
        let state = FormulaState {
            clauses,
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

    fn delete(&mut self, fid: FormulaId) {
        if let Some(slot) = self.formulas.get_mut(fid.0 as usize) {
            if slot.is_some() {
                *slot = None;
                self.free_list.push(fid.0);
            }
        }
    }

    fn step(&mut self, fid: FormulaId, step: &DratStep) -> bool {
        let state = match self.get_state_mut(fid) {
            Some(s) => s,
            None => return false,
        };

        match step {
            DratStep::Add(clause) => {
                // Extend num_vars for new variables in the candidate.
                for &lit in clause.lits() {
                    let v = lit.var().index() as u32;
                    if v > state.num_vars {
                        state.num_vars = v;
                    }
                }

                let num_vars = state.num_vars;
                let lits = clause.lits();

                // AT check.
                let mut model = Model::new(num_vars);
                model.push();
                let at = is_at(&state.clauses, lits, &mut model);
                model.pop();

                let valid = if at {
                    true
                } else {
                    // RAT check (only meaningful for non-empty clauses).
                    !lits.is_empty() && is_rat(&state.clauses, lits, num_vars)
                };

                if !valid {
                    return false;
                }

                if clause.is_empty() {
                    state.complete = true;
                }
                state.clauses.push((lits.to_vec(), true));
            }
            DratStep::Delete(clause) => {
                let target = clause.lits();
                for (lits, active) in &mut state.clauses {
                    if *active && lits_match(lits, target) {
                        *active = false;
                        break;
                    }
                }
            }
        }
        true
    }

    fn is_unsat(&self, fid: FormulaId) -> bool {
        self.get_state(fid).is_some_and(|s| s.complete)
    }
}

// ---------------------------------------------------------------------------
// Clause matching (set-based, order-independent)
// ---------------------------------------------------------------------------

/// Check if two literal slices represent the same clause (same set of
/// literals, regardless of order). Assumes no duplicate literals.
fn lits_match(a: &[Lit], b: &[Lit]) -> bool {
    a.len() == b.len() && a.iter().all(|lit| b.contains(lit))
}

// ---------------------------------------------------------------------------
// AT check
// ---------------------------------------------------------------------------

/// Returns true if `candidate` is an Asymmetric Tautology w.r.t. the
/// given clauses. The model must have an active checkpoint (via `push`).
fn is_at(clauses: &[(Vec<Lit>, bool)], candidate: &[Lit], model: &mut Model) -> bool {
    // Negate each literal in the candidate clause.
    for &lit in candidate {
        if model.get(lit) == Decision::Sat {
            // Complementary literals in candidate → tautology.
            return true;
        }
        if model.get(lit) == Decision::Unknown {
            model.set(lit.var(), !lit.polarity());
        }
    }

    // Full-scan unit propagation.
    loop {
        let mut progress = false;

        for (clause_lits, active) in clauses {
            if !*active {
                continue;
            }

            let mut satisfied = false;
            let mut unset_count = 0u32;
            let mut last_unset = None;

            for &lit in clause_lits {
                match model.get(lit) {
                    Decision::Sat => {
                        satisfied = true;
                        break;
                    }
                    Decision::Unknown => {
                        unset_count += 1;
                        last_unset = Some(lit);
                    }
                    Decision::Unsat => {}
                }
            }

            if satisfied {
                continue;
            }

            if unset_count == 0 {
                // Conflict — all literals false.
                return true;
            }

            if unset_count == 1 {
                let unit_lit = last_unset.unwrap();
                model.set(unit_lit.var(), unit_lit.polarity());
                progress = true;
                break; // restart scan
            }
        }

        if !progress {
            return false;
        }
    }
}

// ---------------------------------------------------------------------------
// RAT check
// ---------------------------------------------------------------------------

/// Returns true if `candidate` is a Resolution Asymmetric Tautology
/// w.r.t. the given clauses, using pivot = `candidate[0]`.
///
/// For each active clause D containing ¬pivot, the resolvent
/// (candidate ∪ D) \ {pivot, ¬pivot} must be AT.
fn is_rat(clauses: &[(Vec<Lit>, bool)], candidate: &[Lit], num_vars: u32) -> bool {
    let pivot = candidate[0];
    let neg_pivot = !pivot;

    for (clause_lits, active) in clauses {
        if !*active {
            continue;
        }
        if !clause_lits.contains(&neg_pivot) {
            continue;
        }

        // Compute resolvent: (candidate ∪ clause_lits) \ {pivot, ¬pivot},
        // deduplicated.
        let mut resolvent: Vec<Lit> = Vec::new();
        for &lit in candidate {
            if lit != pivot && lit != neg_pivot && !resolvent.contains(&lit) {
                resolvent.push(lit);
            }
        }
        for &lit in clause_lits {
            if lit != pivot && lit != neg_pivot && !resolvent.contains(&lit) {
                resolvent.push(lit);
            }
        }

        // Check if the resolvent is AT.
        let mut model = Model::new(num_vars);
        model.push();
        let at = is_at(clauses, &resolvent, &mut model);
        model.pop();

        if !at {
            return false;
        }
    }

    true
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Clause, Cnf, DratProof, DratStep};

    fn check_advised(cnf: &Cnf, proof: &DratProof) -> bool {
        let mut checker = NaiveMultiDratChecker::new();
        let fid = checker.create(cnf);
        check(&mut checker, fid, proof)
    }

    // -- acceptance --

    #[test]
    fn trivial_unsat() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);
        let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
        assert!(check_advised(&cnf, &proof));
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
        assert!(check_advised(&cnf, &proof));
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
        assert!(check_advised(&cnf, &proof));
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
        assert!(check_advised(&cnf, &proof));
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
        assert!(check_advised(&cnf, &proof));
    }

    // -- rejection --

    #[test]
    fn empty_proof_rejected() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);
        assert!(!check_advised(&cnf, &DratProof::new([])));
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
        assert!(!check_advised(
            &cnf,
            &DratProof::new([DratStep::Add(Clause::new([]))])
        ));
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
        assert!(!check_advised(&cnf, &proof));
    }

    #[test]
    fn non_at_clause() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([!x, y]);
        assert!(!check_advised(
            &cnf,
            &DratProof::new([DratStep::Add(Clause::new([!y]))])
        ));
    }

    #[test]
    fn sat_formula_rejected() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        assert!(!check_advised(
            &cnf,
            &DratProof::new([DratStep::Add(Clause::new([]))])
        ));
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
        assert!(!check_advised(&cnf, &proof));
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
        assert!(!check_advised(&cnf, &proof));
    }

    // -- RAT tests --

    #[test]
    fn rat_clause_accepted() {
        // All 8 ternary clauses over 3 vars — unsatisfiable.
        // {a} is NOT AT but IS RAT with pivot a.
        // After adding {a}, {b} is AT, then {} is AT.
        let mut cnf = Cnf::new();
        let a = cnf.fresh();
        let b = cnf.fresh();
        let c = cnf.fresh();
        cnf.clause([a, b, c]);
        cnf.clause([a, b, !c]);
        cnf.clause([a, !b, c]);
        cnf.clause([a, !b, !c]);
        cnf.clause([!a, b, c]);
        cnf.clause([!a, b, !c]);
        cnf.clause([!a, !b, c]);
        cnf.clause([!a, !b, !c]);

        let proof = DratProof::new([
            DratStep::Add(Clause::new([a])), // RAT
            DratStep::Add(Clause::new([b])), // AT
            DratStep::Add(Clause::new([])),  // AT
        ]);
        assert!(check_advised(&cnf, &proof));
    }

    #[test]
    fn rat_clause_rejected_by_at_only() {
        // Same formula — AT-only checker (from drat.rs) rejects the
        // first step since {a} is not AT.
        let mut cnf = Cnf::new();
        let a = cnf.fresh();
        let b = cnf.fresh();
        let c = cnf.fresh();
        cnf.clause([a, b, c]);
        cnf.clause([a, b, !c]);
        cnf.clause([a, !b, c]);
        cnf.clause([a, !b, !c]);
        cnf.clause([!a, b, c]);
        cnf.clause([!a, b, !c]);
        cnf.clause([!a, !b, c]);
        cnf.clause([!a, !b, !c]);

        let proof = DratProof::new([
            DratStep::Add(Clause::new([a])),
            DratStep::Add(Clause::new([b])),
            DratStep::Add(Clause::new([])),
        ]);
        let mut old_checker = crate::NaiveDratChecker::new(&cnf);
        assert!(!crate::check_proof(&mut old_checker, &proof));
    }

    #[test]
    fn vacuous_rat_new_variable() {
        // Adding a clause with a variable not in any existing clause
        // is vacuously RAT (no clause contains ¬pivot).
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);

        let d = Lit::from_dimacs(3).unwrap(); // new variable not in CNF
        let proof = DratProof::new([
            DratStep::Add(Clause::new([d])), // vacuous RAT
            DratStep::Add(Clause::new([])),  // AT (original {x},{!x} still active)
        ]);
        assert!(check_advised(&cnf, &proof));
    }

    // -- lifecycle tests --

    #[test]
    fn is_unsat_after_check() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);
        let proof = DratProof::new([DratStep::Add(Clause::new([]))]);

        let mut checker = NaiveMultiDratChecker::new();
        let fid = checker.create(&cnf);
        assert!(!checker.is_unsat(fid));
        assert!(check(&mut checker, fid, &proof));
        assert!(checker.is_unsat(fid));
    }

    #[test]
    fn multiple_formulas() {
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

        let mut checker = NaiveMultiDratChecker::new();
        let fid1 = checker.create(&cnf1);
        let fid2 = checker.create(&cnf2);
        assert_ne!(fid1, fid2);

        assert!(check(&mut checker, fid1, &proof1));
        assert!(check(&mut checker, fid2, &proof2));
        assert!(checker.is_unsat(fid1));
        assert!(checker.is_unsat(fid2));
    }

    #[test]
    fn deleted_slot_reused() {
        let mut checker = NaiveMultiDratChecker::new();
        let fid1 = checker.create(&Cnf::new());
        let fid2 = checker.create(&Cnf::new());
        assert_eq!(fid1, FormulaId(0));
        assert_eq!(fid2, FormulaId(1));

        checker.delete(fid1);
        let fid3 = checker.create(&Cnf::new());
        assert_eq!(fid3, FormulaId(0)); // slot reused
    }

    #[test]
    fn deleted_formula_returns_defaults() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);

        let mut checker = NaiveMultiDratChecker::new();
        let fid = checker.create(&cnf);
        assert!(!checker.is_unsat(fid));

        checker.delete(fid);
        assert!(!checker.is_unsat(fid));
    }

    #[test]
    fn invalid_formula_id() {
        let checker = NaiveMultiDratChecker::new();
        let bad = FormulaId(99);
        assert!(!checker.is_unsat(bad));
    }
}
