use std::collections::HashMap;

use crate::{Clause, Cnf, Decision, Lit};

/// A single LRAT proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LratStep {
    /// Add a clause with explicit antecedent clause IDs.
    Add {
        id: u64,
        clause: Clause,
        antecedents: Vec<u64>,
    },
    /// Delete clauses by their IDs.
    Delete { id: u64, clause_ids: Vec<u64> },
}

/// An LRAT proof — a sequence of clause addition/deletion steps with
/// explicit clause IDs and antecedent hints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LratProof(Vec<LratStep>);

impl LratProof {
    /// Create a proof from an iterator of steps.
    pub fn new(steps: impl IntoIterator<Item = LratStep>) -> Self {
        LratProof(steps.into_iter().collect())
    }

    /// The steps of this proof.
    pub fn steps(&self) -> &[LratStep] {
        &self.0
    }

    /// Number of steps.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is the proof empty?
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Abstract LRAT checker.
///
/// Implementations maintain a set of active clauses and check each added
/// clause against its explicit antecedent list via unit propagation.
pub trait LratChecker {
    /// Check that `clause` follows from the given `antecedents` via unit
    /// propagation, and add it with `id`.
    fn add_clause(&mut self, id: u64, clause: &Clause, antecedents: &[u64]) -> bool;

    /// Remove clauses by their IDs.
    fn delete_clauses(&mut self, ids: &[u64]);

    /// Has the empty clause been derived?
    fn is_complete(&self) -> bool;
}

/// Drive a checker through all steps of an LRAT proof.
/// Returns true iff every Add step is valid and the empty clause is derived.
pub fn check_lrat_proof(checker: &mut impl LratChecker, proof: &LratProof) -> bool {
    for step in proof.steps() {
        match step {
            LratStep::Add {
                id,
                clause,
                antecedents,
            } => {
                if !checker.add_clause(*id, clause, antecedents) {
                    return false;
                }
            }
            LratStep::Delete { clause_ids, .. } => {
                checker.delete_clauses(clause_ids);
            }
        }
    }
    checker.is_complete()
}

/// Simple LRAT checker using explicit antecedent-based unit propagation.
///
/// Each addition step negates the new clause's literals and then processes
/// the antecedent clauses one by one. Each antecedent must become unit or
/// conflicting under the current assignment. A conflict means the new
/// clause follows from the antecedents.
pub struct NaiveLratChecker {
    /// Clause ID → (literals, active flag).
    clauses: HashMap<u64, (Vec<Lit>, bool)>,
    /// Flat assignment array indexed by var-1.
    assign: Vec<Decision>,
    /// Variables assigned during current check, for reset.
    trail: Vec<usize>,
    num_vars: u32,
    complete: bool,
}

/// Look up a literal's truth value in a flat assignment array (indexed by var-1).
fn assign_get(assign: &[Decision], lit: Lit) -> Decision {
    let val = assign[(lit.var().index() - 1) as usize];
    if lit.is_pos() { val } else { val.not() }
}

/// Set a literal to true, recording the variable index on the trail.
fn assign_set_true(assign: &mut [Decision], trail: &mut Vec<usize>, lit: Lit) {
    let vi = (lit.var().index() - 1) as usize;
    assign[vi] = if lit.is_pos() {
        Decision::Sat
    } else {
        Decision::Unsat
    };
    trail.push(vi);
}

impl NaiveLratChecker {
    /// Create a checker initialized with the clauses from a CNF formula.
    /// Original clauses are numbered 1, 2, 3, … matching DIMACS order.
    pub fn new(cnf: &Cnf) -> Self {
        let mut clauses = HashMap::new();
        for (i, clause) in cnf.clauses().enumerate() {
            clauses.insert((i + 1) as u64, (clause.lits().to_vec(), true));
        }
        NaiveLratChecker {
            clauses,
            assign: vec![Decision::Unknown; cnf.num_vars() as usize],
            trail: Vec::new(),
            num_vars: cnf.num_vars(),
            complete: false,
        }
    }

    /// Ensure the assignment array is large enough for the given variable.
    fn ensure_var(&mut self, var: u32) {
        if var > self.num_vars {
            self.num_vars = var;
            self.assign.resize(var as usize, Decision::Unknown);
        }
    }

    /// Undo all assignments on the trail.
    fn reset(&mut self) {
        for &vi in &self.trail {
            self.assign[vi] = Decision::Unknown;
        }
        self.trail.clear();
    }
}

impl LratChecker for NaiveLratChecker {
    fn add_clause(&mut self, id: u64, clause: &Clause, antecedents: &[u64]) -> bool {
        // Grow assignment if the clause introduces new variables.
        for &lit in clause.lits() {
            self.ensure_var(lit.var().index() as u32);
        }

        // Step 1: Negate each literal in the new clause.
        for &lit in clause.lits() {
            match assign_get(&self.assign, lit) {
                Decision::Unsat => {
                    // Already false — duplicate literal, skip.
                }
                Decision::Sat => {
                    // Complementary literals in the clause — tautology.
                    self.reset();
                    self.clauses.insert(id, (clause.lits().to_vec(), true));
                    return true;
                }
                Decision::Unknown => {
                    assign_set_true(&mut self.assign, &mut self.trail, !lit);
                }
            }
        }

        // Step 2: Process each antecedent via unit propagation.
        for &ante_id in antecedents {
            let ante_lits = match self.clauses.get(&ante_id) {
                Some((lits, true)) => lits.clone(),
                _ => {
                    // Antecedent doesn't exist or is inactive.
                    self.reset();
                    return false;
                }
            };

            // Grow assignment for antecedent variables.
            for &lit in &ante_lits {
                self.ensure_var(lit.var().index() as u32);
            }

            let mut unit_lit: Option<Lit> = None;
            let mut satisfied = false;

            for &lit in &ante_lits {
                match assign_get(&self.assign, lit) {
                    Decision::Sat => {
                        satisfied = true;
                        break;
                    }
                    Decision::Unknown => {
                        if unit_lit == Some(lit) {
                            // Duplicate literal in the antecedent, skip.
                            continue;
                        }
                        if unit_lit.is_some() {
                            // Two different unknown literals — not unit.
                            self.reset();
                            return false;
                        }
                        unit_lit = Some(lit);
                    }
                    Decision::Unsat => {}
                }
            }

            if satisfied {
                continue;
            }

            match unit_lit {
                None => {
                    // All literals false — conflict. Clause is valid.
                    if clause.is_empty() {
                        self.complete = true;
                    }
                    self.reset();
                    self.clauses.insert(id, (clause.lits().to_vec(), true));
                    return true;
                }
                Some(lit) => {
                    assign_set_true(&mut self.assign, &mut self.trail, lit);
                }
            }
        }

        // No conflict found — proof step is invalid.
        self.reset();
        false
    }

    fn delete_clauses(&mut self, ids: &[u64]) {
        for &id in ids {
            if let Some(entry) = self.clauses.get_mut(&id) {
                entry.1 = false;
            }
        }
    }

    fn is_complete(&self) -> bool {
        self.complete
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Cnf;

    #[test]
    fn trivial_unsat_lrat() {
        // {x} ∧ {¬x}, proof: clause 3 = ∅ from antecedents [1, 2]
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);

        let proof = LratProof::new([LratStep::Add {
            id: 3,
            clause: Clause::new([]),
            antecedents: vec![1, 2],
        }]);

        let mut checker = NaiveLratChecker::new(&cnf);
        assert!(check_lrat_proof(&mut checker, &proof));
    }

    #[test]
    fn invalid_antecedent_rejected() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);

        // Reference non-existent antecedent 99.
        let proof = LratProof::new([LratStep::Add {
            id: 3,
            clause: Clause::new([]),
            antecedents: vec![99],
        }]);

        let mut checker = NaiveLratChecker::new(&cnf);
        assert!(!check_lrat_proof(&mut checker, &proof));
    }

    #[test]
    fn tautology_accepted() {
        // A clause with complementary literals is trivially valid.
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);

        let proof = LratProof::new([LratStep::Add {
            id: 2,
            clause: Clause::new([x, !x]),
            antecedents: vec![],
        }]);

        let mut checker = NaiveLratChecker::new(&cnf);
        // Tautology alone doesn't derive the empty clause.
        assert!(!check_lrat_proof(&mut checker, &proof));
        assert!(checker.add_clause(2, &Clause::new([x, !x]), &[]));
    }

    #[test]
    fn deletion_makes_antecedent_invalid() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);

        let proof = LratProof::new([
            LratStep::Delete {
                id: 0,
                clause_ids: vec![1],
            },
            LratStep::Add {
                id: 3,
                clause: Clause::new([]),
                antecedents: vec![1, 2],
            },
        ]);

        let mut checker = NaiveLratChecker::new(&cnf);
        assert!(!check_lrat_proof(&mut checker, &proof));
    }

    #[test]
    fn proof_len_and_empty() {
        let proof = LratProof::new([]);
        assert!(proof.is_empty());
        assert_eq!(proof.len(), 0);

        let proof = LratProof::new([LratStep::Add {
            id: 1,
            clause: Clause::new([]),
            antecedents: vec![],
        }]);
        assert!(!proof.is_empty());
        assert_eq!(proof.len(), 1);
    }
}
