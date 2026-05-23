use crate::{Clause, Cnf, Lit, Model};

/// A single DRAT proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DratStep {
    /// Add a clause (must be an Asymmetric Tautology w.r.t. active clauses).
    Add(Clause),
    /// Delete a clause from the active set.
    Delete(Clause),
}

/// A DRAT proof — a sequence of clause addition/deletion steps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DratProof(Vec<DratStep>);

impl DratProof {
    /// Create a proof from an iterator of steps.
    pub fn new(steps: impl IntoIterator<Item = DratStep>) -> Self {
        DratProof(steps.into_iter().collect())
    }

    /// The steps of this proof.
    pub fn steps(&self) -> &[DratStep] {
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

/// Abstract DRAT verifier.
///
/// Implementations maintain a set of active clauses and check that
/// each added clause is an Asymmetric Tautology (AT).
/// Designed to be implementable both as a pure Rust checker and
/// as a wrapper over the WASM kernel engine.
pub trait DratVerifier {
    /// Check that `clause` is AT w.r.t. active clauses, and if so, add it.
    fn add_clause(&mut self, clause: &Clause) -> bool;

    /// Remove a clause from the active set.
    fn delete_clause(&mut self, clause: &Clause);

    /// Has the empty clause been derived?
    fn is_complete(&self) -> bool;
}

/// Drive a verifier through all steps of a DRAT proof.
/// Returns true iff every Add step is AT and the empty clause is derived.
pub fn check_proof(verifier: &mut impl DratVerifier, proof: &DratProof) -> bool {
    for step in proof.steps() {
        match step {
            DratStep::Add(clause) => {
                if !verifier.add_clause(clause) {
                    return false;
                }
            }
            DratStep::Delete(clause) => {
                verifier.delete_clause(clause);
            }
        }
    }
    verifier.is_complete()
}

/// Simple O(n²) DRAT checker: full clause scan per unit propagation round.
pub struct NaiveDratChecker {
    /// (literals, active flag) for each clause.
    clauses: Vec<(Vec<Lit>, bool)>,
    num_vars: u32,
    complete: bool,
}

impl NaiveDratChecker {
    /// Create a checker initialized with the clauses from a CNF formula.
    pub fn new(cnf: &Cnf) -> Self {
        let clauses = cnf.clauses().map(|c| (c.lits().to_vec(), true)).collect();
        NaiveDratChecker {
            clauses,
            num_vars: cnf.num_vars(),
            complete: false,
        }
    }

    /// AT check: returns true if `lits` is an Asymmetric Tautology w.r.t.
    /// the current active clauses.
    fn is_at(&self, lits: &[Lit], model: &mut Model) -> bool {
        // Assign ¬l for each literal in the candidate clause.
        for &lit in lits {
            let var = lit.var();
            // If two literals in the candidate negate the same variable,
            // the clause is trivially a tautology.
            if model.get(lit) == crate::Decision::Sat {
                return true;
            }
            model.set(var, !lit.polarity());
        }

        // Unit propagation loop.
        loop {
            let mut progress = false;

            for (clause_lits, active) in &self.clauses {
                if !*active {
                    continue;
                }

                let mut satisfied = false;
                let mut unset_count = 0u32;
                let mut last_unset = None;

                for &lit in clause_lits {
                    match model.get(lit) {
                        crate::Decision::Sat => {
                            satisfied = true;
                            break;
                        }
                        crate::Decision::Unknown => {
                            unset_count += 1;
                            last_unset = Some(lit);
                        }
                        crate::Decision::Unsat => {}
                    }
                }

                if satisfied {
                    continue;
                }

                if unset_count == 0 {
                    // Conflict — all literals false → clause is AT.
                    return true;
                }

                if unset_count == 1 {
                    // Unit — assign the remaining literal true.
                    let unit_lit = last_unset.unwrap();
                    model.set(unit_lit.var(), unit_lit.polarity());
                    progress = true;
                    // Restart scan from the beginning.
                    break;
                }
            }

            if !progress {
                // Fixpoint reached without conflict.
                return false;
            }
        }
    }
}

impl DratVerifier for NaiveDratChecker {
    fn add_clause(&mut self, clause: &Clause) -> bool {
        let mut model = Model::new(self.num_vars);
        model.push();

        let at = self.is_at(clause.lits(), &mut model);

        if at {
            if clause.is_empty() {
                self.complete = true;
            }
            // Track num_vars in case the proof introduces new variables.
            for &lit in clause.lits() {
                let idx = lit.var().index() as u32;
                if idx > self.num_vars {
                    self.num_vars = idx;
                }
            }
            self.clauses.push((clause.lits().to_vec(), true));
        }

        at
    }

    fn delete_clause(&mut self, clause: &Clause) {
        let target: &[Lit] = clause.lits();
        for (lits, active) in &mut self.clauses {
            if *active && lits.as_slice() == target {
                *active = false;
                return;
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
    fn trivial_unsat_proof() {
        // {x} ∧ {¬x}, proof: Add(∅)
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([!x]);

        let proof = DratProof::new([DratStep::Add(Clause::new([]))]);

        let mut checker = NaiveDratChecker::new(&cnf);
        assert!(check_proof(&mut checker, &proof));
    }

    #[test]
    fn invalid_proof_rejected() {
        // {x,y} ∧ {x,¬y} ∧ {¬x,y} ∧ {¬x,¬y} — UNSAT but no unit clauses.
        // Unit prop from empty assignment reaches fixpoint without conflict,
        // so ∅ is NOT AT without intermediate steps.
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, y]);
        cnf.clause([x, !y]);
        cnf.clause([!x, y]);
        cnf.clause([!x, !y]);

        let proof = DratProof::new([DratStep::Add(Clause::new([]))]);

        let mut checker = NaiveDratChecker::new(&cnf);
        assert!(!check_proof(&mut checker, &proof));
    }

    #[test]
    fn proof_len_and_empty() {
        let proof = DratProof::new([]);
        assert!(proof.is_empty());
        assert_eq!(proof.len(), 0);

        let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
        assert!(!proof.is_empty());
        assert_eq!(proof.len(), 1);
    }
}
