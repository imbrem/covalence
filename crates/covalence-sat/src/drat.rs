use crate::{Clause, Cnf, Decision, Lit, Model};

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

/// Map a literal to its watch-list index.
/// Positive lit for var v → `2*(v-1)`, negative → `2*(v-1)+1`.
fn lit_watch_idx(lit: Lit) -> usize {
    let v = (lit.var().index() - 1) as usize;
    2 * v + if lit.is_neg() { 1 } else { 0 }
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

/// DRAT checker using two-watched-literal unit propagation.
///
/// More efficient than [`NaiveDratChecker`] for formulas with many clauses:
/// unit propagation only visits clauses whose watched literal was just
/// falsified, instead of scanning the entire clause database each round.
///
/// For clauses with ≥2 literals, the first two elements of the literal
/// vector are the watched pair. When a watched literal becomes false, the
/// clause is inspected: if another non-false literal exists, the watch is
/// relocated; otherwise, the clause is unit or conflicting.
///
/// Empty and unit clauses are tracked separately in a short-clause list
/// and checked eagerly at the start of each AT check.
pub struct WatchedDratChecker {
    /// Clause storage. For clauses with ≥2 literals, `lits[0]` and `lits[1]`
    /// are the watched pair.
    clauses: Vec<WClause>,
    /// Indices into `clauses` for empty/unit clauses (len < 2).
    short: Vec<usize>,
    /// Watch lists indexed by `lit_watch_idx(l)`. Each entry is a list of
    /// clause indices where `l` is one of the two watched literals.
    watches: Vec<Vec<usize>>,
    /// Flat assignment array indexed by var-1. Reset via trail after each AT check.
    assign: Vec<Decision>,
    /// Variables assigned during the current AT check, for efficient reset.
    trail: Vec<usize>,
    num_vars: u32,
    complete: bool,
}

struct WClause {
    lits: Vec<Lit>,
    active: bool,
}

impl WatchedDratChecker {
    /// Create a checker initialized with the clauses from a CNF formula.
    pub fn new(cnf: &Cnf) -> Self {
        let num_vars = cnf.num_vars();
        let mut checker = WatchedDratChecker {
            clauses: Vec::new(),
            short: Vec::new(),
            watches: vec![Vec::new(); 2 * num_vars as usize],
            assign: vec![Decision::Unknown; num_vars as usize],
            trail: Vec::new(),
            num_vars,
            complete: false,
        };
        for clause in cnf.clauses() {
            checker.push_clause(clause.lits().to_vec());
        }
        checker
    }

    /// Grow internal arrays to accommodate `var` (1-indexed).
    fn ensure_var(&mut self, var: u32) {
        if var > self.num_vars {
            self.num_vars = var;
            self.watches.resize_with(2 * var as usize, Vec::new);
            self.assign.resize(var as usize, Decision::Unknown);
        }
    }

    /// Insert a clause into storage and set up watches.
    fn push_clause(&mut self, lits: Vec<Lit>) {
        let idx = self.clauses.len();
        if lits.len() >= 2 {
            self.watches[lit_watch_idx(lits[0])].push(idx);
            self.watches[lit_watch_idx(lits[1])].push(idx);
        } else {
            self.short.push(idx);
        }
        self.clauses.push(WClause { lits, active: true });
    }

    /// Undo all assignments made during the current AT check.
    fn reset(&mut self) {
        for &vi in &self.trail {
            self.assign[vi] = Decision::Unknown;
        }
        self.trail.clear();
    }

    /// AT check: returns true if `candidate` is an Asymmetric Tautology
    /// w.r.t. the current active clauses.
    fn is_at(&mut self, candidate: &[Lit]) -> bool {
        let mut queue: Vec<Lit> = Vec::new();

        // Negate each literal in the candidate clause.
        for &lit in candidate {
            if assign_get(&self.assign, lit) == Decision::Sat {
                // Complementary literals in candidate → trivially a tautology.
                self.reset();
                return true;
            }
            if assign_get(&self.assign, lit) == Decision::Unknown {
                assign_set_true(&mut self.assign, &mut self.trail, !lit);
                queue.push(lit); // lit just became false
            }
        }

        // Check short (empty/unit) clauses eagerly.
        for si in 0..self.short.len() {
            let ci = self.short[si];
            if !self.clauses[ci].active {
                continue;
            }
            if self.clauses[ci].lits.is_empty() {
                self.reset();
                return true; // empty clause → conflict
            }
            let u = self.clauses[ci].lits[0];
            match assign_get(&self.assign, u) {
                Decision::Sat => {}
                Decision::Unsat => {
                    self.reset();
                    return true;
                }
                Decision::Unknown => {
                    assign_set_true(&mut self.assign, &mut self.trail, u);
                    queue.push(!u); // ¬u just became false
                }
            }
        }

        // BCP with two-watched literals.
        let result = self.propagate(&mut queue);
        self.reset();
        result
    }

    /// Boolean constraint propagation using watched literals.
    /// Returns `true` on conflict (meaning the candidate clause is AT).
    fn propagate(&mut self, queue: &mut Vec<Lit>) -> bool {
        while let Some(false_lit) = queue.pop() {
            let widx = lit_watch_idx(false_lit);
            if widx >= self.watches.len() {
                continue;
            }

            // Take the watch list out to avoid borrow conflicts.
            let mut wlist = std::mem::take(&mut self.watches[widx]);
            let mut i = 0;

            while i < wlist.len() {
                let ci = wlist[i];

                if !self.clauses[ci].active {
                    wlist.swap_remove(i);
                    continue;
                }

                // Ensure false_lit is in the second watched position (lits[1]).
                if self.clauses[ci].lits[0] == false_lit {
                    self.clauses[ci].lits.swap(0, 1);
                }

                let other = self.clauses[ci].lits[0];

                // If the other watched literal is satisfied, clause is sat.
                if assign_get(&self.assign, other) == Decision::Sat {
                    i += 1;
                    continue;
                }

                // Try to find a non-false replacement for the watch at lits[1].
                let mut replacement = None;
                for j in 2..self.clauses[ci].lits.len() {
                    let lj = self.clauses[ci].lits[j];
                    if assign_get(&self.assign, lj) != Decision::Unsat {
                        replacement = Some(j);
                        break;
                    }
                }

                if let Some(j) = replacement {
                    // Swap the replacement into the watch position and relocate.
                    self.clauses[ci].lits.swap(1, j);
                    let new_widx = lit_watch_idx(self.clauses[ci].lits[1]);
                    self.watches[new_widx].push(ci);
                    wlist.swap_remove(i);
                    continue; // don't increment — swap_remove moved last element here
                }

                // No replacement found: all lits[2..] are false.
                match assign_get(&self.assign, other) {
                    Decision::Unsat => {
                        // All literals false → conflict.
                        self.watches[widx] = wlist;
                        return true;
                    }
                    Decision::Unknown => {
                        // Unit: propagate the other watched literal.
                        assign_set_true(&mut self.assign, &mut self.trail, other);
                        queue.push(!other);
                    }
                    Decision::Sat => {}
                }
                i += 1;
            }

            self.watches[widx] = wlist;
        }

        false
    }
}

impl DratVerifier for WatchedDratChecker {
    fn add_clause(&mut self, clause: &Clause) -> bool {
        for &lit in clause.lits() {
            self.ensure_var(lit.var().index() as u32);
        }

        let at = self.is_at(clause.lits());

        if at {
            if clause.is_empty() {
                self.complete = true;
            }
            self.push_clause(clause.lits().to_vec());
        }

        at
    }

    fn delete_clause(&mut self, clause: &Clause) {
        let target = clause.lits();
        for c in &mut self.clauses {
            if c.active && c.lits == target {
                c.active = false;
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
