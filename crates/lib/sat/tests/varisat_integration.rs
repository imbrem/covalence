#![cfg(feature = "drat")]
//! Integration test: connect covalence-sat to the varisat CDCL solver.

use covalence_sat::{
    Clause, Cnf, Decision, DratProof, DratStep, Model, NaiveDratChecker, SolveError, Solver,
    check_proof,
};

/// Thin wrapper around [`varisat::Solver`] implementing our [`Solver`] trait.
struct Varisat;

impl Solver for Varisat {
    fn solve(&self, cnf: &Cnf) -> Result<Model, SolveError> {
        use varisat::ExtendFormula;

        let mut solver = varisat::Solver::new();

        for clause in cnf.clauses() {
            let lits: Vec<varisat::Lit> = clause
                .lits()
                .iter()
                .map(|l| varisat::Lit::from_dimacs(l.dimacs() as isize))
                .collect();
            solver.add_clause(&lits);
        }

        let sat = solver
            .solve()
            .map_err(|e| SolveError::Internal(e.to_string()))?;

        if !sat {
            return Err(SolveError::Unsat);
        }

        let varisat_model = solver
            .model()
            .ok_or_else(|| SolveError::Internal("no model after SAT".into()))?;

        // Build our Model from varisat's literal assignments.
        let mut values = vec![false; cnf.num_vars() as usize];
        for &lit in &varisat_model {
            let d = lit.to_dimacs();
            let idx = d.unsigned_abs() - 1;
            values[idx] = d > 0;
        }

        Ok(Model::from_total(values))
    }
}

// --------------------------------------------------------------------
// SAT tests
// --------------------------------------------------------------------

#[test]
fn trivial_sat() {
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]); // (x) — trivially satisfiable

    let model = Varisat.solve(&cnf).expect("should be SAT");
    assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
}

#[test]
fn equivalence_sat() {
    // (x ∨ ¬y) ∧ (¬x ∨ y) — x ≡ y, two satisfying assignments
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    let y = cnf.fresh();
    cnf.clause([x, !y]);
    cnf.clause([!x, y]);

    let model = Varisat.solve(&cnf).expect("should be SAT");
    assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
}

#[test]
fn three_coloring_triangle() {
    // 3-color a triangle (K₃). Variables: c[node][color], 3 nodes × 3 colors = 9 vars.
    let mut cnf = Cnf::new();

    // c[i][k] = variable for "node i has color k"
    let mut c = [[cnf.fresh(); 3]; 3]; // placeholder, overwrite below
    for row in &mut c {
        for slot in row {
            *slot = cnf.fresh();
        }
    }

    // At-least-one color per node
    for &row in &c {
        cnf.clause(row);
    }

    // At-most-one color per node (pairwise exclusion)
    for row in &c {
        for k1 in 0..3 {
            for k2 in (k1 + 1)..3 {
                cnf.clause([!row[k1], !row[k2]]);
            }
        }
    }

    // Adjacent nodes differ (K₃: every pair is an edge)
    let edges = [(0, 1), (0, 2), (1, 2)];
    for &(u, v) in &edges {
        for (&cu, &cv) in c[u].iter().zip(&c[v]) {
            cnf.clause([!cu, !cv]);
        }
    }

    let model = Varisat.solve(&cnf).expect("K₃ is 3-colorable");
    assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
}

// --------------------------------------------------------------------
// UNSAT tests
// --------------------------------------------------------------------

#[test]
fn trivial_unsat() {
    // (x) ∧ (¬x) — contradictory
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let err = Varisat.solve(&cnf).expect_err("should be UNSAT");
    assert!(matches!(err, SolveError::Unsat));
}

#[test]
fn empty_clause_unsat() {
    // A formula containing the empty clause is always UNSAT
    let mut cnf = Cnf::new();
    cnf.clause([]);

    let err = Varisat.solve(&cnf).expect_err("should be UNSAT");
    assert!(matches!(err, SolveError::Unsat));
}

#[test]
fn two_coloring_triangle_unsat() {
    // 2-color K₃ — impossible (K₃ has chromatic number 3)
    let mut cnf = Cnf::new();

    let mut c = [[cnf.fresh(); 2]; 3];
    for row in &mut c {
        for slot in row {
            *slot = cnf.fresh();
        }
    }

    // At-least-one color per node
    for &row in &c {
        cnf.clause(row);
    }

    // At-most-one color per node
    for row in &c {
        cnf.clause([!row[0], !row[1]]);
    }

    // Adjacent nodes differ
    let edges = [(0, 1), (0, 2), (1, 2)];
    for &(u, v) in &edges {
        for (&cu, &cv) in c[u].iter().zip(&c[v]) {
            cnf.clause([!cu, !cv]);
        }
    }

    let err = Varisat.solve(&cnf).expect_err("K₃ is not 2-colorable");
    assert!(matches!(err, SolveError::Unsat));
}

// --------------------------------------------------------------------
// Edge cases
// --------------------------------------------------------------------

#[test]
fn empty_formula_sat() {
    // Empty formula is vacuously satisfiable
    let cnf = Cnf::new();
    let model = Varisat.solve(&cnf).expect("should be SAT");
    assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
}

#[test]
fn large_random_sat() {
    // Generate a formula known to be SAT by construction:
    // pick a random total assignment, then generate clauses that are satisfied by it.
    let num_vars = 50;
    let mut cnf = Cnf::new();
    let vars: Vec<_> = (0..num_vars).map(|_| cnf.fresh()).collect();

    // Target assignment: variable i is true iff i is even
    let target: Vec<bool> = (0..num_vars).map(|i| i % 2 == 0).collect();

    // Generate 200 random 3-clauses satisfied by target
    // Use a simple deterministic "random" for reproducibility
    let mut seed: u64 = 42;
    for _ in 0..200 {
        let mut clause_lits = Vec::new();
        let mut any_satisfied = false;

        for _ in 0..3 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let idx = (seed >> 33) as usize % num_vars;
            let polarity = (seed >> 32) & 1 == 0;

            let lit = if polarity { vars[idx] } else { !vars[idx] };
            // Check if this literal is satisfied by target
            let satisfied = target[idx] == polarity;
            if satisfied {
                any_satisfied = true;
            }
            clause_lits.push(lit);
        }

        // Ensure at least one literal is satisfied
        if !any_satisfied {
            let idx = (seed >> 16) as usize % num_vars;
            let lit = if target[idx] { vars[idx] } else { !vars[idx] };
            clause_lits[0] = lit;
        }

        cnf.clause(clause_lits);
    }

    let model = Varisat.solve(&cnf).expect("constructed to be SAT");
    assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
}

// --------------------------------------------------------------------
// DRAT verification tests
// --------------------------------------------------------------------

#[test]
fn drat_trivial_unsat() {
    // {x} ∧ {¬x}, proof: Add(∅)
    // AT check for ∅: no literals to negate → empty assignment.
    // Unit prop: {x} forces x=true, then {¬x} has all lits false → CONFLICT.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof));
}

#[test]
fn drat_three_clause_unsat() {
    // {x,y} ∧ {x,¬y} ∧ {¬x}, proof: [Add({x}), Add(∅)]
    //
    // Step 1 — Add({x}):
    //   Negate x → assign x=false.
    //   Unit prop: {¬x} satisfied (skip). {x,y}: x false, y unset → unit, assign y=true.
    //   {x,¬y}: x false, ¬y false → CONFLICT. AT ✓
    //
    // Step 2 — Add(∅):
    //   Empty assignment. Unit prop: {¬x} → x=false. {x}: x false → CONFLICT. AT ✓
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
    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof));
}

#[test]
fn drat_with_deletion() {
    // {x} ∧ {¬x}: derive ∅, delete it, then re-derive ∅.
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    let proof = DratProof::new([
        DratStep::Add(Clause::new([])),
        DratStep::Delete(Clause::new([])),
        DratStep::Add(Clause::new([])),
    ]);
    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof));
}

#[test]
fn drat_invalid_proof_rejected() {
    // {x,y} ∧ {x,¬y} ∧ {¬x,y} ∧ {¬x,¬y} — UNSAT but no unit clauses.
    // ∅ is NOT AT without intermediate derivations.
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
fn drat_solver_plus_verifier() {
    // Use varisat to confirm UNSAT, then verify a hand-crafted DRAT proof
    // for the same formula.
    //
    // Formula: {x} ∧ {¬x}
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);

    // SAT solver confirms UNSAT.
    let err = Varisat.solve(&cnf).expect_err("should be UNSAT");
    assert!(matches!(err, SolveError::Unsat));

    // DRAT proof independently confirms UNSAT.
    let proof = DratProof::new([DratStep::Add(Clause::new([]))]);
    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof));
}
