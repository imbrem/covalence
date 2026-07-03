#![cfg(feature = "drat")]
//! Integration tests for the DIMACS/DRAT parsers, loading shared test asset files.

use std::path::PathBuf;

use covalence_sat::{
    Decision, DratProof, Model, NaiveDratChecker, Solver, WatchedDratChecker, check_proof,
    parse::{
        parse_dimacs, parse_drat_binary, parse_drat_text, write_dimacs_to_string,
        write_drat_binary_to_vec, write_drat_text_to_string,
    },
};

fn asset_path(problem: &str, file: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../assets/tests/sat")
        .join(problem)
        .join(file)
}

fn load_cnf(problem: &str) -> covalence_sat::Cnf {
    let path = asset_path(problem, "problem.cnf");
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    parse_dimacs(&content).unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()))
}

fn load_drat(problem: &str) -> DratProof {
    let path = asset_path(problem, "proof.drat");
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    parse_drat_text(&content).unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()))
}

/// Parse the simple model.sat format: lines starting with `v` contain
/// space-separated literal integers terminated by `0`.
fn load_model(problem: &str) -> Vec<i32> {
    let path = asset_path(problem, "model.sat");
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    let mut lits = Vec::new();
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('v') {
            for token in trimmed[1..].split_whitespace() {
                let val: i32 = token.parse().expect("model literal should be integer");
                if val == 0 {
                    break;
                }
                lits.push(val);
            }
        }
    }
    lits
}

// --------------------------------------------------------------------
// Asset loading & structure verification
// --------------------------------------------------------------------

#[test]
fn trivial_unsat_structure() {
    let cnf = load_cnf("trivial-unsat");
    assert_eq!(cnf.num_vars(), 1);
    assert_eq!(cnf.num_clauses(), 2);
    // {x} and {¬x}
    let clauses: Vec<_> = cnf.clauses().collect();
    assert_eq!(clauses[0].len(), 1);
    assert_eq!(clauses[1].len(), 1);
    assert_eq!(clauses[0].lits()[0].dimacs(), 1);
    assert_eq!(clauses[1].lits()[0].dimacs(), -1);
}

#[test]
fn three_clause_unsat_structure() {
    let cnf = load_cnf("three-clause-unsat");
    assert_eq!(cnf.num_vars(), 2);
    assert_eq!(cnf.num_clauses(), 3);
}

#[test]
fn four_clause_unsat_structure() {
    let cnf = load_cnf("four-clause-unsat");
    assert_eq!(cnf.num_vars(), 2);
    assert_eq!(cnf.num_clauses(), 4);
    // All binary clauses.
    for clause in cnf.clauses() {
        assert_eq!(clause.len(), 2);
    }
}

#[test]
fn simple_sat_structure() {
    let cnf = load_cnf("simple-sat");
    assert_eq!(cnf.num_vars(), 2);
    assert_eq!(cnf.num_clauses(), 2);
}

#[test]
fn empty_clause_structure() {
    let cnf = load_cnf("empty-clause");
    assert_eq!(cnf.num_clauses(), 1);
    assert!(cnf.clauses().next().unwrap().is_empty());
}

// --------------------------------------------------------------------
// DRAT proof verification on parsed assets
// --------------------------------------------------------------------

#[test]
fn trivial_unsat_drat_verified() {
    let cnf = load_cnf("trivial-unsat");
    let proof = load_drat("trivial-unsat");
    assert_eq!(proof.len(), 1);

    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof));
}

#[test]
fn three_clause_unsat_drat_verified() {
    let cnf = load_cnf("three-clause-unsat");
    let proof = load_drat("three-clause-unsat");
    assert_eq!(proof.len(), 2);

    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof));
}

#[test]
fn four_clause_unsat_drat_verified() {
    let cnf = load_cnf("four-clause-unsat");
    let proof = load_drat("four-clause-unsat");
    assert_eq!(proof.len(), 3);

    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof));
}

// --------------------------------------------------------------------
// Binary DRAT roundtrip through parsed assets
// --------------------------------------------------------------------

#[test]
fn trivial_unsat_binary_roundtrip() {
    let proof = load_drat("trivial-unsat");
    let binary = write_drat_binary_to_vec(&proof);
    let proof2 = parse_drat_binary(&binary).unwrap();
    assert_eq!(proof, proof2);
}

#[test]
fn three_clause_unsat_binary_roundtrip() {
    let proof = load_drat("three-clause-unsat");
    let binary = write_drat_binary_to_vec(&proof);
    let proof2 = parse_drat_binary(&binary).unwrap();
    assert_eq!(proof, proof2);
}

#[test]
fn four_clause_unsat_binary_roundtrip() {
    let proof = load_drat("four-clause-unsat");
    let binary = write_drat_binary_to_vec(&proof);
    let proof2 = parse_drat_binary(&binary).unwrap();
    assert_eq!(proof, proof2);
}

// --------------------------------------------------------------------
// Binary DRAT verification (text → binary → parse → verify)
// --------------------------------------------------------------------

#[test]
fn binary_drat_verifies_trivial_unsat() {
    let cnf = load_cnf("trivial-unsat");
    let proof = load_drat("trivial-unsat");
    let binary = write_drat_binary_to_vec(&proof);
    let proof2 = parse_drat_binary(&binary).unwrap();

    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof2));
}

#[test]
fn binary_drat_verifies_four_clause_unsat() {
    let cnf = load_cnf("four-clause-unsat");
    let proof = load_drat("four-clause-unsat");
    let binary = write_drat_binary_to_vec(&proof);
    let proof2 = parse_drat_binary(&binary).unwrap();

    let mut checker = NaiveDratChecker::new(&cnf);
    assert!(check_proof(&mut checker, &proof2));
}

// --------------------------------------------------------------------
// SAT model verification
// --------------------------------------------------------------------

#[test]
fn simple_sat_model_satisfies() {
    let cnf = load_cnf("simple-sat");
    let model_lits = load_model("simple-sat");

    // Build a Model from the literals.
    let mut values = vec![false; cnf.num_vars() as usize];
    for &dimacs in &model_lits {
        let idx = dimacs.unsigned_abs() as usize - 1;
        values[idx] = dimacs > 0;
    }
    let model = Model::from_total(values);
    assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
}

// --------------------------------------------------------------------
// Varisat confirms UNSAT, then DRAT proof independently verifies
// --------------------------------------------------------------------

/// Thin wrapper around varisat::Solver for these tests.
struct Varisat;

impl covalence_sat::Solver for Varisat {
    fn solve(&self, cnf: &covalence_sat::Cnf) -> Result<Model, covalence_sat::SolveError> {
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
            .map_err(|e| covalence_sat::SolveError::Internal(e.to_string()))?;

        if !sat {
            return Err(covalence_sat::SolveError::Unsat);
        }

        let varisat_model = solver
            .model()
            .ok_or_else(|| covalence_sat::SolveError::Internal("no model after SAT".into()))?;

        let mut values = vec![false; cnf.num_vars() as usize];
        for &lit in &varisat_model {
            let d = lit.to_dimacs();
            let idx = d.unsigned_abs() - 1;
            values[idx] = d > 0;
        }
        Ok(Model::from_total(values))
    }
}

#[test]
fn varisat_confirms_unsat_then_drat_verifies() {
    for problem in &[
        "trivial-unsat",
        "three-clause-unsat",
        "four-clause-unsat",
        "example-4-vars",
        "example-5-vars",
        "example-Schur",
        "uuf-30-1",
        "uuf-50-2",
    ] {
        let cnf = load_cnf(problem);

        // Varisat confirms UNSAT.
        let err = Varisat
            .solve(&cnf)
            .expect_err(&format!("{problem} should be UNSAT"));
        assert!(
            matches!(err, covalence_sat::SolveError::Unsat),
            "{problem}: expected Unsat, got {err:?}"
        );

        // DRAT proof independently verifies (both checkers support RAT).
        let proof = load_drat(problem);
        let mut naive = NaiveDratChecker::new(&cnf);
        assert!(
            check_proof(&mut naive, &proof),
            "{problem}: NaiveDratChecker verification failed"
        );
        let mut watched = WatchedDratChecker::new(&cnf);
        assert!(
            check_proof(&mut watched, &proof),
            "{problem}: WatchedDratChecker verification failed"
        );
    }
}

#[test]
fn varisat_confirms_simple_sat() {
    let cnf = load_cnf("simple-sat");
    let model = Varisat.solve(&cnf).expect("simple-sat should be SAT");
    assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
}

// --------------------------------------------------------------------
// DIMACS roundtrip: parse asset → write → parse → compare
// --------------------------------------------------------------------

#[test]
fn dimacs_roundtrip_all_assets() {
    for problem in &[
        "trivial-unsat",
        "three-clause-unsat",
        "four-clause-unsat",
        "simple-sat",
        "empty-clause",
        "example-4-vars",
        "example-5-vars",
        "example-Schur",
        "uuf-30-1",
        "uuf-50-2",
    ] {
        let cnf = load_cnf(problem);
        let output = write_dimacs_to_string(&cnf);
        let cnf2 = parse_dimacs(&output)
            .unwrap_or_else(|e| panic!("{problem} roundtrip parse failed: {e}"));
        assert_eq!(cnf, cnf2, "{problem} roundtrip mismatch");
    }
}

// --------------------------------------------------------------------
// DRAT text roundtrip: parse asset → write → parse → compare
// --------------------------------------------------------------------

#[test]
fn drat_text_roundtrip_all_assets() {
    for problem in &[
        "trivial-unsat",
        "three-clause-unsat",
        "four-clause-unsat",
        "example-4-vars",
        "example-5-vars",
        "example-Schur",
        "uuf-30-1",
        "uuf-50-2",
    ] {
        let proof = load_drat(problem);
        let output = write_drat_text_to_string(&proof);
        let proof2 = parse_drat_text(&output)
            .unwrap_or_else(|e| panic!("{problem} DRAT text roundtrip parse failed: {e}"));
        assert_eq!(proof, proof2, "{problem} DRAT text roundtrip mismatch");
    }
}

// --------------------------------------------------------------------
// drat-trim example structure tests
// --------------------------------------------------------------------

#[test]
fn example_4_vars_structure() {
    let cnf = load_cnf("example-4-vars");
    assert_eq!(cnf.num_vars(), 4);
    assert_eq!(cnf.num_clauses(), 8);
    // All ternary clauses.
    for clause in cnf.clauses() {
        assert_eq!(clause.len(), 3);
    }
}

#[test]
fn example_5_vars_structure() {
    let cnf = load_cnf("example-5-vars");
    assert_eq!(cnf.num_vars(), 5);
    assert_eq!(cnf.num_clauses(), 8);

    // Proof introduces auxiliary variable 6 (proper DRAT, not just DRUP).
    let proof = load_drat("example-5-vars");
    let has_var_6 = proof.steps().iter().any(|step| match step {
        covalence_sat::DratStep::Add(c) | covalence_sat::DratStep::Delete(c) => {
            c.lits().iter().any(|l| l.var().index() == 6)
        }
    });
    assert!(has_var_6, "proof should introduce auxiliary variable 6");
}

#[test]
fn example_schur_structure() {
    let cnf = load_cnf("example-Schur");
    assert_eq!(cnf.num_vars(), 9);
    assert_eq!(cnf.num_clauses(), 32);
}

#[test]
fn uuf_30_1_structure() {
    let cnf = load_cnf("uuf-30-1");
    assert_eq!(cnf.num_vars(), 30);
    assert_eq!(cnf.num_clauses(), 127);
    // All 3-SAT clauses.
    for clause in cnf.clauses() {
        assert_eq!(clause.len(), 3);
    }
}

#[test]
fn uuf_50_2_structure() {
    let cnf = load_cnf("uuf-50-2");
    assert_eq!(cnf.num_vars(), 50);
    assert_eq!(cnf.num_clauses(), 209);
}

// --------------------------------------------------------------------
// RAT-capable verification through all drat-trim examples
// --------------------------------------------------------------------

/// Verify a proof using both NaiveDratChecker and WatchedDratChecker.
fn verify_both(problem: &str) {
    let cnf = load_cnf(problem);
    let proof = load_drat(problem);

    let mut naive = NaiveDratChecker::new(&cnf);
    assert!(
        check_proof(&mut naive, &proof),
        "{problem}: NaiveDratChecker verification failed"
    );

    let mut watched = WatchedDratChecker::new(&cnf);
    assert!(
        check_proof(&mut watched, &proof),
        "{problem}: WatchedDratChecker verification failed"
    );
}

#[test]
fn all_checkers_example_schur() {
    verify_both("example-Schur");
}

#[test]
fn all_checkers_uuf_30_1() {
    verify_both("uuf-30-1");
}

#[test]
fn all_checkers_uuf_50_2() {
    verify_both("uuf-50-2");
}

#[test]
fn all_checkers_example_4_vars() {
    verify_both("example-4-vars");
}

#[test]
fn all_checkers_example_5_vars() {
    verify_both("example-5-vars");
}

#[test]
fn all_checkers_existing_proofs() {
    for problem in &["trivial-unsat", "three-clause-unsat", "four-clause-unsat"] {
        verify_both(problem);
    }
}

// --------------------------------------------------------------------
// Binary DRAT roundtrip for drat-trim examples
// --------------------------------------------------------------------

#[test]
fn drat_trim_binary_roundtrip() {
    for problem in &[
        "example-4-vars",
        "example-5-vars",
        "example-Schur",
        "uuf-30-1",
        "uuf-50-2",
    ] {
        let proof = load_drat(problem);
        let binary = write_drat_binary_to_vec(&proof);
        let proof2 = parse_drat_binary(&binary)
            .unwrap_or_else(|e| panic!("{problem} binary roundtrip parse failed: {e}"));
        assert_eq!(proof, proof2, "{problem} binary roundtrip mismatch");

        // Also verify the binary-parsed proof with both checkers.
        let cnf = load_cnf(problem);
        let mut naive = NaiveDratChecker::new(&cnf);
        assert!(
            check_proof(&mut naive, &proof2),
            "{problem}: NaiveDratChecker binary-parsed proof failed verification"
        );
        let mut watched = WatchedDratChecker::new(&cnf);
        assert!(
            check_proof(&mut watched, &proof2),
            "{problem}: WatchedDratChecker binary-parsed proof failed verification"
        );
    }
}
