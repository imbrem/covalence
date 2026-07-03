#![cfg(feature = "drat")]
//! Loop test over all drat-trim examples.
//!
//! Verifies each (CNF, DRAT proof) pair with both [`NaiveDratChecker`]
//! and [`WatchedDratChecker`].

use std::path::PathBuf;

use covalence_sat::{
    Cnf, DratProof, NaiveDratChecker, WatchedDratChecker, check_proof,
    parse::{parse_dimacs, parse_drat_text},
};

fn sat_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../assets/tests/sat")
}

/// Discover all problem directories that contain both problem.cnf and proof.drat.
fn discover_problems() -> Vec<String> {
    let dir = sat_dir();
    let mut problems = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("failed to read sat directory") {
        let entry = entry.expect("failed to read entry");
        let path = entry.path();
        if path.is_dir() {
            let cnf_path = path.join("problem.cnf");
            let drat_path = path.join("proof.drat");
            if cnf_path.exists() && drat_path.exists() {
                let name = path.file_name().unwrap().to_str().unwrap().to_string();
                problems.push(name);
            }
        }
    }
    problems.sort();
    problems
}

fn load_cnf(problem: &str) -> Cnf {
    let path = sat_dir().join(problem).join("problem.cnf");
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    parse_dimacs(&content).unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()))
}

fn load_drat(problem: &str) -> DratProof {
    let path = sat_dir().join(problem).join("proof.drat");
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    parse_drat_text(&content).unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()))
}

#[test]
fn all_drat_trim_examples() {
    let problems = discover_problems();
    assert!(
        !problems.is_empty(),
        "no test problems found in {}",
        sat_dir().display()
    );

    // Skip SAT problems (no UNSAT proof expected).
    let skip = ["simple-sat", "empty-clause"];

    for problem in &problems {
        if skip.contains(&problem.as_str()) {
            continue;
        }

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
}
