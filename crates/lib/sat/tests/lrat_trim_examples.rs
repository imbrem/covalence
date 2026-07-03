#![cfg(feature = "lrat")]
//! Loop test over all LRAT examples.
//!
//! Verifies each (CNF, LRAT proof) pair with [`NaiveLratChecker`].

use std::path::PathBuf;

use covalence_sat::{
    Cnf, LratProof, NaiveLratChecker, check_lrat_proof,
    parse::{parse_dimacs, parse_lrat_text},
};

fn sat_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../assets/tests/sat")
}

/// Discover all problem directories that contain both problem.cnf and proof.lrat.
fn discover_problems() -> Vec<String> {
    let dir = sat_dir();
    let mut problems = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("failed to read sat directory") {
        let entry = entry.expect("failed to read entry");
        let path = entry.path();
        if path.is_dir() {
            let cnf_path = path.join("problem.cnf");
            let lrat_path = path.join("proof.lrat");
            if cnf_path.exists() && lrat_path.exists() {
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

fn load_lrat(problem: &str) -> LratProof {
    let path = sat_dir().join(problem).join("proof.lrat");
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    parse_lrat_text(&content).unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()))
}

#[test]
fn all_lrat_trim_examples() {
    let problems = discover_problems();
    assert!(
        !problems.is_empty(),
        "no LRAT test problems found in {}",
        sat_dir().display()
    );

    for problem in &problems {
        let cnf = load_cnf(problem);
        let proof = load_lrat(problem);

        let mut checker = NaiveLratChecker::new(&cnf);
        assert!(
            check_lrat_proof(&mut checker, &proof),
            "{problem}: NaiveLratChecker verification failed"
        );
    }
}
