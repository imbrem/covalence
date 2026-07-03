use std::path::PathBuf;

use covalence_smt::{
    AletheCommand, AletheProof, Decision, TrivialChecker, check_alethe, parse_alethe,
    parse_smtlib2, write_smtlib2,
};

fn asset_path(problem: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../assets/tests/smt")
        .join(problem)
}

fn load_alethe(problem: &str) -> AletheProof {
    let path = asset_path(problem).join("proof.alethe");
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    parse_alethe(&content).unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()))
}

// --------------------------------------------------------------------
// Structure tests — verify parse results have correct command types
// --------------------------------------------------------------------

#[test]
fn trivial_unsat_structure() {
    let proof = load_alethe("trivial-unsat");
    assert_eq!(proof.len(), 3);
    assert!(matches!(proof.commands()[0], AletheCommand::Assume { .. }));
    assert!(matches!(proof.commands()[1], AletheCommand::Assume { .. }));
    match &proof.commands()[2] {
        AletheCommand::Step {
            id,
            clause,
            rule,
            premises,
            ..
        } => {
            assert_eq!(id, "t1");
            assert!(clause.is_empty(), "resolution to empty clause");
            assert_eq!(rule, "resolution");
            assert_eq!(premises, &["h1", "h2"]);
        }
        other => panic!("expected Step, got {other:?}"),
    }
}

#[test]
fn eq_reasoning_structure() {
    let proof = load_alethe("eq-reasoning");
    assert_eq!(proof.len(), 6);
    // 3 assumes + 3 steps
    let assumes = proof
        .commands()
        .iter()
        .filter(|c| matches!(c, AletheCommand::Assume { .. }))
        .count();
    let steps = proof
        .commands()
        .iter()
        .filter(|c| matches!(c, AletheCommand::Step { .. }))
        .count();
    assert_eq!(assumes, 3);
    assert_eq!(steps, 3);
}

#[test]
fn step_with_args_structure() {
    let proof = load_alethe("step-with-args");
    assert_eq!(proof.len(), 3);
    match &proof.commands()[1] {
        AletheCommand::Step { rule, args, .. } => {
            assert_eq!(rule, "forall_inst");
            assert_eq!(args.len(), 1, "should have one arg binding");
        }
        other => panic!("expected Step with args, got {other:?}"),
    }
}

#[test]
fn with_define_fun_structure() {
    let proof = load_alethe("with-define-fun");
    assert_eq!(proof.len(), 4);
    match &proof.commands()[0] {
        AletheCommand::DefineFun {
            name, params, sort, ..
        } => {
            assert_eq!(name, "f");
            assert_eq!(params.len(), 1);
            assert_eq!(sort.as_symbol(), Some("Bool"));
        }
        other => panic!("expected DefineFun, got {other:?}"),
    }
}

#[test]
fn with_anchor_structure() {
    let proof = load_alethe("with-anchor");
    assert_eq!(proof.len(), 6);
    match &proof.commands()[1] {
        AletheCommand::Anchor { step, args } => {
            assert_eq!(step, "t3");
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Anchor, got {other:?}"),
    }
    // Last step should have :discharge
    match &proof.commands()[5] {
        AletheCommand::Step { discharge, .. } => {
            assert_eq!(discharge, &["h2"]);
        }
        other => panic!("expected Step with discharge, got {other:?}"),
    }
}

#[test]
fn empty_proof_structure() {
    let proof = load_alethe("empty");
    assert!(proof.is_empty());
    assert_eq!(proof.len(), 0);
}

// --------------------------------------------------------------------
// Checker tests — all fixtures parse and TrivialChecker returns Unknown
// --------------------------------------------------------------------

const ALL_FIXTURES: &[&str] = &[
    "trivial-unsat",
    "eq-reasoning",
    "step-with-args",
    "with-define-fun",
    "with-anchor",
    "empty",
    "cvc5-qf-uf",
];

#[test]
fn all_fixtures_parse() {
    for name in ALL_FIXTURES {
        let proof = load_alethe(name);
        // Just ensure no panic — parse succeeded
        let _ = proof.len();
    }
}

#[test]
fn trivial_checker_returns_unknown() {
    for name in ALL_FIXTURES {
        let proof = load_alethe(name);
        let decision = check_alethe(&mut TrivialChecker, &proof);
        assert_eq!(
            decision,
            Decision::Unknown,
            "TrivialChecker should return Unknown for {name}"
        );
    }
}

// --------------------------------------------------------------------
// cvc5-generated proof with ! annotations
// --------------------------------------------------------------------

#[test]
fn cvc5_qf_uf_structure() {
    let proof = load_alethe("cvc5-qf-uf");
    assert_eq!(proof.len(), 8);
    // 3 assumes + 5 steps
    let assumes = proof
        .commands()
        .iter()
        .filter(|c| matches!(c, AletheCommand::Assume { .. }))
        .count();
    let steps = proof
        .commands()
        .iter()
        .filter(|c| matches!(c, AletheCommand::Step { .. }))
        .count();
    assert_eq!(assumes, 3);
    assert_eq!(steps, 5);
    // Last step is resolution to empty clause
    match &proof.commands()[7] {
        AletheCommand::Step {
            id, clause, rule, ..
        } => {
            assert_eq!(id, "t4");
            assert!(clause.is_empty());
            assert_eq!(rule, "resolution");
        }
        other => panic!("expected Step, got {other:?}"),
    }
}

// --------------------------------------------------------------------
// Problem parsing tests
// --------------------------------------------------------------------

const PROBLEM_FIXTURES: &[&str] = &["trivial-unsat", "cvc5-qf-uf"];

#[test]
fn problem_fixtures_parse() {
    for name in PROBLEM_FIXTURES {
        let path = asset_path(name).join("problem.smt2");
        let content = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        let problem = parse_smtlib2(&content)
            .unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()));
        assert!(
            !problem.assertions().is_empty(),
            "problem {name} should have assertions"
        );
    }
}

#[test]
fn trivial_unsat_problem_structure() {
    let path = asset_path("trivial-unsat").join("problem.smt2");
    let content = std::fs::read_to_string(&path).unwrap();
    let problem = parse_smtlib2(&content).unwrap();
    assert_eq!(problem.logic(), Some("QF_UF"));
    assert_eq!(problem.funs().len(), 1); // declare-const a
    assert_eq!(problem.assertions().len(), 2);
}

#[test]
fn cvc5_qf_uf_problem_structure() {
    let path = asset_path("cvc5-qf-uf").join("problem.smt2");
    let content = std::fs::read_to_string(&path).unwrap();
    let problem = parse_smtlib2(&content).unwrap();
    assert_eq!(problem.logic(), Some("QF_UF"));
    assert_eq!(problem.sorts().len(), 1);
    assert_eq!(problem.sorts()[0].name, "U");
    assert_eq!(problem.funs().len(), 3); // a, b, p
    assert_eq!(problem.assertions().len(), 3);
}

// --------------------------------------------------------------------
// write_smtlib2 round-trip tests
// --------------------------------------------------------------------

#[test]
fn write_smtlib2_roundtrip() {
    for name in PROBLEM_FIXTURES {
        let path = asset_path(name).join("problem.smt2");
        let content = std::fs::read_to_string(&path).unwrap();
        let original = parse_smtlib2(&content).unwrap();

        let mut buf = Vec::new();
        write_smtlib2(&original, &mut buf).unwrap();
        let serialized = String::from_utf8(buf).unwrap();

        let reparsed = parse_smtlib2(&serialized)
            .unwrap_or_else(|e| panic!("failed to reparse {name}: {e}\nserialized:\n{serialized}"));

        assert_eq!(
            original.logic(),
            reparsed.logic(),
            "logic mismatch for {name}"
        );
        assert_eq!(
            original.sorts().len(),
            reparsed.sorts().len(),
            "sorts count mismatch for {name}"
        );
        assert_eq!(
            original.funs().len(),
            reparsed.funs().len(),
            "funs count mismatch for {name}"
        );
        assert_eq!(
            original.assertions().len(),
            reparsed.assertions().len(),
            "assertions count mismatch for {name}"
        );
    }
}

// --------------------------------------------------------------------
// cvc5 solver test (feature-gated)
// --------------------------------------------------------------------

#[cfg(feature = "cvc5")]
#[test]
fn cvc5_solve_trivial_unsat() {
    use covalence_smt::{Cvc5Solver, SmtSolver};

    let solver = Cvc5Solver::from_path();
    let path = asset_path("trivial-unsat").join("problem.smt2");
    let content = std::fs::read_to_string(&path).unwrap();
    let problem = parse_smtlib2(&content).unwrap();

    let proof = solver.solve(&problem).unwrap();
    assert!(!proof.is_empty());
    let decision = check_alethe(&mut TrivialChecker, &proof);
    assert_eq!(decision, Decision::Unknown);
}

// --------------------------------------------------------------------
// Parse test-workbench/test.alethe if it exists
// --------------------------------------------------------------------

#[test]
fn parse_workbench_test_alethe() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../test-workbench/test.alethe");
    if !path.exists() {
        return;
    }
    let content = std::fs::read_to_string(&path).unwrap();
    let proof = parse_alethe(&content)
        .unwrap_or_else(|e| panic!("failed to parse workbench test.alethe: {e}"));
    assert!(!proof.is_empty());
}
