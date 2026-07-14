//! End-to-end SAT-proof import: a CNF → CaDiCaL LRAT → replay into a HOL
//! kernel theorem `⊢ ⊥`.
//!
//! The `embedded_*` test uses a **checked-in LRAT proof** so CI passes with no
//! solver present. The `live` module (feature `cadical`) shells out to a real
//! `cadical` on `$PATH`, gated to skip when absent — mirroring
//! `covalence-alethe`'s `discharge.rs`.

use covalence_kernel_sat::{ClauseBackend, Cnf, HolClauseBackend, replay_lrat};
use covalence_sat::parse::parse_lrat_text;

/// The 3-variable all-clauses contradiction: every one of the 8 assignments to
/// `(x1, x2, x3)` is ruled out, so the CNF is UNSAT. Its LRAT refutation chains
/// resolution through several derived clauses.
fn unsat_cnf() -> Cnf {
    let mut cnf = Cnf::new();
    let x1 = cnf.fresh();
    let x2 = cnf.fresh();
    let x3 = cnf.fresh();
    for &a in &[x1, !x1] {
        for &b in &[x2, !x2] {
            for &c in &[x3, !x3] {
                cnf.clause([a, b, c]);
            }
        }
    }
    cnf
}

/// A CaDiCaL 2.x `--lrat=true --no-binary` refutation of [`unsat_cnf`],
/// captured so the core test is deterministic without a solver. Input clauses
/// are ids 1..=8 in DIMACS order; the empty clause is derived at id 16.
const UNSAT_LRAT: &str = "\
9 1 2 0 1 2 0
10 1 -2 0 4 3 0
11 -1 2 0 6 5 0
12 -1 -2 0 7 8 0
13 2 0 9 11 0
14 -2 0 10 12 0
15 -2 0 14 0
16 0 15 13 0
";

/// Replay a CNF + LRAT text through the HOL backend and assert the result is a
/// genuine `⊢ ⊥` whose hypotheses are a subset of the input clauses.
fn assert_refutation(cnf: &Cnf, lrat: &str) {
    let proof = parse_lrat_text(lrat).expect("parse LRAT");
    let mut backend = HolClauseBackend::new();
    let thm = replay_lrat(&mut backend, cnf, &proof).expect("replay LRAT into HOL");

    // The refutation is the empty clause `⊢ F`.
    assert_eq!(
        thm.concl().as_bool(),
        Some(false),
        "expected the empty clause `⊢ F`, got `{}`",
        thm.concl()
    );

    // Genuine: every hypothesis is one of the input clauses (read as the same
    // right-associated disjunction the backend assumes them as).
    let mut prover = HolClauseBackend::new();
    let inputs: Vec<_> = cnf
        .clauses()
        .map(|c| prover.assume_clause(c).unwrap().concl().clone())
        .collect();
    for h in thm.hyps().iter() {
        assert!(
            inputs.contains(h),
            "refutation hypothesis `{h}` is not an input clause"
        );
    }
}

#[test]
fn embedded_lrat_replays_to_false() {
    assert_refutation(&unsat_cnf(), UNSAT_LRAT);
}

/// A minimal two-clause contradiction `{x} ∧ {¬x}`: CaDiCaL emits the empty
/// clause directly from antecedents `[1, 2]`, exercising the single-resolution
/// path.
#[test]
fn embedded_trivial_unit_contradiction() {
    let mut cnf = Cnf::new();
    let x = cnf.fresh();
    cnf.clause([x]);
    cnf.clause([!x]);
    assert_refutation(&cnf, "3 0 1 2 0\n");
}

// ---------------------------------------------------------------------
// Live CaDiCaL — generate the LRAT ourselves, then replay.
// ---------------------------------------------------------------------

#[cfg(feature = "cadical")]
mod live {
    use super::*;
    use covalence_kernel_sat::Lit;
    use covalence_sat::parse::write_dimacs_to_string;
    use std::process::Command;

    /// Run `cadical --lrat=true --no-binary -q <cnf> <out>` on a CNF, returning
    /// the LRAT text — or `None` if cadical is absent / the run failed.
    fn run_cadical(cnf: &Cnf) -> Option<String> {
        let dir = std::env::temp_dir();
        let stamp = format!(
            "cov-sat-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        );
        let cnf_path = dir.join(format!("{stamp}.cnf"));
        let lrat_path = dir.join(format!("{stamp}.lrat"));
        std::fs::write(&cnf_path, write_dimacs_to_string(cnf)).ok()?;

        let status = Command::new("cadical")
            // `--plain` disables inprocessing so the LRAT is RUP-only (no RAT).
            .args(["--plain", "--lrat=true", "--no-binary", "-q"])
            .arg(&cnf_path)
            .arg(&lrat_path)
            .status();

        let out = match status {
            // Exit 20 = UNSAT (the only case that yields a refutation).
            Ok(s) if s.code() == Some(20) => std::fs::read_to_string(&lrat_path).ok(),
            Ok(s) => {
                eprintln!("cadical exited with {s:?} (10 = SAT); skipping");
                None
            }
            Err(e) => {
                eprintln!("skipping live cadical test: {e}");
                None
            }
        };
        let _ = std::fs::remove_file(&cnf_path);
        let _ = std::fs::remove_file(&lrat_path);
        out
    }

    #[test]
    fn live_cadical_refutes_and_replays() {
        let cnf = unsat_cnf();
        let Some(lrat) = run_cadical(&cnf) else {
            return; // skipped: no cadical / SAT
        };
        assert_refutation(&cnf, &lrat);
    }

    /// `PHP(4,3)` — the pigeonhole principle, a real structured UNSAT whose RUP
    /// chains have several complementary pairs per step (so the pivot must be
    /// computed by propagation, not guessed). `--plain` keeps it RUP-only.
    #[test]
    fn live_cadical_pigeonhole() {
        let (pigeons, holes) = (4, 3);
        let mut cnf = Cnf::new();
        let p: Vec<Vec<Lit>> = (0..pigeons)
            .map(|_| (0..holes).map(|_| cnf.fresh()).collect())
            .collect();
        for row in &p {
            cnf.clause(row.iter().copied());
        }
        for j in 0..holes {
            for i1 in 0..pigeons {
                for i2 in (i1 + 1)..pigeons {
                    cnf.clause([!p[i1][j], !p[i2][j]]);
                }
            }
        }
        let Some(lrat) = run_cadical(&cnf) else {
            return;
        };
        assert_refutation(&cnf, &lrat);
    }

    /// A 4-variable unsat core to force a longer resolution chain.
    #[test]
    fn live_cadical_four_var() {
        let mut cnf = Cnf::new();
        let v: Vec<Lit> = (0..4).map(|_| cnf.fresh()).collect();
        // All 16 full assignments negated → UNSAT.
        for mask in 0..16u32 {
            let clause: Vec<Lit> = v
                .iter()
                .enumerate()
                .map(|(i, &lit)| if mask & (1 << i) == 0 { lit } else { !lit })
                .collect();
            cnf.clause(clause);
        }
        let Some(lrat) = run_cadical(&cnf) else {
            return;
        };
        assert_refutation(&cnf, &lrat);
    }
}
