//! End-to-end SAT-proof import through the **sequent-form** backend
//! ([`SequentClauseBackend`]) — the scale fix. Mirrors `cadical_e2e.rs`, but
//! resolution is a hypothesis-set cut, so per-step cost is flat in clause size.
//!
//! The `embedded_*` tests use checked-in LRAT so CI passes with no solver. The
//! `live` module (feature `cadical`) shells out to a real `cadical` and includes
//! a **scaling benchmark** (`bench_pigeonhole_scaling`) comparing the disjunction
//! and sequent backends across `PHP(h+1, h)`.

use covalence_kernel_sat::{Cnf, SatProblem, SequentClauseBackend, replay_lrat};
use covalence_sat::parse::parse_lrat_text;

/// The 3-variable all-clauses contradiction (same as `cadical_e2e`).
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

/// Replay a CNF + LRAT through the **sequent** backend and assert a genuine
/// `⊢ ⊥` whose hypotheses are a subset of the input clauses.
fn assert_refutation(cnf: &Cnf, lrat: &str) {
    let proof = parse_lrat_text(lrat).expect("parse LRAT");
    let mut backend = SequentClauseBackend::new();
    let thm = replay_lrat(&mut backend, cnf, &proof).expect("replay LRAT into HOL (sequent)");

    // The refutation is `⊢ F` (the *defined* falsity or the literal — both count).
    let concl = thm.concl();
    let is_false = matches!(concl.as_bool(), Some(false))
        || matches!(
            concl.kind(),
            covalence_core::TermKind::Spec(h, _) if h.ptr_eq(&covalence_core::defs::fal_spec())
        );
    assert!(is_false, "expected `⊢ F`, got `{concl}`");

    // Genuine: every hypothesis is one of the input clause disjunctions. (The
    // sequent backend cuts every `~`-literal away; only the `C` disjunctions of
    // input clauses may survive.)
    let prover = SequentClauseBackend::new();
    let inputs: Vec<_> = cnf.clauses().map(|c| prover.clause(c)).collect();
    for h in thm.hyps().iter() {
        assert!(
            inputs.contains(h),
            "refutation hypothesis `{h}` is not an input clause disjunction"
        );
    }
}

#[test]
fn embedded_lrat_replays_to_false_sequent() {
    assert_refutation(&unsat_cnf(), UNSAT_LRAT);
}

#[test]
fn embedded_trivial_unit_contradiction_sequent() {
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
    use covalence_kernel_sat::{HolClauseBackend, Lit};
    use covalence_sat::parse::write_dimacs_to_string;
    use std::process::Command;
    use std::time::Instant;

    /// Run `cadical --plain --lrat=true --no-binary -q <cnf> <out>`, returning the
    /// LRAT text — or `None` if cadical is absent / the run did not yield UNSAT.
    fn run_cadical(cnf: &Cnf) -> Option<String> {
        let dir = std::env::temp_dir();
        let stamp = format!(
            "cov-sat-seq-{}-{}",
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
            .args(["--plain", "--lrat=true", "--no-binary", "-q"])
            .arg(&cnf_path)
            .arg(&lrat_path)
            .status();

        let out = match status {
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

    /// Build the pigeonhole CNF `PHP(pigeons, holes)`: `pigeons` pigeons into
    /// `holes` holes, UNSAT when `pigeons > holes`.
    fn pigeonhole(pigeons: usize, holes: usize) -> Cnf {
        let mut cnf = Cnf::new();
        let p: Vec<Vec<Lit>> = (0..pigeons)
            .map(|_| (0..holes).map(|_| cnf.fresh()).collect())
            .collect();
        // Each pigeon in some hole.
        for row in &p {
            cnf.clause(row.iter().copied());
        }
        // No two pigeons share a hole.
        for j in 0..holes {
            for i1 in 0..pigeons {
                for i2 in (i1 + 1)..pigeons {
                    cnf.clause([!p[i1][j], !p[i2][j]]);
                }
            }
        }
        cnf
    }

    #[test]
    fn live_cadical_refutes_and_replays_sequent() {
        let cnf = unsat_cnf();
        let Some(lrat) = run_cadical(&cnf) else {
            return;
        };
        assert_refutation(&cnf, &lrat);
    }

    /// `PHP(4,3)` through the sequent backend — a real structured UNSAT whose RUP
    /// chains have several complementary pairs per step.
    #[test]
    fn live_cadical_pigeonhole_sequent() {
        let cnf = pigeonhole(4, 3);
        let Some(lrat) = run_cadical(&cnf) else {
            return;
        };
        assert_refutation(&cnf, &lrat);
    }

    /// **Scaling benchmark.** Replay `PHP(h+1, h)` for h = 3..=8 through *both*
    /// backends and print a timing table. The sequent backend's per-step cost is
    /// flat in clause size (a hypothesis-set cut), so it stays far ahead of the
    /// disjunction backend as the proofs grow.
    ///
    /// Run with:
    /// ```sh
    /// cargo test -p covalence-kernel-sat --features cadical --release \
    ///     bench_pigeonhole_scaling -- --nocapture --ignored
    /// ```
    #[test]
    #[ignore = "benchmark: run explicitly with --ignored --nocapture (slow at h≥7)"]
    fn bench_pigeonhole_scaling() {
        println!(
            "\n{:>3} | {:>7} | {:>7} | {:>12} | {:>12} | {:>8}",
            "h", "vars", "steps", "disjunction", "sequent", "speedup"
        );
        println!("{}", "-".repeat(70));

        for h in 3..=8usize {
            let cnf = pigeonhole(h + 1, h);
            let n_vars = (h + 1) * h;
            let Some(lrat) = run_cadical(&cnf) else {
                println!("{h:>3} | (cadical unavailable / not UNSAT — skipped)");
                continue;
            };
            let proof = parse_lrat_text(&lrat).expect("parse LRAT");
            let n_steps = proof.steps().len();

            // Disjunction backend. Cap its runtime at the larger sizes — it is
            // O(clause-size) per step and blows up (~44 s at h=7).
            let disj = if h <= 7 {
                let mut b = HolClauseBackend::new();
                let t = Instant::now();
                let thm = replay_lrat(&mut b, &cnf, &proof).expect("disjunction replay");
                assert!(is_false_concl(thm.concl()));
                Some(t.elapsed())
            } else {
                None
            };

            // Sequent backend.
            let mut b = SequentClauseBackend::new();
            let t = Instant::now();
            let thm = replay_lrat(&mut b, &cnf, &proof).expect("sequent replay");
            assert!(is_false_concl(thm.concl()));
            let seq = t.elapsed();

            match disj {
                Some(d) => println!(
                    "{h:>3} | {n_vars:>7} | {n_steps:>7} | {:>10.3?} | {:>10.3?} | {:>7.1}x",
                    d,
                    seq,
                    d.as_secs_f64() / seq.as_secs_f64()
                ),
                None => println!(
                    "{h:>3} | {n_vars:>7} | {n_steps:>7} | {:>12} | {:>10.3?} | {:>8}",
                    "(skipped)", seq, "—"
                ),
            }
        }
    }

    fn is_false_concl(concl: &covalence_core::Term) -> bool {
        matches!(concl.as_bool(), Some(false))
            || matches!(
                concl.kind(),
                covalence_core::TermKind::Spec(h, _) if h.ptr_eq(&covalence_core::defs::fal_spec())
            )
    }
}
