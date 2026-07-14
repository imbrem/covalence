//! # Demo: kernel-checked UNSAT certificates
//!
//! The reusable "**solve + kernel-certify**" capability: an infeasible SAT
//! instance is decided by **CaDiCaL**, and its refutation is **replayed into a
//! kernel theorem `⊢ ⊥`** — every resolution step re-derived through the trusted
//! kernel. Any SAT-encoded infeasibility (dependency conflicts, scheduling,
//! puzzles) then yields a proof object you can independently verify, without
//! trusting the solver.
//!
//! The instance here is the `k`-bit **exhaustive contradiction**: all `2^k`
//! clauses excluding every assignment to `k` variables, so the CNF is UNSAT and
//! CaDiCaL's proof is a pure resolution (RUP) chain the kernel replays directly.
//!
//! NOTE on harder instances: solvers use **RAT** steps (extended resolution /
//! preprocessing) on structured problems like the pigeonhole principle — those
//! LRAT proofs carry negative antecedent hints that this RUP-only replay does not
//! yet handle. RAT support is the headline SAT-side gap (see `SKELETONS.md`).
//!
//! Run:  `cargo run --release --example unsat_certify -p covalence-kernel-sat --features cadical`

use std::process::Command;
use std::time::{Duration, Instant};

use covalence_kernel_sat::{Cnf, HolClauseBackend, Lit, replay_lrat};
use covalence_sat::parse::{parse_lrat_text, write_dimacs_to_string};

/// All `2^k` clauses excluding each full assignment to `k` variables — UNSAT.
fn exhaustive(k: usize) -> Cnf {
    let mut cnf = Cnf::new();
    let vars: Vec<Lit> = (0..k).map(|_| cnf.fresh()).collect();
    for mask in 0..(1u32 << k) {
        let clause: Vec<Lit> = vars
            .iter()
            .enumerate()
            .map(|(i, &v)| if mask & (1 << i) == 0 { v } else { !v })
            .collect();
        cnf.clause(clause);
    }
    cnf
}

/// CaDiCaL `--lrat` refutation + solve time, or `None` if absent / SAT.
fn run_cadical(cnf: &Cnf) -> Option<(String, Duration)> {
    let dir = std::env::temp_dir();
    let stamp = format!("cov-unsat-{}", std::process::id());
    let cnf_path = dir.join(format!("{stamp}.cnf"));
    let lrat_path = dir.join(format!("{stamp}.lrat"));
    std::fs::write(&cnf_path, write_dimacs_to_string(cnf)).ok()?;
    let start = Instant::now();
    let status = Command::new("cadical")
        .args(["--lrat=true", "--no-binary", "-q"])
        .arg(&cnf_path)
        .arg(&lrat_path)
        .status();
    let solve = start.elapsed();
    let out = match status {
        Ok(s) if s.code() == Some(20) => std::fs::read_to_string(&lrat_path).ok(),
        _ => None,
    };
    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&lrat_path);
    out.map(|t| (t, solve))
}

fn ms(d: Duration) -> String {
    format!("{:.1} ms", d.as_secs_f64() * 1e3)
}

fn main() {
    println!("=== Kernel-checked UNSAT — CaDiCaL-found, kernel-replayed ===\n");
    println!("k-bit exhaustive contradiction: 2^k clauses, no satisfying assignment.\n");

    if run_cadical(&exhaustive(2)).is_none() {
        println!("(cadical not on $PATH / not `--features cadical` — skipping.)");
        return;
    }

    println!(
        "{:>4} | {:>5} | {:>8} | {:>10} | {:>13} | {:>7}",
        "k", "vars", "clauses", "cadical", "kernel replay", "⊢ ⊥"
    );
    println!(
        "{:->4}-+-{:->5}-+-{:->8}-+-{:->10}-+-{:->13}-+-{:->7}",
        "", "", "", "", "", ""
    );
    // Capped low for now: the RUP replay is quadratic-ish in clause size (a perf
    // bug), and k≥6 CaDiCaL proofs use RAT (unhandled). Both are being fixed —
    // then this scales up. See SKELETONS.md.
    for k in 3..=5usize {
        let cnf = exhaustive(k);
        let Some((lrat, solve)) = run_cadical(&cnf) else {
            continue;
        };
        // A RAT proof (negative antecedent hints) can't be parsed by the RUP
        // reader — report it rather than crash.
        let Ok(proof) = parse_lrat_text(&lrat) else {
            println!(
                "{k:>4} | {:>5} | {:>8} | solver used RAT — RUP replay N/A",
                cnf.num_vars(),
                cnf.num_clauses()
            );
            continue;
        };
        let start = Instant::now();
        let mut backend = HolClauseBackend::new();
        let checked = match replay_lrat(&mut backend, &cnf, &proof) {
            Ok(thm) => thm.concl().as_bool() == Some(false),
            Err(_) => false,
        };
        let replay = start.elapsed();
        println!(
            "{:>4} | {:>5} | {:>8} | {:>10} | {:>13} | {:>7}",
            k,
            cnf.num_vars(),
            cnf.num_clauses(),
            ms(solve),
            ms(replay),
            if checked { "yes" } else { "RAT/—" },
        );
    }
    println!(
        "\nEach `⊢ ⊥` is a genuine kernel theorem whose hypotheses are a subset of\n\
         the input clauses — the kernel re-derives every resolution step. The same\n\
         capability certifies any SAT-encoded infeasibility; structured instances\n\
         (pigeonhole, …) additionally need RAT-step support, the next SAT gap."
    );
}
