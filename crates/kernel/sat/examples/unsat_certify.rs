//! # Demo: kernel-checked UNSAT certificates (the pigeonhole principle)
//!
//! The reusable "**solve + kernel-certify**" capability: an infeasible SAT
//! instance is decided by **CaDiCaL**, and its refutation is **replayed into a
//! kernel theorem `⊢ ⊥`** — every resolution step re-derived through the trusted
//! kernel. Any SAT-encoded infeasibility (dependency conflicts, scheduling,
//! puzzles) then yields a proof object you can independently verify.
//!
//! `PHP(h+1, h)` — `h+1` pigeons into `h` holes, each pigeon in some hole, no two
//! sharing a hole — is unsatisfiable and famously has only *exponentially large*
//! resolution proofs, so it is a genuine stress test for the replay.
//!
//! We run CaDiCaL with `--plain`, which emits **RUP-only** LRAT (no RAT steps),
//! so the resolution replay applies directly. (General RAT proofs — non-`--plain`,
//! other solvers — need the extension-variable reconstruction; see `SKELETONS.md`.)
//!
//! Run:  `cargo run --release --example unsat_certify -p covalence-kernel-sat --features cadical`

use std::process::Command;
use std::time::{Duration, Instant};

use covalence_kernel_sat::{Cnf, HolClauseBackend, Lit, replay_lrat};
use covalence_sat::parse::{parse_lrat_text, write_dimacs_to_string};

/// `PHP(pigeons, holes)`: `p[i][j]` = "pigeon `i` in hole `j`". UNSAT when
/// `pigeons > holes`.
fn php_cnf(pigeons: usize, holes: usize) -> Cnf {
    let mut cnf = Cnf::new();
    let p: Vec<Vec<Lit>> = (0..pigeons)
        .map(|_| (0..holes).map(|_| cnf.fresh()).collect())
        .collect();
    for row in &p {
        cnf.clause(row.iter().copied()); // each pigeon in ≥1 hole
    }
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                cnf.clause([!p[i1][j], !p[i2][j]]); // no hole holds two pigeons
            }
        }
    }
    cnf
}

/// CaDiCaL `--plain --lrat` (RUP-only) refutation + solve time.
fn run_cadical(cnf: &Cnf) -> Option<(String, Duration)> {
    let dir = std::env::temp_dir();
    let stamp = format!("cov-php-{}", std::process::id());
    let cnf_path = dir.join(format!("{stamp}.cnf"));
    let lrat_path = dir.join(format!("{stamp}.lrat"));
    std::fs::write(&cnf_path, write_dimacs_to_string(cnf)).ok()?;
    let start = Instant::now();
    let status = Command::new("cadical")
        .args(["--plain", "--lrat=true", "--no-binary", "-q"])
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
    println!("=== Pigeonhole — CaDiCaL-found, kernel-checked UNSAT ===\n");
    println!("PHP(h+1, h): h+1 pigeons, h holes — infeasible; exponential resolution proofs.\n");

    if run_cadical(&php_cnf(3, 2)).is_none() {
        println!("(cadical not on $PATH / not `--features cadical` — skipping.)");
        return;
    }

    println!(
        "{:>4} | {:>5} | {:>8} | {:>7} | {:>10} | {:>13} | {:>5}",
        "h", "vars", "clauses", "steps", "cadical", "kernel replay", "⊢ ⊥"
    );
    println!(
        "{:->4}-+-{:->5}-+-{:->8}-+-{:->7}-+-{:->10}-+-{:->13}-+-{:->5}",
        "", "", "", "", "", "", ""
    );
    // Replay cost grows with the (exponential) resolution-proof size; capped
    // where it stays interactive. Scaling further wants the sequent-form clause
    // backend (near-O(1) resolution) — see SKELETONS.md.
    for h in 3..=6usize {
        let cnf = php_cnf(h + 1, h);
        let Some((lrat, solve)) = run_cadical(&cnf) else {
            continue;
        };
        let Ok(proof) = parse_lrat_text(&lrat) else {
            println!("{h:>4} | solver used RAT — see SKELETONS.md");
            continue;
        };
        let steps = proof.steps().len();
        let start = Instant::now();
        let mut backend = HolClauseBackend::new();
        let checked = match replay_lrat(&mut backend, &cnf, &proof) {
            Ok(thm) => thm.concl().as_bool() == Some(false),
            Err(_) => false,
        };
        let replay = start.elapsed();
        println!(
            "{:>4} | {:>5} | {:>8} | {:>7} | {:>10} | {:>13} | {:>5}",
            h,
            cnf.num_vars(),
            cnf.num_clauses(),
            steps,
            ms(solve),
            ms(replay),
            if checked { "yes" } else { "—" },
        );
    }
    println!(
        "\nEach `⊢ ⊥` is a genuine kernel theorem whose hypotheses are a subset of\n\
         the input clauses — the kernel re-derives every one of the (many) resolution\n\
         steps. A machine-checked proof that the pigeons don't fit; the same\n\
         capability certifies any SAT-encoded infeasibility."
    );
}
