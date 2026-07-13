//! Benchmark the pure Metamath pipeline on a `.mm` database: read the file,
//! parse it into a [`Database`], and verify every `$p` proof with the in-crate
//! RPN checker. No HOL involved — this measures `covalence-metamath` itself
//! (the HOL import has its own bench, `covalence-hol`'s `mm_import_bench`).
//!
//! Prints one JSON object on stdout (everything else goes to stderr) so it
//! pipes into `jq`:
//!
//! ```sh
//! cargo run -p covalence-metamath --example mm_verify_bench --release -- \
//!     /tmp/covalence-set.mm | jq .
//! ```
//!
//! Usage: `mm_verify_bench <path.mm> [reps]`
//!   reps  repeat parse+verify this many times and report the fastest (default
//!         1; use >1 to stabilise numbers or to give a profiler more samples).
//!
//! The normal entry point is `bun run bench:setmm` (`scripts/bench-setmm.mjs`),
//! which downloads/caches set.mm and can wrap this binary in `perf record` for
//! a flamegraph.

use std::time::{Duration, Instant};

use covalence_metamath::{parse, verify_all};

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().unwrap_or_else(|| {
        eprintln!("usage: mm_verify_bench <path.mm> [reps]");
        std::process::exit(2);
    });
    let reps: usize = args
        .next()
        .map(|s| s.parse().expect("reps must be a number"))
        .unwrap_or(1)
        .max(1);

    let t_read = Instant::now();
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("[mm-verify-bench] cannot read {path}: {e}");
        std::process::exit(1);
    });
    let read_ms = t_read.elapsed().as_secs_f64() * 1e3;
    eprintln!(
        "[mm-verify-bench] {path}: {:.1} MB read in {read_ms:.0} ms",
        src.len() as f64 / 1e6
    );

    let mut best_parse = Duration::MAX;
    let mut best_verify = Duration::MAX;
    let mut proofs = 0usize;
    let mut assertions = 0usize;
    let mut statements = 0usize;

    for rep in 0..reps {
        let t_parse = Instant::now();
        let db = match parse(&src) {
            Ok(db) => db,
            Err(e) => {
                eprintln!("[mm-verify-bench] parse error: {e}");
                std::process::exit(1);
            }
        };
        let parse_t = t_parse.elapsed();

        let t_verify = Instant::now();
        proofs = match verify_all(&db) {
            Ok(n) => n,
            Err(e) => {
                eprintln!("[mm-verify-bench] verification FAILED: {e}");
                std::process::exit(1);
            }
        };
        let verify_t = t_verify.elapsed();

        statements = db.statements().len();
        assertions = db.assertions().count();
        best_parse = best_parse.min(parse_t);
        best_verify = best_verify.min(verify_t);
        eprintln!(
            "[mm-verify-bench] rep {}/{reps}: parse {:.0} ms, verify {proofs} proofs {:.0} ms",
            rep + 1,
            parse_t.as_secs_f64() * 1e3,
            verify_t.as_secs_f64() * 1e3,
        );
    }

    let parse_ms = best_parse.as_secs_f64() * 1e3;
    let verify_ms = best_verify.as_secs_f64() * 1e3;
    println!(
        "{{\"path\":{path:?},\"bytes\":{},\"read_ms\":{read_ms:.1},\"reps\":{reps},\
         \"statements\":{statements},\"assertions\":{assertions},\"proofs\":{proofs},\
         \"axioms\":{},\"parse_ms\":{parse_ms:.1},\"verify_ms\":{verify_ms:.1},\
         \"total_ms\":{:.1},\"proofs_per_s\":{:.0}}}",
        src.len(),
        assertions - proofs,
        parse_ms + verify_ms,
        proofs as f64 / best_verify.as_secs_f64(),
    );
}
