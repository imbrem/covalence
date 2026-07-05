//! Benchmark the Metamath → HOL import for one `.mm` file.
//!
//! Parses the database, then imports the first `limit` logical (`|-`) theorems
//! (or all of them) through the real parallel kernel path
//! ([`import_labels_parallel`]), and prints **one machine-readable JSON object**
//! to stdout: parse time, import time, throughput, ok/failed counts, and the
//! per-theorem timing distribution (median / p99 / slowest). All human chatter
//! goes to stderr so the JSON pipes cleanly into `jq` or the profile script.
//!
//! Usage:
//!   cargo run --release --example mm_import_bench -- <path.mm> [limit] [workers]
//!     limit   = max theorems to import (0 or omitted = all)
//!     workers = worker threads (0 or omitted = available parallelism)

use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use covalence_init::metalogic::mm_database::Parser;
use covalence_init::metalogic::mm_import::{import_labels_parallel, theorem_labels};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = args.get(1).cloned().unwrap_or_else(|| {
        eprintln!("usage: mm_import_bench <path.mm> [limit] [workers]");
        eprintln!("       mm_import_bench <path.mm> --only <label> [reps]");
        std::process::exit(2);
    });

    // Single-theorem mode: derive ONE theorem `reps` times on one thread (for
    // `perf record` / flamegraphs of a specific slow proof). `--only-cons`
    // routes the replay through a fresh per-derive `HashCons` (interning) to
    // measure interning's effect on a single proof.
    let only = args.get(2).map(String::as_str);
    if only == Some("--only") || only == Some("--only-cons") {
        let cons_mode = only == Some("--only-cons");
        let label = args.get(3).cloned().unwrap_or_else(|| {
            eprintln!("--only needs a label");
            std::process::exit(2);
        });
        let reps: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(50);
        let source = std::fs::read_to_string(&path).expect("read .mm");
        let db = covalence_init::metamath::parse(&source).expect("parse");
        let parser = Parser::new(&db);
        // A persistent clause cache across warmup + timed reps, matching the
        // real parallel import (one `ClauseCache` per worker, reused across all
        // its theorems) — so the timed reps measure the *per-theorem* replay
        // cost, not the one-time clause encoding the real import amortizes.
        use covalence_init::metalogic::mm_database::{ClauseCache, derive_theorem_cached};
        let mut cache = ClauseCache::new();
        let mut derive = |db: &_, parser: &_, label: &str| {
            if cons_mode {
                let mut cons = covalence_core::HashCons::new();
                covalence_init::metalogic::mm_database::derive_theorem_with_cons(
                    db, parser, label, &mut cons,
                )
            } else {
                derive_theorem_cached(db, parser, label, &mut cache)
            }
        };
        // Warm once (don't time the first, page-fault-heavy run); this also
        // populates the clause cache for the timed reps.
        let _ = derive(&db, &parser, &label).expect("derive");
        let t0 = Instant::now();
        for _ in 0..reps {
            let _ = derive(&db, &parser, &label).expect("derive");
        }
        let per = t0.elapsed().as_secs_f64() * 1000.0 / reps as f64;
        let tag = if cons_mode { "cons" } else { "plain" };
        eprintln!("[import-bench] {label} ({tag}): {per:.3} ms/derive over {reps} reps");
        println!(
            "{{\"label\":{label:?},\"mode\":{tag:?},\"reps\":{reps},\"ms_per_derive\":{per:.3}}}"
        );
        return;
    }
    let limit: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    let workers: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(0);

    eprintln!("[import-bench] reading {path}");
    let source = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("[import-bench] read failed: {e}");
        std::process::exit(1);
    });

    let t_parse = Instant::now();
    let db = covalence_init::metamath::parse(&source).unwrap_or_else(|e| {
        eprintln!("[import-bench] parse failed: {e}");
        std::process::exit(1);
    });
    let parse_ms = t_parse.elapsed().as_secs_f64() * 1000.0;

    // Select the theorems to import (the first `limit`, or all).
    let mut labels = theorem_labels(&db);
    let n_available = labels.len();
    if limit > 0 && limit < labels.len() {
        labels.truncate(limit);
    }
    eprintln!(
        "[import-bench] parsed in {parse_ms:.1} ms; importing {} of {} |- theorems",
        labels.len(),
        n_available
    );

    let ok = AtomicUsize::new(0);
    let failed = AtomicUsize::new(0);
    // (micros, label) per theorem, for the timing distribution.
    let timings: Mutex<Vec<(u128, String)>> = Mutex::new(Vec::with_capacity(labels.len()));

    let t_import = Instant::now();
    import_labels_parallel(
        &db,
        &labels,
        workers,
        |_total| {},
        |_label| {},
        |_done, _total, label, result, elapsed| {
            match &result {
                Ok(_) => {
                    ok.fetch_add(1, Ordering::Relaxed);
                }
                Err(e) => {
                    failed.fetch_add(1, Ordering::Relaxed);
                    eprintln!("[FAILED] {label}: {e}");
                }
            }
            timings
                .lock()
                .unwrap()
                .push((elapsed.as_micros(), label.to_string()));
        },
    );
    let import_ms = t_import.elapsed().as_secs_f64() * 1000.0;

    let ok = ok.load(Ordering::Relaxed);
    let failed = failed.load(Ordering::Relaxed);
    let n = ok + failed;

    let mut ts = timings.into_inner().unwrap();
    ts.sort_unstable_by_key(|t| std::cmp::Reverse(t.0)); // slowest first
    let us_at = |frac: f64| -> f64 {
        if ts.is_empty() {
            return 0.0;
        }
        // `ts` is sorted slowest→fastest; index from the fast end for percentiles.
        let idx = (((1.0 - frac) * (ts.len() as f64 - 1.0)).round() as usize).min(ts.len() - 1);
        ts[idx].0 as f64 / 1000.0
    };
    let slowest: Vec<String> = ts
        .iter()
        .take(10)
        .map(|(us, l)| format!("{{\"label\":{:?},\"ms\":{:.3}}}", l, *us as f64 / 1000.0))
        .collect();

    let n_workers = if workers == 0 {
        std::thread::available_parallelism()
            .map(|p| p.get())
            .unwrap_or(4)
    } else {
        workers
    };
    let throughput = if import_ms > 0.0 {
        n as f64 / (import_ms / 1000.0)
    } else {
        0.0
    };

    eprintln!(
        "[import-bench] imported {n} ({ok} ok, {failed} failed) in {import_ms:.1} ms \
         = {throughput:.0} thm/s ({n_workers} workers)"
    );

    // One JSON object on stdout.
    println!(
        "{{\
\"file\":{:?},\
\"theorems\":{n},\
\"ok\":{ok},\
\"failed\":{failed},\
\"available\":{n_available},\
\"workers\":{n_workers},\
\"parse_ms\":{:.3},\
\"import_ms\":{:.3},\
\"throughput_per_s\":{:.1},\
\"median_ms\":{:.3},\
\"p99_ms\":{:.3},\
\"slowest\":[{}]\
}}",
        path,
        parse_ms,
        import_ms,
        throughput,
        us_at(0.5),
        us_at(0.99),
        slowest.join(",")
    );
}
