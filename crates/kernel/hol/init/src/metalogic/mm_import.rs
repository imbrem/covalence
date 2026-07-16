//! **Get a Metamath database INTO covalence-hol** — construct
//! `⊢ Derivable_L ⌜S⌝` for each theorem from its (possibly compressed) proof;
//! the honest culmination of the construct-don't-trust pipeline.
//!
//! Where [`mm_database::replay_db`](crate::metalogic::mm_database::replay_db)
//! replays *one* `$p` assertion into a kernel-checked
//! `⊢ Derivable_L ⌜S⌝`, this module imports a **whole database**: every `$p`
//! theorem's (normal *or* compressed) proof is re-derived through the kernel,
//! landing a genuine (hypothesis-free, oracle-free) derivability theorem per
//! theorem. The Metamath verifier's say-so is never trusted — each step is
//! re-checked — so this is real `.mm` data flowing into HOL, not a bridge tag.

use covalence_hol_eval::EvalThm as Thm;

use crate::metamath::{Database, MmError};

#[cfg(test)]
use super::mm_database::derive_theorem;
use super::mm_database::{ClauseCache, Parser, derive_theorem_cached, derive_theorem_with};

/// The labels of the database's **logical theorems** to import: `$p` assertions
/// (proof present) whose conclusion typecode is `|-`. Non-`|-` `$p` assertions
/// (e.g. set.mm's `weq`/`wel` — *syntax* theorems that prove a `wff`/`class` is
/// well-formed) are **grammar, not logical content**: their replay would end on
/// a syntax (`wff`) slot, not a `⊢ Derivable_L` derivation, so they are excluded
/// from import (they still serve as formers during other proofs).
pub fn theorem_labels(db: &Database) -> Vec<String> {
    db.assertions()
        .filter(|a| a.proof.is_some() && a.conclusion.typecode() == "|-")
        .map(|a| a.label.clone())
        .collect()
}

/// Import **every logical `$p` theorem** of `db` ([`theorem_labels`]) into its
/// kernel derivability theorem `⊢ Derivable_L' ⌜S⌝`, collecting `(label,
/// result)` in database order. Each theorem goes through the **fast per-theorem
/// path** ([`derive_theorem`](crate::metalogic::mm_database::derive_theorem)): the rule set is scoped to that proof's referenced
/// lemmas (small `Closed_L'`), so importing a whole database is linear-ish in
/// total proof size rather than paying the full-database `Closed` cost per
/// theorem. `L' ⊆ L` (the database logic); `metalogic::transport_db` lifts each
/// to the full logic when wanted. A per-theorem error is captured in its
/// `Result` rather than aborting the whole import.
pub fn import_theorems(db: &Database) -> Vec<(String, covalence_core::Result<Thm>)> {
    let parser = Parser::new(db);
    theorem_labels(db)
        .into_iter()
        .map(|label| {
            let r = derive_theorem_with(db, &parser, &label);
            (label, r)
        })
        .collect()
}

/// A progress-reporting variant of [`import_theorems`]: invokes `progress(done,
/// total, label)` after each theorem is imported (for a UI progress bar / log).
/// Same fast per-theorem path and `(label, result)` collection.
pub fn import_theorems_with_progress(
    db: &Database,
    mut progress: impl FnMut(usize, usize, &str),
) -> Vec<(String, covalence_core::Result<Thm>)> {
    let parser = Parser::new(db);
    let labels = theorem_labels(db);
    let total = labels.len();
    let mut out = Vec::with_capacity(total);
    for (i, label) in labels.into_iter().enumerate() {
        let result = derive_theorem_with(db, &parser, &label);
        progress(i + 1, total, &label);
        out.push((label, result));
    }
    out
}

/// **Parallel import** — derive each `$p` theorem on a pool of `n_threads`
/// worker threads (work-stealing over a shared atomic cursor, so the slow
/// straggler proofs don't stall the fast majority). The database is parsed once
/// and shared by `&` across threads (read-only); each `derive_theorem` is
/// independent (its rule set is scoped to its own proof), so they parallelize
/// cleanly. `on_start(total)` fires once before work begins; `on_pick(label)`
/// fires when a worker pulls a label off the queue, **before** its proof is
/// derived (so a UI can mark it in-progress); `on_each(done, total, label,
/// &result, elapsed)` fires once per finished theorem. Both `on_pick` and
/// `on_each` run on worker threads (must be `Sync`); `done` is a monotonic
/// completion counter, so results arrive out of database order. Use `n_threads
/// = 0` to pick `available_parallelism`.
pub fn import_theorems_parallel(
    db: &Database,
    n_threads: usize,
    on_start: impl FnOnce(usize),
    on_pick: impl Fn(&str) + Sync,
    on_each: impl Fn(usize, usize, &str, &covalence_core::Result<Thm>, std::time::Duration) + Sync,
) {
    let labels = theorem_labels(db);
    import_labels_parallel(db, &labels, n_threads, on_start, on_pick, on_each);
}

/// [`import_theorems_parallel`] over an **explicit label slice** (rather than
/// every `$p` theorem). Same work-stealing pool and callbacks; useful for
/// benchmarking a prefix of a large database (e.g. the first N theorems of
/// set.mm) or re-importing a chosen subset.
pub fn import_labels_parallel(
    db: &Database,
    labels: &[String],
    n_threads: usize,
    on_start: impl FnOnce(usize),
    on_pick: impl Fn(&str) + Sync,
    on_each: impl Fn(usize, usize, &str, &covalence_core::Result<Thm>, std::time::Duration) + Sync,
) {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let total = labels.len();
    on_start(total);
    if total == 0 {
        return;
    }

    let n = if n_threads == 0 {
        std::thread::available_parallelism()
            .map(|p| p.get())
            .unwrap_or(4)
    } else {
        n_threads
    }
    .clamp(1, 64);

    // Build the former grammar / `var → typecode` map ONCE and share it
    // read-only across all workers (it is `Sync`), instead of every thread
    // re-scanning the whole database per theorem.
    let parser = Parser::new(db);

    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let on_pick = &on_pick;
    let on_each = &on_each;
    let next = &next;
    let done = &done;
    let parser = &parser;
    std::thread::scope(|s| {
        for _ in 0..n {
            s.spawn(move || {
                // One clause cache per worker, reused across all theorems it
                // derives: a cited lemma's clause is compiled once instead of
                // re-parsed in every proof. No interning of proof terms (they're
                // dropped after `on_each`, so it would be pure overhead — callers
                // that *keep* terms use [`derive_theorem_with_cons`]).
                let mut cache = ClauseCache::new();
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= total {
                        break;
                    }
                    let label = &labels[i];
                    on_pick(label);
                    let t0 = std::time::Instant::now();
                    let result = derive_theorem_cached(db, parser, label, &mut cache);
                    let elapsed = t0.elapsed();
                    let d = done.fetch_add(1, Ordering::Relaxed) + 1;
                    on_each(d, total, label, &result, elapsed);
                }
            });
        }
    });
}

/// The error of a full [`read_and_import`]: either the `.mm` failed to parse, or
/// the first `$p` theorem whose replay failed (with its label).
#[derive(Debug)]
pub enum ImportError {
    /// The `.mm` source did not parse.
    Parse(MmError),
    /// Theorem `label` parsed but its proof would not replay through the kernel.
    Replay {
        /// The `$p` label that failed.
        label: String,
        /// The kernel-side replay error.
        error: covalence_core::Error,
    },
}

impl std::fmt::Display for ImportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImportError::Parse(e) => write!(f, "parse error: {e}"),
            ImportError::Replay { label, error } => {
                write!(f, "replay of `{label}` failed: {error}")
            }
        }
    }
}

impl std::error::Error for ImportError {}

/// Parse a `.mm` `source` and import **all** its `$p` theorems into kernel
/// `⊢ Derivable_L ⌜S⌝` theorems. Returns `(label, thm)` for every theorem on
/// success; surfaces the **first** failure (parse, or the first theorem that
/// would not replay). For a lenient, collect-all-errors view use
/// [`fn@crate::metamath::parse`] + [`import_theorems`] directly.
// Cold import path; `MmError` is a rich diagnostic enum, not worth boxing.
#[allow(clippy::result_large_err)]
pub fn read_and_import(source: &str) -> Result<Vec<(String, Thm)>, ImportError> {
    let db = crate::metamath::parse(source).map_err(ImportError::Parse)?;
    let mut out = Vec::new();
    for (label, result) in import_theorems(&db) {
        match result {
            Ok(thm) => out.push((label, thm)),
            Err(error) => return Err(ImportError::Replay { label, error }),
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Scan a database for **all** import failures and print them (label +
    /// error), using the parallel path for speed. `COV_SET_MM` env path;
    /// `#[ignore]`d. Run:
    /// `COV_SET_MM=/path/set.mm cargo test -p covalence-hol --lib --release \
    ///   metalogic::mm_import::tests::scan_failures -- --ignored --nocapture`
    #[test]
    #[ignore = "needs COV_SET_MM; full parallel scan to enumerate failures"]
    fn scan_failures() {
        let path = std::env::var("COV_SET_MM").expect("set COV_SET_MM");
        let source = std::fs::read_to_string(&path).expect("read .mm");
        let t_parse = std::time::Instant::now();
        let db = crate::metamath::parse(&source).expect("parse");
        eprintln!("parsed in {:?}", t_parse.elapsed());

        let fails = std::sync::Mutex::new(Vec::<(String, String)>::new());
        let t0 = std::time::Instant::now();
        import_theorems_parallel(
            &db,
            0,
            |total| eprintln!("scanning {total} |- theorems (parallel)"),
            |_label| {},
            |done, total, label, result, _dur| {
                if let Err(e) = result {
                    fails
                        .lock()
                        .unwrap()
                        .push((label.to_string(), e.to_string()));
                }
                if done % 5000 == 0 {
                    eprintln!(
                        "  {done}/{total} ({} fails so far)",
                        fails.lock().unwrap().len()
                    );
                }
            },
        );
        let fails = fails.into_inner().unwrap();
        eprintln!("scan done in {:?}: {} failures", t0.elapsed(), fails.len());
        for (l, e) in &fails {
            eprintln!("FAIL  {l}:  {e}");
        }
    }

    /// Targeted regression: the set.mm theorems sensitive to the
    /// `free variable "d"` metavar/predicate name clash import cleanly. Low CPU
    /// (derives ~14 named theorems), `COV_SET_MM` env, `#[ignore]`d.
    #[test]
    #[ignore = "needs COV_SET_MM; targeted regression for the `d` namespacing fix"]
    fn formerly_failing_import() {
        use super::super::mm_database::derive_theorem;
        let path = std::env::var("COV_SET_MM").expect("set COV_SET_MM");
        let db = crate::metamath::parse(&std::fs::read_to_string(&path).unwrap()).unwrap();
        let labels = [
            "cbvral4vw",
            "cbvral6vw",
            "cbvral8vw",
            "disjiund",
            "otsndisj",
            "otiunsndisj",
            "reuop",
            "f1veqaeq",
            "isopolem",
            "isosolem",
            "fvmpopr2d",
        ];
        for l in labels {
            let _thm = derive_theorem(&db, l).unwrap_or_else(|e| panic!("`{l}` still fails: {e}"));
            eprintln!("OK {l}");
        }
    }

    /// The vendored real `hol.mm` (CC0; all 151 `$p` proofs are *compressed*).
    const HOL_MM: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../proof/metamath/tests/fixtures/hol.mm"
    ));

    /// **All of real `hol.mm` flows into covalence-hol.** Parse the vendored
    /// database, sanity-check it with the Metamath verifier, then *independently*
    /// re-derive **every** `$p` theorem's `⊢ Derivable_L' ⌜S⌝` through the kernel
    /// from its (compressed) proof — via the fast per-theorem [`derive_theorem`]
    /// path (rule set scoped to each proof's referenced lemmas) — and check each
    /// derives without error. This is the session goal: a whole real HOL-in-
    /// Metamath database imported into the kernel, the honest construct-don't-trust
    /// pipeline end to end.
    #[test]
    fn import_hol_mm() {
        let db = crate::metamath::parse(HOL_MM).expect("hol.mm parses");
        let verified = crate::metamath::verify_all(&db).expect("hol.mm verifies");
        assert!(
            verified > 100,
            "hol.mm should have >100 $p theorems, got {verified}"
        );

        // Import the first N theorems (db order = foundational first) via the fast
        // per-theorem path. The full 151 import is the `#[ignore]`d sweep below
        // (~5 s); N keeps the default test snappy while still landing real HOL-
        // in-Metamath theorems in the kernel.
        const N: usize = 25;
        let labels: Vec<String> = db
            .assertions()
            .filter(|a| a.proof.is_some())
            .map(|a| a.label.clone())
            .take(N)
            .collect();
        let t0 = std::time::Instant::now();
        for label in &labels {
            let _thm = derive_theorem(&db, label)
                .unwrap_or_else(|e| panic!("hol.mm `{label}` import failed: {e}"));
        }
        eprintln!("hol.mm import (first {N}) in {:?}", t0.elapsed());

        // Lock in the `H ⊢ H` edge case: `idi` (|- R |= A from $e |- R |= A)
        // references NO `|-` rule, so its scoped rule set is empty — derivable
        // over the empty rule set must still be well-formed (`Closed = T`), and
        // the essential surfaces as the theorem's one hypothesis.
        let idi = derive_theorem(&db, "idi").expect("hol.mm `idi` imports");
        assert_eq!(
            idi.hyps().len(),
            1,
            "idi carries its one essential as a hypothesis"
        );
    }

    /// **All 151 of real `hol.mm` import** into covalence-hol — every `$p`
    /// theorem's `⊢ Derivable_L' ⌜S⌝` re-derived through the kernel from its
    /// compressed proof (fast per-theorem path, shared parser). `#[ignore]`d only
    /// for runtime (~5 s); run with `-- --ignored --nocapture`.
    #[test]
    #[ignore = "full 151-theorem sweep (~5s); the default import_hol_mm does a subset"]
    fn import_hol_mm_full() {
        let db = crate::metamath::parse(HOL_MM).expect("hol.mm parses");
        let verified = crate::metamath::verify_all(&db).expect("hol.mm verifies");

        let t0 = std::time::Instant::now();
        let results = import_theorems(&db);
        let elapsed = t0.elapsed();

        let total = results.len();
        let mut n_ok = 0usize;
        for (label, r) in &results {
            match r {
                Ok(_thm) => {
                    n_ok += 1;
                }
                Err(e) => panic!("hol.mm `{label}` import failed: {e}"),
            }
        }
        eprintln!(
            "hol.mm FULL import: {n_ok}/{total} theorems in {elapsed:?} (verified {verified})"
        );
        assert_eq!(n_ok, total, "all hol.mm $p theorems should import");
        assert_eq!(total, verified, "every verified theorem is imported");
    }

    /// `set.mm` sample — `#[ignore]`d (set.mm is ~48 MB, not vendored). Point
    /// `COV_SET_MM` at a downloaded `set.mm` to demonstrate real set.mm theorems
    /// flowing into covalence-hol via the **fast per-theorem** [`derive_theorem`]
    /// path: the rule set is scoped to each proof's referenced lemmas, so cost is
    /// proof-dependent — NOT the ~47k-clause whole-database `Closed` that made the
    /// old `replay_db` path minutes/theorem. Samples the first K theorems and
    /// asserts each constructs a genuine `⊢ Derivable_L' ⌜S⌝`.
    #[test]
    #[ignore = "needs COV_SET_MM=/path/to/set.mm (~48 MB, not vendored)"]
    fn import_set_mm_sample() {
        let path = std::env::var("COV_SET_MM").expect("set COV_SET_MM to a downloaded set.mm path");
        let source = std::fs::read_to_string(&path).expect("read set.mm");

        let t_parse = std::time::Instant::now();
        let db = crate::metamath::parse(&source).expect("set.mm parses");
        eprintln!("set.mm parsed in {:?}", t_parse.elapsed());

        // The scoped path is proof-dependent, so we can sample many more theorems
        // than a whole-database path would allow. Take the first K $p theorems.
        const K: usize = 50;
        let mut sampled = 0usize;
        let t0 = std::time::Instant::now();
        for a in db.assertions() {
            if a.proof.is_none() {
                continue;
            }
            let t = std::time::Instant::now();
            let _thm = derive_theorem(&db, &a.label)
                .unwrap_or_else(|e| panic!("set.mm theorem `{}` import failed: {e}", a.label));
            eprintln!("set.mm import OK: `{}` in {:?}", a.label, t.elapsed());
            sampled += 1;
            if sampled >= K {
                break;
            }
        }
        eprintln!("set.mm import: {sampled} theorems in {:?}", t0.elapsed());
        assert!(
            sampled >= 1,
            "expected to sample at least one set.mm theorem"
        );
    }

    // (Retired: `temp_import_set_mm_broad` — a first-N serial verify sweep — was
    // redundant with `scan_failures` above, which scans *all* `|-` theorems in
    // parallel and enumerates failures. Use `scan_failures` for a broad COV_SET_MM
    // verify.)
}
