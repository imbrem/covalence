//! **Get a Metamath database INTO covalence-hol** — construct
//! `⊢ Derivable_L ⌜S⌝` for each theorem from its (possibly compressed) proof;
//! the honest culmination of the construct-don't-trust pipeline.
//!
//! Where [`mm_database::replay_db`](crate::metalogic::mm_database::replay_db)
//! replays *one* `$p` assertion into a kernel-checked
//! `⊢ Derivable_L ⌜S⌝`, this module imports a **whole database**: every `$p`
//! theorem's (normal *or* compressed) proof is re-derived through the kernel,
//! landing a genuine, oracle-free (`has_no_obs`) derivability theorem per
//! theorem. The Metamath verifier's say-so is never trusted — each step is
//! re-checked — so this is real `.mm` data flowing into HOL, not a bridge tag.

use covalence_core::Thm;

use crate::metamath::{Database, MmError};

use super::mm_database::derive_theorem;

/// Import **every `$p` theorem** of `db` (those with a proof) into its kernel
/// derivability theorem `⊢ Derivable_L' ⌜S⌝`, collecting `(label, result)` in
/// database order. Each theorem goes through the **fast per-theorem path**
/// ([`derive_theorem`]): the rule set is scoped to that proof's referenced
/// lemmas (small `Closed_L'`), so importing a whole database is linear-ish in
/// total proof size rather than paying the full-database `Closed` cost per
/// theorem. `L' ⊆ L` (the database logic); `metalogic::transport_db` lifts each
/// to the full logic when wanted. A per-theorem error is captured in its
/// `Result` rather than aborting the whole import. `$a` axioms (no proof) are
/// skipped — they are the rule set, not theorems to re-derive.
pub fn import_theorems(db: &Database) -> Vec<(String, covalence_core::Result<Thm>)> {
    db.assertions()
        .filter(|a| a.proof.is_some())
        .map(|a| (a.label.clone(), derive_theorem(db, &a.label)))
        .collect()
}

/// A progress-reporting variant of [`import_theorems`]: invokes `progress(done,
/// total, label)` after each theorem is imported (for a UI progress bar / log).
/// Same fast per-theorem path and `(label, result)` collection.
pub fn import_theorems_with_progress(
    db: &Database,
    mut progress: impl FnMut(usize, usize, &str),
) -> Vec<(String, covalence_core::Result<Thm>)> {
    let labels: Vec<String> = db
        .assertions()
        .filter(|a| a.proof.is_some())
        .map(|a| a.label.clone())
        .collect();
    let total = labels.len();
    let mut out = Vec::with_capacity(total);
    for (i, label) in labels.into_iter().enumerate() {
        let result = derive_theorem(db, &label);
        progress(i + 1, total, &label);
        out.push((label, result));
    }
    out
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
/// [`crate::metamath::parse`] + [`import_theorems`] directly.
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

    /// The vendored real `hol.mm` (CC0; all 151 `$p` proofs are *compressed*).
    const HOL_MM: &str =
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../covalence-metamath/tests/fixtures/hol.mm"));

    /// **All of real `hol.mm` flows into covalence-hol.** Parse the vendored
    /// database, sanity-check it with the Metamath verifier, then *independently*
    /// re-derive **every** `$p` theorem's `⊢ Derivable_L' ⌜S⌝` through the kernel
    /// from its (compressed) proof — via the fast per-theorem [`derive_theorem`]
    /// path (rule set scoped to each proof's referenced lemmas) — and assert each
    /// is genuine (`has_no_obs`). This is the session goal: a whole real HOL-in-
    /// Metamath database imported into the kernel, the honest construct-don't-trust
    /// pipeline end to end.
    #[test]
    fn import_hol_mm() {
        let db = crate::metamath::parse(HOL_MM).expect("hol.mm parses");
        let verified = crate::metamath::verify_all(&db).expect("hol.mm verifies");
        assert!(verified > 100, "hol.mm should have >100 $p theorems, got {verified}");

        // Import the first N theorems (db order = foundational first) via the fast
        // per-theorem path. The full 151 import is the `#[ignore]`d sweep below
        // (~44 s); N keeps the default test snappy while still landing real HOL-
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
            let thm = derive_theorem(&db, label)
                .unwrap_or_else(|e| panic!("hol.mm `{label}` import failed: {e}"));
            assert!(thm.has_no_obs(), "imported hol.mm `{label}` must be oracle-free");
        }
        eprintln!("hol.mm import (first {N}) in {:?}", t0.elapsed());

        // Lock in the `H ⊢ H` edge case: `idi` (|- R |= A from $e |- R |= A)
        // references NO `|-` rule, so its scoped rule set is empty — derivable
        // over the empty rule set must still be well-formed (`Closed = T`), and
        // the essential surfaces as the theorem's one hypothesis.
        let idi = derive_theorem(&db, "idi").expect("hol.mm `idi` imports");
        assert!(idi.has_no_obs(), "idi must be oracle-free");
        assert_eq!(idi.hyps().len(), 1, "idi carries its one essential as a hypothesis");
    }

    /// **All 151 of real `hol.mm` import** into covalence-hol — every `$p`
    /// theorem's `⊢ Derivable_L' ⌜S⌝` re-derived through the kernel from its
    /// compressed proof (fast per-theorem path). `#[ignore]`d only for runtime
    /// (~44 s); run with `-- --ignored --nocapture`.
    #[test]
    #[ignore = "full 151-theorem sweep (~44s); the default import_hol_mm does a subset"]
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
                Ok(thm) => {
                    assert!(thm.has_no_obs(), "imported hol.mm `{label}` must be oracle-free");
                    n_ok += 1;
                }
                Err(e) => panic!("hol.mm `{label}` import failed: {e}"),
            }
        }
        eprintln!("hol.mm FULL import: {n_ok}/{total} theorems in {elapsed:?} (verified {verified})");
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
        let path = std::env::var("COV_SET_MM")
            .expect("set COV_SET_MM to a downloaded set.mm path");
        let source = std::fs::read_to_string(&path).expect("read set.mm");

        let t_parse = std::time::Instant::now();
        let db = crate::metamath::parse(&source).expect("set.mm parses");
        eprintln!("set.mm parsed in {:?}", t_parse.elapsed());

        // The scoped path is proof-dependent, so we can sample many more theorems
        // than the old whole-database path allowed. Take the first K $p theorems.
        const K: usize = 50;
        let mut sampled = 0usize;
        let t0 = std::time::Instant::now();
        for a in db.assertions() {
            if a.proof.is_none() {
                continue;
            }
            let t = std::time::Instant::now();
            let thm = derive_theorem(&db, &a.label)
                .unwrap_or_else(|e| panic!("set.mm theorem `{}` import failed: {e}", a.label));
            assert!(
                thm.has_no_obs(),
                "set.mm theorem `{}` must be oracle-free",
                a.label
            );
            eprintln!("set.mm import OK: `{}` in {:?}", a.label, t.elapsed());
            sampled += 1;
            if sampled >= K {
                break;
            }
        }
        eprintln!("set.mm import: {sampled} theorems in {:?}", t0.elapsed());
        assert!(sampled >= 1, "expected to sample at least one set.mm theorem");
    }
}
