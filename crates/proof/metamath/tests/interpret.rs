//! Cross-database interpretation against the real, pinned `iset.mm` / `set.mm`.
//!
//! The headline exploration: **how much of intuitionistic `iset.mm` is
//! witnessed, statement-for-statement (identity σ), inside classical
//! `set.mm`?** Every core IZF/intuitionistic axiom that classical set theory
//! also proves (as an axiom or a theorem) is a step toward a fully checked
//! IZF → ZF interpretation; the rest are recorded as the remaining gap.
//!
//! `#[ignore]`d + env-gated exactly like `tests/axiom_sets.rs` (same pinned
//! cache paths; `bun run bench:setmm` populates them).
//!
//! ```sh
//! COV_SET_MM=/tmp/covalence-set.mm-bcfef9892b61 \
//! COV_ISET_MM=/tmp/covalence-iset.mm-bcfef9892b61 \
//! cargo test -p covalence-metamath --test interpret --release -- --ignored --nocapture
//! ```

use std::collections::BTreeSet;
use std::path::PathBuf;

use covalence_metamath::interpret::matching_witnesses;
use covalence_metamath::{Database, Statement, parse};

const PINNED_REV: &str = "bcfef9892b61";

fn db_path(env: &str, base: &str) -> PathBuf {
    match std::env::var_os(env) {
        Some(p) => PathBuf::from(p),
        None => std::env::temp_dir().join(format!("covalence-{base}-{PINNED_REV}")),
    }
}

fn load(env: &str, base: &str) -> Database {
    let path = db_path(env, base);
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "read {}: {e}\nrun `bun run bench:setmm` to populate the pinned cache, \
             or point {env} at a downloaded {base} (revision {PINNED_REV})",
            path.display()
        )
    });
    parse(&src).unwrap_or_else(|e| panic!("{base} should parse: {e}"))
}

/// The core intuitionistic-logic + IZF axioms of `iset.mm` (the propositional
/// and predicate calculus plus the set-theoretic axioms) — the labels a full
/// IZF → ZF interpretation must witness.
const CORE_IZF: &[&str] = &[
    // intuitionistic propositional calculus
    "ax-mp",
    "ax-1",
    "ax-2",
    "ax-ia1",
    "ax-ia2",
    "ax-ia3",
    "ax-in1",
    "ax-in2",
    "ax-io",
    // predicate calculus
    "ax-5",
    "ax-7",
    "ax-gen",
    "ax-ie1",
    "ax-ie2",
    "ax-8",
    "ax-10",
    "ax-11",
    "ax-i12",
    "ax-bndl",
    "ax-4",
    "ax-17",
    "ax-i9",
    "ax-ial",
    "ax-i5r",
    "ax-13",
    "ax-14",
    // IZF set theory
    "ax-ext",
    "ax-coll",
    "ax-sep",
    "ax-nul",
    "ax-pow",
    "ax-pr",
    "ax-un",
    "ax-setind",
    "ax-iinf",
];

/// Identity-σ statement match: for each core `iset.mm` axiom, does `set.mm`
/// contain an assertion with the identical statement (axiom or theorem)?
/// Reports the matched/unmatched split and asserts a snapshot so drift in
/// either database is caught, plus the invariant that the whole propositional
/// core and the shared set-theory axioms are covered.
#[test]
#[ignore = "requires the pinned iset.mm/set.mm caches; see module docs"]
fn izf_core_witnessed_in_setmm() {
    let iset = load("COV_ISET_MM", "iset.mm");
    let set = load("COV_SET_MM", "set.mm");

    let mut matched: BTreeSet<&str> = BTreeSet::new();
    let mut unmatched: Vec<&str> = Vec::new();
    for &label in CORE_IZF {
        let Some(Statement::Assert(ax)) = iset.statement_by_label(label) else {
            panic!("{label} is not an assertion in iset.mm");
        };
        assert!(
            ax.proof.is_none(),
            "{label} should be a $a axiom in iset.mm"
        );
        let witnesses = matching_witnesses(&set, ax);
        match witnesses.first() {
            Some(w) => {
                matched.insert(label);
                eprintln!(
                    "{label} ↦ set.mm `{}` ({})",
                    w.label,
                    if w.proof.is_none() {
                        "axiom"
                    } else {
                        "theorem"
                    }
                );
            }
            None => {
                unmatched.push(label);
                eprintln!("{label} ↦ (no identical-statement witness in set.mm)");
            }
        }
    }

    eprintln!(
        "\nIZF core witnessed in set.mm (identity σ): {}/{} matched; unmatched: {unmatched:?}",
        matched.len(),
        CORE_IZF.len(),
    );

    // Invariant 1: the entire shared propositional/predicate core that is
    // *classically valid* is witnessed. (Intuitionistic-specific axioms whose
    // classical counterpart is a different statement — e.g. `ax-ia1` vs the
    // classical `simpl` — may need an override; those show up as unmatched and
    // are the recorded gap, not a regression.)
    for must in ["ax-mp", "ax-1", "ax-2"] {
        assert!(
            matched.contains(must),
            "{must} must be witnessed identically in set.mm"
        );
    }
    // Invariant 2: the set-theory axioms that ZF states identically to IZF are
    // witnessed (extensionality, union, power set, pairing).
    for must in ["ax-ext", "ax-un", "ax-pow", "ax-pr"] {
        assert!(
            matched.contains(must),
            "{must} must be witnessed identically in set.mm"
        );
    }

    // Snapshot at the pinned revision: exactly 32/35 core axioms are witnessed
    // statement-for-statement. The 3 unmatched are the constructively-vs-
    // classically DIFFERENT set axioms — collection (vs replacement), set
    // induction (vs foundation), and the IZF infinity form — which need a
    // derived-witness bridge, not an identical statement (interpret.rs
    // SKELETONS). Update deliberately when bumping the pin (note it in
    // notes/vibes/logics/metamath-axiom-set-metatheory.md). Freezing this
    // fails the test on silent drift in either database.
    assert_eq!(
        unmatched,
        ["ax-coll", "ax-setind", "ax-iinf"],
        "the unmatched core axioms should be exactly collection / set-induction / IZF-infinity"
    );
    assert_eq!(
        matched.len(),
        32,
        "32/35 core IZF axioms witnessed identically in set.mm"
    );
}
