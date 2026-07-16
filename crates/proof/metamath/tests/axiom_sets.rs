//! Axiom-set metatheory against the real, pinned `set.mm` / `iset.mm`.
//!
//! These tests validate the vendored [`covalence_metamath::axioms`] constants
//! against the pinned database revision and exercise the implication /
//! axiom-usage machinery at full scale. They are `#[ignore]`d because the
//! databases (~51 MB / ~12 MB) are not vendored.
//!
//! Database resolution: `$COV_SET_MM` / `$COV_ISET_MM` if set, else the
//! pinned cache path `${TMPDIR:-/tmp}/covalence-set.mm-bcfef9892b61` (resp.
//! `covalence-iset.mm-…`). Running `bun run bench:setmm` populates the cache
//! (see `scripts/_setmm.mjs` for the pinned revision).
//!
//! ```sh
//! COV_SET_MM=/tmp/covalence-set.mm-bcfef9892b61 \
//! COV_ISET_MM=/tmp/covalence-iset.mm-bcfef9892b61 \
//! cargo test -p covalence-metamath --test axiom_sets --release -- --ignored --nocapture
//! ```

use std::path::PathBuf;
use std::sync::OnceLock;

use covalence_metamath::axioms::{classify_axioms, iset, sets};
use covalence_metamath::{
    AxiomSet, Database, MetaError, allow_definitions, check_implication, derivable_from, parse,
    setmm_witness,
};

/// The pinned metamath/set.mm revision (`scripts/_setmm.mjs`).
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

fn set_mm() -> &'static Database {
    static DB: OnceLock<Database> = OnceLock::new();
    DB.get_or_init(|| load("COV_SET_MM", "set.mm"))
}

fn iset_mm() -> &'static Database {
    static DB: OnceLock<Database> = OnceLock::new();
    DB.get_or_init(|| load("COV_ISET_MM", "iset.mm"))
}

const IGNORE: &str = "requires the pinned set.mm/iset.mm cache (bun run bench:setmm) \
                      or COV_SET_MM/COV_ISET_MM; large + slow, use --release";

/// 1. Every vendored `set.mm` axiom set resolves against the pinned database:
/// each label is a `$a` with the `|-` typecode. This is the drift detector.
#[test]
#[ignore = "requires the pinned set.mm cache; see module docs"]
fn setmm_vendored_sets_resolve() {
    let _ = IGNORE;
    let db = set_mm();
    for s in [
        &sets::PROP,
        &sets::PRED,
        &sets::ZF_KERNEL,
        &sets::ZF,
        &sets::ZFC,
        &sets::TARSKI_GROTHENDIECK,
        &sets::REALS,
    ] {
        let resolved = s
            .resolve(db)
            .unwrap_or_else(|e| panic!("{} should resolve against set.mm: {e}", s.name));
        assert_eq!(resolved.len(), s.labels().len());
        eprintln!("{}: {} axioms resolve", s.name, resolved.len());
    }
}

/// 2. THE HEADLINE: the axiomatic reals are conservative over ZFC + definitions.
/// Every one of the 25 `ax-*cn*`/`ax-pre-*` axioms has a same-statement witness
/// theorem (`axcnex`, …, `axpre-sup`) proved from ZFC axioms plus `df-*`s only.
#[test]
#[ignore = "requires the pinned set.mm cache; see module docs"]
fn reals_conservative_over_zfc() {
    let db = set_mm();
    let imp = check_implication(
        db,
        &sets::ZFC,
        &sets::REALS,
        &|ax| setmm_witness(ax),
        &allow_definitions,
    )
    .expect("ZFC (+ definitions) implies the axiomatic reals");

    // Every REALS-only axiom is witnessed; ZFC members are trivial.
    let witnessed: Vec<_> = imp
        .witnesses
        .iter()
        .filter(|w| w.theorem.is_some())
        .collect();
    assert_eq!(imp.witnesses.len(), sets::REALS.labels().len());
    assert_eq!(witnessed.len(), 25, "all 25 reals axioms have witnesses");
    // Every witness follows set.mm's `ax-foo` ↦ `axfoo` restatement convention.
    for w in &witnessed {
        assert_eq!(
            w.theorem.as_deref(),
            setmm_witness(&w.axiom).as_deref(),
            "witness for {} follows the axfoo convention",
            w.axiom
        );
    }

    let admitted = imp.admitted();
    assert!(!admitted.is_empty());
    assert!(admitted.iter().all(|d| d.starts_with("df-")));
    let sample: Vec<_> = admitted.iter().take(8).collect();
    eprintln!(
        "ZFC => REALS: {} witnessed axioms, {} admitted definitions, e.g. {:?}",
        witnessed.len(),
        admitted.len(),
        sample
    );
}

/// 3a. The redundant ZF axioms are derivable from the non-redundant kernel —
/// but only as a *chain* of implications: set.mm proves `axnul` from the
/// (redundant) `ax-sep`, `axpr` from the (redundant) `ax-nul`, and `axinf2`
/// may lean on earlier redundant axioms too, so the one-step check correctly
/// fails, and layering `ax-sep`, `ax-nul`, `ax-pr`, `ax-inf2` one at a time
/// succeeds. By transitivity of the transport metatheorem, ZF_KERNEL ⇒ ZF.
#[test]
#[ignore = "requires the pinned set.mm cache; see module docs"]
fn zf_kernel_implies_zf_layered() {
    let db = set_mm();

    // The one-step check fails honestly: a witness rests on a redundant axiom
    // that is not (yet) in the stronger set.
    let err = check_implication(
        db,
        &sets::ZF_KERNEL,
        &sets::ZF,
        &|ax| setmm_witness(ax),
        &allow_definitions,
    )
    .expect_err("one-step ZF_KERNEL => ZF should fail: witnesses cite redundant axioms");
    eprintln!("one-step ZF_KERNEL => ZF fails as expected: {err}");
    assert!(matches!(err, MetaError::ForbiddenAxiom { .. }));

    // Layered: each step admits one more redundant axiom, witnessed from the
    // previous layer.
    static STEP_SEP: AxiomSet = AxiomSet {
        name: "ZF_KERNEL+sep",
        extends: &[&sets::ZF_KERNEL],
        delta: &["ax-sep"],
    };
    static STEP_NUL: AxiomSet = AxiomSet {
        name: "ZF_KERNEL+sep+nul",
        extends: &[&STEP_SEP],
        delta: &["ax-nul"],
    };
    static STEP_PR: AxiomSet = AxiomSet {
        name: "ZF_KERNEL+sep+nul+pr",
        extends: &[&STEP_NUL],
        delta: &["ax-pr"],
    };
    let chain: [(&AxiomSet, &AxiomSet, &str); 4] = [
        (&sets::ZF_KERNEL, &STEP_SEP, "axsep"),
        (&STEP_SEP, &STEP_NUL, "axnul"),
        (&STEP_NUL, &STEP_PR, "axpr"),
        (&STEP_PR, &sets::ZF, "axinf2"),
    ];
    for (stronger, weaker, expect_witness) in chain {
        let imp = check_implication(
            db,
            stronger,
            weaker,
            &|ax| setmm_witness(ax),
            &allow_definitions,
        )
        .unwrap_or_else(|e| panic!("{} => {} should hold: {e}", stronger.name, weaker.name));
        let witnessed: Vec<_> = imp
            .witnesses
            .iter()
            .filter_map(|w| w.theorem.as_deref())
            .collect();
        assert_eq!(witnessed, [expect_witness]);
        eprintln!(
            "{} => {}: witness {} (+{} admitted definitions)",
            stronger.name,
            weaker.name,
            expect_witness,
            imp.admitted().len()
        );
    }
}

/// 3b. Choice is NOT derivable: ZF does not imply ZFC. set.mm *does* have
/// theorems named `axac`/`axac2`, but they derive each choice form from the
/// other, so the check fails with ForbiddenAxiom (the witness rests on the
/// other choice axiom) rather than NoWitness.
#[test]
#[ignore = "requires the pinned set.mm cache; see module docs"]
fn zf_does_not_imply_choice() {
    let db = set_mm();
    let err = check_implication(
        db,
        &sets::ZF,
        &sets::ZFC,
        &|ax| setmm_witness(ax),
        &allow_definitions,
    )
    .expect_err("choice is not derivable from ZF");
    eprintln!("ZF => ZFC fails as expected: {err}");
    match &err {
        MetaError::ForbiddenAxiom { axiom, used, .. } => {
            assert!(axiom == "ax-ac" || axiom == "ax-ac2");
            assert!(used == "ax-ac" || used == "ax-ac2");
        }
        other => panic!("expected ForbiddenAxiom (axac/axac2 cite the other form), got {other}"),
    }
}

/// 3c. Grothendieck universes are NOT derivable: ZFC does not imply
/// Tarski–Grothendieck. There is no `axgroth` theorem at all → NoWitness.
#[test]
#[ignore = "requires the pinned set.mm cache; see module docs"]
fn zfc_does_not_imply_tarski_grothendieck() {
    let db = set_mm();
    let err = check_implication(
        db,
        &sets::ZFC,
        &sets::TARSKI_GROTHENDIECK,
        &|ax| setmm_witness(ax),
        &allow_definitions,
    )
    .expect_err("ax-groth is not derivable from ZFC");
    eprintln!("ZFC => TARSKI_GROTHENDIECK fails as expected: {err}");
    match &err {
        MetaError::NoWitness { axiom, .. } => assert_eq!(axiom, "ax-groth"),
        other => panic!("expected NoWitness for ax-groth, got {other}"),
    }
}

/// 4. Axiom-usage reasoning on real theorems. `2p2e4` is stated in the
/// axiomatic-reals development, so its proof rests on the reals *axioms*
/// (`ax-1cn`, `ax-addcl`, …) — it is NOT within ZFC + definitions as proved
/// (even though the reals axioms are themselves ZFC-derivable, set.mm proofs
/// cite the axioms, not their witness restatements). From REALS it is fine.
/// So is `sqrt2irr`.
#[test]
#[ignore = "requires the pinned set.mm cache; see module docs"]
fn axiom_usage_of_real_theorems() {
    let db = set_mm();

    let err = derivable_from(db, "2p2e4", &sets::ZFC, &allow_definitions)
        .expect_err("2p2e4 as proved cites reals axioms, so it is not within ZFC+definitions");
    eprintln!("2p2e4 from ZFC fails as expected: {err}");
    match &err {
        MetaError::NotDerivableFrom { used, .. } => {
            assert!(
                sets::REALS.contains(used),
                "blocker {used} is a reals axiom"
            )
        }
        other => panic!("expected NotDerivableFrom, got {other}"),
    }

    let admitted = derivable_from(db, "2p2e4", &sets::REALS, &allow_definitions)
        .expect("2p2e4 is derivable from the reals axioms + definitions");
    eprintln!(
        "2p2e4 from REALS: ok, {} admitted definitions",
        admitted.len()
    );

    let admitted = derivable_from(db, "sqrt2irr", &sets::REALS, &allow_definitions)
        .expect("sqrt2irr is derivable from the reals axioms + definitions");
    eprintln!(
        "sqrt2irr from REALS: ok, {} admitted definitions",
        admitted.len()
    );
}

/// 5. The vendored `iset.mm` sets resolve against the pinned database, and the
/// IZF union covers the core intuitionistic axioms (while excluding the
/// axioms iset.mm itself marks obsolete/redundant: `ax-10o`, `ax-11o`,
/// `ax-16`, and the CZF/BJ `ax-bd*` mathbox layer).
#[test]
#[ignore = "requires the pinned iset.mm cache; see module docs"]
fn isetmm_vendored_sets_resolve() {
    let db = iset_mm();
    for s in [&iset::PROP, &iset::PRED, &iset::IZF] {
        let resolved = s
            .resolve(db)
            .unwrap_or_else(|e| panic!("{} should resolve against iset.mm: {e}", s.name));
        assert_eq!(resolved.len(), s.labels().len());
        eprintln!("{}: {} axioms resolve", s.name, resolved.len());
    }

    // Core axioms are members of the union.
    let izf = iset::IZF.labels();
    for core in [
        "ax-mp",
        "ax-io",
        "ax-gen",
        "ax-ie2",
        "ax-bndl",
        "ax-i9",
        "ax-ial",
        "ax-13",
        "ax-14",
        "ax-ext",
        "ax-coll",
        "ax-sep",
        "ax-nul",
        "ax-pow",
        "ax-pr",
        "ax-un",
        "ax-setind",
        "ax-iinf",
    ] {
        assert!(
            izf.contains(core),
            "core IZF axiom {core} missing from the vendored union"
        );
    }
    // Obsolete/legacy forms stay out.
    for obsolete in ["ax-3", "ax-10o", "ax-11o", "ax-16"] {
        assert!(!izf.contains(obsolete), "{obsolete} should not be vendored");
    }

    // Report every |- axiom of iset.mm the vendored sets do NOT cover, and
    // check none of them is a core logic/IZF axiom (they should all be the
    // CZF/BJ boundedness layer, the constructive reals, or legacy forms).
    let report = classify_axioms(db, &[&iset::PROP, &iset::PRED, &iset::IZF]);
    let outside: Vec<&str> = report
        .iter()
        .filter(|(_, sets)| sets.is_empty())
        .map(|(l, _)| *l)
        .collect();
    // Definitions (`df-*`) are `|-`-typecode `$a`s in iset.mm too — expected to
    // fall outside the *logical*-axiom sets. The point of this loop is to catch
    // a genuine core logic/IZF axiom being left uncovered, so definitions and
    // the known non-core layers are whitelisted; anything else fails loudly.
    let non_def_outside: Vec<&str> = outside
        .iter()
        .copied()
        .filter(|l| !l.starts_with("df-"))
        .collect();
    eprintln!(
        "iset.mm |- axioms outside the vendored sets: {} total, {} non-definition: {non_def_outside:?}",
        outside.len(),
        non_def_outside.len(),
    );
    for l in &non_def_outside {
        assert!(
            l.starts_with("ax-bd")            // bounded-formula CZF layer
                || l.starts_with("ax-bj-")    // BJ mathbox
                || ["ax-10o", "ax-11o", "ax-16"].contains(l) // legacy forms
                || ["ax-inf2", "ax-infvn", "ax-strcoll", "ax-sscoll"].contains(l) // CZF layer
                // the constructive reals postulates
                || sets::REALS.contains(l)
                || [
                    "ax-0id", "ax-0lt1", "ax-1re", "ax-addcom", "ax-arch", "ax-caucvg",
                    "ax-ddkcomp", "ax-precex", "ax-pre-apti", "ax-pre-ltirr", "ax-pre-ltwlin",
                    "ax-pre-mulext", "ax-pre-suploc",
                ]
                .contains(l),
            "unexpected uncovered |- axiom in iset.mm: {l} — is a core axiom missing \
             from the vendored iset sets?"
        );
    }
}

/// 6. `classify_axioms` smoke test on set.mm: every REALS label classifies as
/// a REALS member, and `ax-groth` is in TARSKI_GROTHENDIECK only.
#[test]
#[ignore = "requires the pinned set.mm cache; see module docs"]
fn classify_axioms_smoke() {
    let db = set_mm();
    let all = [
        &sets::PROP,
        &sets::PRED,
        &sets::ZF_KERNEL,
        &sets::ZF,
        &sets::ZFC,
        &sets::TARSKI_GROTHENDIECK,
        &sets::REALS,
    ];
    let report = classify_axioms(db, &all);
    for label in sets::REALS.labels() {
        let members = report
            .get(label)
            .unwrap_or_else(|| panic!("{label} should be a |- axiom of set.mm"));
        assert!(
            members.contains(&"REALS"),
            "{label} should classify as REALS"
        );
    }
    let groth = report
        .get("ax-groth")
        .expect("ax-groth is a |- axiom of set.mm");
    assert_eq!(groth, &["TARSKI_GROTHENDIECK"]);
    let uncovered = report.values().filter(|m| m.is_empty()).count();
    eprintln!(
        "set.mm: {} |- axioms total, {} outside every vendored set (mathboxes &c.)",
        report.len(),
        uncovered
    );
}
