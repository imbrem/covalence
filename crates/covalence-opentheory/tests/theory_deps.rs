//! Integration tests for theory dependency resolution.
//!
//! These tests process real OpenTheory standard library packages from the
//! `assets/opentheory/` directory, validating the full dependency chain.

use covalence_hol::types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID};
use covalence_opentheory::{FileResolver, NameTable, TheoryCache, check_theory, register_select};
use covalence_shell::HolPrim;

fn assets_dir() -> std::path::PathBuf {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest.join("../../assets/opentheory")
}

fn setup() -> (HolPrim, NameTable) {
    let names = NameTable::new();
    let kernel = HolPrim::new(FUN_TYCON_ID, BOOL_TYCON_ID, EQ_CONST_ID);
    (kernel, names)
}

fn setup_with_select() -> (HolPrim, NameTable) {
    let (mut kernel, mut names) = setup();
    register_select(&mut kernel, &mut names);
    (kernel, names)
}

// -------------------------------------------------------------------
// Single package (no deps)
// -------------------------------------------------------------------

#[test]
fn test_bool_def_true_standalone() {
    let (mut kernel, mut names) = setup();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(
        &mut kernel,
        &mut names,
        &resolver,
        "bool-def-true",
        &mut cache,
    )
    .unwrap();
    assert_eq!(
        theory.theorems.len(),
        1,
        "bool-def-true should export 1 theorem"
    );
    assert!(
        theory.assumptions.is_empty(),
        "bool-def-true has no assumptions"
    );
}

#[test]
fn test_bool_def_let_standalone() {
    let (mut kernel, mut names) = setup();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(
        &mut kernel,
        &mut names,
        &resolver,
        "bool-def-let",
        &mut cache,
    )
    .unwrap();
    assert_eq!(
        theory.theorems.len(),
        1,
        "bool-def-let should export 1 theorem"
    );
    assert!(
        theory.assumptions.is_empty(),
        "bool-def-let has no assumptions"
    );
}

// -------------------------------------------------------------------
// Two-package chain: bool-def-true → bool-def-and
// -------------------------------------------------------------------

#[test]
fn test_bool_def_and_with_dep() {
    let (mut kernel, mut names) = setup();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(
        &mut kernel,
        &mut names,
        &resolver,
        "bool-def-and",
        &mut cache,
    )
    .unwrap();
    assert_eq!(
        theory.theorems.len(),
        1,
        "bool-def-and should export 1 theorem"
    );
    assert!(
        theory.assumptions.is_empty(),
        "bool-def-and has no assumptions"
    );
}

// -------------------------------------------------------------------
// Three-package chain: bool-def-true → bool-def-and → bool-def-imp
// -------------------------------------------------------------------

#[test]
fn test_bool_def_imp_chain() {
    let (mut kernel, mut names) = setup();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(
        &mut kernel,
        &mut names,
        &resolver,
        "bool-def-imp",
        &mut cache,
    )
    .unwrap();
    assert_eq!(
        theory.theorems.len(),
        1,
        "bool-def-imp should export 1 theorem"
    );
    assert!(
        theory.assumptions.is_empty(),
        "bool-def-imp has no assumptions"
    );
}

// -------------------------------------------------------------------
// Diamond dependency: bool-def-exists needs both bool-def-imp and bool-def-forall,
// both of which depend on bool-def-true (directly or transitively).
// -------------------------------------------------------------------

#[test]
fn test_bool_def_exists_diamond() {
    let (mut kernel, mut names) = setup();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(
        &mut kernel,
        &mut names,
        &resolver,
        "bool-def-exists",
        &mut cache,
    )
    .unwrap();
    assert_eq!(
        theory.theorems.len(),
        1,
        "bool-def-exists should export 1 theorem"
    );
    assert!(
        theory.assumptions.is_empty(),
        "bool-def-exists has no assumptions"
    );
}

// -------------------------------------------------------------------
// Full boolean definitions chain: all 11 packages with shared cache
// -------------------------------------------------------------------

#[test]
fn test_all_bool_defs() {
    let (mut kernel, mut names) = setup_with_select();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();

    // Process all bool-def packages with a shared cache.
    let packages = [
        "bool-def-true",
        "bool-def-and",
        "bool-def-forall",
        "bool-def-imp",
        "bool-def-exists",
        "bool-def-false",
        "bool-def-not",
        "bool-def-or",
        "bool-def-exists-unique",
        "bool-def-cond",
        "bool-def-let",
    ];
    for &pkg in &packages {
        let theory = check_theory(&mut kernel, &mut names, &resolver, pkg, &mut cache).unwrap();
        assert_eq!(theory.theorems.len(), 1, "{pkg} should export 1 theorem");
        assert!(
            theory.assumptions.is_empty(),
            "{pkg} should have no unsatisfied assumptions"
        );
    }
}

// -------------------------------------------------------------------
// Axiom packages
// -------------------------------------------------------------------

#[test]
fn test_axiom_choice() {
    let (mut kernel, mut names) = setup_with_select();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(
        &mut kernel,
        &mut names,
        &resolver,
        "axiom-choice",
        &mut cache,
    )
    .unwrap();
    assert_eq!(
        theory.theorems.len(),
        1,
        "axiom-choice should export 1 theorem"
    );
    // axiom-choice introduces 1 axiom about select.
    assert_eq!(
        theory.assumptions.len(),
        1,
        "axiom-choice has 1 axiom assumption"
    );
}

#[test]
fn test_axiom_extensionality() {
    let (mut kernel, mut names) = setup();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(
        &mut kernel,
        &mut names,
        &resolver,
        "axiom-extensionality",
        &mut cache,
    )
    .unwrap();
    assert_eq!(
        theory.theorems.len(),
        1,
        "axiom-extensionality should export 1 theorem"
    );
    // axiom-extensionality introduces 1 axiom about function extensionality.
    assert_eq!(
        theory.assumptions.len(),
        1,
        "axiom-extensionality has 1 axiom assumption"
    );
}

// -------------------------------------------------------------------
// The big one: unit-def with 7+ transitive dependencies
// -------------------------------------------------------------------

#[test]
#[ignore = "betaConv IllTypedInput — substituted Lam body has stale type info"]
fn test_unit_def_full_chain() {
    let (mut kernel, mut names) = setup_with_select();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(&mut kernel, &mut names, &resolver, "unit-def", &mut cache).unwrap();
    assert_eq!(theory.theorems.len(), 1, "unit-def should export 1 theorem");
    // unit-def has axioms about select and other primitives that aren't satisfied
    // by the bool-def packages (they provide definitions, not the axioms).
    println!(
        "unit-def: {} theorems, {} unsatisfied assumptions",
        theory.theorems.len(),
        theory.assumptions.len()
    );
}

// -------------------------------------------------------------------
// The biggest: unit-thm, depends on unit-def + many bool packages
// -------------------------------------------------------------------

#[test]
#[ignore = "betaConv IllTypedInput — substituted Lam body has stale type info"]
fn test_unit_thm_full_chain() {
    let (mut kernel, mut names) = setup_with_select();
    let resolver = FileResolver::new(assets_dir());
    let mut cache = TheoryCache::default();
    let theory = check_theory(&mut kernel, &mut names, &resolver, "unit-thm", &mut cache).unwrap();
    assert_eq!(
        theory.theorems.len(),
        4,
        "unit-thm should export 4 theorems"
    );
    println!(
        "unit-thm: {} theorems, {} unsatisfied assumptions",
        theory.theorems.len(),
        theory.assumptions.len()
    );
}

// ===================================================================
// Standard library tests (from assets/opentheory/std/)
//
// These test against the real OpenTheory standard library packages.
// They skip (not fail) if the std directory is not populated.
// ===================================================================

fn std_dir() -> std::path::PathBuf {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest.join("../../assets/opentheory/std")
}

fn std_resolver() -> Option<FileResolver> {
    let dir = std_dir();
    if !dir.exists() || std::fs::read_dir(&dir).ok()?.next().is_none() {
        eprintln!("skip: std packages not downloaded (run with --ignored to fetch)");
        return None;
    }
    Some(FileResolver::new(dir))
}

// -------------------------------------------------------------------
// Umbrella: bool (bool-def + bool-int + axioms + bool-ext + bool-class)
//
// NOTE: These tests are #[ignore] because the std packages use a
// combined article format that references constants not yet supported
// by the checker. Run with `--ignored` once the checker is extended.
// -------------------------------------------------------------------

#[test]
#[ignore]
fn test_std_bool_def() {
    let Some(resolver) = std_resolver() else {
        return;
    };
    let (mut kernel, mut names) = setup_with_select();
    let mut cache = TheoryCache::default();
    let theory = check_theory(&mut kernel, &mut names, &resolver, "bool-def", &mut cache).unwrap();
    assert!(
        theory.theorems.len() >= 11,
        "bool-def should export at least 11 theorems (one per definition), got {}",
        theory.theorems.len()
    );
}

#[test]
#[ignore]
fn test_std_bool_umbrella() {
    let Some(resolver) = std_resolver() else {
        return;
    };
    let (mut kernel, mut names) = setup_with_select();
    let mut cache = TheoryCache::default();
    let theory = check_theory(&mut kernel, &mut names, &resolver, "bool", &mut cache).unwrap();
    assert!(
        !theory.theorems.is_empty(),
        "bool umbrella should export theorems"
    );
    println!(
        "std bool: {} theorems, {} assumptions",
        theory.theorems.len(),
        theory.assumptions.len()
    );
}

// -------------------------------------------------------------------
// Umbrella: unit
// -------------------------------------------------------------------

#[test]
#[ignore]
fn test_std_unit() {
    let Some(resolver) = std_resolver() else {
        return;
    };
    let (mut kernel, mut names) = setup_with_select();
    let mut cache = TheoryCache::default();
    let theory = check_theory(&mut kernel, &mut names, &resolver, "unit", &mut cache).unwrap();
    assert!(
        !theory.theorems.is_empty(),
        "unit umbrella should export theorems"
    );
    println!(
        "std unit: {} theorems, {} assumptions",
        theory.theorems.len(),
        theory.assumptions.len()
    );
}

// -------------------------------------------------------------------
// Umbrella: pair
// -------------------------------------------------------------------

#[test]
#[ignore]
fn test_std_pair() {
    let Some(resolver) = std_resolver() else {
        return;
    };
    let (mut kernel, mut names) = setup_with_select();
    let mut cache = TheoryCache::default();
    let theory = check_theory(&mut kernel, &mut names, &resolver, "pair", &mut cache).unwrap();
    assert!(
        !theory.theorems.is_empty(),
        "pair umbrella should export theorems"
    );
    println!(
        "std pair: {} theorems, {} assumptions",
        theory.theorems.len(),
        theory.assumptions.len()
    );
}

// -------------------------------------------------------------------
// Umbrella: natural
// -------------------------------------------------------------------

#[test]
#[ignore]
fn test_std_natural() {
    let Some(resolver) = std_resolver() else {
        return;
    };
    let (mut kernel, mut names) = setup_with_select();
    let mut cache = TheoryCache::default();
    let theory = check_theory(&mut kernel, &mut names, &resolver, "natural", &mut cache).unwrap();
    assert!(
        !theory.theorems.is_empty(),
        "natural umbrella should export theorems"
    );
    println!(
        "std natural: {} theorems, {} assumptions",
        theory.theorems.len(),
        theory.assumptions.len()
    );
}
