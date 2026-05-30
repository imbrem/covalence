//! Integration tests for theory dependency resolution.
//!
//! These tests process real OpenTheory standard library packages from the
//! `assets/opentheory/` directory, validating the full dependency chain.

use covalence_hol::light::HolKernel;
use covalence_hol::types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID};
use covalence_opentheory::{FileResolver, NameTable, TheoryCache, check_theory, register_select};

fn assets_dir() -> std::path::PathBuf {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest.join("../../assets/opentheory")
}

fn setup() -> (HolKernel, NameTable) {
    let names = NameTable::new();
    let kernel = HolKernel::new(FUN_TYCON_ID, BOOL_TYCON_ID, EQ_CONST_ID);
    (kernel, names)
}

fn setup_with_select() -> (HolKernel, NameTable) {
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
