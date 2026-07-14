//! End-to-end article verification through the native kernel backend.
//!
//! Runs the hand-written test articles (and small vendored `gilith` packages)
//! from `assets/opentheory/` through `ArticleInterp<NativeOt>`.

#![cfg(feature = "native")]

use std::path::PathBuf;

use covalence_opentheory::FileResolver;
use covalence_opentheory::{
    ArticleInterp, NameTable, NativeOt, TheoryCache, check_theory, register_select,
};

/// Path to the vendored `gilith` package tree.
fn gilith_dirs() -> Vec<PathBuf> {
    let base = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../assets/opentheory/gilith");
    vec![base.join("std"), base]
}

/// Check a package (and its transitive deps) offline against a fresh kernel,
/// returning `(#theorems, #unsatisfied_assumptions)` for the requested package.
fn check_pkg(package: &str) -> (usize, usize) {
    let mut kernel = NativeOt::new();
    let mut names = NameTable::new();
    register_select(&mut kernel, &mut names);
    let resolver = FileResolver::with_dirs(gilith_dirs());
    let mut cache: TheoryCache<NativeOt> = TheoryCache::new();
    let theory = check_theory(&mut kernel, &mut names, &resolver, package, &mut cache)
        .unwrap_or_else(|e| panic!("check_theory({package}) failed: {e}"));
    (theory.theorems.len(), theory.assumptions.len())
}

fn asset(rel: &str) -> String {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../assets/opentheory")
        .join(rel);
    std::fs::read_to_string(&root).unwrap_or_else(|e| panic!("cannot read {}: {e}", root.display()))
}

/// Interpret one article string against a fresh kernel, returning
/// `(#theorems, #assumptions)`.
fn run(article: &str) -> (usize, usize) {
    let mut kernel = NativeOt::new();
    let mut names = NameTable::new();
    let interp = ArticleInterp::new(&mut kernel, &mut names);
    let result = interp
        .interpret(article)
        .unwrap_or_else(|e| panic!("interpret failed: {e}"));
    (result.theorems.len(), result.assumptions.len())
}

#[test]
fn refl_article() {
    // proves |- x = x — one theorem, no assumptions.
    let (thms, axioms) = run(&asset("refl.art"));
    assert_eq!(thms, 1, "refl.art exports exactly one theorem");
    assert_eq!(axioms, 0, "refl.art introduces no axioms");
}

#[test]
fn assume_article() {
    // proves {p} |- p — one theorem, no axioms (the hyp is from `assume`).
    let (thms, axioms) = run(&asset("assume.art"));
    assert_eq!(thms, 1);
    assert_eq!(axioms, 0);
}

#[test]
fn beta_article() {
    // proves |- (\x. x) x = x — one theorem, no assumptions.
    let (thms, axioms) = run(&asset("beta.art"));
    assert_eq!(thms, 1);
    assert_eq!(axioms, 0);
}

// ---------------------------------------------------------------------------
// Package-level checks against the vendored gilith std tree (offline).
// ---------------------------------------------------------------------------

#[test]
fn pkg_bool_def_true() {
    // Leaf package: defines Data.Bool.T via defineConst. No deps, no axioms.
    let (thms, _assumptions) = check_pkg("bool-def-true");
    assert!(thms > 0, "bool-def-true should export at least one theorem");
}

#[test]
fn pkg_bool_def() {
    // Leaf: defines the logical connectives (T, /\, ==>, !, ?, F, ~, ...).
    let (thms, _a) = check_pkg("bool-def");
    assert!(thms > 0, "bool-def should export theorems");
}

#[test]
fn pkg_unit_def() {
    // Exercises defineTypeOp v6 (the unit type) + the `bool` umbrella dependency
    // + polymorphic-axiom type-instance tolerance.
    let (thms, _a) = check_pkg("unit-def");
    assert!(thms > 0, "unit-def should export theorems");
}

#[test]
fn pkg_bool() {
    // The `bool` umbrella: the full boolean theory (defs + classical + ext/int).
    let (thms, _a) = check_pkg("bool");
    assert!(thms > 0, "bool should export theorems");
}

#[test]
fn pkg_function_def() {
    let (thms, _a) = check_pkg("function-def");
    assert!(thms > 0);
}

#[test]
fn pkg_pair_def() {
    // defineTypeOp for the product type.
    let (thms, _a) = check_pkg("pair-def");
    assert!(thms > 0);
}

#[test]
fn pkg_axiom_infinity() {
    // The infinity axiom over the primitive (opaque) `ind` type.
    let _ = check_pkg("axiom-infinity");
}

#[test]
fn pkg_function() {
    let (thms, _a) = check_pkg("function");
    assert!(thms > 0);
}

#[test]
fn pkg_natural_def() {
    // The natural numbers: defineTypeOp + the numeral (bit0/bit1) definitions.
    let (thms, _a) = check_pkg("natural-def");
    assert!(thms > 0);
}

// NOTE: `natural` (umbrella), `list-def` (defineConstList) et al. require
// packages not present in the vendored offline tree (e.g. `natural-order-def`).
// They are exercised by the downloading benchmark (`bun run opentheory`).
