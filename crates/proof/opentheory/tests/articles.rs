//! End-to-end article verification through the native kernel backend.
//!
//! Runs the hand-written test articles (and small vendored `gilith` packages)
//! from `assets/opentheory/` through `ArticleInterp<NativeOt>`.

#![cfg(feature = "native")]

use std::path::PathBuf;

use covalence_opentheory::{ArticleInterp, NameTable, NativeOt};

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
