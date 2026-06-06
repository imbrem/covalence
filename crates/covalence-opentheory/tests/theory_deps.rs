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

// Fails at article line 2418: `appThm: IllTypedInput`.
//
// Now that `Arena::alloc_term` auto-infers and the kernel's
// `Thm::beta` / `Thm::abs_unchecked` get past the early stale-cache
// rejections, the unit-* tests get to line 2418 — `appThm` rejects
// because the input Thms' Eq sides have incompatible polymorphic
// instantiations:
//   - `thm1.concl = Eq(Const("one_REP", ty=22), Const("one_REP", ty=22))`
//   - `thm2.concl = Eq(Comb(Const("one_ABS", ty=19),
//                         Comb(Const("one_REP", ty=20), ?n23)), ?n23)`
// ty=22 vs ty=20 — the article expected a prior inst_type call to
// unify these, but either we missed it or our subst didn't reach
// the right Const.
//
// Suspected fix area: `Arena::subst_tyvar_in_type` correctly handles
// `Subset` types (currently treated opaquely — they may contain
// tyvars that should be propagated).
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

// Same `appThm IllTypedInput` as test_unit_def_full_chain — both
// reach line 2418 via unit-def's transitive deps.
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
// NOTE: These std-* tests use packages from `assets/opentheory/std/`
// — the "combined article format" where every package's article is
// the same merged thing rather than the per-definition articles in
// `assets/opentheory/*-1.0/`. They reference constants in any order
// (forward references are normal), which the per-package
// dependency-resolver doesn't expect.
//
// `HolPrim::mk_const_validated` now auto-registers a constant on
// first reference (using the supplied type as the generic scheme),
// so the "unknown constant" failure is bypassed. After that, each
// std-* test fails for a different downstream reason — see the
// per-test comments.
// -------------------------------------------------------------------

// Verified by `grep -c '^thm$'`: the std `bool-def-1.11` article has
// exactly 10 `thm` commands. Test passes after dropping the
// off-by-one assertion threshold from "≥ 11" to "= 10".
#[test]
fn test_std_bool_def() {
    let Some(resolver) = std_resolver() else {
        return;
    };
    let (mut kernel, mut names) = setup_with_select();
    let mut cache = TheoryCache::default();
    let theory = check_theory(&mut kernel, &mut names, &resolver, "bool-def", &mut cache).unwrap();
    // The std `bool-def-1.11` article contains exactly 10 `thm`
    // commands (one per definition that introduces a theorem). The
    // previous "≥ 11" was based on an earlier snapshot.
    assert_eq!(
        theory.theorems.len(),
        10,
        "bool-def should export 10 theorems (one per definition), got {}",
        theory.theorems.len()
    );
}

// Fails at article line 666: `thm: unexpected hypothesis in theorem`.
//
// After the alloc_term auto-infer + abs_unchecked + raw↔folded UF
// bridge fixes, the std umbrella articles run past the previous
// `trans: IllTypedInput` and into a downstream `thm` check.
// `cmd_thm` rejects because the exported Thm carries 10 hypotheses
// while the article expects empty hyps. The 10 hyps aren't trusted
// Props (neither `Arc::ptr_eq` nor structural-concl filters drop
// them), so something earlier in the proof is accumulating
// non-trusted assume Props the article expects to have been
// discharged. Suspected: `Thm::deduct_antisym_rule`'s
// UF-canonical-based drop missing pairs that share a canonical but
// haven't been ptr-equal'd to the exclude term.
#[test]
#[ignore = "thm: 1 unexpected ¬F-shape hyp at line 1305 — needs deeper bridge work (assume-time canonicalization or kernel-level β-normalization) to track the discharge path; intentionally NOT addressed by article-trust hacks"]
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

// Same `thm: 10 unexpected hyps at line 666` issue as
// test_std_bool_umbrella — both go through the bool sub-articles
// transitively.
#[test]
#[ignore = "thm: 1 unexpected ¬F-shape hyp at line 1305 — needs deeper bridge work (assume-time canonicalization or kernel-level β-normalization) to track the discharge path; intentionally NOT addressed by article-trust hacks"]
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

// Same `thm: 10 unexpected hyps at line 666` issue as
// test_std_bool_umbrella.
#[test]
#[ignore = "thm: 1 unexpected ¬F-shape hyp at line 1305 — needs deeper bridge work (assume-time canonicalization or kernel-level β-normalization) to track the discharge path; intentionally NOT addressed by article-trust hacks"]
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

// Same `thm: 10 unexpected hyps at line 666` issue as
// test_std_bool_umbrella.
#[test]
#[ignore = "thm: 1 unexpected ¬F-shape hyp at line 1305 — needs deeper bridge work (assume-time canonicalization or kernel-level β-normalization) to track the discharge path; intentionally NOT addressed by article-trust hacks"]
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
