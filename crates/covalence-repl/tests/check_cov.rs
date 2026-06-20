//! Integration tests for the `.cov` proof-checking REPL commands:
//! `check-cov` (a proof script on the stack) and `check-cov-hash` (a proof
//! script fetched from the store by hash).

use covalence_repl::Session;
use covalence_shell::Kernel;

fn fresh_session() -> Session {
    Session::new(Box::new(Kernel::new()), false, false)
}

/// A minimal core-only proof: `⊢ T`.
const TRUTH_COV: &str = "(#import core)(#open core)\
    (#thm truth (#concl true)\
      (#proof (eq-mp (reduce-prim (= true true)) (refl true))))";

#[test]
fn check_cov_direct_accepts_a_valid_proof() {
    let mut s = fresh_session();
    let out = s.eval(&format!("{TRUTH_COV:?} check-cov"));
    assert!(
        out.contains("checked 1 theorem(s): truth"),
        "unexpected output: {out}"
    );
}

#[test]
fn check_cov_direct_reports_a_bad_proof() {
    let mut s = fresh_session();
    // A conclusion the proof does not actually establish.
    let bad = "(#import core)(#open core)\
        (#thm wrong (#concl (= true false))\
          (#proof (refl true)))";
    let out = s.eval(&format!("{bad:?} check-cov"));
    assert!(out.contains("error"), "a bad proof should error: {out}");
}

#[test]
fn check_cov_resolves_the_logic_library() {
    let mut s = fresh_session();
    // `(#import logic)` must resolve through the standard-library prelude;
    // `and.comm` is one of its proved lemmas, referenced here by bare name.
    let src = "(#import core)(#open core)(#import logic)(#open logic)\
        (#thm reuse (#concl (==> (and p q) (and q p)))\
          (#proof (and.comm)))";
    let out = s.eval(&format!("{src:?} check-cov"));
    assert!(
        out.contains("checked 1 theorem(s): reuse"),
        "unexpected output: {out}"
    );
}

#[test]
fn check_cov_hash_checks_a_stored_file() {
    let mut s = fresh_session();
    // Store the `.cov` source, then check it by its hash — the indirect path.
    let out = s.eval(&format!("{TRUTH_COV:?} store check-cov-hash"));
    assert!(
        out.contains("checked 1 theorem(s): truth"),
        "unexpected output: {out}"
    );
}

#[test]
fn check_cov_hash_errors_on_missing_blob() {
    let mut s = fresh_session();
    // `hash` computes a content hash without storing, so the blob is absent.
    let out = s.eval("\"never stored\" hash check-cov-hash");
    assert!(
        out.contains("error") && out.contains("not found"),
        "a missing blob should error: {out}"
    );
}
