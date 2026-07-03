//! Differential smoke test against the trusted Rust hash references in
//! `covalence-hash` / `blake3`.
//!
//! For every hash spec in `ALL_SPECS`, hash a small fixed fixture set
//! in the WASM component (one-shot path) and compare bit-equal with
//! `common::reference_hash`. Fixtures hit one input per
//! distinct-block-size boundary the four hash algorithms care about,
//! plus the two RFC starter vectors. Kept tight so `cargo test` stays
//! fast — see `fuzz/fuzz_targets/sha1_*_differential.rs` (and follow-up
//! targets per algo) for the comprehensive boundary sweep + long-input
//! coverage.
//!
//! BLAKE3 keyed-hash and derive-key are exercised by `kat.rs` against
//! the committed `vectors.json`.

mod common;

use common::{Harness, all_specs, is_hash_spec, reference_hash};
use covalence_wasm_spec::KatMode;

fn fixtures() -> Vec<(&'static str, Vec<u8>)> {
    vec![
        ("empty", Vec::new()),
        ("abc", b"abc".to_vec()),
        // SHA-1 / SHA-256 block (64 B) boundary.
        ("a_x_64", vec![b'a'; 64]),
        // SHA-512 block (128 B) boundary.
        ("a_x_128", vec![b'a'; 128]),
        // BLAKE3 chunk (1024 B) boundary — also a full SHA-1/256/512 multi-block input.
        ("a_x_1024", vec![b'a'; 1024]),
    ]
}

#[test]
fn against_reference() {
    let fixtures = fixtures();
    let specs = all_specs();
    assert!(!specs.is_empty(), "no specs registered");
    for spec in specs {
        if !is_hash_spec(spec) {
            continue;
        }
        for (name, data) in &fixtures {
            let Some(want) = reference_hash(spec.name, KatMode::OneShot, None, data) else {
                // Algorithm/mode not yet covered by the reference
                // dispatch — skip with a heads-up rather than panic so
                // adding a new spec doesn't immediately break the suite.
                eprintln!(
                    "skipping {}/{} input={name}: no reference dispatch",
                    spec.name, spec.variant
                );
                continue;
            };
            let mut h = Harness::new(spec);
            let got = h.hash(data);
            assert_eq!(
                got,
                want,
                "{}/{} input={name} mismatch (got len={} want len={})",
                spec.name,
                spec.variant,
                got.len(),
                want.len(),
            );
        }
    }
}
