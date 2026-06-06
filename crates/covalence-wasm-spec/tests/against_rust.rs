//! Differential test against the trusted Rust hash references in
//! `covalence-hash` / `blake3`.
//!
//! For every hash spec in `ALL_SPECS`, hash a fixed fixture set in the
//! WASM component (one-shot path) and compare bit-equal with
//! `common::reference_hash`. Fixtures hit padding edge cases (block
//! boundaries, counter rollover) plus the FIPS-style million-'a'
//! long-message vector — built at test runtime so it never lands in
//! the committed `vectors.json`.
//!
//! BLAKE3 keyed-hash and derive-key are exercised by `kat.rs` against
//! the committed `vectors.json`, not here: their fixture set is
//! mode-specific and lives next to the rest of the BLAKE3 KATs.

mod common;

use common::{Harness, all_specs, is_hash_spec, reference_hash};
use covalence_wasm_spec::KatMode;

fn fixtures() -> Vec<(String, Vec<u8>)> {
    let mut v: Vec<(String, Vec<u8>)> = Vec::new();
    v.push(("empty".into(), Vec::new()));
    v.push(("abc".into(), b"abc".to_vec()));
    v.push(("kib_55".into(), vec![0x55u8; 1024]));
    v.push(("million_a".into(), vec![b'a'; 1_000_000]));
    // Block-boundary / counter-rollover lengths. SHA-1/256 have
    // 512-bit blocks (55/56 is the L mod 64 transition); SHA-512 has
    // 1024-bit blocks (so 111/112 is its transition). BLAKE3's
    // chunk size is 1024 bytes — 1023/1024/1025 hit its boundary.
    for n in [
        1usize, 55, 56, 57, 63, 64, 65, 111, 112, 113, 119, 120, 127, 128, 129, 192, 256, 511, 512,
        513, 1023, 1024, 1025,
    ] {
        v.push((format!("a_x_{n}"), vec![b'a'; n]));
    }
    v
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
                got, want,
                "{}/{} input={name} mismatch (got len={} want len={})",
                spec.name,
                spec.variant,
                got.len(),
                want.len(),
            );
        }
    }
}
