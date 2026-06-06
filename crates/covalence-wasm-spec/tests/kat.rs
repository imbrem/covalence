//! Known-answer-test harness.
//!
//! For each spec in `ALL_SPECS`, instantiate the component and run
//! every `Kat` listed in its `kats` slice. The KAT modes are:
//!
//! * `OneShot` / `Streaming` — feed `input` and compare the returned
//!   digest against `expected`. Both call the composed `hash` export;
//!   the streaming KAT additionally exercises chunked feeding for
//!   stateful specs (resource specs go through the composed `hash`
//!   either way — their streaming is covered by
//!   `streaming_consistency.rs`).
//! * `Compress` — call `compress(state, block)` directly.
//!
//! For stateful specs we instantiate a fresh module per KAT to ensure
//! "object model" semantics: each hash run sees a clean instance.

mod common;

use common::{BLAKE3_TEST_VECTOR_CONTEXT, Harness, all_specs, is_stateful};
use covalence_wasm_spec::KatMode;

#[test]
fn run_all_kats() {
    let specs = all_specs();
    assert!(!specs.is_empty(), "no specs registered");
    for spec in specs {
        for kat in spec.kats {
            // Stateful spec → fresh instance per KAT (validates the
            // object-model usage pattern). Resource specs could in
            // principle reuse an instance, but freshness is cheap and
            // keeps the harness uniform.
            let mut h = Harness::new(spec);
            match kat.mode {
                KatMode::OneShot => {
                    let got = h.hash(kat.input);
                    assert_eq!(
                        got, kat.expected,
                        "{}/{} kat={} one-shot mismatch",
                        spec.name, spec.variant, kat.name
                    );
                }
                KatMode::Streaming => {
                    // For stateful: chunk the input in 17-byte pieces
                    // through init/update*/finalize. For resource: the
                    // composed `hash` IS a constructor→update→finalize
                    // call, so it covers the streaming path.
                    let got = if is_stateful(spec) {
                        let chunks: Vec<&[u8]> = kat.input.chunks(17).collect();
                        h.stateful_stream(&chunks)
                    } else {
                        h.hash(kat.input)
                    };
                    assert_eq!(
                        got, kat.expected,
                        "{}/{} kat={} streaming mismatch",
                        spec.name, spec.variant, kat.name
                    );
                }
                KatMode::Compress => {
                    // input is expected to be `state || block` (20 + 64 = 84 bytes
                    // for SHA-1). Caller-provided test vectors decide this.
                    let split = match spec.name {
                        "sha1" => 20,
                        "sha256" => 32,
                        "sha512" => 64,
                        "blake3" => 32,
                        _ => continue,
                    };
                    if kat.input.len() < split + 1 {
                        panic!(
                            "compress KAT input too short for {}/{}: {} bytes",
                            spec.name,
                            spec.variant,
                            kat.input.len()
                        );
                    }
                    let (state, block) = kat.input.split_at(split);
                    let got = h.compress(state, block);
                    assert_eq!(
                        got, kat.expected,
                        "{}/{} kat={} compress mismatch",
                        spec.name, spec.variant, kat.name
                    );
                }
                KatMode::KeyedHash => {
                    let key = kat.key.expect("keyed-hash KAT must carry a key");
                    let got = h.keyed_hash(key, kat.input);
                    assert_eq!(
                        got, kat.expected,
                        "{}/{} kat={} keyed-hash mismatch",
                        spec.name, spec.variant, kat.name
                    );
                }
                KatMode::Verify => {
                    // Verify KATs reuse the Kat field layout for a sign
                    // spec: `key` carries the public key, `input` the
                    // message, `expected` the signature, and
                    // `expected_result` the expected boolean return.
                    let pk = kat.key.expect("verify KAT must carry public key in `key`");
                    let got = h.verify(pk, kat.input, kat.expected);
                    assert_eq!(
                        got, kat.expected_result,
                        "{}/{} kat={} verify mismatch (got {got}, expected {})",
                        spec.name, spec.variant, kat.name, kat.expected_result
                    );
                }
                KatMode::DeriveKey => {
                    // If the KAT did not embed a `context`, default
                    // to the BLAKE3 canonical test-vector context.
                    let ctx_bytes = kat.key.unwrap_or(BLAKE3_TEST_VECTOR_CONTEXT.as_bytes());
                    let ctx = std::str::from_utf8(ctx_bytes)
                        .expect("derive-key KAT context must be valid UTF-8");
                    let got = h.derive_key(ctx, kat.input);
                    assert_eq!(
                        got, kat.expected,
                        "{}/{} kat={} derive-key mismatch",
                        spec.name, spec.variant, kat.name
                    );
                }
            }
        }
    }
}
