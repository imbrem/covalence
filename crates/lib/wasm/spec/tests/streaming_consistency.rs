//! Streaming-consistency test.
//!
//! For every hash spec take a 4 KiB pseudo-random input and verify
//! that the digest is invariant under any partition of the input into
//! `update` calls.
//!
//! For stateful specs we instantiate a fresh component per cut
//! pattern, validating the "instance is the object" semantics. For
//! resource specs we exercise constructor → update* → finalize
//! directly through the dynamic API.

mod common;

use common::{Harness, all_specs, is_hash_spec, is_stateful};

fn fixture() -> Vec<u8> {
    let mut v = Vec::with_capacity(4096);
    let mut x: u32 = 0xDEADBEEF;
    for _ in 0..4096 {
        x = x.wrapping_mul(1664525).wrapping_add(1013904223);
        v.push((x >> 16) as u8);
    }
    v
}

fn cut_patterns(len: usize) -> Vec<Vec<usize>> {
    vec![
        vec![len],
        vec![len / 2, len - len / 2],
        vec![1, len - 1],
        vec![63, len - 63],
        vec![64, len - 64],
        vec![65, len - 65],
        vec![17, 31, 64, 65, len - 17 - 31 - 64 - 65],
    ]
}

fn chunks<'a>(input: &'a [u8], sizes: &[usize]) -> Vec<&'a [u8]> {
    let mut out = Vec::with_capacity(sizes.len());
    let mut p = 0;
    for &s in sizes {
        let end = p + s;
        out.push(&input[p..end]);
        p = end;
    }
    assert_eq!(p, input.len());
    out
}

#[test]
fn streaming_invariant() {
    let input = fixture();
    let specs = all_specs();
    assert!(!specs.is_empty(), "no specs registered");
    for spec in specs {
        if !is_hash_spec(spec) {
            continue;
        }
        let mut baseline_harness = Harness::new(spec);
        let one_shot = baseline_harness.hash(&input);
        for sizes in cut_patterns(input.len()) {
            let ck = chunks(&input, &sizes);
            let mut h = Harness::new(spec);
            let got = if is_stateful(spec) {
                h.stateful_stream(&ck)
            } else {
                h.resource_stream(&ck)
            };
            assert_eq!(
                got, one_shot,
                "{}/{} streaming cut {:?} != one-shot",
                spec.name, spec.variant, sizes
            );
        }
    }
}
