#![no_main]

//! Differential fuzz: hash random inputs through the SHA-1 *resource*
//! component and compare with `covalence_hash::sha1`. Inputs are
//! `Arbitrary`-biased to padding-edge lengths (FIPS §5.1.1) — the
//! sizes around a 64-byte block boundary that historically break
//! hand-written SHA-1 padding logic.

use libfuzzer_sys::fuzz_target;
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

use covalence_wasm::engine::wasmtime::{
    Engine, Store,
    component::{Component, ComponentExportIndex, Linker, Val},
};
use covalence_wasm_spec::ALL_SPECS;

/// Lengths to hit padding edges: 0, single-byte, just under/over a 64-byte
/// block, double-block boundary, all the way out to a few blocks.
const EDGE_LENGTHS: &[usize] = &[
    0, 1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 192, 256,
];

#[derive(Debug)]
struct Input {
    bytes: Vec<u8>,
}

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        // 75% of the time pick an edge length; 25% pick a free length.
        let pick: u8 = u.arbitrary()?;
        let len = if pick < 192 {
            EDGE_LENGTHS[(pick as usize) % EDGE_LENGTHS.len()]
        } else {
            (u.arbitrary::<u16>()? as usize) % 4096
        };
        let mut bytes = Vec::with_capacity(len);
        for _ in 0..len {
            bytes.push(u.arbitrary()?);
        }
        Ok(Self { bytes })
    }
}

fn run_resource(input: &[u8]) -> Vec<u8> {
    let spec = ALL_SPECS
        .iter()
        .find(|s| s.name == "sha1" && s.variant == "handwritten")
        .expect("sha1/handwritten in ALL_SPECS");
    let engine = {
        let mut c = covalence_wasm::engine::wasmtime::Config::new();
        c.wasm_component_model(true);
        Engine::new(&c).unwrap()
    };
    let component = Component::from_binary(&engine, spec.wasm).unwrap();
    let mut linker = Linker::<()>::new(&engine);
    linker.define_unknown_imports_as_traps(&component).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = linker.instantiate(&mut store, &component).unwrap();
    let api: ComponentExportIndex = instance
        .get_export_index(&mut store, None, "covalence:hash/api@0.1.0")
        .unwrap();
    let hash_idx = instance
        .get_export_index(&mut store, Some(&api), "hash")
        .unwrap();
    let hash = instance.get_func(&mut store, &hash_idx).unwrap();
    let args = [Val::List(input.iter().copied().map(Val::U8).collect())];
    let mut results = [Val::Bool(false)];
    hash.call(&mut store, &args, &mut results).unwrap();
    match &results[0] {
        Val::List(items) => items
            .iter()
            .map(|v| match v {
                Val::U8(b) => *b,
                _ => unreachable!(),
            })
            .collect(),
        _ => unreachable!(),
    }
}

fuzz_target!(|input: Input| {
    let got = run_resource(&input.bytes);
    let want = covalence_hash::sha1(&input.bytes).to_vec();
    assert_eq!(got, want, "mismatch for input len {}", input.bytes.len());
});
