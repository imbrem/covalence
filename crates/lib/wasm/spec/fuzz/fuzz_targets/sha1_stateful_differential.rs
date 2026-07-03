#![no_main]

//! Differential fuzz: hash random inputs through the SHA-1 *stateful*
//! component and compare with `covalence_hash::sha1`. Like the
//! resource target, inputs are biased to SHA-1 padding edges.

use libfuzzer_sys::fuzz_target;
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

use covalence_wasm::engine::wasmtime::{
    Engine, Store,
    component::{Component, ComponentExportIndex, Linker, Val},
};
use covalence_wasm_spec::ALL_SPECS;

const EDGE_LENGTHS: &[usize] = &[
    0, 1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 192, 256,
];

#[derive(Debug)]
struct Input {
    bytes: Vec<u8>,
}

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
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

fn run_stateful(input: &[u8]) -> Vec<u8> {
    let spec = ALL_SPECS
        .iter()
        .find(|s| s.name == "sha1" && s.variant == "handwritten-stateful")
        .expect("sha1/handwritten-stateful in ALL_SPECS");
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
    let got = run_stateful(&input.bytes);
    let want = covalence_hash::sha1(&input.bytes).to_vec();
    assert_eq!(got, want, "mismatch for input len {}", input.bytes.len());
});
