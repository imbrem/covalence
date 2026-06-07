//! Shared helpers for integration tests.
//!
//! Loads every spec in `ALL_SPECS`, exposes a [`Harness`] that
//! instantiates the component on demand, and provides `hash` /
//! `compress` / streaming wrappers.
//!
//! All hash specs (resource AND stateful) place their exports inside
//! the `covalence:hash/api@0.1.0` exported interface; the harness
//! drills into that instance to look up functions.

#![allow(dead_code)] // each test file only uses a subset.

use covalence_wasm::engine::wasmtime::{
    Engine, Store,
    component::{Component, ComponentExportIndex, Func, Linker, Val},
};
use covalence_wasm_spec::{ALL_SPECS, KatMode, Spec};

/// Hash-spec interface name (resource + stateful both expose this).
const HASH_API: &str = "covalence:hash/api@0.1.0";
/// Sign-spec interface name (Ed25519 verify lives here).
const SIGN_API: &str = "covalence:sign/api@0.1.0";

/// BLAKE3's canonical context string for the published test vectors
/// (see `BLAKE3-team/BLAKE3/test_vectors/test_vectors.json`). Used by
/// the harness when a `derive-key` KAT does not embed a `context`
/// field.
pub const BLAKE3_TEST_VECTOR_CONTEXT: &str = "BLAKE3 2019-12-27 16:29:52 test vectors context";

pub fn engine() -> Engine {
    let mut config = covalence_wasm::engine::wasmtime::Config::new();
    config.wasm_component_model(true);
    Engine::new(&config).expect("engine")
}

/// One running instance of a spec, plus its store. Recreate per test
/// to avoid leaking handle pool slots between cases (and to validate
/// the object-model semantics of stateful specs).
pub struct Harness {
    pub spec: &'static Spec<'static>,
    pub store: Store<()>,
    pub instance: covalence_wasm::engine::wasmtime::component::Instance,
    api_index: ComponentExportIndex,
    /// Which interface name we drilled into. Used by error messages.
    api_name: &'static str,
}

impl Harness {
    pub fn new(spec: &'static Spec<'static>) -> Self {
        let engine = engine();
        let component = Component::from_binary(&engine, spec.wasm).expect("component");
        let mut linker = Linker::<()>::new(&engine);
        // Resource specs import canonical-ABI intrinsics for the
        // exported `hasher` resource (drop, new, rep); stub them all
        // out — wit-component provides no-op host shims.
        linker
            .define_unknown_imports_as_traps(&component)
            .expect("stub imports");
        let mut store = Store::new(&engine, ());
        let instance = linker
            .instantiate(&mut store, &component)
            .expect("instantiate");
        // Pick the right exported interface: sign specs live behind
        // `covalence:sign/api@0.1.0`, everything else (hash specs) is
        // `covalence:hash/api@0.1.0`.
        let api_name = match spec.kind {
            covalence_wasm_spec::SpecKind::Sign(_) => SIGN_API,
            covalence_wasm_spec::SpecKind::Hash(_) => HASH_API,
        };
        let api_index = instance
            .get_export_index(&mut store, None, api_name)
            .unwrap_or_else(|| panic!("missing api instance export {api_name}"));
        Self {
            spec,
            store,
            instance,
            api_index,
            api_name,
        }
    }

    fn api_func(&mut self, name: &str) -> Func {
        let api = self.api_name;
        let idx = self
            .instance
            .get_export_index(&mut self.store, Some(&self.api_index), name)
            .unwrap_or_else(|| panic!("missing export {api}#{name}"));
        self.instance
            .get_func(&mut self.store, &idx)
            .unwrap_or_else(|| panic!("export {api}#{name} is not a function"))
    }

    /// Call the one-shot `hash` export.
    pub fn hash(&mut self, input: &[u8]) -> Vec<u8> {
        let func = self.api_func("hash");
        let args = [val_list_u8(input)];
        let mut results = [Val::Bool(false)];
        func.call(&mut self.store, &args, &mut results)
            .expect("hash call");
        list_u8_to_vec(&results[0])
    }

    /// Call the `compress` block primitive.
    pub fn compress(&mut self, state: &[u8], block: &[u8]) -> Vec<u8> {
        let func = self.api_func("compress");
        let args = [val_list_u8(state), val_list_u8(block)];
        let mut results = [Val::Bool(false)];
        func.call(&mut self.store, &args, &mut results)
            .expect("compress call");
        list_u8_to_vec(&results[0])
    }

    /// Call the one-shot `keyed-hash(key, data)` export. Used by BLAKE3.
    pub fn keyed_hash(&mut self, key: &[u8], data: &[u8]) -> Vec<u8> {
        let func = self.api_func("keyed-hash");
        let args = [val_list_u8(key), val_list_u8(data)];
        let mut results = [Val::Bool(false)];
        func.call(&mut self.store, &args, &mut results)
            .expect("keyed-hash call");
        list_u8_to_vec(&results[0])
    }

    /// Call the one-shot `derive-key(context, key-material)` export.
    /// Used by BLAKE3. `context` is a UTF-8 string.
    pub fn derive_key(&mut self, context: &str, key_material: &[u8]) -> Vec<u8> {
        let func = self.api_func("derive-key");
        let args = [Val::String(context.to_string()), val_list_u8(key_material)];
        let mut results = [Val::Bool(false)];
        func.call(&mut self.store, &args, &mut results)
            .expect("derive-key call");
        list_u8_to_vec(&results[0])
    }

    /// Call the `verify(public-key, message, signature)` export on a
    /// sign spec. Returns the boolean the component reported.
    pub fn verify(&mut self, public_key: &[u8], message: &[u8], signature: &[u8]) -> bool {
        let func = self.api_func("verify");
        let args = [
            val_list_u8(public_key),
            val_list_u8(message),
            val_list_u8(signature),
        ];
        let mut results = [Val::Bool(false)];
        func.call(&mut self.store, &args, &mut results)
            .expect("verify call");
        match results[0] {
            Val::Bool(b) => b,
            ref other => panic!("expected bool, got {other:?}"),
        }
    }

    /// For stateful specs only: call `init`, `update(chunk)`*, `finalize()`.
    /// Panics for resource specs (which have no `init` export).
    pub fn stateful_stream(&mut self, chunks: &[&[u8]]) -> Vec<u8> {
        let init = self.api_func("init");
        init.call(&mut self.store, &[], &mut []).expect("init call");

        let update = self.api_func("update");
        for c in chunks {
            update
                .call(&mut self.store, &[val_list_u8(c)], &mut [])
                .expect("update call");
        }

        let finalize = self.api_func("finalize");
        let mut results = [Val::Bool(false)];
        finalize
            .call(&mut self.store, &[], &mut results)
            .expect("finalize call");
        list_u8_to_vec(&results[0])
    }

    /// For resource specs: explicit construct → update* → finalize, so we
    /// can vary the streaming cuts. Returns the digest.
    pub fn resource_stream(&mut self, chunks: &[&[u8]]) -> Vec<u8> {
        let ctor = self.api_func("[constructor]hasher");
        let mut results = [Val::Bool(false)];
        ctor.call(&mut self.store, &[], &mut results)
            .expect("constructor call");
        let resource = results[0].clone();

        let update = self.api_func("[method]hasher.update");
        for c in chunks {
            update
                .call(
                    &mut self.store,
                    &[resource.clone(), val_list_u8(c)],
                    &mut [],
                )
                .expect("update call");
        }

        let finalize = self.api_func("[method]hasher.finalize");
        let mut f_res = [Val::Bool(false)];
        finalize
            .call(&mut self.store, &[resource], &mut f_res)
            .expect("finalize call");
        list_u8_to_vec(&f_res[0])
    }
}

fn val_list_u8(bytes: &[u8]) -> Val {
    Val::List(bytes.iter().copied().map(Val::U8).collect())
}

fn list_u8_to_vec(v: &Val) -> Vec<u8> {
    match v {
        Val::List(items) => items
            .iter()
            .map(|it| match it {
                Val::U8(b) => *b,
                other => panic!("expected u8, got {other:?}"),
            })
            .collect(),
        other => panic!("expected list, got {other:?}"),
    }
}

pub fn all_specs() -> &'static [&'static Spec<'static>] {
    ALL_SPECS
}

pub fn is_stateful(spec: &Spec<'_>) -> bool {
    spec.variant.ends_with("-stateful")
}

pub fn is_sha1(spec: &Spec<'_>) -> bool {
    spec.name == "sha1"
}

pub fn is_hash_spec(spec: &Spec<'_>) -> bool {
    matches!(spec.kind, covalence_wasm_spec::SpecKind::Hash(_))
}

pub fn is_sign_spec(spec: &Spec<'_>) -> bool {
    matches!(spec.kind, covalence_wasm_spec::SpecKind::Sign(_))
}

/// Dispatch table: compute the expected digest of `data` (and `key`
/// where relevant) using the trusted Rust reference implementation in
/// `covalence-hash` / the upstream `blake3` crate. Returned digest is
/// the variable-width "true" output of the function — caller compares
/// bit-equal with the WASM output.
///
/// `Compress` is intentionally not handled here: a clean single-block
/// reference would require duplicating each algorithm's compression
/// function, which is exactly what the WASM spec is meant to define.
/// `kat.rs` covers Compress against the committed expected bytes
/// directly.
pub fn reference_hash(
    spec_name: &str,
    mode: KatMode,
    key: Option<&[u8]>,
    data: &[u8],
) -> Option<Vec<u8>> {
    match (spec_name, mode) {
        ("sha1", KatMode::OneShot | KatMode::Streaming) => {
            Some(covalence_hash::sha1(data).to_vec())
        }
        ("sha256", KatMode::OneShot | KatMode::Streaming) => {
            Some(covalence_hash::sha256(data).to_vec())
        }
        ("sha512", KatMode::OneShot | KatMode::Streaming) => {
            Some(covalence_hash::sha512(data).to_vec())
        }
        ("blake3", KatMode::OneShot | KatMode::Streaming) => {
            Some(covalence_hash::blake3::hash(data).as_bytes().to_vec())
        }
        ("blake3", KatMode::KeyedHash) => {
            let key = key.expect("keyed-hash KAT missing key");
            let key32: [u8; 32] = key.try_into().expect("keyed-hash key must be 32 bytes");
            Some(covalence_hash::blake3_keyed_hash(&key32, data).to_vec())
        }
        ("blake3", KatMode::DeriveKey) => {
            // If the KAT did not embed a context, use the BLAKE3
            // canonical test-vector context string.
            let ctx_bytes = key.unwrap_or(BLAKE3_TEST_VECTOR_CONTEXT.as_bytes());
            let ctx_str =
                std::str::from_utf8(ctx_bytes).expect("derive-key context must be valid UTF-8");
            Some(covalence_hash::blake3_derive_key(ctx_str, data).to_vec())
        }
        // Compress has no clean single-block reference (see doc above).
        (_, KatMode::Compress) => None,
        // Other (algo, mode) pairs are silently unsupported — callers
        // should skip if they get None.
        _ => None,
    }
}
