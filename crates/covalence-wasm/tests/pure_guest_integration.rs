//! End-to-end test: real WASM guest proves theorems via `cov:pure/api`.
//!
//! Flow per test:
//!
//! 1. Build the `covalence-pure-test-guest` crate for `wasm32-unknown-unknown`
//!    once per test process (cached in a [`OnceLock`]).
//! 2. Wrap the core module into a component via `wit_component`.
//! 3. Spin up a wasmtime engine + linker; register the `cov:pure/api`
//!    imports via the bindgen-generated `add_to_linker`.
//! 4. Instantiate the component over a [`PureHost`] store.
//! 5. Call `run-prover(name)` and verify the returned rendered theorem.
//!
//! The same scaffold drops in unchanged for `cov:kernel/api`,
//! `cov:hol-light/api`, etc. — clone the guest crate, change the WIT
//! world the bindgen targets, and use the matching host bindings here.

#![cfg(feature = "runtime")]

use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;

use wasmtime::component::{Component, HasSelf, Linker};
use wasmtime::{Config, Engine, Store};

use covalence_wasm::pure::{PureGuest, PureHost};

// ============================================================================
// Build & encode the guest once per test process
// ============================================================================

/// Build `covalence-pure-test-guest` for wasm32 and encode the result
/// as a WASM component. Cached so multiple tests share one build.
fn guest_component_bytes() -> &'static [u8] {
    static CACHE: OnceLock<Vec<u8>> = OnceLock::new();
    CACHE.get_or_init(|| {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let workspace_root = manifest_dir
            .parent()
            .expect("crate dir")
            .parent()
            .expect("workspace root");

        // Use a separate target dir from the outer cargo invocation so
        // we don't fight for the build lock.
        let guest_target = workspace_root.join("target/test-guest-build");

        let status = Command::new(env!("CARGO"))
            .args([
                "build",
                "-p",
                "covalence-pure-test-guest",
                "--target",
                "wasm32-unknown-unknown",
                "--release",
                "--target-dir",
                guest_target
                    .to_str()
                    .expect("guest target dir is utf-8"),
            ])
            .current_dir(workspace_root)
            .status()
            .expect("invoke cargo for guest build");
        assert!(status.success(), "guest cargo build failed");

        let core_wasm_path = guest_target
            .join("wasm32-unknown-unknown/release/covalence_pure_test_guest.wasm");
        let core_bytes = std::fs::read(&core_wasm_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", core_wasm_path.display()));

        // wit-bindgen embeds the `component-type` custom section in
        // the core module. `wit_component::ComponentEncoder::module`
        // reads that to wrap the core into a real component.
        wit_component::ComponentEncoder::default()
            .module(&core_bytes)
            .expect("set core module")
            .encode()
            .expect("encode core module as component")
    })
}

// ============================================================================
// Engine + store + linker plumbing
// ============================================================================

fn run_guest_prover(prover_name: &str) -> Result<String, String> {
    let component_bytes = guest_component_bytes();

    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config).expect("engine");
    let component = Component::from_binary(&engine, component_bytes).expect("component");

    let mut store = Store::new(&engine, PureHost::new());
    let mut linker = Linker::<PureHost>::new(&engine);

    // Wire up all `cov:pure/api` imports on the linker. The closure
    // tells wasmtime how to recover &mut PureHost from the store data.
    covalence_wasm::pure::cov::pure::api::add_to_linker::<_, HasSelf<PureHost>>(
        &mut linker,
        |s: &mut PureHost| s,
    )
    .expect("add cov:pure/api to linker");

    let bindings = PureGuest::instantiate(&mut store, &component, &linker)
        .expect("instantiate guest");

    bindings
        .call_run_prover(&mut store, prover_name)
        .expect("call run-prover trap")
}

// ============================================================================
// Tests
// ============================================================================

#[test]
fn guest_refl_blob() {
    let s = run_guest_prover("refl-blob").expect("refl-blob");
    // Expected: `⊢ (blob[5] ≡ blob[5])` ("hello" is 5 bytes).
    assert!(s.starts_with("⊢"), "got: {s}");
    assert!(s.contains("blob[5]"), "got: {s}");
    assert!(s.contains("≡"), "got: {s}");
}

#[test]
fn guest_trans_refl_refl() {
    let s = run_guest_prover("trans-refl-refl").expect("trans-refl-refl");
    assert!(s.starts_with("⊢"), "got: {s}");
    assert!(s.contains("blob[1]"), "got: {s}");
}

#[test]
fn guest_imp_intro_p_implies_p() {
    let s = run_guest_prover("imp-intro-p-implies-p").expect("imp-intro");
    // Expected: `⊢ (p ⟹ p)`.
    assert!(s.starts_with("⊢"), "got: {s}");
    assert!(s.contains("p"), "got: {s}");
    assert!(s.contains("⟹") || s.contains("==>") || s.contains("->"), "got: {s}");
}

#[test]
fn guest_beta_identity() {
    let s = run_guest_prover("beta-identity").expect("beta");
    // Expected: `⊢ ((λx:bytes. @0) "hi" ≡ "hi")`.
    assert!(s.starts_with("⊢"), "got: {s}");
    assert!(s.contains("λ"), "got: {s}");
    assert!(s.contains("blob[2]"), "got: {s}");
}

#[test]
fn guest_all_intro_elim() {
    let s = run_guest_prover("all-intro-elim").expect("all-intro-elim");
    // After specializing x ↦ "hi": `⊢ (blob[2] ≡ blob[2])`.
    assert!(s.starts_with("⊢"), "got: {s}");
    assert!(s.contains("blob[2]"), "got: {s}");
}

#[test]
fn guest_inst_tfree() {
    let s = run_guest_prover("inst-tfree").expect("inst-tfree");
    // After ⋀x:'a. x ≡ x with 'a ↦ bytes.
    assert!(s.starts_with("⊢"), "got: {s}");
    assert!(s.contains("bytes") || s.contains("byte"), "got: {s}");
}

#[test]
fn guest_unknown_prover_returns_error() {
    let err = run_guest_prover("not-a-real-prover").expect_err("expected error");
    assert!(err.contains("unknown prover"), "got: {err}");
}
