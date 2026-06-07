//! Host-side binding for the `cov:pure@0.1.0` WIT package.
//!
//! See `wit/pure.wit` for the interface definitions. This module
//! generates the wasmtime bindings; the actual resource trait impls
//! and a guest-runnable example live in `covalence-wasm-store` or
//! a follow-up crate (TBD).
//!
//! For now this is a *bindgen-only* module — its purpose is to ensure
//! the WIT file is syntactically well-formed and that the resource
//! mapping compiles. Implementation comes with the WASM theorem-
//! proving test work.

use covalence_pure as cp;

/// Backing type for the `cov:pure/api.pure-type` resource.
pub struct HostPureType(pub cp::Type);

/// Backing type for the `cov:pure/api.term` resource.
pub struct HostTerm(pub cp::Term);

/// Backing type for the `cov:pure/api.term-set` resource.
///
/// Currently backed by an `Arc<BTreeSet<Term>>` snapshot, but the
/// WIT surface deliberately hides this: guests interact only via
/// `len` / `is-empty` / `contains` / `at`. A future swap to a
/// persistent set or hash-trie is invisible to guest code.
pub struct HostTermSet(pub std::sync::Arc<std::collections::BTreeSet<cp::Term>>);

impl HostTermSet {
    /// Indexed access in BTreeSet order. This is the "current"
    /// stable ordering — guests must not depend on any particular
    /// total order, only on stability for the resource's lifetime.
    pub fn at(&self, idx: u32) -> Option<cp::Term> {
        self.0.iter().nth(idx as usize).cloned()
    }
}

/// Backing type for the `cov:pure/api.thm` resource.
pub struct HostThm(pub cp::Thm);

// Bindgen-generate the host trait surface. We aren't implementing
// it here yet — that lands with the WASM-test crate that needs to
// drive a guest end-to-end. The bindgen call validates the WIT.
wasmtime::component::bindgen!({
    path: "wit/pure.wit",
    world: "pure-guest",
    with: {
        "cov:pure/api.pure-type": HostPureType,
        "cov:pure/api.term": HostTerm,
        "cov:pure/api.term-set": HostTermSet,
        "cov:pure/api.thm": HostThm,
    },
    imports: { default: trappable },
});
