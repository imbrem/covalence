//! Browser front-end for the Covalence kernel.
//!
//! A thin `wasm-bindgen` shim over [`covalence_kernel::KernelService`] — the
//! single, target-agnostic check surface. JS stays an executor: the editor /
//! UI calls [`check`] and renders the result; all proof-checking logic is this
//! crate compiled to `wasm32-unknown-unknown`.
//!
//! Build: `bun run build:web-kernel` (cargo → `wasm-bindgen --target web`),
//! which emits the JS glue + `.wasm` into `apps/covalence-web/src/lib/kernel/`.
//!
//! Today [`check`] is **synchronous** and resolves only the built-in
//! standard-library prelude (self-contained articles). Network dependency
//! loading is the async `ArticleSource` path driven via `wasm-bindgen-futures`
//! — see `notes/web-kernel.md` and `crates/covalence-kernel/src/service.rs`.

use covalence_kernel::KernelService;
use wasm_bindgen::prelude::*;

/// Install a panic hook that routes Rust panics to `console.error` (dev aid).
/// Runs automatically when the module is instantiated.
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

/// Check a `.cov` article and return the [`CheckReport`] as a JSON string.
///
/// JS side: `JSON.parse(check(src))` →
/// `{ ok: boolean, theorems: [{ name, statement }], diagnostics: [{ severity, message, span }] }`.
///
/// Returns a JSON string for a robust, dependency-light boundary (no
/// `serde-wasm-bindgen`); the shape is stable and small.
#[wasm_bindgen]
pub fn check(src: &str) -> String {
    report_json(KernelService::new().check(src))
}

/// Check an article written against the abstract `Nat` **model** interface,
/// resolving `(#import natmodel)` to `model` (`"nat/self"` → kernel `nat`,
/// `"nat/unary"` → `list unit`). Same source, different carrier per model.
/// Returns the same JSON shape as [`check`].
#[wasm_bindgen]
pub fn check_model(src: &str, model: &str) -> String {
    report_json(KernelService::new().check_model(src, model))
}

fn report_json(report: covalence_kernel::CheckReport) -> String {
    serde_json::to_string(&report)
        .unwrap_or_else(|e| format!(r#"{{"ok":false,"theorems":[],"diagnostics":[{{"severity":"error","message":"internal: failed to serialize report: {e}","span":null}}]}}"#))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_returns_json() {
        let json =
            check("(#import core) (#open core) (#thm bad (#concl true) (#proof (refl true)))");
        // A broken proof → ok:false with at least one diagnostic.
        assert!(json.contains("\"ok\":false"), "json: {json}");
        assert!(json.contains("\"diagnostics\""), "json: {json}");
    }
}
