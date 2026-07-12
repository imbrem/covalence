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
//! — see `notes/vibes/web-kernel.md` and `crates/kernel/core/src/service.rs`.

use covalence_kernel::KernelService;
use wasm_bindgen::prelude::*;

/// Install a panic hook that routes Rust panics to `console.error` (dev aid).
/// Runs automatically when the module is instantiated.
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

/// Check a `.cov` article and return the [`CheckReport`](covalence_kernel::CheckReport) as a JSON string.
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

/// Parse a snippet of the **Haskell dialect** and lower it to the canonical
/// S-expression interchange text — the live front end for the `/haskell` demo
/// page. Tries a whole module (top-level `f x = …` defs) first, then falls back
/// to a single expression.
///
/// JS side: `JSON.parse(haskell_to_sexpr(src))` →
/// `{ ok: true, sexpr: string }` or `{ ok: false, error: string }`.
///
/// Kernel-agnostic: this drives only `covalence-haskell`'s parser + lowering
/// (no proof-checking, no TCB), so it is cheap enough to run on the main thread.
#[wasm_bindgen]
pub fn haskell_to_sexpr(src: &str) -> String {
    match covalence_haskell::parse::parse_module(src) {
        Ok(m) => haskell_json_ok(&covalence_haskell::lower::module_to_text(&m)),
        Err(mod_err) => match covalence_haskell::parse::parse_expr(src) {
            Ok(e) => haskell_json_ok(&covalence_haskell::lower::expr_to_sexpr(&e).to_text()),
            // Report the module-parse error: input failing both parses is
            // usually intended as a module and its error is more informative.
            Err(_) => haskell_json_err(&format!("{mod_err}")),
        },
    }
}

fn haskell_json_str(s: &str) -> String {
    serde_json::to_string(s).unwrap_or_else(|_| "\"\"".to_string())
}
fn haskell_json_ok(sexpr: &str) -> String {
    format!(r#"{{"ok":true,"sexpr":{}}}"#, haskell_json_str(sexpr))
}
fn haskell_json_err(msg: &str) -> String {
    format!(r#"{{"ok":false,"error":{}}}"#, haskell_json_str(msg))
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

    #[test]
    fn haskell_to_sexpr_lowers_a_module() {
        // A top-level def lowers to the S-expression interchange.
        let json = haskell_to_sexpr("compose f g x = f (g x)");
        assert!(json.contains("\"ok\":true"), "json: {json}");
        assert!(json.contains("compose"), "json: {json}");
        assert!(json.contains("lambda"), "json: {json}");
    }

    #[test]
    fn haskell_to_sexpr_lowers_a_bare_expression() {
        let json = haskell_to_sexpr("\\x -> x");
        assert!(json.contains("\"ok\":true"), "json: {json}");
        assert!(json.contains("lambda"), "json: {json}");
    }

    #[test]
    fn haskell_to_sexpr_reports_a_parse_error() {
        let json = haskell_to_sexpr("\\x ->");
        assert!(json.contains("\"ok\":false"), "json: {json}");
        assert!(json.contains("\"error\""), "json: {json}");
    }
}
