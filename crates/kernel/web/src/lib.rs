//! Browser front-end for the Covalence kernel.
//!
//! A thin `wasm-bindgen` shim over [`covalence_kernel::KernelService`] — the
//! single, target-agnostic check surface. JS stays an executor: the editor /
//! UI calls one of these functions and renders the returned JSON; all
//! proof-checking logic is this crate compiled to `wasm32-unknown-unknown`.
//!
//! Build: `bun run build:web-kernel` (cargo → `wasm-bindgen --target web`),
//! which emits the JS glue + `.wasm` into `apps/covalence-web/src/lib/kernel/`.
//!
//! # Surface
//!
//! - [`check`] / [`check_model`] — check a `.cov` article (synchronous; resolves
//!   the built-in stdlib prelude only — network `ArticleSource` loading is the
//!   async path, see `notes/vibes/web-kernel.md`).
//! - [`haskell_to_sexpr`] — parse a Haskell-dialect snippet and lower it to the
//!   canonical S-expression interchange text (kernel-agnostic).
//! - [`haskell_to_hol_term`] — realize the same input to an untyped carved
//!   `sexpr` kernel [`Term`](covalence_haskell::hol) (the `hol` backend).
//! - [`haskell_to_typed_hol`] — lower an *annotated* dialect def/expr to a
//!   **well-typed** HOL term via the trait-backed `hol-typed` backend, returning
//!   the term and its HOL type.
//! - [`check_haskell_proofs`] — link a dialect theorem module against a separate
//!   S-expression proof file and report, per theorem, whether it is proved / a
//!   hole / an axiom / rejected — proof-checked end-to-end through the kernel.
//!
//! Every `haskell_*` function returns a JSON string of one of two shapes:
//! `{ "ok": true, … }` or `{ "ok": false, "error": string }` — a robust,
//! dependency-light boundary (no `serde-wasm-bindgen`); the JS side does
//! `JSON.parse`.

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
    use covalence_haskell::{lower, parse};
    match parse::parse_module(src) {
        Ok(m) => json_ok_field("sexpr", &lower::module_to_text(&m)),
        Err(mod_err) => match parse::parse_expr(src) {
            Ok(e) => json_ok_field("sexpr", &lower::expr_to_sexpr(&e).to_text()),
            // Report the module-parse error: input failing both parses is
            // usually intended as a module and its error is more informative.
            Err(_) => json_err(&format!("{mod_err}")),
        },
    }
}

/// Parse a Haskell-dialect snippet and lower it through the **untyped HOL
/// backend** to a genuine carved `sexpr` kernel [`Term`](covalence_haskell::hol)
/// — the same kernel data structure the `.cov` reader produces — then render it.
/// This is the dialect "connected to the kernel": the browser builds a real
/// `covalence` term, not just interchange text. (The carved representation is
/// untyped, so any dialect input works; a *typed* HOL term needs annotations —
/// see [`haskell_to_typed_hol`].)
///
/// JS side: `JSON.parse(haskell_to_hol_term(src))` →
/// `{ ok: true, term: string }` or `{ ok: false, error: string }`.
#[wasm_bindgen]
pub fn haskell_to_hol_term(src: &str) -> String {
    use covalence_haskell::hol::HolBackend;
    use covalence_haskell::realize::realize;
    use covalence_haskell::{lower, parse};

    let sexprs = match parse::parse_module(src) {
        Ok(m) => lower::module_to_sexprs(&m),
        Err(mod_err) => match parse::parse_expr(src) {
            Ok(e) => vec![lower::expr_to_sexpr(&e)],
            Err(_) => return json_err(&format!("{mod_err}")),
        },
    };
    let mut backend = HolBackend;
    let mut rendered = Vec::new();
    for sx in &sexprs {
        match realize(sx, &mut backend) {
            Ok(term) => rendered.push(format!("{term}")),
            Err(e) => return json_err(&format!("kernel realization failed: {e}")),
        }
    }
    json_ok_field("term", &rendered.join("\n"))
}

/// Lower an **annotated** Haskell-dialect def or expression through the
/// **typed HOL backend** (`covalence-hol-api`'s `Hol` + `Nat` traits, backed by
/// [`NativeHol`](covalence_hol_api::NativeHol)) to a genuine, *well-typed* kernel
/// [`Term`](covalence_hol_api::Term) — and report its HOL type.
///
/// Unlike [`haskell_to_hol_term`] (which carves an untyped term from any input),
/// the typed backend does no inference: every lambda binder and every free
/// variable must carry a type it can resolve (an annotation like
/// `\(x :: nat) -> x`, or a `name :: Ty` signature on a top-level def). Input
/// that lacks the annotations the backend needs is reported as a clean error,
/// never a panic.
///
/// Tries a whole module first (the *last* signature-carrying definition is
/// lowered — the "answer"), then a bare expression.
///
/// JS side: `JSON.parse(haskell_to_typed_hol(src))` →
/// `{ ok: true, term: string, type: string }` or `{ ok: false, error: string }`.
#[wasm_bindgen]
pub fn haskell_to_typed_hol(src: &str) -> String {
    use covalence_haskell::ast::Item;
    use covalence_haskell::parse;
    use covalence_haskell::typed::{Env, lower_decl, lower_expr};
    use covalence_hol_api::{Hol, NativeHol};

    let hol = NativeHol;

    // Lower to a typed term: prefer the last signature-carrying definition of a
    // module (a `name :: Ty` + `name … = body`); otherwise a bare expression.
    let term = match parse::parse_items(src) {
        Ok(items) => {
            let last_def = items.into_iter().rev().find_map(|it| match it {
                Item::Def(d) if d.sig.is_some() => Some(d),
                _ => None,
            });
            match last_def {
                Some(d) => lower_decl(&hol, &d).map(|(_name, t)| t),
                // A parseable module but no annotated definition: fall back to
                // trying the whole source as a single annotated expression.
                None => match parse::parse_expr(src) {
                    Ok(e) => lower_expr(&hol, &Env::new(), &e),
                    Err(_) => {
                        return json_err(
                            "no annotated definition found — the typed backend needs a \
                             signature (`name :: Ty`) on a definition, or an annotated \
                             expression like `\\(x :: nat) -> x`",
                        );
                    }
                },
            }
        }
        Err(mod_err) => match parse::parse_expr(src) {
            Ok(e) => lower_expr(&hol, &Env::new(), &e),
            Err(_) => return json_err(&format!("{mod_err}")),
        },
    };

    let term = match term {
        Ok(t) => t,
        Err(e) => return json_err(&format!("{e}")),
    };
    let ty = match hol.type_of(&term) {
        Ok(ty) => ty,
        Err(e) => return json_err(&format!("cannot type the lowered term: {e}")),
    };
    json_ok_fields(&[("term", &format!("{term}")), ("type", &format!("{ty}"))])
}

/// **Proof-check** a Haskell-dialect theorem module against a separate
/// S-expression proof file, end-to-end through the kernel.
///
/// Parses `module_src` (theorem / axiom declarations plus any definitions) and
/// `proof_src` (the [`ProofSet`](covalence_haskell::proof::ProofSet) of
/// name-keyed proofs), pre-loads the standard `Nat` Peano lemmas
/// ([`Lemmas::with_nat_accessors`](covalence_haskell::proof::Lemmas)), then for
/// each theorem lowers its statement to a HOL proposition and links it to its
/// proof via [`link_theorem`](covalence_haskell::proof::link_theorem) —
/// replaying the proof through [`NativeHol`](covalence_hol_api::NativeHol) and
/// checking the produced conclusion α-equals the statement.
///
/// The demo types every statement variable as `nat` (matching
/// `examples/nat_theorems.hs`); there is no inference.
///
/// JS side: `JSON.parse(check_haskell_proofs(module_src, proof_src))` →
/// ```json
/// { "ok": true, "results": [
///     { "name": "add_base_thm", "statement": "…",
///       "outcome": "proved" | "axiom" | "hole" | "mismatch", "detail": "…" }
/// ] }
/// ```
/// or `{ "ok": false, "error": string }` on a parse / lowering failure.
#[wasm_bindgen]
pub fn check_haskell_proofs(module_src: &str, proof_src: &str) -> String {
    use covalence_haskell::ast::Item;
    use covalence_haskell::parse::parse_items;
    use covalence_haskell::proof::{Lemmas, LinkOutcome, ProofSet, link_theorem};
    use covalence_haskell::typed::{Env, free_vars};
    use covalence_hol_api::{Hol, Nat, NativeHol};

    let hol = NativeHol;

    let items = match parse_items(module_src) {
        Ok(items) => items,
        Err(e) => return json_err(&format!("module parse error: {e}")),
    };
    let proofs = match ProofSet::parse(proof_src) {
        Ok(p) => p,
        Err(e) => return json_err(&format!("proof-file parse error: {e}")),
    };
    let lemmas = match Lemmas::with_nat_accessors(&hol) {
        Ok(l) => l,
        Err(e) => return json_err(&format!("failed to load Nat lemmas: {e}")),
    };

    let theorems: Vec<_> = items
        .into_iter()
        .filter_map(|it| match it {
            Item::Thm(t) => Some(t),
            Item::Def(_) => None,
        })
        .collect();

    // Type every statement variable as `nat` (the demo convention). The env
    // binds the union of all statements' free variables so lowering can look
    // each one up; no ambient theory operations, so every free var is ∀-closed.
    let mut env: Env<NativeHol> = Env::new();
    for t in &theorems {
        for v in free_vars(&t.statement) {
            env.bind(&v, Nat::nat_ty(&hol));
        }
    }

    let ambient_ops = std::collections::BTreeSet::new();
    let mut entries = Vec::new();
    for t in &theorems {
        // Lower the statement to a HOL proposition (∀-closing its free vars).
        let stmt = match covalence_haskell::proof::lower_theorem_statement(
            &hol,
            &env,
            &t.statement,
            &ambient_ops,
        ) {
            Ok(s) => s,
            Err(e) => {
                entries.push(result_entry(
                    &t.name,
                    "",
                    "mismatch",
                    &format!("statement does not lower: {e}"),
                ));
                continue;
            }
        };
        let statement_str = format!("{stmt}");

        let (outcome, detail) = match link_theorem(&hol, &lemmas, &proofs, &t.name, &stmt, t.axiom)
        {
            LinkOutcome::Proved(thm) => ("proved", format!("⊢ {}", hol.concl(&thm))),
            LinkOutcome::Axiom => ("axiom", "postulated (no proof expected)".to_string()),
            LinkOutcome::Hole => ("hole", "no proof supplied for this theorem".to_string()),
            LinkOutcome::Mismatch(reason) => ("mismatch", reason),
        };
        entries.push(result_entry(&t.name, &statement_str, outcome, &detail));
    }

    format!(r#"{{"ok":true,"results":[{}]}}"#, entries.join(","))
}

// ---------------------------------------------------------------------------
// Little-language REPL demos — /lisp, /forsp, /forth.
// ---------------------------------------------------------------------------

/// Evaluate one cell of **Little Schemer ch1 Lisp** and return the printed
/// value — the live front end for the `/lisp` demo page.
///
/// Creates a fresh kernel-backed [`Session`](covalence_lisp::Session) (stateless
/// per call: ch1 has no persistent `defun` dictionary), parses + evaluates the
/// source, and returns the value **read off a genuine `⊢ program = value`
/// kernel theorem** — the Lisp `Session`'s honesty invariant: nothing is printed
/// that did not come off a theorem.
///
/// JS side: `JSON.parse(lisp_eval_cell(src))` →
/// `{ ok: true, result: string }` or `{ ok: false, error: string }`.
#[wasm_bindgen]
pub fn lisp_eval_cell(src: &str) -> String {
    use covalence_lisp::session::Session;
    let mut session = match Session::new() {
        Ok(s) => s,
        Err(e) => return json_err(&format!("failed to start Lisp session: {e}")),
    };
    match session.eval_cell(src) {
        Ok(value) => json_ok_field("result", &value),
        Err(e) => json_err(&format!("{e}")),
    }
}

/// Evaluate one cell of **Forsp** (a concatenative read → compute → print
/// language) and return the top-of-stack value as an S-expression string — the
/// live front end for the `/forsp` demo page.
///
/// Runs the program on a fresh [`Forsp`](covalence_forsp::Forsp) runtime, then
/// renders the top of the resulting stack via `to_sexp`. An empty stack (a
/// program that pushes nothing) reports the empty result.
///
/// JS side: `JSON.parse(forsp_eval_cell(src))` →
/// `{ ok: true, result: string }` or `{ ok: false, error: string }`.
#[wasm_bindgen]
pub fn forsp_eval_cell(src: &str) -> String {
    use covalence_forsp::Forsp;
    let mut f = Forsp::new();
    if let Err(e) = f.run(src) {
        return json_err(&format!("{e}"));
    }
    // Render the top of the resulting stack (the "result" of the program) as a
    // Forsp S-expression string (`show` handles closures via `!<hash>`).
    match f.try_peek() {
        Ok(top) => {
            let rendered = f.show(top);
            json_ok_field("result", &rendered)
        }
        // An empty stack is a legal outcome (e.g. a program that only defines
        // words or prints); report it as an empty result rather than an error.
        Err(_) => json_ok_field("result", "()"),
    }
}

/// Placeholder for a future **Forth** REPL demo (`/forth` page). Always reports
/// `{ ok: false, error: "forth: coming soon" }` — the route + wasm seam exist so
/// the page renders, but there is no evaluator yet.
#[wasm_bindgen]
pub fn forth_eval_cell(_src: &str) -> String {
    json_err("forth: coming soon")
}

// ---------------------------------------------------------------------------
// JSON helpers — a small, dependency-light boundary shared by the `haskell_*`
// functions. Values are escaped via `serde_json` (strings only); the object
// shells are formatted by hand to keep the wasm surface tiny.
// ---------------------------------------------------------------------------

/// Escape a string as a JSON string literal (including the surrounding quotes).
fn json_str(s: &str) -> String {
    serde_json::to_string(s).unwrap_or_else(|_| "\"\"".to_string())
}

/// `{ "ok": true, "<field>": "<val>" }`.
fn json_ok_field(field: &str, val: &str) -> String {
    format!(r#"{{"ok":true,{}:{}}}"#, json_str(field), json_str(val))
}

/// `{ "ok": true, "<f0>": "<v0>", … }` — several string fields at once.
fn json_ok_fields(fields: &[(&str, &str)]) -> String {
    let body: Vec<String> = fields
        .iter()
        .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
        .collect();
    format!(r#"{{"ok":true,{}}}"#, body.join(","))
}

/// `{ "ok": false, "error": "<msg>" }`.
fn json_err(msg: &str) -> String {
    format!(r#"{{"ok":false,"error":{}}}"#, json_str(msg))
}

/// One `check_haskell_proofs` result object.
fn result_entry(name: &str, statement: &str, outcome: &str, detail: &str) -> String {
    format!(
        r#"{{"name":{},"statement":{},"outcome":{},"detail":{}}}"#,
        json_str(name),
        json_str(statement),
        json_str(outcome),
        json_str(detail),
    )
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

    #[test]
    fn haskell_to_hol_term_builds_a_kernel_term() {
        // The dialect, connected to the kernel: lowers to a real carved sexpr Term.
        let json = haskell_to_hol_term("\\x -> x");
        assert!(json.contains("\"ok\":true"), "json: {json}");
        assert!(json.contains("\"term\""), "json: {json}");
    }

    #[test]
    fn haskell_to_hol_term_reports_a_parse_error() {
        let json = haskell_to_hol_term("\\x ->");
        assert!(json.contains("\"ok\":false"), "json: {json}");
    }

    // --- typed HOL lowering ------------------------------------------------

    #[test]
    fn typed_hol_lowers_an_annotated_lambda() {
        // An annotated binder gives the typed backend the type it needs.
        let json = haskell_to_typed_hol("\\(x :: nat) -> x");
        assert!(json.contains("\"ok\":true"), "json: {json}");
        assert!(json.contains("\"term\""), "json: {json}");
        // Its HOL type is `nat -> nat`.
        assert!(json.contains("\"type\""), "json: {json}");
        assert!(json.contains("nat"), "json: {json}");
    }

    #[test]
    fn typed_hol_lowers_an_annotated_def() {
        // A `name :: Ty` signature types the parameters of the following def.
        let json = haskell_to_typed_hol("dbl :: nat -> nat\ndbl x = x + x");
        assert!(json.contains("\"ok\":true"), "json: {json}");
        assert!(json.contains("\"term\""), "json: {json}");
    }

    #[test]
    fn typed_hol_rejects_an_unannotated_binder() {
        // No annotation → a clean error, not a panic.
        let json = haskell_to_typed_hol("\\x -> x");
        assert!(json.contains("\"ok\":false"), "json: {json}");
        assert!(json.contains("\"error\""), "json: {json}");
    }

    #[test]
    fn typed_hol_reports_a_parse_error() {
        let json = haskell_to_typed_hol("\\x ->");
        assert!(json.contains("\"ok\":false"), "json: {json}");
    }

    // --- proof checking ----------------------------------------------------

    const NAT_THEOREMS: &str = include_str!("../../../lang/haskell/examples/nat_theorems.hs");
    const NAT_PROOFS: &str = include_str!("../../../lang/haskell/examples/nat_theorems.proof");

    #[test]
    fn check_haskell_proofs_reports_proved_and_hole() {
        let json = check_haskell_proofs(NAT_THEOREMS, NAT_PROOFS);
        assert!(json.contains("\"ok\":true"), "json: {json}");
        // refl_a and add_base_thm are genuinely proved; add_comm_thm is a hole.
        assert!(json.contains("\"name\":\"refl_a\""), "json: {json}");
        assert!(json.contains("\"outcome\":\"proved\""), "json: {json}");
        assert!(json.contains("\"name\":\"add_comm_thm\""), "json: {json}");
        assert!(json.contains("\"outcome\":\"hole\""), "json: {json}");
    }

    #[test]
    fn check_haskell_proofs_rejects_a_wrong_proof() {
        // A proof of ∀a.a=a supplied for add_base_thm (∀m. 0+m=m): valid
        // derivation, wrong conclusion → mismatch, not proved.
        let wrong = "(proof add_base_thm (refl (var a nat)) (all-intro #1 a nat))";
        let json = check_haskell_proofs(NAT_THEOREMS, wrong);
        assert!(json.contains("\"ok\":true"), "json: {json}");
        // add_base_thm is rejected …
        assert!(
            json.contains("\"name\":\"add_base_thm\"") && json.contains("\"outcome\":\"mismatch\""),
            "json: {json}"
        );
        // … and the un-proven refl_a is a hole (no proof in this file).
        assert!(json.contains("\"name\":\"refl_a\""), "json: {json}");
    }

    #[test]
    fn check_haskell_proofs_reports_parse_errors_cleanly() {
        let json = check_haskell_proofs("theorem bad.", "");
        assert!(json.contains("\"ok\":false"), "json: {json}");
        assert!(json.contains("\"error\""), "json: {json}");
    }
}
