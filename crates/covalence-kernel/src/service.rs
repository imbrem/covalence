//! The kernel **service** surface — the single, target-agnostic entry point for
//! checking a `.cov` article into a report of theorems + diagnostics.
//!
//! Every front-end wraps *this*, so the proof-checking logic lives in exactly
//! one place:
//!
//!   - the **browser** prover/IDE (a `wasm32-unknown-unknown` + `wasm-bindgen`
//!     shim — a separate crate),
//!   - the native **LSP** (`covalence-lsp`, which today only does syntax
//!     diagnostics — proof checking lands by wrapping this),
//!   - the **`serve`** HTTP/WebSocket API.
//!
//! See `docs/web-kernel.md` for the architecture (one shared service, one wasm
//! target, native-only LSP) and the async/trust roadmap.
//!
//! # Status
//!
//! [`KernelService::check`] is synchronous and portable: on `wasm32` the
//! underlying proof core runs on `futures::executor::block_on`, so it is
//! callable straight from the browser main thread for **self-contained**
//! articles (whose only dependencies are the standard-library prelude).
//!
//! The genuinely-async path — loading article dependencies over the network via
//! [`ArticleSource`], driven through `covalence_hol::script::run_async` so a
//! `fetch` can be `await`ed instead of dead-locking a blocking executor — is the
//! next step and is recorded in `SKELETONS.md`. The [`ArticleSource`] trait and
//! [`TrustPolicy`] are defined now as the seams those front-ends target.

use covalence_hol::init::check_script;
use covalence_hol::script::{NamedThm, ScriptError};
use covalence_hol::sexp::{UnitObs, term_to_sexp};

/// Severity of a [`Diagnostic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "lowercase"))]
pub enum Severity {
    Error,
    Warning,
    Info,
}

/// A source span as byte offsets into the article source.
///
/// Always `None` on diagnostics today: the `.cov` script layer does not yet
/// carry source extents (see `crates/covalence-hol/src/script/SKELETONS.md`).
/// Editor-grade, in-source error squiggles depend on that work landing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// A diagnostic produced while checking an article.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: String,
    /// Byte span of the offending source, once the script layer carries extents.
    pub span: Option<Span>,
}

/// A checked, named theorem, rendered for display.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct TheoremInfo {
    pub name: String,
    /// The conclusion rendered as a **canonical S-expression**. A
    /// notation/pretty-printer (`(eq (app f x) y)` → `f x = y`, and onward to
    /// MathML for articles) is future work — see `docs/web-kernel.md`.
    pub statement: String,
}

/// The result of checking an article: every theorem the kernel re-derived from
/// the article's own proofs, plus any diagnostics.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct CheckReport {
    /// `true` iff the article checked with no error diagnostics.
    pub ok: bool,
    pub theorems: Vec<TheoremInfo>,
    pub diagnostics: Vec<Diagnostic>,
}

/// How an article's `#import`ed dependencies are treated.
///
/// The article's *own* theorems are always re-derived by the kernel — never
/// trusted. This policy governs only its dependencies, so an article author can
/// trade verification cost against trust explicitly (and the UI can flag it).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TrustLevel {
    /// Admit a dependency's exported theorem *statements* without replaying its
    /// proofs — the fast default for article dependencies (e.g. `category.wiki`
    /// articles building on already-published ones). Surfaced as a "trusted
    /// dependency" badge in the renderer.
    #[default]
    TrustStatements,
    /// Re-check every dependency from its source — nothing trusted. Not yet
    /// enforced (see `SKELETONS.md`).
    DeepCheck,
}

/// Trust configuration for a check.
#[derive(Debug, Clone, Copy, Default)]
pub struct TrustPolicy {
    pub deps: TrustLevel,
}

/// An async source of dependency articles, resolved by name (or, later, by
/// content hash).
///
/// This is the seam each front-end fills: the browser with a `fetch`-backed
/// loader, the native side with the store / filesystem. Wiring it through
/// [`covalence_hol::script::run_async`] (so an `#import` of an unresolved
/// dependency `await`s a real fetch) is the next step — see `SKELETONS.md`.
#[allow(async_fn_in_trait)]
pub trait ArticleSource {
    /// Fetch the `.cov` source of the dependency named `name`, or `None` if this
    /// source does not provide it (so the caller can fall through to the
    /// standard-library prelude or error).
    async fn fetch(&self, name: &str) -> Option<String>;
}

/// The kernel service: a thin, target-agnostic façade over the `.cov` checker.
#[derive(Debug, Clone, Default)]
pub struct KernelService {
    pub trust: TrustPolicy,
}

impl KernelService {
    /// A service with the default trust policy ([`TrustLevel::TrustStatements`]).
    pub fn new() -> Self {
        Self::default()
    }

    /// Check a self-contained `.cov` article against the standard-library
    /// prelude, returning the theorems it proves and any diagnostics.
    ///
    /// The article's own theorems are re-derived by the kernel; nothing in the
    /// text is trusted. The only dependencies resolved today are the built-in
    /// standard-library theories (`core`, `nat`, `logic`, …). Network
    /// dependency loading is the async [`ArticleSource`] path (pending).
    ///
    /// Synchronous and browser-safe — see the module docs.
    pub fn check(&self, src: &str) -> CheckReport {
        match check_script(src) {
            Ok(thms) => CheckReport {
                ok: true,
                theorems: thms.iter().map(render_thm).collect(),
                diagnostics: Vec::new(),
            },
            Err(e) => CheckReport {
                ok: false,
                theorems: Vec::new(),
                diagnostics: vec![diagnostic_from_error(&e)],
            },
        }
    }

    /// Check an article written against the **abstract `Nat` model interface**
    /// (`m.zero`/`m.succ`/`m.add`, the addition axioms `zero.add`/`add.zero`/
    /// `succ.add`/`add.succ`, and the induction handler `m.induct`), resolving
    /// `(#import natmodel)` to the chosen model.
    ///
    /// The whole point of the `models` design: the **same source** proves the
    /// same statement at a *different carrier* per model — `"nat/self"` → kernel
    /// `nat` (integer commutativity), `"nat/unary"` → `list unit` (append
    /// commutativity, true only because every element is the `unit` singleton).
    /// `model` defaults to `"nat/self"` when empty.
    pub fn check_model(&self, src: &str, model: &str) -> CheckReport {
        let natmodel = match build_nat_model_env(model) {
            Ok(e) => e,
            Err(msg) => return error_report(msg),
        };
        let outcome = covalence_hol::script::run(
            src,
            move |name| match name {
                "core" => Some(covalence_hol::script::Env::core()),
                "natmodel" => Some(natmodel.clone()),
                _ => None,
            },
            |_| None,
        )
        .and_then(|lt| lt.resolve_blocking());
        match outcome {
            Ok(theory) => CheckReport {
                ok: true,
                theorems: theory.thms.iter().map(render_thm).collect(),
                diagnostics: Vec::new(),
            },
            Err(e) => error_report(e.to_string()),
        }
    }
}

std::thread_local! {
    /// Per-thread memo of built model envs. Building a model proves its addition
    /// axioms at the carrier (cheap for `nat/self`, but `nat/unary` proves four
    /// `list unit` inductions) — pure work whose result is immutable proven
    /// theorems, so it is sound to cache and reuse across checks. Without this,
    /// every debounced re-check under `nat/unary` re-proves the axioms.
    static MODEL_ENV_CACHE: std::cell::RefCell<std::collections::HashMap<String, covalence_hol::script::Env>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Build (or fetch the memoized) `natmodel` env for a named model: its operators
/// + addition axioms + induction handler, under the abstract names the
/// model-relative proof uses.
fn build_nat_model_env(model: &str) -> Result<covalence_hol::script::Env, String> {
    use covalence_hol::models::{Logic, NatSelf, NatUnary};
    let key = if model.is_empty() { "nat/self" } else { model };
    if let Some(env) = MODEL_ENV_CACHE.with(|c| c.borrow().get(key).cloned()) {
        return Ok(env);
    }
    let built = match key {
        "nat/self" => NatSelf.nat_model(),
        "nat/unary" => NatUnary.nat_model(),
        other => {
            return Err(format!(
                "unknown model `{other}` (expected `nat/self` or `nat/unary`)"
            ));
        }
    };
    let env = built
        .map(|m| m.env())
        .map_err(|e| format!("building model `{model}`: {e}"))?;
    MODEL_ENV_CACHE.with(|c| c.borrow_mut().insert(key.to_string(), env.clone()));
    Ok(env)
}

/// A failed [`CheckReport`] carrying a single error diagnostic.
fn error_report(message: String) -> CheckReport {
    CheckReport {
        ok: false,
        theorems: Vec::new(),
        diagnostics: vec![Diagnostic {
            severity: Severity::Error,
            message,
            span: None,
        }],
    }
}

/// Render a checked theorem's conclusion to a display string (canonical
/// S-expression for now).
fn render_thm(nt: &NamedThm) -> TheoremInfo {
    let statement = term_to_sexp(nt.thm.concl(), &UnitObs)
        .map(|s| sexp_to_string(&s))
        .unwrap_or_else(|_| "<unrenderable>".to_string());
    TheoremInfo {
        name: nt.name.clone(),
        statement,
    }
}

/// Pretty-print a single S-expression to a one-line-ish string.
fn sexp_to_string(s: &covalence_sexp::SExpr) -> String {
    let mut buf = Vec::new();
    let _ = covalence_sexp::prettyprint(std::slice::from_ref(s), &mut buf);
    String::from_utf8_lossy(&buf).trim_end().to_string()
}

/// Lower a [`ScriptError`] into a [`Diagnostic`]. Spans are not yet available
/// from the script layer, so every diagnostic is currently whole-document.
fn diagnostic_from_error(e: &ScriptError) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        message: e.to_string(),
        span: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A minimal self-contained article checks and reports its theorem.
    #[test]
    fn checks_a_trivial_theorem() {
        // `truth` (⊢ true) is the canonical smallest proof against the prelude.
        let src = r#"
            (#import core)
            (#open core)
            (#thm truth
              (#concl true)
              (#proof (eq-mp (reduce-prim (= true true)) (refl true))))
        "#;
        let report = KernelService::new().check(src);
        assert!(report.ok, "diagnostics: {:?}", report.diagnostics);
        assert_eq!(report.theorems.len(), 1);
        assert_eq!(report.theorems[0].name, "truth");
        assert!(report.diagnostics.is_empty());
    }

    /// A bad proof surfaces as an error diagnostic, not a panic.
    #[test]
    fn reports_a_broken_proof_as_diagnostic() {
        let src = "(#import core) (#open core) (#thm bad (#concl true) (#proof (refl true)))";
        let report = KernelService::new().check(src);
        assert!(!report.ok);
        assert!(!report.diagnostics.is_empty());
        assert_eq!(report.diagnostics[0].severity, Severity::Error);
    }

    /// The abstract `Nat` commutativity proof — written once against the model
    /// interface — checks at BOTH carriers, each yielding a real theorem over
    /// its own carrier (kernel `nat` vs `list unit`).
    const ABSTRACT_ADD_COMM: &str = r#"
        (#import core) (#open core)
        (#import natmodel) (#open natmodel)
        (#thm add.comm
          (#concl (forall (a) (forall (b) (= (m.add a b) (m.add b a)))))
          (#by
            (m.induct a
              (#by (intro b) (rw (all-elim b (zero.add))) (sym) (rw (all-elim b (add.zero))) (refl))
              (#by
                (intro b)
                (rw (all-elim b (all-elim a (succ.add))))
                (rw (all-elim b (assume (forall (b) (= (m.add a b) (m.add b a))))))
                (sym)
                (rw (all-elim a (all-elim b (add.succ))))
                (refl)))))
    "#;

    #[test]
    fn abstract_add_comm_checks_at_nat_self() {
        let report = KernelService::new().check_model(ABSTRACT_ADD_COMM, "nat/self");
        assert!(report.ok, "diagnostics: {:?}", report.diagnostics);
        assert_eq!(report.theorems.len(), 1);
        assert_eq!(report.theorems[0].name, "add.comm");
        // The carrier is kernel `nat`: the statement mentions `nat.add`.
        assert!(report.theorems[0].statement.contains("nat.add"), "stmt: {}", report.theorems[0].statement);
    }

    #[test]
    fn abstract_add_comm_checks_at_nat_unary() {
        let report = KernelService::new().check_model(ABSTRACT_ADD_COMM, "nat/unary");
        assert!(report.ok, "diagnostics: {:?}", report.diagnostics);
        assert_eq!(report.theorems[0].name, "add.comm");
        // Different carrier (`list unit`): the SAME proof, a different statement.
        assert!(!report.theorems[0].statement.contains("nat.add"), "stmt: {}", report.theorems[0].statement);
    }

    #[test]
    fn unknown_model_is_a_diagnostic_not_a_panic() {
        let report = KernelService::new().check_model(ABSTRACT_ADD_COMM, "nat/bogus");
        assert!(!report.ok);
        assert!(report.diagnostics[0].message.contains("unknown model"));
    }
}
