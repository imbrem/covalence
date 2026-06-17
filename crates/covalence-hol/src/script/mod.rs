//! Proof scripts — an S-expression authoring + replay layer over the
//! kernel, the bottom rung of the surface-syntax ladder
//! (`docs/surface-syntax.md`).
//!
//! A script file is a sequence of directives:
//!
//! ```text
//! (#import core) (#open core)                         ;; seed the name-resolution prelude
//!
//! (#thm NAME
//!   (#fix (p bool) (q bool))           ;; optional: typed free variables
//!   (#concl  TERM)                     ;; the statement (a drift assertion)
//!   (#proof  DRV))                     ;; the proof term, replayed by `check`
//! ```
//!
//! The pipeline is **author → parse → replay**: the named term syntax
//! (`syntax.rs`) resolves catalogue names through [`Env`] (the `defs/`
//! churn-absorber); the proof term ([`Drv`]) is replayed by [`check`],
//! which is the only kernel-coupled code. Nothing is trusted from the
//! text — the kernel re-derives every theorem. See `Drv`'s docs.
//!
//! Two directions are deliberately **not** built yet (see SKELETONS.md):
//! pretty-printing a `Drv`/`Term` back to this syntax, and content-hashing
//! proof terms for `(lemma …)`-by-hash references. Authoring (parse +
//! replay) is the immediate goal: porting the Rust `init/` theorems.

mod drv;
mod env;
mod handle;
mod infer;
mod scope;
mod syntax;
mod tactic;

pub use drv::{Drv, Rule, check, parse_drv};
pub use env::{ConstDef, Env};
pub use handle::LazyEnv;
pub use scope::Scope;
pub use syntax::{parse_term, parse_type};
pub use tactic::{Interp, Tactic};

use std::sync::Arc;

use covalence_core::{Thm, Type};
use covalence_sexp::SExpr;

/// A replayed theory in its **in-progress** state, the value `run`/`run_async`
/// return. Every `#thm` is already checked (`thms`); [`LazyTheory::resolve`]
/// forces it to a [`Theory`].
///
/// The two types are nominally distinct (in-progress vs "done") to keep the
/// async-prover API shape — `run` → `LazyTheory`, force → `Theory`. The
/// machinery that made a theorem genuinely *open* (proof holes / obligations)
/// was removed pending a clean channel-based rebuild (`#hole` receives from an
/// env channel that `#fill` pushes to); see SKELETONS.md. So today resolving is
/// trivial — nothing is ever pending.
pub struct LazyTheory {
    /// The explicitly-exported public interface (`(#export …)`).
    exports: Env,
    /// The full running environment (its `lemmas` may still be `#compute`-ing).
    internal: Env,
    /// The eagerly-checked theorems.
    pub thms: Vec<NamedThm>,
    /// Names of `(#compute …)` theorems still running on a blocking thread,
    /// awaited from `internal` and folded into `thms` when the theory is forced.
    computed_names: Vec<String>,
}

impl LazyTheory {
    /// The exported environment — pass it as an `(#import NAME) (#open NAME)` target when
    /// running a downstream script. Empty unless the script `(#export …)`s.
    pub fn env(&self) -> Env {
        self.exports.clone()
    }

    /// Look up an **exported** lemma by name (panics if not exported — for
    /// the `cov_theory!` accessor functions, which name lemmas statically;
    /// exposing one as a Rust `fn` therefore requires `(#export …)`ing it).
    pub fn lemma(&self, name: &str) -> Thm {
        self.exports
            .lemma_ready(name)
            .unwrap_or_else(|| panic!("theory does not export lemma `{name}`"))
    }

    /// **Force** the theory to its fully-proved [`Theory`]: await every
    /// still-`#compute`-ing theorem (each running on a blocking thread) and
    /// fold its result into `thms`. For a synchronous caller use
    /// [`LazyTheory::resolve_blocking`].
    pub async fn resolve(self) -> Result<Theory, ScriptError> {
        let LazyTheory {
            exports,
            internal,
            mut thms,
            mut computed_names,
        } = self;
        // Await the background computations (in name order for determinism),
        // each looked up — and awaited — from the running env.
        computed_names.sort();
        for name in computed_names {
            let thm = internal
                .lookup_lemma(&name)
                .await
                .expect("computed name is bound in internal")?;
            thms.push(NamedThm { name, thm });
        }
        Ok(Theory { exports, thms })
    }

    /// Force the theory on the current thread — the blocking wrapper over
    /// [`LazyTheory::resolve`]. Runs on a tokio current-thread runtime (see
    /// [`block_on`]); native only, and not for callers already inside a tokio
    /// runtime (which should `.resolve().await` instead).
    pub fn resolve_blocking(self) -> Result<Theory, ScriptError> {
        block_on(self.resolve())
    }
}

/// A theory all of whose `#thm`s are checked — the result of forcing a
/// [`LazyTheory`]. This is the "done" state: a `Thm` for every theorem.
pub struct Theory {
    exports: Env,
    pub thms: Vec<NamedThm>,
}

impl Theory {
    /// The exported environment (see [`LazyTheory::env`]).
    pub fn env(&self) -> Env {
        self.exports.clone()
    }

    /// Look up an **exported** lemma by name (see [`LazyTheory::lemma`]).
    pub fn lemma(&self, name: &str) -> Thm {
        self.exports
            .lemma_ready(name)
            .unwrap_or_else(|| panic!("theory does not export lemma `{name}`"))
    }
}

/// A bare environment becomes a handle with no theorems (e.g. the `core`
/// prelude, imported for its constants/tactics).
impl From<Env> for LazyTheory {
    fn from(exports: Env) -> Self {
        LazyTheory {
            exports,
            internal: Env::empty(),
            thms: Vec::new(),
            computed_names: Vec::new(),
        }
    }
}

/// A resolved [`Theory`] casts back to a (trivially in-progress) handle — what
/// lets an `#import` receive a fully-proved theory through the future-returning
/// resolver.
impl From<Theory> for LazyTheory {
    fn from(t: Theory) -> Self {
        LazyTheory {
            exports: t.exports,
            internal: Env::empty(),
            thms: t.thms,
            computed_names: Vec::new(),
        }
    }
}

/// The result of resolving an `#import`: a **future** yielding the imported
/// [`LazyTheory`]. `#import` awaits it — the script layer's first genuinely
/// async operation — so an import need not be ready (or fully proved) when it
/// is requested. Boxed so a resolver can return differently-shaped futures.
pub type Import = std::pin::Pin<Box<dyn std::future::Future<Output = LazyTheory>>>;

/// Wrap an already-available env/theory as a ready [`Import`] — the common case
/// where an import resolves synchronously (the future is immediately ready).
pub fn ready_import(handle: impl Into<LazyTheory> + 'static) -> Import {
    Box::pin(async move { handle.into() })
}

/// Errors from parsing or replaying a proof script.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ScriptError {
    #[error("syntax: {0}")]
    Syntax(String),
    #[error("unbound name: {0}")]
    Unbound(String),
    #[error(transparent)]
    Kernel(#[from] covalence_core::Error),
    #[error("conclusion mismatch in `{name}`:\n  stated:  {expected}\n  derived: {got}")]
    ConclMismatch {
        name: String,
        expected: String,
        got: String,
    },
}

/// A checked, named theorem produced by a script.
pub struct NamedThm {
    pub name: String,
    pub thm: Thm,
}

/// Parse and replay a whole script. `(#import NAME)` resolves `NAME` via
/// `resolver` and registers it as an importable namespace; `(#import NAME) (#open NAME)`
/// brings a previously-imported namespace's bindings into scope; `(#thm …)`
/// directives are checked and accumulate so later theorems can reference
/// earlier ones — and any opened namespace's lemmas — via `(lemma NAME)`.
/// Replay a script, blocking until the whole theory is proved. The blocking
/// half of the async core ([`run_async`]) — see [`block_on`]. This is the
/// stable entry point; the kernel/TCB stays synchronous, so today the future
/// completes without ever pending.
pub fn run(
    src: &str,
    resolver: impl Fn(&str) -> Option<Env>,
    tactics: impl Fn(&str) -> Option<Arc<dyn Tactic>>,
) -> Result<LazyTheory, ScriptError> {
    // Adapt the synchronous `Env` resolver to the async core's future-returning
    // one: each import is already available, so it resolves immediately.
    block_on(run_async(
        src,
        |name| resolver(name).map(ready_import),
        tactics,
    ))
}

/// The async core: parse a whole script into structured [`Stmt`]s and execute
/// them into a [`LazyTheory`].
///
/// `#import` is the one genuinely **async** step: it `await`s the
/// `resolver`-supplied [`Import`] future, so an imported theory can be produced
/// lazily / remotely / while still in progress. Everything else runs
/// synchronously and in order (the cooperative scheduler that lets a *blocked*
/// statement yield to the next is future work — see SKELETONS.md).
pub async fn run_async(
    src: &str,
    resolver: impl Fn(&str) -> Option<Import>,
    tactics: impl Fn(&str) -> Option<Arc<dyn Tactic>>,
) -> Result<LazyTheory, ScriptError> {
    let exprs =
        covalence_sexp::parse(src).map_err(|e| ScriptError::Syntax(format!("sexp: {e}")))?;
    // Stage 1: parse every directive into a typed statement (structural errors
    // surface here, before any execution).
    let stmts = exprs
        .iter()
        .map(parse_stmt)
        .collect::<Result<Vec<_>, _>>()?;

    // Stage 2: execute.
    let mut internal = Env::empty();
    let mut exports = Env::empty();
    let mut thms = Vec::new();
    let mut computed_names: Vec<String> = Vec::new();
    for stmt in stmts {
        match stmt {
            // The async step: await the import's future, then register its
            // exported environment under NAME.
            Stmt::Import(name) => {
                let future = resolver(&name)
                    .ok_or_else(|| ScriptError::Unbound(format!("environment `{name}`")))?;
                let handle = future.await;
                internal.import(name, handle.env());
            }
            Stmt::Open(name) => internal.open(&name)?,
            Stmt::Use { module, prefix } => internal.use_ns(&module, &prefix)?,
            // `(#extend MODULE)` — re-export MODULE's symbols at the *root*
            // (no prefix), e.g. fold `logic` into the prelude.
            Stmt::Extend(module) => {
                let ns = imported(&internal, &module)?;
                exports.merge_prefixed(&ns, "");
            }
            // `(#provide MODULE)` / `(#provide (#alias MODULE PREFIX))` —
            // re-export MODULE's symbols *under a prefix* (default the module's
            // own name), e.g. `nat` → `nat.*`, or aliased `nat` → `init.nat.*`.
            Stmt::Provide { module, prefix } => {
                let ns = imported(&internal, &module)?;
                exports.merge_prefixed(&ns, &prefix);
            }
            Stmt::RegisterFfiTactic(name) => {
                let tac = tactics(&name).ok_or_else(|| {
                    ScriptError::Unbound(format!("ffi tactic `{name}` (not provided by host)"))
                })?;
                internal.register_tactic(name, tac);
            }
            // `(#dep NAME)` — force a dependency: a synchronous availability
            // guard today; the real `await`-until-`NAME`-completes semantics
            // depend on the cooperative scheduler (see SKELETONS.md).
            Stmt::Dep(name) => {
                let known = internal.has_lemma(&name)
                    || internal.lookup_const(&name).is_some()
                    || internal.lookup_tactic(&name).is_some()
                    || internal.get_import(&name).is_some();
                if !known {
                    return Err(ScriptError::Unbound(format!(
                        "#dep: unknown dependency `{name}`"
                    )));
                }
            }
            Stmt::Thm(sexpr) => {
                let ch = syntax::list(&sexpr, "#thm")?;
                // `check` awaits any `(lemma …)` it references that is still
                // `#compute`-ing — lemma lookup is now async.
                let nt = run_thm(ch, &internal).await?;
                internal.define_lemma(nt.name.clone(), nt.thm.clone());
                thms.push(nt);
            }
            // `(#compute NAME …)` — kick off the proof on a blocking thread
            // and bind NAME to the still-running task in the env. Execution
            // moves straight on; a later proof's `(lemma NAME)` (or the force)
            // simply **awaits** it.
            Stmt::Compute(sexpr) => {
                let ch = syntax::list(&sexpr, "#compute")?;
                let name = syntax::sym(&ch[1], "compute name")?.to_string();
                let env = internal.clone();
                let task = tokio::task::spawn_blocking(move || {
                    let ch = syntax::list(&sexpr, "#compute")?;
                    // Drive the (async) proof to completion on this blocking
                    // thread — its own runtime, not nested in the caller's.
                    block_on(run_thm(ch, &env)).map(|nt| nt.thm)
                });
                internal.define_computing(name.clone(), task);
                computed_names.push(name);
            }
            // `(#export NAME …)` — build the public interface explicitly: each
            // name is a proven lemma or an imported lemma/const/tactic. A lemma
            // is **awaited** (so an exported `#compute` lands ready).
            Stmt::Export(names) => {
                for name in names {
                    if let Some(c) = internal.lookup_const(&name) {
                        exports.define_const(name, c.clone());
                    } else if let Some(t) = internal.lookup_tactic(&name) {
                        exports.register_tactic(name, t);
                    } else if let Some(thm) = internal.lookup_lemma(&name).await {
                        exports.define_lemma(name, thm?);
                    } else {
                        return Err(ScriptError::Unbound(format!(
                            "#export: nothing named `{name}` to export"
                        )));
                    }
                }
            }
        }
    }
    Ok(LazyTheory {
        exports,
        internal,
        thms,
        computed_names,
    })
}

/// Await every `(lemma NAME)` reference in `sexpr` that is still
/// Fetch an imported namespace's environment, erroring if it was never
/// `(#import …)`ed.
fn imported(internal: &Env, name: &str) -> Result<Env, ScriptError> {
    internal
        .get_import(name)
        .cloned()
        .ok_or_else(|| ScriptError::Unbound(format!("environment not imported: `{name}`")))
}

/// Drive the async proof core to completion — the blocking half of the API.
/// Runs on a fresh **tokio** current-thread runtime, which is the scheduler
/// the prover is built on: cooperative concurrency (block a task → run another
/// → resume it) today, swappable for a multi-thread runtime when we want true
/// parallel verification. Native only, and must not be called from inside an
/// existing tokio runtime (the `cov_theory!` loads + tests run it from plain
/// sync context).
fn block_on<F: std::future::Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new_current_thread()
        .build()
        .expect("build a current-thread tokio runtime for the proof core")
        .block_on(future)
}

/// Replay a script whose only available environment is the `core` prelude,
/// returning the theorems it proves.
pub fn run_str(src: &str) -> Result<Vec<NamedThm>, ScriptError> {
    Ok(run(src, |name| (name == "core").then(Env::core), |_| None)?.thms)
}

/// A structured top-level script directive — the first stage of the eventual
/// parse → untyped-elaborate → typecheck → typed-elaborate → execute pipeline.
/// (`#thm` bodies stay as raw `SExpr` for now; their typed elaboration is a
/// later stage. Source extents are not yet carried — see SKELETONS.md.)
enum Stmt {
    /// `(#import NAME)` — resolve and register NAME (the async step).
    Import(String),
    /// `(#open NAME)` — merge an imported namespace UNQUALIFIED into scope.
    Open(String),
    /// `(#use NAME)` / `(#use (#alias MODULE PREFIX))` — merge QUALIFIED.
    Use { module: String, prefix: String },
    /// `(#extend MODULE)` — re-export MODULE's symbols at the root (no prefix).
    Extend(String),
    /// `(#provide MODULE)` / `(#provide (#alias MODULE PREFIX))` — re-export
    /// MODULE's symbols under a prefix (default: the module's own name).
    Provide { module: String, prefix: String },
    /// `(#register-ffi-tactic NAME)` — register a host-supplied tactic.
    RegisterFfiTactic(String),
    /// `(#dep NAME)` — force/await a dependency.
    Dep(String),
    /// `(#thm …)` — the whole directive; parsed + checked at execution.
    Thm(SExpr),
    /// `(#compute NAME …)` — like `#thm`, but checked on a **blocking thread**
    /// (`spawn_blocking`) so it runs while later statements proceed; awaited
    /// when the theory is forced.
    Compute(SExpr),
    /// `(#export NAME …)` — the public interface.
    Export(Vec<String>),
}

/// Parse one directive S-expression into a typed [`Stmt`].
fn parse_stmt(e: &SExpr) -> Result<Stmt, ScriptError> {
    let ch = syntax::list(e, "directive")?;
    // Structural directives are `#`-prefixed; bare names (inside proofs) are
    // rules/terms resolved from the environment, never directives.
    Ok(match syntax::head_sym(ch)? {
        "#import" => {
            syntax::arity(ch, 2, "#import")?;
            Stmt::Import(syntax::sym(&ch[1], "environment name")?.to_string())
        }
        "#open" => {
            syntax::arity(ch, 2, "#open")?;
            Stmt::Open(syntax::sym(&ch[1], "environment name")?.to_string())
        }
        "#use" => {
            syntax::arity(ch, 2, "#use")?;
            let (module, prefix) = parse_module_target(&ch[1])?;
            Stmt::Use { module, prefix }
        }
        "#extend" => {
            syntax::arity(ch, 2, "#extend")?;
            Stmt::Extend(syntax::sym(&ch[1], "module name")?.to_string())
        }
        "#provide" => {
            syntax::arity(ch, 2, "#provide")?;
            let (module, prefix) = parse_module_target(&ch[1])?;
            Stmt::Provide { module, prefix }
        }
        "#register-ffi-tactic" => {
            syntax::arity(ch, 2, "#register-ffi-tactic")?;
            Stmt::RegisterFfiTactic(syntax::sym(&ch[1], "tactic name")?.to_string())
        }
        "#dep" => {
            syntax::arity(ch, 2, "#dep")?;
            Stmt::Dep(syntax::sym(&ch[1], "dependency name")?.to_string())
        }
        "#thm" => Stmt::Thm(e.clone()),
        "#compute" => Stmt::Compute(e.clone()),
        "#export" => {
            if ch.len() < 2 {
                return Err(ScriptError::Syntax(
                    "#export: expected (#export NAME …)".into(),
                ));
            }
            let names = ch[1..]
                .iter()
                .map(|item| Ok(syntax::sym(item, "export name")?.to_string()))
                .collect::<Result<Vec<_>, ScriptError>>()?;
            Stmt::Export(names)
        }
        other => return Err(ScriptError::Syntax(format!("unknown directive: {other}"))),
    })
}

/// Parse a module target — `MODULE` (prefix = `MODULE`) or `(#alias MODULE
/// PREFIX)` (prefix = `PREFIX`). Shared by `#use` and `#provide`.
fn parse_module_target(s: &SExpr) -> Result<(String, String), ScriptError> {
    match s {
        covalence_sexp::SExp::Atom(_) => {
            let n = syntax::sym(s, "module name")?;
            Ok((n.to_string(), n.to_string()))
        }
        covalence_sexp::SExp::List(a) => {
            if syntax::head_sym(a)? != "#alias" {
                return Err(ScriptError::Syntax(
                    "expected MODULE or (#alias MODULE PREFIX)".into(),
                ));
            }
            syntax::arity(a, 3, "#alias")?;
            Ok((
                syntax::sym(&a[1], "module name")?.to_string(),
                syntax::sym(&a[2], "alias prefix")?.to_string(),
            ))
        }
    }
}

/// Load a `.cov` proof script as a Rust module: run it once, lazily, with
/// the given `import`ed environments available for the script to `(#open …)`
/// (or otherwise reference), then expose chosen lemmas as `fn() -> Thm`
/// accessors plus the resulting environment via `env()` (which downstream
/// theories can in turn `import`).
///
/// `import NAME = EXPR;` makes the environment `EXPR` *available* to the
/// script under `NAME`; the `.cov` decides what to do with it (today, an
/// `(#import NAME) (#open NAME)` directive merges it in — later it may bind it under a
/// namespace instead, which is why this is `import`, not `open`).
///
/// ```ignore
/// crate::cov_theory! {
///     /// Propositional logic, ported from Rust.
///     pub mod cov from "logic.cov" {
///         import "core" = crate::script::Env::core();
///         "truth"    => pub fn truth;
///         "and.comm" => pub fn and_comm;
///     }
/// }
/// pub use cov::{and_comm, truth};   // drop-in replacements for the old fns
/// ```
///
/// The `include_str!` path is relative to the invoking file, so place the
/// `.cov` beside the `.rs` that loads it. Parse/check failures panic at
/// first use (like `cached_thm!`), since a theory is a static resource.
#[macro_export]
macro_rules! cov_theory {
    (
        $(#[$meta:meta])*
        $vis:vis mod $modname:ident from $src:literal {
            $( import $oname:literal = $oenv:expr ; )*
            $( ffi-tactic $tname:literal = $texpr:expr ; )*
            $( $lemma:literal => $lvis:vis fn $fn:ident ; )*
        }
    ) => {
        $(#[$meta])*
        $vis mod $modname {
            #[allow(unused_imports)]
            use super::*;

            static THEORY: ::std::sync::LazyLock<$crate::script::Theory> =
                ::std::sync::LazyLock::new(|| {
                    $crate::script::run(
                        include_str!($src),
                        |__name| match __name {
                            $( $oname => Some($oenv), )*
                            _ => None,
                        },
                        |__tname| -> ::core::option::Option<
                            ::std::sync::Arc<dyn $crate::script::Tactic>,
                        > {
                            match __tname {
                                $( $tname => Some(::std::sync::Arc::new($texpr)), )*
                                _ => None,
                            }
                        },
                    )
                    // A `cov_theory!` is a finished resource — force it to its
                    // resolved (fully-proved) state, discharging any `#fill`s.
                    .and_then(|__t| __t.resolve_blocking())
                    .unwrap_or_else(|__e| {
                        panic!("cov_theory `{}`: {}", stringify!($modname), __e)
                    })
                });

            /// This theory's exported environment, as a lazily-built static.
            /// Reference it in another theory's `import …` clause (or `open`
            /// it via a resolver) to bring its exports into scope.
            $vis static ENV: ::std::sync::LazyLock<$crate::script::Env> =
                ::std::sync::LazyLock::new(|| THEORY.env());

            /// The exported environment (a clone of [`ENV`]) — convenient
            /// where an owned `Env` is wanted, e.g. a resolver return.
            $vis fn env() -> $crate::script::Env {
                (*ENV).clone()
            }

            $(
                $lvis fn $fn() -> $crate::Thm {
                    THEORY.lemma($lemma)
                }
            )*
        }
    };
}

async fn run_thm(ch: &[SExpr], env: &Env) -> Result<NamedThm, ScriptError> {
    if ch.len() < 4 {
        return Err(ScriptError::Syntax(
            "#thm: expected (#thm NAME [(#fix …)] (#concl …) (#proof …))".into(),
        ));
    }
    let name = syntax::sym(&ch[1], "thm name")?.to_string();
    let mut idx = 2;

    // optional (#fix x (y T) …) — annotations are optional; omitted types
    // (and omitted `#fix` entirely) are inferred from the conclusion.
    let mut fix: Vec<(String, Option<Type>)> = Vec::new();
    if let SExpr::List(f) = &ch[idx]
        && f.first().and_then(|x| x.as_symbol()) == Some("#fix")
    {
        for v in &f[1..] {
            fix.push(infer::parse_binder_spec(v)?);
        }
        idx += 1;
    }

    // Elaborate the conclusion: this infers the type of every free
    // variable, which then seeds the proof so both share one typing.
    let concl_ch = syntax::list(&ch[idx], "#concl")?;
    let concl_payload = syntax::expect_head(concl_ch, "#concl")?;
    let (expected, vars) = infer::elaborate_concl(concl_payload, &fix, env)?;
    let mut scope = Scope::with_vars(vars);
    idx += 1;

    // The proof body is `(#proof DRV)` (tree mode) or `(#by STEP…)`
    // (goal-directed tactic mode). Tree mode checks a `Drv` to a `Thm`;
    // tactic mode produces the `Thm` directly by driving the goal.
    let thm = tactic::prove(&expected, &ch[idx], &mut scope, env).await?;
    if thm.concl() != &expected {
        return Err(ScriptError::ConclMismatch {
            name,
            expected: format!("{expected}"),
            got: format!("{}", thm.concl()),
        });
    }
    Ok(NamedThm { name, thm })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Replay a single `(#thm …)` and return its checked theorem.
    fn one(src: &str) -> Thm {
        let mut thms = run_str(src).expect("script should replay");
        assert_eq!(thms.len(), 1);
        thms.pop().unwrap().thm
    }

    #[test]
    fn run_async_is_driven_by_block_on() {
        // The async core is reachable directly; `block_on` drives it exactly
        // as the sync `run` wrapper does.
        let theory = block_on(run_async(
            r#"
            (#import core)
            (#open core)
            (#thm add.2.3
              (#concl (= (nat.add 2 3) 5))
              (#proof (reduce-prim (nat.add 2 3))))
            "#,
            |name| (name == "core").then(|| ready_import(Env::core())),
            |_| None,
        ))
        .expect("async run");
        assert_eq!(theory.thms.len(), 1);
    }

    #[test]
    fn dep_forces_known_and_rejects_unknown() {
        // `(#dep NAME)` is satisfied by an available lemma…
        let ok = run_str(
            r#"
            (#import core)
            (#open core)
            (#thm id (#fix (p bool)) (#concl (==> p p))
              (#proof (imp-intro p (assume p))))
            (#dep id)
            "#,
        );
        assert!(ok.is_ok(), "#dep on a proven lemma should pass");
        // …and rejects an unknown name (today a synchronous availability
        // guard; the cooperative `await` semantics come with the scheduler).
        let bad = run_str("(#import core)(#open core)(#dep nonexistent)");
        assert!(
            matches!(bad, Err(ScriptError::Unbound(_))),
            "#dep on unknown should error"
        );
    }

    #[test]
    fn closure_tactic_captures_state() {
        // A host tactic built from a CLOSURE that captures a precomputed
        // theorem — impossible with the old bare-`fn`-pointer registry, and
        // the concrete reason `Tactic` is now a trait. It ignores the goal
        // and returns the captured `Thm`.
        let canned: Arc<dyn Tactic> = {
            let thm = one(r#"
                (#import core)
                (#open core)
                (#thm t (#concl (= (nat.add 2 3) 5))
                  (#proof (reduce-prim (nat.add 2 3))))
                "#);
            Arc::new(move |_s: &[SExpr], _rest: &[SExpr], _it: &mut Interp| Ok(thm.clone()))
        };
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#register-ffi-tactic canned)
            (#thm u (#concl (= (nat.add 2 3) 5)) (#by (canned)))
            "#,
            |name| (name == "core").then(Env::core),
            move |name| (name == "canned").then(|| canned.clone()),
        )
        .expect("closure tactic registers and runs");
        assert_eq!(theory.thms.len(), 1);
        assert!(theory.thms[0].thm.hyps().is_empty());
    }

    #[test]
    fn and_comm_ports_from_rust() {
        // The S-expression rewrite of `init::logic::and_comm`.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm and.comm
              (#fix (p bool) (q bool))
              (#concl (==> (and p q) (and q p)))
              (#proof
                (imp-intro (and p q)
                  (and-intro
                    (and-elim-r (assume (and p q)))
                    (and-elim-l (assume (and p q)))))))
            "#);
        assert!(thm.hyps().is_empty(), "and.comm must be hypothesis-free");
        // It must match the hand-written Rust theorem exactly.
        let rust = crate::init::logic::and_comm();
        assert_eq!(thm.concl(), rust.concl());
    }

    #[test]
    fn ground_arithmetic_via_reduce_prim() {
        // ⊢ 2 + 3 = 5, by primitive computation.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm add.2.3
              (#concl (= (nat.add 2 3) 5))
              (#proof (reduce-prim (nat.add 2 3))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn tauto_tactic_proves_a_trivial_tautology() {
        // `p ⟹ p`, discharged by the `tauto` tactic (delegating to
        // `init::logic::tauto`) rather than an explicit derivation —
        // proving the tactic layer elaborates to kernel rules. (The
        // existing `tauto` decides *trivial* tautologies — those that
        // `normalize` reduces to `T` — not arbitrary propositional
        // goals like ∧-commutativity.)
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm imp.refl.auto
              (#fix (p bool))
              (#concl (==> p p))
              (#proof (tauto (==> p p))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn tauto_tactic_comes_from_logic() {
        // The `tauto` *tactic* (goal mode) is registered into `logic`'s env
        // via `(#register-ffi-tactic tauto)` + the `ffi-tactic` macro clause
        // — NOT into `core`. Opening logic brings it into scope.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#import logic)
            (#open logic)
            (#thm imp.refl.by
              (#concl (==> p p))
              (#by (tauto)))
            "#,
            |name| match name {
                "core" => Some(Env::core()),
                "logic" => Some(crate::init::logic::cov::env()),
                _ => None,
            },
            |_| None,
        )
        .expect("the tauto tactic is available via the logic env");
        assert!(theory.thms[0].thm.hyps().is_empty());

        // Without opening logic, the `tauto` *tactic* is not in scope.
        let missing = run_str(
            r#"
            (#import core)
            (#open core)
            (#thm t (#concl (==> p p)) (#by (tauto)))
            "#,
        );
        assert!(missing.is_err(), "tauto tactic must not be a core tactic");
    }

    #[test]
    fn use_qualifies_a_namespace() {
        // `(#use logic)` brings logic's exports in QUALIFIED: `and.comm`
        // becomes `logic.and.comm`. `#provide (#alias …)` re-exports everything
        // under a prefix.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#import logic)
            (#use logic)
            (#thm uses.qualified
              (#concl (and b a))
              (#proof
                (imp-elim
                  (inst p a (inst q b (lemma logic.and.comm)))
                  (assume (and a b)))))
            (#provide (#alias logic prelude))
            "#,
            |name| match name {
                "core" => Some(Env::core()),
                "logic" => Some(crate::init::logic::cov::env()),
                _ => None,
            },
            |_| None,
        )
        .expect("qualified use of logic");
        // `lemma logic.and.comm` resolved (the proof checked).
        assert_eq!(theory.thms.len(), 1);
        // the alias `lg.` and the re-export `prelude.` are both present
        let env = theory.env();
        assert!(
            env.has_lemma("prelude.and.comm"),
            "re-exported under prelude"
        );
    }

    #[test]
    fn extend_and_provide_reexport() {
        // `#extend` folds a module in at the root; `#provide` puts it under a
        // prefix (the module name, or an alias).
        let theory = run(
            r#"
            (#import core)(#open core)
            (#import logic)
            (#extend logic)
            (#provide logic)
            (#provide (#alias logic pre))
            "#,
            |name| match name {
                "core" => Some(Env::core()),
                "logic" => Some(crate::init::logic::cov::env()),
                _ => None,
            },
            |_| None,
        )
        .unwrap();
        let env = theory.env();
        assert!(env.has_lemma("and.comm"), "#extend re-exports at the root");
        assert!(
            env.has_lemma("logic.and.comm"),
            "#provide under module name"
        );
        assert!(env.has_lemma("pre.and.comm"), "#provide under an alias");
    }

    #[test]
    fn import_awaits_a_pending_future() {
        // The import future *yields* before producing its handle — `#import`
        // awaits it (the script layer's first genuinely async step).
        let theory = block_on(run_async(
            r#"
            (#import core)
            (#open core)
            (#thm t (#concl (= 1 1)) (#proof (refl 1)))
            "#,
            |name| {
                (name == "core").then(|| -> Import {
                    Box::pin(async {
                        tokio::task::yield_now().await;
                        Env::core().into()
                    })
                })
            },
            |_| None,
        ))
        .expect("import awaits the pending future");
        assert_eq!(theory.thms.len(), 1);
    }

    #[test]
    fn compute_runs_in_the_background_and_lands_on_resolve() {
        // A `#compute`d theorem runs on a blocking thread while later
        // statements proceed; it is NOT in `thms` until the theory is forced.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#thm eager (#concl (= 1 1)) (#proof (refl 1)))
            (#compute slow (#concl (= (nat.add 2 3) 5))
              (#proof (reduce-prim (nat.add 2 3))))
            "#,
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .unwrap();
        assert!(theory.thms.iter().any(|nt| nt.name == "eager"));
        assert!(
            !theory.thms.iter().any(|nt| nt.name == "slow"),
            "the #compute is still pending pre-force"
        );
        let resolved = theory
            .resolve_blocking()
            .expect("forcing awaits the compute");
        assert!(resolved.thms.iter().any(|nt| nt.name == "slow"));
        assert!(resolved.thms.iter().any(|nt| nt.name == "eager"));
    }

    #[test]
    fn a_proof_awaits_a_computed_lemma() {
        // A later `#thm` references a `#compute`d theorem via `(lemma …)`:
        // `check`'s `Drv::Lemma` arm now AWAITS the still-computing lemma
        // directly (lemma lookup is async), so `#compute`d lemmas are usable
        // by later proofs.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#compute base (#concl (= 0 0)) (#proof (refl 0)))
            (#thm uses (#concl (= 0 0)) (#proof (lemma base)))
            "#,
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .unwrap();
        // `uses` checked eagerly (after awaiting `base`); `base` lands on force.
        assert!(theory.thms.iter().any(|nt| nt.name == "uses"));
        let resolved = theory.resolve_blocking().unwrap();
        assert!(resolved.thms.iter().any(|nt| nt.name == "base"));
        assert!(resolved.thms.iter().any(|nt| nt.name == "uses"));
    }

    #[test]
    fn async_tactic_can_yield_mid_proof() {
        // A custom tactic whose `apply` AWAITS (yields) before producing its
        // theorem — only possible because `Tactic::apply` is async. It hands
        // back a precomputed theorem after a real suspension point.
        let thm = one(
            "(#import core)(#open core)(#thm t (#concl (= (nat.add 2 3) 5))
              (#proof (reduce-prim (nat.add 2 3))))",
        );
        struct AsyncCanned(Thm);
        #[async_trait::async_trait]
        impl Tactic for AsyncCanned {
            async fn apply(
                &self,
                _s: &[SExpr],
                _rest: &[SExpr],
                _it: &mut Interp,
            ) -> Result<Thm, ScriptError> {
                tokio::task::yield_now().await; // genuine mid-proof yield
                Ok(self.0.clone())
            }
        }
        let tac: Arc<dyn Tactic> = Arc::new(AsyncCanned(thm));
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#register-ffi-tactic acanned)
            (#thm u (#concl (= (nat.add 2 3) 5)) (#by (acanned)))
            "#,
            |name| (name == "core").then(Env::core),
            move |name| (name == "acanned").then(|| tac.clone()),
        )
        .expect("async tactic runs");
        assert_eq!(theory.thms.len(), 1);
    }

    #[test]
    fn registry_rule_in_tree_mode_can_await() {
        // A custom **derivation rule** that AWAITS mid-derivation, then returns
        // its sub-derivation's theorem — proving tree-mode `check` is async and
        // that unknown heads dispatch through the `Env` rule registry.
        struct YieldId;
        #[async_trait::async_trait]
        impl Rule for YieldId {
            async fn apply(&self, args: &[Thm], _env: &Env) -> Result<Thm, ScriptError> {
                tokio::task::yield_now().await; // genuine mid-derivation await
                args.first()
                    .cloned()
                    .ok_or_else(|| ScriptError::Syntax("yield-id: needs one arg".into()))
            }
        }
        let mut rule_env = Env::empty();
        rule_env.register_rule("yield-id", Arc::new(YieldId));
        let theory = run(
            r#"
            (#import core)(#open core)
            (#import rules)(#open rules)
            (#thm t (#concl (= 0 0)) (#proof (yield-id (refl 0))))
            "#,
            move |name| match name {
                "core" => Some(Env::core()),
                "rules" => Some(rule_env.clone()),
                _ => None,
            },
            |_| None,
        )
        .expect("registry rule resolves in tree mode");
        assert_eq!(theory.thms.len(), 1);
    }

    #[test]
    fn compute_failure_surfaces_on_resolve() {
        // A `#compute` whose proof is wrong errors only when forced.
        let theory = run(
            r#"
            (#import core)(#open core)
            (#compute bad (#concl (= 1 2)) (#proof (refl 1)))
            "#,
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .unwrap();
        assert!(theory.resolve_blocking().is_err());
    }

    #[test]
    fn resolved_theory_imports_via_cast() {
        // A fully-proved `Theory` casts to a `LazyTheory` (From<Theory>) and
        // can be `#import`ed by a downstream script.
        let handle: LazyTheory = run(
            "(#import core)(#open core)(#thm foo (#concl (= 0 0)) (#proof (refl 0)))(#export foo)",
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .unwrap()
        .resolve_blocking()
        .unwrap()
        .into();
        assert!(handle.env().has_lemma("foo"));
        assert_eq!(handle.thms.len(), 1);
    }

    #[test]
    fn resolve_blocking_forces_an_eager_theory() {
        // With no open obligations, forcing is trivial: every `#thm` is already
        // checked, and `resolve` just hands back the `Theory`.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#thm add.2.3 (#concl (= (nat.add 2 3) 5))
              (#proof (reduce-prim (nat.add 2 3))))
            "#,
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .unwrap();
        let resolved = theory.resolve_blocking().expect("eager theory resolves");
        assert_eq!(resolved.thms.len(), 1);
        // And the async entry is awaitable directly.
        let theory =
            run_str("(#import core)(#open core)(#thm t (#concl (= 1 1)) (#proof (refl 1)))");
        assert!(theory.is_ok());
    }

    #[test]
    fn derive_and_drv_alias_the_old_exact() {
        // `exact` was renamed to `derive` (short alias `drv`): both close a
        // goal with a tree-mode derivation.
        let a = one(
            "(#import core)(#open core)(#thm t (#fix (p bool)) (#concl (==> p p))
              (#by (derive (imp-intro p (assume p)))))",
        );
        let b = one(
            "(#import core)(#open core)(#thm t (#fix (p bool)) (#concl (==> p p))
              (#by (drv (imp-intro p (assume p)))))",
        );
        assert_eq!(a.concl(), b.concl());
    }

    #[test]
    fn excluded_middle_via_lem() {
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm lem.p
              (#fix (p bool))
              (#concl (or p (not p)))
              (#proof (lem p)))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn rw_tactic_rewrites_with_a_hypothesis() {
        // `rw` is a full congruence — it rewrites *every* occurrence of
        // the equation's LHS. From `a = b` (assumed) and `⊢ a = a`
        // (refl), rewriting `a ↦ b` everywhere gives {a = b} ⊢ b = b.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm rw.demo
              (#fix (a nat) (b nat))
              (#concl (= b b))
              (#proof (rw (assume (= a b)) (refl a))))
            "#);
        // carries the single hypothesis a = b
        assert_eq!(thm.hyps().len(), 1);
    }

    #[test]
    fn infers_free_var_types_without_fix() {
        // No `fix`: p, q are inferred `bool` from their use under `and`.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm and.comm.implicit
              (#concl (==> (and p q) (and q p)))
              (#proof
                (imp-intro (and p q)
                  (and-intro
                    (and-elim-r (assume (and p q)))
                    (and-elim-l (assume (and p q)))))))
            "#);
        assert_eq!(thm.concl(), crate::init::logic::and_comm().concl());
    }

    #[test]
    fn opens_a_loaded_theory_env() {
        // A separate script `(#import logic) (#open logic)`s the environment produced by the
        // `cov_theory!`-loaded `init::logic::cov`, and applies one of its
        // lemmas by name — demonstrating the exposed env + cross-theory
        // `(lemma …)` reference.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#import logic)
            (#open logic)
            (#thm use.and.comm
              (#concl (and b a))
              (#proof
                (imp-elim
                  (inst p a (inst q b (lemma and.comm)))
                  (assume (and a b)))))
            "#,
            |name| match name {
                "core" => Some(Env::core()),
                "logic" => Some(crate::init::logic::cov::env()),
                _ => None,
            },
            |_| None,
        )
        .expect("should replay against the opened `logic` env");
        assert_eq!(theory.thms.len(), 1);
        // {a ∧ b} ⊢ b ∧ a — carries the single hypothesis
        assert_eq!(theory.thms[0].thm.hyps().len(), 1);
        // the same exported env is reachable as a lazy static
        assert!(crate::init::logic::cov::ENV.has_lemma("and.comm"));
    }

    #[test]
    fn exists_intro_reified() {
        // The ∃-introduction derivation ported to the script layer:
        //   ⊢ ∀(P : 'a → bool). ∀(w : 'a). (P w) ⟹ (∃x. P x)
        // exercising the quantifier-operator form (`exists-op`), `unfold-at-1`
        // to unfold the `∃` definition, and the ∀/⟹ rules — the harder,
        // definition-unfolding case (cf. the propositional `and.comm`).
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm exists.intro
              (#concl
                (forall (P (fun 'a bool))
                  (forall (w 'a)
                    (==> (app P w) (app (exists-op 'a) P)))))
              (#proof
                (all-intro P (fun 'a bool)
                  (all-intro w 'a
                    (imp-intro (app P w)
                      (eq-mp
                        (sym (unfold-at-1 (exists-op 'a) P))
                        (all-intro q bool
                          (imp-intro (forall (x) (==> (app P x) q))
                            (imp-elim
                              (all-elim w (assume (forall (x) (==> (app P x) q))))
                              (assume (app P w)))))))))))
            "#);
        assert!(thm.hyps().is_empty(), "the reified ∃-intro rule is closed");
    }

    #[test]
    fn export_controls_the_public_env() {
        // Two lemmas are proven; only one is `(#export …)`ed, so only it is
        // in the exported env. Both still appear in `thms`.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#thm a (#concl true)
              (#proof (eq-mp (reduce-prim (= true true)) (refl true))))
            (#thm b (#concl (or p (not p))) (#proof (lem p)))
            (#export a)
            "#,
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .expect("should replay");
        let env = theory.env();
        assert!(env.has_lemma("a"), "exported lemma is public");
        assert!(!env.has_lemma("b"), "un-exported lemma stays internal");
        assert_eq!(theory.thms.len(), 2, "both lemmas were proven");
    }

    #[test]
    fn by_tactic_mode_proves_and_comm() {
        // Goal-directed: `intro` the implication, then `exact` a tree-mode
        // proof of the swapped conjunction. The `#by` block elaborates to
        // the same `Drv` the tree-mode `and.comm` produces.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm and.comm.by
              (#concl (==> (and p q) (and q p)))
              (#by
                (intro h)
                (derive
                  (and-intro
                    (and-elim-r (assume (and p q)))
                    (and-elim-l (assume (and p q)))))))
            "#);
        assert_eq!(thm.concl(), crate::init::logic::and_comm().concl());
    }

    #[test]
    fn by_intro_and_assumption() {
        // `intro` moves `p` into the context; `assumption` closes the goal.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm imp.refl.by
              (#concl (==> p p))
              (#by (intro h) (assumption)))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_intro_over_forall() {
        // ∀-introduction in tactic mode, closed by `refl`: ⊢ ∀(x:nat). x = x.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm eq.refl.by
              (#concl (forall (x nat) (= x x)))
              (#by (intro x) (refl)))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_have_brings_a_fact_into_context() {
        // `#have` proves an intermediate fact in (nested) tree mode and
        // makes it available; `assumption` then discharges the goal with it.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm dup.by
              (#concl (==> p (and p p)))
              (#by
                (intro h)
                (#have (and p p) (#proof (and-intro (assume p) (assume p))))
                (assumption)))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_multi_intro_and_sym() {
        // `intro a b h` peels three binders at once; `sym` swaps the
        // equation goal; `assumption` closes it with the hypothesis.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm eq.sym.by
              (#concl (forall (a nat) (forall (b nat) (==> (= a b) (= b a)))))
              (#by (intro a b h) (sym) (assumption)))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_not_intro() {
        // `not-intro` turns goal `¬F` into `F ⟹ F`.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm not.false.by
              (#concl (not false))
              (#by (not-intro) (intro h) (assumption)))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_induct_on_nat() {
        // The `induct` tactic: ⊢ ∀(n:nat). n = n, base + step both by `refl`.
        // Exercises the kernel's `nat_induct` plus the β-conv bookkeeping.
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm nat.eq.refl.by
              (#concl (forall (n nat) (= n n)))
              (#by (induct n (#by (refl)) (#by (refl)))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn conclusion_mismatch_is_caught() {
        let res = run_str(
            r#"
            (#import core)
            (#open core)
            (#thm wrong
              (#fix (p bool) (q bool))
              (#concl (and p q))
              (#proof (assume (and q p))))
            "#,
        );
        assert!(
            matches!(res, Err(ScriptError::ConclMismatch { .. })),
            "expected ConclMismatch, got {:?}",
            res.err()
        );
    }
}
