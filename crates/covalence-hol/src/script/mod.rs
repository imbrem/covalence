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
//! The pipeline is **author → replay**: the named term syntax (`syntax.rs`)
//! resolves catalogue names through [`Env`] (the `defs/` churn-absorber); a
//! proof S-expr is replayed by [`check`], which dispatches each head through
//! the [`Env`] **derivation registry** (`drv.rs`) — the only kernel-coupled
//! code. Nothing is trusted from the text — the kernel re-derives every
//! theorem. See `drv.rs`'s docs.
//!
//! Two directions are deliberately **not** built yet (see SKELETONS.md):
//! pretty-printing a proof / `Term` back to this syntax, and content-hashing
//! proof terms for lemma-by-hash references. Authoring (parse +
//! replay) is the immediate goal: porting the Rust `init/` theorems.

mod drv;
mod env;
mod handle;
mod inductive;
mod infer;
mod scope;
pub(crate) mod syntax;
pub(crate) mod tactic;
pub(crate) mod theory;
mod unify;

pub use drv::{CheckCtx, check, core_rules};
pub use env::{ConstDef, Env};
pub use scope::Scope;
pub use syntax::{parse_term, parse_type};
pub use tactic::{Hyp, Interp, Tactic};
pub use theory::{Model, SigOp, Signature, Spec, Theory as TheoryDecl};

use std::sync::Arc;

use covalence_core::{Thm, Type};
use covalence_sexp::SExpr;
use futures::FutureExt;

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
    /// The full running environment (its `lemmas` may still be `#spawn`-ing).
    internal: Env,
    /// The eagerly-checked theorems.
    pub thms: Vec<NamedThm>,
    /// Names of `(#spawn …)` theorems still deferred as cooperative async
    /// tasks, awaited from `internal` and folded into `thms` when forced.
    spawned_names: Vec<String>,
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
    /// still-`#spawn`-ing theorem (each a deferred cooperative task) and fold
    /// its result into `thms`. For a synchronous caller use
    /// [`LazyTheory::resolve_blocking`].
    pub async fn resolve(self) -> Result<Theory, ScriptError> {
        let LazyTheory {
            exports,
            internal,
            mut thms,
            mut spawned_names,
        } = self;
        // Await the background computations (in name order for determinism),
        // each looked up — and awaited — from the running env.
        spawned_names.sort();
        for name in spawned_names {
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
            spawned_names: Vec::new(),
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
            spawned_names: Vec::new(),
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
/// earlier ones — and any opened namespace's lemmas — via `(NAME)` (by name).
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
    let mut spawned_names: Vec<String> = Vec::new();
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
                // `check` awaits any lemma reference it makes that is still
                // `#spawn`-ing — lemma lookup is now async.
                let nt = run_thm(ch, &internal).await?;
                internal.define_lemma(nt.name.clone(), nt.thm.clone());
                thms.push(nt);
            }
            // `(#inductive NAME …)` — declare a datatype: elaborate it through
            // the active logic, then bind its constructors (as catalogue
            // constants) and its recursor/induction theorems (as lemmas) under
            // the `NAME.` prefix. The emitted theorems also accumulate in
            // `thms`, so a downstream proof can `(NAME.rec)`/`(NAME.induct)`.
            Stmt::Inductive(sexpr) => {
                use inductive::LogicInductive;
                let ch = syntax::list(&sexpr, "#inductive")?;
                let decl = inductive::parse_decl(ch)?;
                let elab = inductive::HolMetalogic.elaborate(&decl)?;
                for (local, c) in elab.ctors {
                    internal.define_const(format!("{}.{}", decl.name, local), c);
                }
                for (local, thm) in elab.thms {
                    let name = format!("{}.{}", decl.name, local);
                    internal.define_lemma(name.clone(), thm.clone());
                    thms.push(NamedThm { name, thm });
                }
            }
            // The four **definition directives** — inline term/type definitions
            // (`docs/surface-syntax.md §1.4`), the script-layer counterpart of
            // `covalence-core`'s `defs::cov` parser. Each elaborates its body
            // against the running env and binds the result, replacing the old
            // Rust `*_env()` / `*prim` givens pattern (a constant built in Rust
            // only to be referenced from `.cov`).
            Stmt::Def(sexpr) => def_directive(&sexpr, &mut internal)?,
            // Type definitions are inherently part of the public interface
            // (a downstream module that references the type by name needs to
            // see it), so they register into BOTH the running env and the
            // exports — unlike `#def`/`#thm`, which need an explicit `#export`.
            Stmt::Newtype(sexpr) => {
                let (name, spec) = newtype_directive(&sexpr, &internal)?;
                internal.define_type(name.clone(), spec.clone());
                exports.define_type(name, spec);
            }
            Stmt::Subtype(sexpr) => {
                let (name, spec) = subtype_directive(&sexpr, &internal)?;
                internal.define_type(name.clone(), spec.clone());
                exports.define_type(name, spec);
            }
            Stmt::Quot(sexpr) => {
                let (name, spec) = quot_directive(&sexpr, &internal)?;
                internal.define_type(name.clone(), spec.clone());
                exports.define_type(name, spec);
            }
            // `(#spawn NAME …)` — defer the proof as a cooperative async task
            // bound to NAME in the env. Execution moves straight on; a later
            // proof's `(NAME)` (by name) (or the force) simply **awaits** it,
            // polling it on the shared runtime. No blocking thread, no nested
            // `block_on` — any genuinely blocking work is the FFI tactic's own
            // responsibility (see SKELETONS.md / docs/surface-syntax.md).
            Stmt::Spawn(sexpr) => {
                let ch = syntax::list(&sexpr, "#spawn")?;
                let name = syntax::sym(&ch[1], "spawn name")?.to_string();
                let env = internal.clone();
                let fut = async move {
                    let ch = syntax::list(&sexpr, "#spawn")?;
                    run_thm(ch, &env).await.map(|nt| nt.thm)
                }
                .boxed();
                internal.define_spawned(name.clone(), fut);
                spawned_names.push(name);
            }
            // `(#export NAME …)` — build the public interface explicitly: each
            // name is a proven lemma or an imported lemma/const/tactic. A lemma
            // is **awaited** (so an exported `#spawn` lands ready).
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
            // `(#in MODEL STMT…)` — dispatch: open MODEL's namespace (its
            // operators + axioms + induction handler) on top of a fresh scope,
            // run each nested `#thm`, and bind the result under `MODEL.NAME`.
            // The SAME nested proof text dispatches to whichever model is named
            // — the surface form of the model-replay (`docs/surface-compiler.md`
            // §2/§3). Only `#thm` is supported inside a block today (enough to
            // replay `add_comm`); richer nesting is future work (SKELETONS).
            Stmt::In { model, body } => {
                let mut scoped = internal.clone();
                scoped.open(&model)?;
                for stmt in &body {
                    let ch = syntax::list(stmt, "#in body")?;
                    if syntax::head_sym(ch)? != "#thm" {
                        return Err(ScriptError::Syntax(format!(
                            "#in: only `#thm` is supported inside a `(#in {model} …)` block"
                        )));
                    }
                    let nt = run_thm(ch, &scoped).await?;
                    let qualified = format!("{model}.{}", nt.name);
                    // Bind under MODEL.NAME in the scoped env (so a later nested
                    // theorem can reference it) and accumulate for the caller.
                    scoped.define_lemma(qualified.clone(), nt.thm.clone());
                    internal.define_lemma(qualified.clone(), nt.thm.clone());
                    thms.push(NamedThm {
                        name: qualified,
                        thm: nt.thm,
                    });
                }
            }
            // `(#sig …)` — parse + register a signature declaration.
            Stmt::Sig(sexpr) => {
                let ch = syntax::list(&sexpr, "#sig")?;
                let sig = theory::parse_sig(ch, &internal)?;
                internal.define_signature(sig.name.clone(), sig);
            }
            // `(#thy …)` — parse + register a theory declaration (its axioms
            // validated against the signature's abstract vocabulary).
            Stmt::Thy(sexpr) => {
                let ch = syntax::list(&sexpr, "#thy")?;
                let thy = theory::parse_thy(ch, &internal)?;
                internal.define_theory_decl(thy.name.clone(), thy);
            }
            // `(#model …)` — parse + register a model declaration (interpretation
            // typechecked at the carrier; no axioms yet — that is `#models`).
            Stmt::Model(sexpr) => {
                let ch = syntax::list(&sexpr, "#model")?;
                let m = theory::parse_model(ch, &internal)?;
                internal.define_model_decl(m.name.clone(), m);
            }
            // `(#models M T …)` — certify `M ⊨ T`: prove each axiom at the
            // carrier (or pull from a `(from W)` witness), accumulate the
            // verified theorems under `M.axname`, and `#import` M's dispatch env
            // so a later `(#in M …)` opens it.
            Stmt::Models {
                model,
                theory: thy_name,
                clauses,
            } => {
                let m = internal.lookup_model_decl(&model).ok_or_else(|| {
                    ScriptError::Unbound(format!("#models: model `{model}` not declared"))
                })?;
                let thy = internal.lookup_theory_decl(&thy_name).ok_or_else(|| {
                    ScriptError::Unbound(format!("#models: theory `{thy_name}` not declared"))
                })?;
                let (dispatch_env, verified) =
                    theory::run_models(&m, &thy, &clauses, &internal).await?;
                // Register M's dispatch env as an importable namespace (so
                // `(#in M …)` can open it) and accumulate the certificates.
                internal.import(model.clone(), dispatch_env);
                for nt in verified {
                    let qualified = format!("{model}.{}", nt.name);
                    internal.define_lemma(qualified.clone(), nt.thm.clone());
                    thms.push(NamedThm {
                        name: qualified,
                        thm: nt.thm,
                    });
                }
            }
        }
    }
    Ok(LazyTheory {
        exports,
        internal,
        thms,
        spawned_names,
    })
}

/// Await every `(NAME)` (by name) reference in `sexpr` that is still
/// Fetch an imported namespace's environment, erroring if it was never
/// `(#import …)`ed.
fn imported(internal: &Env, name: &str) -> Result<Env, ScriptError> {
    internal
        .get_import(name)
        .cloned()
        .ok_or_else(|| ScriptError::Unbound(format!("environment not imported: `{name}`")))
}

/// Drive the async proof core to completion — the blocking half of the API.
/// Runs on a fresh **tokio** current-thread runtime, which is the scheduler the
/// prover is built on: cooperative concurrency (block a task → run another →
/// resume it) today, swappable for a multi-thread runtime when we want true
/// parallel verification.
///
/// Native only, and must not be called from inside an existing tokio runtime
/// (nesting panics). The `cov_theory!` loader force-evaluates its `import …`
/// envs eagerly — *before* this `block_on` — so forcing one `.cov` theory never
/// nests on forcing an imported one.
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
    /// `(#spawn NAME …)` — like `#thm`, but deferred as a **cooperative async
    /// task** that runs while later statements proceed; awaited when first
    /// referenced or when the theory is forced.
    Spawn(SExpr),
    /// `(#inductive NAME (ctor ARGTY…) …)` — declare a datatype and elaborate
    /// it (through the active logic) into its constructors + recursor +
    /// induction principle. See [`inductive`].
    Inductive(SExpr),
    /// `(#def NAME TERM)` — define a **term constant** `NAME ≡ TERM` inline
    /// (a `defs/` `TermSpec`), bound into the env so later proofs can use it
    /// and `unfold`/`delta` it. The TERM is the full directive's `SExpr`,
    /// elaborated against the running env at execution. See [`def_directive`].
    Def(SExpr),
    /// `(#newtype NAME TY)` — define a type `NAME := TY` (the carrier copied,
    /// no predicate), bound as a user type constructor.
    Newtype(SExpr),
    /// `(#subtype NAME TY PRED)` — define `NAME := { x : TY | PRED x }`.
    Subtype(SExpr),
    /// `(#quot NAME TY REL)` — define the quotient `NAME := TY / REL`.
    Quot(SExpr),
    /// `(#export NAME …)` — the public interface.
    Export(Vec<String>),
    /// `(#in MODEL STMT…)` — run the nested `#thm` statements with a
    /// previously-`#import`ed **model** namespace opened on top of scope, so
    /// `(induct …)`/`+`/`succ`/`0`/the axioms dispatch to that model's
    /// handlers + interpretation (`docs/surface-compiler.md` §2/§3). Each
    /// nested theorem is bound under the `MODEL.` prefix so multiple `#in`
    /// blocks (one per model) can replay the *same* proof without colliding.
    In { model: String, body: Vec<SExpr> },
    /// `(#sig NAME (sort α) (op …) …)` — declare a [signature](theory::Signature).
    Sig(SExpr),
    /// `(#thy NAME (over SIG) (axiom …) …)` — declare a [theory](theory::Theory).
    Thy(SExpr),
    /// `(#model NAME (of SIG) (carrier TY) (OP TERM) … (induct T))` — declare a
    /// [model](theory::Model) (pure interpretation, no axioms yet).
    Model(SExpr),
    /// `(#models M T (axname (#by …)) … | (from WITNESS))` — certify `M ⊨ T`:
    /// prove each axiom at the carrier, then register `M`'s dispatch env so
    /// `(#in M …)` opens it.
    Models {
        model: String,
        theory: String,
        clauses: Vec<SExpr>,
    },
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
        "#spawn" => Stmt::Spawn(e.clone()),
        "#inductive" => Stmt::Inductive(e.clone()),
        "#def" => Stmt::Def(e.clone()),
        "#newtype" => Stmt::Newtype(e.clone()),
        "#subtype" => Stmt::Subtype(e.clone()),
        "#quot" => Stmt::Quot(e.clone()),
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
        "#in" => {
            if ch.len() < 2 {
                return Err(ScriptError::Syntax(
                    "#in: expected (#in MODEL STMT…)".into(),
                ));
            }
            let model = syntax::sym(&ch[1], "model name")?.to_string();
            Stmt::In {
                model,
                body: ch[2..].to_vec(),
            }
        }
        "#sig" => Stmt::Sig(e.clone()),
        "#thy" => Stmt::Thy(e.clone()),
        "#model" => Stmt::Model(e.clone()),
        "#models" => {
            if ch.len() < 3 {
                return Err(ScriptError::Syntax(
                    "#models: expected (#models MODEL THEORY (axname (#by …)) … | (from W))".into(),
                ));
            }
            let model = syntax::sym(&ch[1], "model name")?.to_string();
            let theory = syntax::sym(&ch[2], "theory name")?.to_string();
            Stmt::Models {
                model,
                theory,
                clauses: ch[3..].to_vec(),
            }
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
                    // Force the import envs EAGERLY, before `run`'s `block_on`,
                    // so forcing this theory never nests its `block_on` on
                    // forcing an imported `.cov` theory (e.g. `logic`).
                    let __imports: ::std::vec::Vec<(&'static str, $crate::script::Env)> =
                        ::std::vec![ $( ($oname, $oenv), )* ];
                    $crate::script::run(
                        include_str!($src),
                        move |__name| {
                            __imports
                                .iter()
                                .find(|(__n, _)| *__n == __name)
                                .map(|(_, __e)| __e.clone())
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
            fix.push(infer::parse_binder_spec(v, env)?);
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

    // The proof body is `(#proof DERIV)` (tree mode) or `(#by STEP…)`
    // (goal-directed tactic mode). Tree mode replays a proof S-expr to a
    // `Thm`; tactic mode produces the `Thm` directly by driving the goal.
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

// ============================================================================
// Definition directives — `#def` / `#newtype` / `#subtype` / `#quot`
//
// The script-layer counterpart of `covalence_core::defs::cov`'s four-directive
// parser. They elaborate their body through the **script** elaborator
// (`syntax`/`infer`), so a `.cov` author writes definitions in the same richer
// surface syntax used for proofs (implicit types, named binders, catalogue
// references), and bind the result into the running `Env` for later directives.
// ============================================================================

use covalence_core::Term;
use covalence_core::defs::{TermSpec, TypeSpec};
use smol_str::SmolStr;

/// Elaborate a single closed term from a directive body against `env`.
fn elaborate_def_term(s: &SExpr, env: &Env) -> Result<Term, ScriptError> {
    let mut scope = Scope::new();
    syntax::parse_term(s, &mut scope, env)
}

/// `(#def NAME TERM)` — define a term constant `NAME ≡ TERM` as a `defs/`
/// [`TermSpec`] (an opaque-`SmolStr`-symbol defined constant), then bind it
/// into `env`. Because it is a genuine `TermSpec`, the constant carries a
/// δ-unfolding equation — so a later proof can `(unfold-at-* NAME …)` /
/// `(delta NAME)` it exactly like a hand-written `defs::*` constant. A body
/// with free type variables is registered **polymorphically** (`Poly`), so the
/// constant can appear at several type instances in one proof; a monomorphic
/// body is an `Op`.
fn def_directive(e: &SExpr, env: &mut Env) -> Result<(), ScriptError> {
    let ch = syntax::list(e, "#def")?;
    syntax::arity(ch, 3, "#def")?;
    let name = syntax::sym(&ch[1], "#def name")?.to_string();
    let body = elaborate_def_term(&ch[2], env)?;
    let ty = body.type_of()?;
    // Build the defined constant. Its free type variables (read off the
    // body's type) are the schematic parameters: instantiate the spec at
    // them so the stored constant is `Term::term_spec(spec, ['a, 'b…])`.
    let spec = TermSpec::new(SmolStr::from(name.as_str()), Some(ty.clone()), Some(body));
    let tvars = ty.free_tvars();
    let args: Vec<Type> = tvars.iter().map(|v| Type::tfree(v.clone())).collect();
    let constant = Term::term_spec(spec, args);
    let cdef = if tvars.is_empty() {
        ConstDef::Op(constant)
    } else {
        ConstDef::Poly(constant)
    };
    env.define_const(name, cdef);
    Ok(())
}

/// `(#newtype NAME TY)` — define an opaque copy of `TY` (`TypeSpec::newtype`),
/// returning the `(name, spec)` for the caller to bind.
fn newtype_directive(e: &SExpr, env: &Env) -> Result<(String, TypeSpec), ScriptError> {
    let ch = syntax::list(e, "#newtype")?;
    syntax::arity(ch, 3, "#newtype")?;
    let name = syntax::sym(&ch[1], "#newtype name")?.to_string();
    let base = parse_type(&ch[2], env)?;
    let spec = TypeSpec::newtype(SmolStr::from(name.as_str()), base);
    Ok((name, spec))
}

/// `(#subtype NAME TY PRED)` — define `NAME := { x : TY | PRED x }`
/// (`TypeSpec::subtype`), returning the `(name, spec)`.
fn subtype_directive(e: &SExpr, env: &Env) -> Result<(String, TypeSpec), ScriptError> {
    let ch = syntax::list(e, "#subtype")?;
    syntax::arity(ch, 4, "#subtype")?;
    let name = syntax::sym(&ch[1], "#subtype name")?.to_string();
    let carrier = parse_type(&ch[2], env)?;
    let pred = elaborate_def_term(&ch[3], env)?;
    let spec = TypeSpec::subtype(SmolStr::from(name.as_str()), carrier, pred);
    Ok((name, spec))
}

/// `(#quot NAME TY REL)` — define the quotient `NAME := TY / REL`
/// (`TypeSpec::quot`; the carrier is the powerset `TY → bool`), returning the
/// `(name, spec)`.
fn quot_directive(e: &SExpr, env: &Env) -> Result<(String, TypeSpec), ScriptError> {
    let ch = syntax::list(e, "#quot")?;
    syntax::arity(ch, 4, "#quot")?;
    let name = syntax::sym(&ch[1], "#quot name")?.to_string();
    let base = parse_type(&ch[2], env)?;
    let rel = elaborate_def_term(&ch[3], env)?;
    let spec = TypeSpec::quot(SmolStr::from(name.as_str()), base, rel);
    Ok((name, spec))
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
    fn rw_matches_a_quantified_equation() {
        // `rw` instantiates QUANTIFIED equations by matching their LHS against a
        // subterm of the goal — by BARE NAME (no `all-elim`, no wrapping list),
        // and several equations in one `rw`, applied in sequence.
        let thms = run_str(
            r#"(#import core)(#open core)
               (#thm idem   (#concl (forall (p bool) (= (and p p) p)))
                 (#by (intro p) (derive (prop-eq (and p p) p))))
               (#thm orself (#concl (forall (p bool) (= (or p p) p)))
                 (#by (intro p) (derive (prop-eq (or p p) p))))
               (#thm one  (#concl (= (and a a) a)) (#by (rw idem) (refl)))
               (#thm many (#concl (= (and (or a a) (or a a)) a))
                 (#by (rw orself idem) (refl)))"#,
        )
        .expect("rw-unification replays");
        assert_eq!(thms.len(), 4);
        for nt in &thms {
            assert!(nt.thm.hyps().is_empty(), "{} should be hyp-free", nt.name);
        }
    }

    #[test]
    fn apply_unifies_and_bare_lemma_names() {
        let thms = run_str(
            r#"(#import core)(#open core)
               (#thm my_refl (#concl (forall (n nat) (= n n)))
                 (#by (induct n (#by (refl)) (#by (refl)))))
               ;; apply by unification (tactic) — matches `∀n. n = n` against `5 = 5`
               (#thm five_a (#concl (= 5 5)) (#by (apply my_refl)))
               ;; bare lemma name + explicit witness (tree) — `(all-elim 5 (my_refl))`
               (#thm five_b (#concl (= 5 5)) (#proof (my_refl 5)))
               ;; apply as a derivation with an explicit target (tree)
               (#thm five_c (#concl (= 5 5)) (#proof (apply my_refl (= 5 5))))
               ;; apply with a premise discharged inline
               (#thm imp_self (#concl (forall (p bool) (==> p p))) (#by (intro p h) (assumption)))
               (#thm zero_eq (#concl (= 0 0)) (#by (apply imp_self (refl 0))))"#,
        )
        .expect("apply / bare-lemma script replays");
        assert_eq!(thms.len(), 6);
        for nt in &thms {
            assert!(nt.thm.hyps().is_empty(), "{} should be hyp-free", nt.name);
        }
    }

    #[test]
    fn spec_machinery_rules_replay() {
        // The subtype/spec rules added for porting the non-`nat` modules.
        // `eta-conv`: ⊢ (λx. succ x) = succ.
        let eta = one(r#"(#import core)(#open core)
               (#thm eta (#concl (= (lam (x nat) (succ x)) succ))
                 (#proof (eta-conv (lam (x nat) (succ x)))))"#);
        assert!(eta.hyps().is_empty());
        // `reduce`: full βι normal form — `(λx. x) 0` reduces to `0`.
        let red = one(r#"(#import core)(#open core)
               (#thm red (#concl (= (app (lam (x nat) x) 0) 0))
                 (#proof (reduce (app (lam (x nat) x) 0))))"#);
        assert!(red.hyps().is_empty());
    }

    #[test]
    fn exists_rules_replay() {
        // `exists-intro` reaches into `logic.cov`'s reified `exists_intro_thm`,
        // whose lazylock `block_on`s; force it once here (no runtime active) so
        // the cache is warm before `run_str`'s own `block_on` runs the rule. In
        // real `.cov` modules importing "logic" the macro forces it eagerly.
        let _ = crate::init::logic::exists_intro_thm();
        // `exists-intro`: from `⊢ (λx. x = 0) 0` (got from `⊢ 0 = 0` by undoing
        // the β-step) conclude `⊢ ∃x. x = 0`.
        let intro = one(
            r#"(#import core)(#open core)
               (#thm ex (#concl (exists (x nat) (= x 0)))
                 (#proof
                   (exists-intro
                     (lam (x nat) (= x 0))
                     0
                     (eq-mp (sym (beta-conv (app (lam (x nat) (= x 0)) 0))) (refl 0)))))"#,
        );
        assert!(intro.hyps().is_empty());
        // `exists-elim`: from `⊢ ∃x. x = 0` and the step
        // `⊢ ∀x. (λx. x = 0) x ⟹ ∃y. y = 0` conclude `⊢ ∃y. y = 0` (here the
        // two existentials coincide). The step re-introduces the existential
        // straight from the assumed predicate application (which, locally
        // nameless, is literally `(λ. #0 = 0) x` — the same term either way).
        let elim = one(
            r#"(#import core)(#open core)
               (#thm ex2 (#concl (exists (y nat) (= y 0)))
                 (#proof
                   (exists-elim
                     (exists-intro
                       (lam (x nat) (= x 0)) 0
                       (eq-mp (sym (beta-conv (app (lam (x nat) (= x 0)) 0))) (refl 0)))
                     (exists (y nat) (= y 0))
                     (all-intro x nat
                       (imp-intro (app (lam (x nat) (= x 0)) x)
                         (exists-intro
                           (lam (y nat) (= y 0)) x
                           (assume (app (lam (x nat) (= x 0)) x))))))))"#,
        );
        assert!(elim.hyps().is_empty());
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
        // The S-expression rewrite of `init::logic::and_comm_mp` (the
        // implication direction; `and.comm` itself is now the EQUATION).
        let thm = one(r#"
            (#import core)
            (#open core)
            (#thm and.comm.mp
              (#fix (p bool) (q bool))
              (#concl (==> (and p q) (and q p)))
              (#proof
                (imp-intro (and p q)
                  (and-intro
                    (and-elim-r (assume (and p q)))
                    (and-elim-l (assume (and p q)))))))
            "#);
        assert!(thm.hyps().is_empty(), "and.comm.mp must be hypothesis-free");
        // It must match the hand-written Rust theorem exactly.
        let rust = crate::init::logic::and_comm_mp();
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
    fn one_inference_serves_both_modes_and_errors_when_misused() {
        // `tauto` is a single dual-mode inference: tactic mode `(tauto)` and
        // tree mode `(tauto TERM)` are two facets of one registered object.
        // Opening `logic` brings BOTH (core carries only the tree facet).
        // Force logic's `ENV` lazylock *outside* `run`'s runtime first (it
        // `block_on`s) so the in-`run` resolver call is a cheap clone.
        let _ = crate::init::logic::cov::env();
        let resolver = |name: &str| match name {
            "core" => Some(Env::core()),
            "logic" => Some(crate::init::logic::cov::env()),
            _ => None,
        };
        let theory = run(
            r#"
            (#import core)(#open core)
            (#import logic)(#open logic)
            (#thm tree (#fix (p bool)) (#concl (==> p p)) (#proof (tauto (==> p p))))
            (#thm tac  (#fix (p bool)) (#concl (==> p p)) (#by (tauto)))
            "#,
            resolver,
            |_| None,
        )
        .expect("tauto works in both modes via logic");
        assert_eq!(theory.thms.len(), 2);

        // Using a TREE-only rule (`trans`) as a tactic hits the default
        // "cannot be used as a `#by` tactic" error — not a silent wrong answer.
        let misused = run_str("(#import core)(#open core)(#thm t (#concl (= 0 0)) (#by (trans)))");
        assert!(misused.is_err(), "a rule-only inference is not a tactic");
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
                  (inst p a (inst q b (logic.and.comm.mp)))
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
    fn spawn_runs_in_the_background_and_lands_on_resolve() {
        // A `#spawn`ed theorem is deferred as a cooperative task while later
        // statements proceed; it is NOT in `thms` until the theory is forced.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#thm eager (#concl (= 1 1)) (#proof (refl 1)))
            (#spawn slow (#concl (= (nat.add 2 3) 5))
              (#proof (reduce-prim (nat.add 2 3))))
            "#,
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .unwrap();
        assert!(theory.thms.iter().any(|nt| nt.name == "eager"));
        assert!(
            !theory.thms.iter().any(|nt| nt.name == "slow"),
            "the #spawn is still pending pre-force"
        );
        let resolved = theory
            .resolve_blocking()
            .expect("forcing awaits the spawned proof");
        assert!(resolved.thms.iter().any(|nt| nt.name == "slow"));
        assert!(resolved.thms.iter().any(|nt| nt.name == "eager"));
    }

    #[test]
    fn a_proof_awaits_a_spawned_lemma() {
        // A later `#thm` references a `#spawn`ed theorem via a lemma reference:
        // the lemma registry rule AWAITS the still-pending lemma directly
        // (lemma lookup is async), so `#spawn`ed lemmas are usable by later
        // proofs — cooperatively, with no blocking thread.
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#spawn base (#concl (= 0 0)) (#proof (refl 0)))
            (#thm uses (#concl (= 0 0)) (#proof (base)))
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
        impl Tactic for YieldId {
            // Override only the tree-mode (`rule`) facet; `apply` defaults to
            // the "not a tactic" error.
            async fn rule(
                &self,
                args: &[SExpr],
                ctx: &mut CheckCtx<'_>,
            ) -> Result<Thm, ScriptError> {
                tokio::task::yield_now().await; // genuine mid-derivation await
                let first = args
                    .first()
                    .ok_or_else(|| ScriptError::Syntax("yield-id: needs one arg".into()))?;
                ctx.check(first).await // self-parse + check the sub-derivation
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
    fn spawn_failure_surfaces_on_resolve() {
        // A `#spawn` whose proof is wrong errors only when forced.
        let theory = run(
            r#"
            (#import core)(#open core)
            (#spawn bad (#concl (= 1 2)) (#proof (refl 1)))
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
        assert_eq!(thm.concl(), crate::init::logic::and_comm_mp().concl());
    }

    #[test]
    fn opens_a_loaded_theory_env() {
        // A separate script `(#import logic) (#open logic)`s the environment produced by the
        // `cov_theory!`-loaded `init::logic::cov`, and applies one of its
        // lemmas by name — demonstrating the exposed env + cross-theory
        // a lemma reference reference.
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
                  (inst p a (inst q b (and.comm.mp)))
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
        // the same derivation the tree-mode `and.comm` produces.
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
        assert_eq!(thm.concl(), crate::init::logic::and_comm_mp().concl());
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

    // ========================================================================
    // Equational-reasoning primitives: beta / congr / funext / #comp.
    // ========================================================================

    #[test]
    fn beta_rule_normalizes_a_redex() {
        // Tree mode: `(beta TERM)` → ⊢ TERM = βnf(TERM), a *full* normal form
        // (beyond the kernel one-shot `beta-conv`): the nested redex
        // `(λx. (λy. y) x) 0` β-normalizes to `0` in one `beta` step.
        let thm = one(r#"
            (#import core)(#open core)
            (#thm b (#concl (= (app (lam (x nat) (app (lam (y nat) y) x)) 0) 0))
              (#proof (beta (app (lam (x nat) (app (lam (y nat) y) x)) 0))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn beta_tactic_closes_a_convertible_goal() {
        // Tactic mode: `(beta)` closes an equation whose two sides share a
        // β-normal form. `(λx. x) 0 = 0` — LHS reduces to RHS.
        let thm = one(r#"
            (#import core)(#open core)
            (#thm bt (#concl (= (app (lam (x nat) x) 0) 0))
              (#by (beta)))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn congr_builds_an_n_ary_congruence() {
        // `(congr HEAD EQ1 EQ2)` → ⊢ HEAD a1 a2 = HEAD b1 b2 from the two
        // argument equations. Here `nat.add (0+0) (0+0) = nat.add 0 0` from two
        // copies of `⊢ 0 + 0 = 0` (via reduce-prim).
        let thm = one(r#"
            (#import core)(#open core)
            (#thm cg
              (#concl (= (nat.add (nat.add 0 0) (nat.add 0 0)) (nat.add 0 0)))
              (#proof
                (congr nat.add
                  (reduce-prim (nat.add 0 0))
                  (reduce-prim (nat.add 0 0)))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn funext_rule_from_pointwise_forall() {
        // Tree mode: `(funext SUB)` where SUB : ⊢ ∀x. (λy.y) x = (λz.z) x.
        // Both functions are the identity, so funext yields ⊢ (λy.y) = (λz.z).
        // The pointwise equality is proved by β on each side.
        let thm = one(r#"
            (#import core)(#open core)
            (#thm fe
              (#concl (= (lam (y nat) y) (lam (z nat) z)))
              (#proof
                (funext
                  (all-intro x nat
                    (trans
                      (beta-conv (app (lam (y nat) y) x))
                      (sym (beta-conv (app (lam (z nat) z) x))))))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn funext_tactic_reduces_goal_to_a_point() {
        // Tactic mode: `(funext x)` turns goal `(λy.y) = (λz.z)` into the
        // pointwise goal `(λy.y) x = (λz.z) x`, closed by `beta`.
        let thm = one(r#"
            (#import core)(#open core)
            (#thm fet
              (#concl (= (lam (y nat) y) (lam (z nat) z)))
              (#by (funext x) (beta)))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn comp_chain_folds_trans() {
        // `#comp` chains explicit equational steps, folding `trans`.
        //   2+3 = 5 (reduce-prim) ; 5 = 5 (refl) — ⊢ 2+3 = 5.
        let thm = one(r#"
            (#import core)(#open core)
            (#thm cc (#concl (= (nat.add 2 3) 5))
              (#proof
                (#comp (nat.add 2 3)
                  (= 5 (reduce-prim (nat.add 2 3)))
                  (= 5 (refl 5)))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn comp_default_handler_closes_omitted_steps() {
        // An omitted justification is closed by the equational default
        // (β-convertibility): `(λx.x) 0 = 0` closes with no `BY`.
        let thm = one(r#"
            (#import core)(#open core)
            (#thm cd (#concl (= (app (lam (x nat) x) 0) 0))
              (#proof
                (#comp (app (lam (x nat) x) 0)
                  (= 0))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn comp_by_sets_a_block_default() {
        // `#:by` sets a block default justification applied to every omitted
        // step. Here `beta` reduces `(λx.x) 0 → 0`.
        let thm = one(r#"
            (#import core)(#open core)
            (#thm cb (#concl (= (app (lam (x nat) x) 0) 0))
              (#proof
                (#comp (app (lam (x nat) x) 0) #:by (beta (app (lam (x nat) x) 0))
                  (= 0))))
            "#);
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn comp_unclosable_step_is_a_clear_error() {
        // A step the default handler cannot close is a diagnostic pointing at
        // that step — never a silent gap. `0 = 1` is not β-convertible.
        let bad = run_str(r#"
            (#import core)(#open core)
            (#thm bad (#concl (= 0 1))
              (#proof (#comp 0 (= 1))))
            "#);
        assert!(matches!(bad, Err(ScriptError::Syntax(m)) if m.contains("#comp")),
            "an un-closable #comp step must error mentioning #comp");
    }

    #[test]
    fn comp_mismatched_justification_errors() {
        // An explicit justification that proves the wrong equation is rejected
        // (the chain term, not the justification, drives the conclusion).
        let bad = run_str(r#"
            (#import core)(#open core)
            (#thm bad (#concl (= (nat.add 2 3) 5))
              (#proof
                (#comp (nat.add 2 3)
                  (= 5 (reduce-prim (nat.add 1 1))))))
            "#);
        assert!(matches!(bad, Err(ScriptError::Syntax(_))),
            "a justification proving a different equation must error");
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

    // ====================================================================
    // Definition directives — `#def` / `#newtype` / `#subtype` / `#quot`
    // ====================================================================

    /// Run a script over `core` and return its (exported) environment.
    fn run_env(src: &str) -> Env {
        run(src, |name| (name == "core").then(Env::core), |_| None)
            .expect("script should replay")
            .resolve_blocking()
            .expect("force")
            .env()
    }

    /// Pull the defining body (`TermSpec::tm`) out of a `#def`-introduced
    /// constant exported under `name`.
    fn def_body(env: &Env, name: &str) -> Term {
        let c = env.lookup_const(name).expect("const exported");
        let constant = match &c {
            ConstDef::Op(t) | ConstDef::Poly(t) => t.clone(),
            ConstDef::Eq => panic!("not a defined const"),
        };
        let (spec, _) = constant.as_spec().expect("a TermSpec leaf");
        spec.tm().expect("defined body").clone()
    }

    /// `#def` binds a usable term constant: a later `#thm` can apply it and
    /// `unfold`/`delta` it (it is a genuine `defs/` `TermSpec`).
    #[test]
    fn def_directive_defines_a_usable_constant() {
        // `myand ≡ λp q. p ∧ q`; the `#def`'d constant is a genuine `TermSpec`,
        // so `unfold-at-2` δ-unfolds + β-reduces it to its body `and T F`.
        let theory = run(
            r#"
            (#import core)(#open core)
            (#def myand (lam (p bool) (lam (q bool) (and p q))))
            (#thm unfolds
              (#concl (= (myand true false) (and true false)))
              (#proof (unfold-at-2 myand true false)))
            "#,
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .expect("def + use replays");
        assert_eq!(theory.thms.len(), 1);
        assert!(theory.thms[0].thm.hyps().is_empty());
    }

    /// A polymorphic `#def` body is registered `Poly` — usable at two distinct
    /// type instances in one proof.
    #[test]
    fn def_directive_polymorphic_constant() {
        let env = run_env(
            r#"
            (#import core)(#open core)
            (#def myid (lam (x 'a) x))
            (#export myid)
            "#,
        );
        let c = env.lookup_const("myid").expect("myid exported");
        assert!(matches!(c, ConstDef::Poly(_)), "polymorphic def is Poly");
    }

    /// **Equivalence test (deliverable 3).** A `#def` in the covalence-hol
    /// script layer and the same directive interpreted by the covalence-core
    /// synchronous `.cov` system produce the **same** kernel body: both resolve
    /// the connectives to the cached `defs::*` accessors, so the two bodies are
    /// byte-identical (`==`, which bottoms out in pointer identity on the
    /// catalogue spec leaves they reference).
    #[test]
    fn script_def_agrees_with_core_cov() {
        use covalence_core::defs::cov;

        // Script side: `#def myand (lam (p bool) (lam (q bool) (and p q)))`.
        let env = run_env(
            r#"
            (#import core)(#open core)
            (#def myand (lam (p bool) (lam (q bool) (and p q))))
            (#export myand)
            "#,
        );
        let script_body = def_body(&env, "myand");

        // Core side: the same directive in the core `.cov` sublanguage
        // (`#lam`, `bool.and`).
        let core_env = cov::parse_core(
            "(#def myand (#lam (p bool) (#lam (q bool) (bool.and p q))))",
        )
        .expect("core .cov parses");
        let core_body = core_env.term("myand").expect("core myand").clone();

        assert_eq!(
            script_body, core_body,
            "script `#def` and core `#def` must agree byte-for-byte"
        );
    }

    /// `#newtype` binds a user type constructor that later directives /
    /// proofs can name.
    #[test]
    fn newtype_directive_defines_a_type() {
        let env = run_env(
            r#"
            (#import core)(#open core)
            (#newtype mynat nat)
            "#,
        );
        let spec = env.lookup_type_spec("mynat").expect("mynat defined");
        assert_eq!(spec.symbol().label(), "mynat");
        assert_eq!(spec.ty().unwrap(), &Type::nat());
    }

    /// `#subtype` over `core`-defined connectives, matching the core `.cov`
    /// `#subtype` shape (the `unit` singleton `{ b : bool | b = T }`).
    #[test]
    fn subtype_directive_matches_core_carrier_and_pred() {
        use covalence_core::defs::cov;

        let env = run_env(
            r#"
            (#import core)(#open core)
            (#subtype myunit bool (lam (b bool) (= b true)))
            "#,
        );
        let script_spec = env.lookup_type_spec("myunit").expect("myunit defined");

        let core_env = cov::parse_core(
            "(#subtype myunit bool (#lam (b bool) (#eq b T)))",
        )
        .expect("core .cov parses");
        let core_spec = core_env.type_spec("myunit").expect("core myunit").clone();

        // Carrier + predicate agree (the symbol differs only by identity).
        assert_eq!(script_spec.ty(), core_spec.ty());
        assert_eq!(script_spec.tm(), core_spec.tm());
    }

    /// `#quot` builds a quotient type-spec end-to-end (carrier is the powerset
    /// `nat → bool`).
    #[test]
    fn quot_directive_defines_a_quotient() {
        let env = run_env(
            r#"
            (#import core)(#open core)
            (#quot mynateq nat (lam (x nat) (lam (y nat) (= x y))))
            "#,
        );
        let spec = env.lookup_type_spec("mynateq").expect("mynateq defined");
        assert_eq!(spec.symbol().label(), "mynateq");
        assert_eq!(spec.ty().unwrap(), &Type::fun(Type::nat(), Type::bool()));
    }

    /// A later directive / proof can *reference* a `#newtype`'d type by name:
    /// `(mypair)` resolves to its `Type::spec` leaf, usable in a binder.
    #[test]
    fn defined_type_is_referenceable_downstream() {
        let theory = run(
            r#"
            (#import core)(#open core)
            (#newtype mybool bool)
            (#def onmybool (lam (x mybool) x))
            (#thm refl.mybool
              (#concl (= onmybool onmybool))
              (#proof (refl onmybool)))
            "#,
            |name| (name == "core").then(Env::core),
            |_| None,
        )
        .expect("a #newtype'd type is usable in a later #def + #thm");
        assert_eq!(theory.thms.len(), 1);
    }
}
