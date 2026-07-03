//! `project` — compiling a **multi-file `.cov` project** as one unit.
//!
//! Today each `.cov` theory is wired by hand: a `cov_theory!` block names its
//! `import …` dependencies and a [`crate::init::library_env`] match arm maps a
//! string name to a pre-built [`Env`]. The dependency order is implicit in the
//! Rust call graph and the `LazyLock` forcing order — there is no project-level
//! dependency graph and no topological build.
//!
//! This module is the first concrete step toward the vision in
//! [`notes/vibes/cov-project.md`]: a single [`compile_project`] entry point that takes
//! a set of `.cov` sources (plus the Rust-supplied "seam" envs / FFI tactics
//! they need), reads the `(#import NAME)` edges **out of the sources
//! themselves**, builds the dependency graph, topologically orders it, and
//! checks each theory through the real kernel — earlier theories' exported
//! environments feeding later ones automatically.
//!
//! What it covers today (the most concrete win):
//!
//! - **`.cov` → `.cov` import ordering.** A project is a graph of `.cov`
//!   sources connected by `(#import NAME)`; we compile them in dependency
//!   order with no hand-written ordering and no `library_env` arm per theory.
//! - **`.cov` → Rust seam envs / tactics.** A `.cov` may import a
//!   Rust-supplied [`Env`] (the `natrec` / `ratprim` / `setprim` "givens"
//!   pattern) or an FFI [`Tactic`] (`tauto`); these are registered as project
//!   inputs and resolved the same way.
//!
//! What is **deferred** (see `SKELETONS.md`): the *reverse* edge — Rust code
//! that depends on a `.cov`-defined constant/theorem — and therefore genuine
//! mutual recursion between a Rust module and a `.cov` file (the two-phase /
//! SCC fixpoint described in the design doc), plus the longer-term framing of a
//! Covalence project as a WASM component compiled against an abstract API and
//! distributed via Cargo features. See [`notes/vibes/cov-project.md`].

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::script::{Env, NamedThm, ScriptError, Tactic};

/// One source unit in a project: a name and its `.cov` text.
///
/// The name is what other units `(#import …)` and what the host uses to look
/// the compiled environment back up. The source is checked verbatim through
/// the kernel — nothing in it is trusted.
#[derive(Clone)]
pub struct CovSource {
    /// The unit's name — the `(#import …)` target other units use.
    pub name: String,
    /// The `.cov` source text (e.g. from `include_str!`).
    pub src: String,
}

impl CovSource {
    /// A source unit from a name and its text.
    pub fn new(name: impl Into<String>, src: impl Into<String>) -> Self {
        CovSource {
            name: name.into(),
            src: src.into(),
        }
    }
}

/// A project to compile: a set of `.cov` source units plus the Rust-supplied
/// inputs they may import.
///
/// - **`sources`** — the `.cov` units. Their `(#import NAME)` edges to *other*
///   units are discovered automatically (the dependency graph).
/// - **`rust_envs`** — Rust-supplied "seam" environments (the `natrec` /
///   `ratprim` / `setprim` givens; or `core`). A `.cov`'s `(#import NAME)`
///   resolves here when `NAME` is not another source unit. These are project
///   *leaves* — they have no `.cov` body and are always available.
/// - **`tactics`** — Rust-supplied FFI tactics (e.g. `tauto`), resolved by
///   `(#register-ffi-tactic NAME)`.
///
/// `core` need not be listed: it is always provided (`Env::core()`).
#[derive(Default)]
pub struct Project {
    sources: Vec<CovSource>,
    rust_envs: BTreeMap<String, Env>,
    tactics: BTreeMap<String, Arc<dyn Tactic>>,
}

/// A compiled project: every unit's exported [`Env`] plus the full list of
/// checked theorems, in topological (dependency-first) order.
pub struct CompiledProject {
    /// Each unit's exported environment, by unit name. Downstream Rust (or a
    /// later compile) can pull a `.cov`-defined lemma/const out of these.
    pub envs: BTreeMap<String, Env>,
    /// Every theorem checked across the whole project, unit by unit, in the
    /// order the units were compiled (dependencies first).
    pub thms: Vec<(String, Vec<NamedThm>)>,
    /// The topological order the units were compiled in (for diagnostics).
    pub order: Vec<String>,
}

impl CompiledProject {
    /// The exported environment of unit `name`, if it compiled.
    pub fn env(&self, name: &str) -> Option<&Env> {
        self.envs.get(name)
    }

    /// Total number of checked theorems across all units.
    pub fn thm_count(&self) -> usize {
        self.thms.iter().map(|(_, t)| t.len()).sum()
    }
}

/// Errors specific to assembling and ordering a project, plus a pass-through
/// for a unit's own kernel/script failure (carrying the unit name).
#[derive(Debug, thiserror::Error)]
pub enum ProjectError {
    /// A unit `(#import NAME)`ed a name that is neither another source unit nor
    /// a registered Rust env (and is not `core`).
    #[error(
        "unit `{unit}` imports `{missing}`, which is not a project source or a registered Rust env"
    )]
    UnknownImport { unit: String, missing: String },
    /// The import graph has a cycle: the listed units mutually depend with no
    /// dependency-free entry point. (Mutual recursion between units is the
    /// deferred two-phase/SCC case — see `SKELETONS.md`.)
    #[error("import cycle among units: {0:?}")]
    Cycle(Vec<String>),
    /// Two source units share a name.
    #[error("duplicate project unit name: `{0}`")]
    DuplicateUnit(String),
    /// A unit failed to parse or check through the kernel.
    #[error("unit `{unit}`: {source}")]
    Unit {
        unit: String,
        #[source]
        source: ScriptError,
    },
}

impl Project {
    /// An empty project.
    pub fn new() -> Self {
        Project::default()
    }

    /// Add a `.cov` source unit.
    pub fn source(mut self, name: impl Into<String>, src: impl Into<String>) -> Self {
        self.sources.push(CovSource::new(name, src));
        self
    }

    /// Register a Rust-supplied seam environment under `name` (a project leaf —
    /// the `natrec` / `ratprim` / `setprim` givens pattern, or any pre-built
    /// `Env` a `.cov` may `(#import …)`).
    pub fn rust_env(mut self, name: impl Into<String>, env: Env) -> Self {
        self.rust_envs.insert(name.into(), env);
        self
    }

    /// Register a Rust-supplied FFI tactic under `name` (resolved by
    /// `(#register-ffi-tactic NAME)` inside a unit).
    pub fn tactic(mut self, name: impl Into<String>, tac: Arc<dyn Tactic>) -> Self {
        self.tactics.insert(name.into(), tac);
        self
    }

    /// The set of names a unit imports, read out of its `(#import NAME)`
    /// directives. Best-effort: a source that fails to parse here will fail
    /// the same way (with a precise error) when it is compiled, so we return
    /// what parsed and let the compile pass surface the syntax error.
    fn imports_of(src: &str) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        let Ok(forms) = covalence_sexp::parse(src) else {
            return out;
        };
        for form in &forms {
            if let Some(items) = form.as_list()
                && items.first().and_then(|s| s.as_symbol()) == Some("#import")
                && let Some(name) = items.get(1).and_then(|s| s.as_symbol())
            {
                out.insert(name.to_string());
            }
        }
        out
    }

    /// Build the dependency graph (unit → the *other source units* it imports),
    /// validating every import resolves to a source unit, a registered Rust
    /// env, or `core`.
    ///
    /// Imports of Rust envs / `core` are NOT graph edges — those leaves are
    /// always available — but they are still validated here so a typo fails
    /// before any kernel work.
    fn dep_graph(&self) -> Result<BTreeMap<String, BTreeSet<String>>, ProjectError> {
        let unit_names: BTreeSet<&str> = self.sources.iter().map(|s| s.name.as_str()).collect();
        if unit_names.len() != self.sources.len() {
            // Find the first duplicate for a precise message.
            let mut seen = BTreeSet::new();
            for s in &self.sources {
                if !seen.insert(s.name.clone()) {
                    return Err(ProjectError::DuplicateUnit(s.name.clone()));
                }
            }
        }
        let mut graph: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for s in &self.sources {
            let mut edges = BTreeSet::new();
            for imp in Self::imports_of(&s.src) {
                if unit_names.contains(imp.as_str()) {
                    edges.insert(imp); // a `.cov` → `.cov` edge
                } else if imp == "core" || self.rust_envs.contains_key(&imp) {
                    // a leaf (always-available) input — not a graph edge
                } else {
                    return Err(ProjectError::UnknownImport {
                        unit: s.name.clone(),
                        missing: imp,
                    });
                }
            }
            graph.insert(s.name.clone(), edges);
        }
        Ok(graph)
    }

    /// Topologically order the units so each comes after every unit it imports.
    /// Deterministic (units are visited in name order). Errors with the
    /// remaining units if a cycle prevents a complete ordering.
    fn topo_order(graph: &BTreeMap<String, BTreeSet<String>>) -> Result<Vec<String>, ProjectError> {
        // Kahn's algorithm over in-degree, with a name-sorted ready set for
        // determinism. `graph[u]` is the set of units `u` depends ON, so an
        // edge dep → u means u becomes ready once dep is done.
        let mut indegree: BTreeMap<&str, usize> = graph
            .iter()
            .map(|(u, deps)| (u.as_str(), deps.len()))
            .collect();
        // ready = units with no outstanding dependencies, kept sorted.
        let mut ready: BTreeSet<&str> = indegree
            .iter()
            .filter(|&(_, &d)| d == 0)
            .map(|(&u, _)| u)
            .collect();
        // Reverse adjacency: dep → units that depend on it.
        let mut dependents: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for (u, deps) in graph {
            for dep in deps {
                dependents.entry(dep.as_str()).or_default().push(u.as_str());
            }
        }
        let mut order = Vec::with_capacity(graph.len());
        while let Some(&next) = ready.iter().next() {
            ready.remove(next);
            order.push(next.to_string());
            if let Some(deps) = dependents.get(next) {
                for &d in deps {
                    let e = indegree.get_mut(d).unwrap();
                    *e -= 1;
                    if *e == 0 {
                        ready.insert(d);
                    }
                }
            }
        }
        if order.len() != graph.len() {
            // The units never reaching in-degree 0 form (or feed) the cycle.
            let mut remaining: Vec<String> = graph
                .keys()
                .filter(|u| !order.contains(*u))
                .cloned()
                .collect();
            remaining.sort();
            return Err(ProjectError::Cycle(remaining));
        }
        Ok(order)
    }

    /// Compile the whole project: build + order the dependency graph, then
    /// check each unit through the real kernel in dependency order, threading
    /// each compiled unit's exported [`Env`] to the units that import it.
    ///
    /// Returns the per-unit exported environments and every checked theorem.
    /// Every theorem is re-derived by the kernel — the sources are untrusted.
    pub fn compile(self) -> Result<CompiledProject, ProjectError> {
        let graph = self.dep_graph()?;
        let order = Self::topo_order(&graph)?;

        // Compiled units' exported envs, accumulated as we go (a later unit's
        // `(#import NAME)` of an earlier unit resolves out of here).
        let mut compiled_envs: BTreeMap<String, Env> = BTreeMap::new();
        let mut thms: Vec<(String, Vec<NamedThm>)> = Vec::new();

        // Index sources by name for the compile loop.
        let by_name: BTreeMap<&str, &CovSource> =
            self.sources.iter().map(|s| (s.name.as_str(), s)).collect();

        for unit in &order {
            let source = by_name[unit.as_str()];
            // Resolver: `core` → the prelude; a compiled sibling unit → its
            // exported env; a registered Rust seam env → itself.
            let compiled_envs_ref = &compiled_envs;
            let rust_envs_ref = &self.rust_envs;
            let resolver = move |name: &str| -> Option<Env> {
                if name == "core" {
                    return Some(Env::core());
                }
                if let Some(e) = compiled_envs_ref.get(name) {
                    return Some(e.clone());
                }
                rust_envs_ref.get(name).cloned()
            };
            let tactics_ref = &self.tactics;
            let tactics =
                move |name: &str| -> Option<Arc<dyn Tactic>> { tactics_ref.get(name).cloned() };

            let theory = crate::script::run(&source.src, resolver, tactics)
                .and_then(|t| t.resolve_blocking())
                .map_err(|source| ProjectError::Unit {
                    unit: unit.clone(),
                    source,
                })?;

            compiled_envs.insert(unit.clone(), theory.env());
            // `theory.thms` is consumed; collect names+thms for the report.
            let unit_thms = theory.thms;
            thms.push((unit.clone(), unit_thms));
        }

        Ok(CompiledProject {
            envs: compiled_envs,
            thms,
            order,
        })
    }
}

/// Compile a project of `.cov` sources (with optional Rust seam envs / FFI
/// tactics) as one unit — the free-function form of [`Project::compile`].
///
/// This is the prototype of the single `compile_project(…)` entry point the
/// design doc envisions: pass the `.cov` units and the Rust inputs they need,
/// get back the compiled environments + checked theorems, with dependency
/// ordering handled automatically.
pub fn compile_project(
    sources: impl IntoIterator<Item = CovSource>,
    rust_envs: impl IntoIterator<Item = (String, Env)>,
    tactics: impl IntoIterator<Item = (String, Arc<dyn Tactic>)>,
) -> Result<CompiledProject, ProjectError> {
    let mut p = Project::new();
    for s in sources {
        p.sources.push(s);
    }
    for (name, env) in rust_envs {
        p.rust_envs.insert(name, env);
    }
    for (name, tac) in tactics {
        p.tactics.insert(name, tac);
    }
    p.compile()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A chained two-unit project: `base` proves a lemma and exports it;
    /// `mid` imports `base`, uses that lemma by name, and proves its own. The
    /// loader must discover the `base → mid` edge from `mid`'s `(#import base)`,
    /// compile `base` first, and thread its env into `mid` — all through the
    /// real kernel.
    #[test]
    fn chained_two_units_compile_in_order() {
        let base = CovSource::new(
            "base",
            r#"
            (#import core)
            (#open core)
            (#thm base.refl (#concl (= 0 0)) (#proof (refl 0)))
            (#export base.refl)
            "#,
        );
        // `mid` depends on `base`; its proof references `base`'s exported lemma
        // by name (`(base.refl)`), so it only checks if `base` compiled first
        // and its env was threaded in.
        let mid = CovSource::new(
            "mid",
            r#"
            (#import core)
            (#open core)
            (#import base)
            (#open base)
            (#thm mid.uses (#concl (= 0 0)) (#proof (base.refl)))
            (#export mid.uses)
            "#,
        );

        // Deliberately list `mid` BEFORE `base` to prove ordering is by graph,
        // not by input order.
        let compiled = Project::new()
            .source(mid.name.clone(), mid.src.clone())
            .source(base.name.clone(), base.src.clone())
            .compile()
            .expect("chained project compiles");

        assert_eq!(compiled.order, vec!["base".to_string(), "mid".to_string()]);
        assert!(compiled.env("base").unwrap().has_lemma("base.refl"));
        assert!(compiled.env("mid").unwrap().has_lemma("mid.uses"));
        assert_eq!(compiled.thm_count(), 2);
    }

    /// A diamond: `top` is imported by both `left` and `right`, which are both
    /// imported by `bottom`. The topo order must place `top` first and
    /// `bottom` last, with `left`/`right` in (deterministic, name-sorted)
    /// between.
    #[test]
    fn diamond_orders_correctly() {
        let mk = |name: &str, body: &str| {
            CovSource::new(name, format!("(#import core)(#open core){body}"))
        };
        let compiled = Project::new()
            .source(
                "bottom",
                "(#import core)(#open core)(#import left)(#import right)(#open left)(#open right)\
                 (#thm b (#concl (= 0 0)) (#proof (l)))(#export b)",
            )
            .source(
                "left",
                "(#import core)(#open core)(#import top)(#open top)\
                 (#thm l (#concl (= 0 0)) (#proof (t)))(#export l)",
            )
            .source(
                "right",
                "(#import core)(#open core)(#import top)(#open top)\
                 (#thm r (#concl (= 0 0)) (#proof (t)))(#export r)",
            )
            .source(
                mk(
                    "top",
                    "(#thm t (#concl (= 0 0)) (#proof (refl 0)))(#export t)",
                )
                .name,
                "(#import core)(#open core)(#thm t (#concl (= 0 0)) (#proof (refl 0)))(#export t)",
            )
            .compile()
            .expect("diamond compiles");
        // top first, bottom last.
        assert_eq!(compiled.order.first().unwrap(), "top");
        assert_eq!(compiled.order.last().unwrap(), "bottom");
        // name-sorted middle.
        assert_eq!(
            &compiled.order[1..3],
            &["left".to_string(), "right".to_string()]
        );
    }

    /// A `.cov` unit importing a Rust-supplied seam env (the `natrec` /
    /// `ratprim` "givens" pattern). The env is a project leaf, always
    /// available, and not a graph edge.
    #[test]
    fn cov_imports_a_rust_seam_env() {
        // A trivial Rust seam env exporting one lemma the `.cov` will use.
        let theory = crate::script::run(
            "(#import core)(#open core)(#thm given (#concl (= 1 1)) (#proof (refl 1)))(#export given)",
            |n| (n == "core").then(Env::core),
            |_| None,
        )
        .unwrap()
        .resolve_blocking()
        .unwrap();
        let seam = theory.env();

        let compiled = Project::new()
            .rust_env("seam", seam)
            .source(
                "user",
                r#"
                (#import core)(#open core)
                (#import seam)(#open seam)
                (#thm user.uses (#concl (= 1 1)) (#proof (given)))
                (#export user.uses)
                "#,
            )
            .compile()
            .expect("project with a rust seam env compiles");
        // Only `user` is a source unit; the seam is a leaf.
        assert_eq!(compiled.order, vec!["user".to_string()]);
        assert!(compiled.env("user").unwrap().has_lemma("user.uses"));
    }

    /// An unknown import is rejected before any kernel work, with a precise
    /// unit+name error.
    #[test]
    fn unknown_import_is_rejected() {
        let err = match Project::new()
            .source("u", "(#import core)(#open core)(#import nope)(#open nope)")
            .compile()
        {
            Err(e) => e,
            Ok(_) => panic!("unknown import should not compile"),
        };
        assert!(matches!(
            err,
            ProjectError::UnknownImport { ref unit, ref missing }
                if unit == "u" && missing == "nope"
        ));
    }

    /// A two-unit import cycle is detected and reported (the units involved),
    /// rather than looping or producing a partial build. Genuine mutual
    /// recursion between units is the deferred two-phase case (SKELETONS).
    #[test]
    fn import_cycle_is_detected() {
        let err = match Project::new()
            .source("a", "(#import core)(#open core)(#import b)(#open b)")
            .source("b", "(#import core)(#open core)(#import a)(#open a)")
            .compile()
        {
            Err(e) => e,
            Ok(_) => panic!("cyclic project should not compile"),
        };
        match err {
            ProjectError::Cycle(units) => {
                assert_eq!(units, vec!["a".to_string(), "b".to_string()]);
            }
            other => panic!("expected a cycle error, got {other:?}"),
        }
    }

    /// A unit whose proof is wrong fails the compile with its name attached —
    /// the kernel really checks every theorem (no trust).
    #[test]
    fn a_bad_proof_fails_the_unit() {
        let err = match Project::new()
            .source(
                "bad",
                "(#import core)(#open core)(#thm wrong (#concl (= 1 2)) (#proof (refl 1)))",
            )
            .compile()
        {
            Err(e) => e,
            Ok(_) => panic!("a wrong proof should fail the compile"),
        };
        assert!(matches!(err, ProjectError::Unit { ref unit, .. } if unit == "bad"));
    }

    /// The free-function entry point mirrors `Project::compile`.
    #[test]
    fn compile_project_free_function() {
        let sources = vec![
            CovSource::new(
                "base",
                "(#import core)(#open core)(#thm t (#concl (= 0 0)) (#proof (refl 0)))(#export t)",
            ),
            CovSource::new(
                "top",
                "(#import core)(#open core)(#import base)(#open base)\
                 (#thm u (#concl (= 0 0)) (#proof (t)))(#export u)",
            ),
        ];
        let compiled = compile_project(sources, [], []).expect("free fn compiles");
        assert_eq!(compiled.order, vec!["base".to_string(), "top".to_string()]);
    }
}
