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
mod infer;
mod scope;
mod syntax;
mod tactic;

pub use drv::{Drv, check, parse_drv};
pub use env::{ConstDef, Env};
pub use scope::Scope;
pub use syntax::{parse_term, parse_type};
pub use tactic::{Interp, Tactic};

use covalence_core::{Thm, Type};
use covalence_sexp::SExpr;

/// A replayed theory. Its **export** environment — the public interface,
/// built explicitly by `(#export …)` directives — is what other theories
/// `import`/`open` and what the `cov_theory!` accessors expose. The full
/// internal environment (every import + every proven lemma) is used only
/// for resolution *during* the run and is not surfaced.
pub struct Theory {
    /// The explicitly-exported public interface (`(#export …)`).
    exports: Env,
    pub thms: Vec<NamedThm>,
}

impl Theory {
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
            .lookup_lemma(name)
            .cloned()
            .unwrap_or_else(|| panic!("theory does not export lemma `{name}`"))
    }
}

/// Errors from parsing or replaying a proof script.
#[derive(Debug, thiserror::Error)]
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
pub fn run(
    src: &str,
    resolver: impl Fn(&str) -> Option<Env>,
    tactics: impl Fn(&str) -> Option<Tactic>,
) -> Result<Theory, ScriptError> {
    let exprs =
        covalence_sexp::parse(src).map_err(|e| ScriptError::Syntax(format!("sexp: {e}")))?;
    let mut internal = Env::empty();
    let mut exports = Env::empty();
    let mut thms = Vec::new();
    for e in &exprs {
        let ch = syntax::list(e, "directive")?;
        // Structural directives are `#`-prefixed; bare names (inside proofs)
        // are rules/terms resolved from the environment, never directives.
        match syntax::head_sym(ch)? {
            "#import" => {
                syntax::arity(ch, 2, "#import")?;
                let name = syntax::sym(&ch[1], "environment name")?;
                let env = resolver(name)
                    .ok_or_else(|| ScriptError::Unbound(format!("environment `{name}`")))?;
                internal.import(name, env);
            }
            "#open" => {
                syntax::arity(ch, 2, "#open")?;
                internal.open(syntax::sym(&ch[1], "environment name")?)?;
            }
            // `(#use NAME)` / `(#use (#alias NAME PREFIX))` — bring an
            // imported namespace into scope QUALIFIED, so `and.comm` becomes
            // `NAME.and.comm` (or `PREFIX.and.comm`).
            "#use" => {
                syntax::arity(ch, 2, "#use")?;
                let (name, prefix) = parse_use_target(&ch[1])?;
                internal.use_ns(&name, &prefix)?;
            }
            // `(#export-all NAME)` / `(#export-all NAME as PREFIX)` — re-export
            // *every* symbol of an imported namespace, optionally re-prefixed
            // (e.g. `nat` → `init.nat`, or `logic` → `prelude`).
            "#export-all" => {
                let name = syntax::sym(&ch[1], "namespace name")?;
                let prefix = match ch.len() {
                    2 => "",
                    4 if syntax::sym(&ch[2], "as")? == "as" => {
                        syntax::sym(&ch[3], "export prefix")?
                    }
                    _ => {
                        return Err(ScriptError::Syntax(
                            "#export-all: expected (#export-all NAME [as PREFIX])".into(),
                        ));
                    }
                };
                let ns = internal.get_import(name).cloned().ok_or_else(|| {
                    ScriptError::Unbound(format!("environment not imported: `{name}`"))
                })?;
                exports.merge_prefixed(&ns, prefix);
            }
            // `(#register-ffi-tactic NAME)` — register a host-supplied native
            // tactic (the pointer comes from `tactics`, e.g. a `cov_theory!`
            // `ffi-tactic` clause) into the running environment under NAME.
            "#register-ffi-tactic" => {
                syntax::arity(ch, 2, "#register-ffi-tactic")?;
                let name = syntax::sym(&ch[1], "tactic name")?;
                let tac = tactics(name).ok_or_else(|| {
                    ScriptError::Unbound(format!("ffi tactic `{name}` (not provided by host)"))
                })?;
                internal.register_tactic(name, tac);
            }
            "#thm" => {
                let nt = run_thm(ch, &internal)?;
                internal.define_lemma(nt.name.clone(), nt.thm.clone());
                thms.push(nt);
            }
            // `(#export NAME …)` — build the public interface explicitly.
            // Each name is looked up in the running environment (a proven
            // lemma, or an imported lemma/constant) and added to `exports`.
            "#export" => {
                if ch.len() < 2 {
                    return Err(ScriptError::Syntax("#export: expected (#export NAME …)".into()));
                }
                for item in &ch[1..] {
                    let name = syntax::sym(item, "export name")?;
                    if let Some(thm) = internal.lookup_lemma(name) {
                        exports.define_lemma(name, thm.clone());
                    } else if let Some(c) = internal.lookup_const(name) {
                        exports.define_const(name, c.clone());
                    } else if let Some(t) = internal.lookup_tactic(name) {
                        exports.register_tactic(name, t);
                    } else {
                        return Err(ScriptError::Unbound(format!(
                            "#export: nothing named `{name}` to export"
                        )));
                    }
                }
            }
            other => {
                return Err(ScriptError::Syntax(format!("unknown directive: {other}")));
            }
        }
    }
    Ok(Theory { exports, thms })
}

/// Replay a script whose only available environment is the `core` prelude,
/// returning the theorems it proves.
pub fn run_str(src: &str) -> Result<Vec<NamedThm>, ScriptError> {
    Ok(run(src, |name| (name == "core").then(Env::core), |_| None)?.thms)
}

/// Parse a `#use` target — `NAME` (qualify by `NAME`) or
/// `(#alias NAME PREFIX)` (qualify by `PREFIX`).
fn parse_use_target(s: &SExpr) -> Result<(String, String), ScriptError> {
    match s {
        covalence_sexp::SExp::Atom(_) => {
            let n = syntax::sym(s, "namespace name")?;
            Ok((n.to_string(), n.to_string()))
        }
        covalence_sexp::SExp::List(a) => {
            if syntax::head_sym(a)? != "#alias" {
                return Err(ScriptError::Syntax(
                    "#use: expected NAME or (#alias NAME PREFIX)".into(),
                ));
            }
            syntax::arity(a, 3, "#alias")?;
            Ok((
                syntax::sym(&a[1], "alias name")?.to_string(),
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
                        |__tname| match __tname {
                            $( $tname => Some($texpr as $crate::script::Tactic), )*
                            _ => None,
                        },
                    )
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

fn run_thm(ch: &[SExpr], env: &Env) -> Result<NamedThm, ScriptError> {
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
    let thm = tactic::prove(&expected, &ch[idx], &mut scope, env)?;
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
    fn and_comm_ports_from_rust() {
        // The S-expression rewrite of `init::logic::and_comm`.
        let thm = one(
            r#"
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
            "#,
        );
        assert!(thm.hyps().is_empty(), "and.comm must be hypothesis-free");
        // It must match the hand-written Rust theorem exactly.
        let rust = crate::init::logic::and_comm();
        assert_eq!(thm.concl(), rust.concl());
    }

    #[test]
    fn ground_arithmetic_via_reduce_prim() {
        // ⊢ 2 + 3 = 5, by primitive computation.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm add.2.3
              (#concl (= (nat.add 2 3) 5))
              (#proof (reduce-prim (nat.add 2 3))))
            "#,
        );
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
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm imp.refl.auto
              (#fix (p bool))
              (#concl (==> p p))
              (#proof (tauto (==> p p))))
            "#,
        );
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
        // becomes `logic.and.comm`. An alias re-prefixes; `#export-all`
        // re-exports everything under a layer.
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
            (#export-all logic as prelude)
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
        assert!(env.has_lemma("prelude.and.comm"), "re-exported under prelude");
    }

    #[test]
    fn excluded_middle_via_lem() {
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm lem.p
              (#fix (p bool))
              (#concl (or p (not p)))
              (#proof (lem p)))
            "#,
        );
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn rw_tactic_rewrites_with_a_hypothesis() {
        // `rw` is a full congruence — it rewrites *every* occurrence of
        // the equation's LHS. From `a = b` (assumed) and `⊢ a = a`
        // (refl), rewriting `a ↦ b` everywhere gives {a = b} ⊢ b = b.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm rw.demo
              (#fix (a nat) (b nat))
              (#concl (= b b))
              (#proof (rw (assume (= a b)) (refl a))))
            "#,
        );
        // carries the single hypothesis a = b
        assert_eq!(thm.hyps().len(), 1);
    }


    #[test]
    fn infers_free_var_types_without_fix() {
        // No `fix`: p, q are inferred `bool` from their use under `and`.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm and.comm.implicit
              (#concl (==> (and p q) (and q p)))
              (#proof
                (imp-intro (and p q)
                  (and-intro
                    (and-elim-r (assume (and p q)))
                    (and-elim-l (assume (and p q)))))))
            "#,
        );
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
        let thm = one(
            r#"
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
            "#,
        );
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
        assert!(
            !env.has_lemma("b"),
            "un-exported lemma stays internal"
        );
        assert_eq!(theory.thms.len(), 2, "both lemmas were proven");
    }

    #[test]
    fn by_tactic_mode_proves_and_comm() {
        // Goal-directed: `intro` the implication, then `exact` a tree-mode
        // proof of the swapped conjunction. The `#by` block elaborates to
        // the same `Drv` the tree-mode `and.comm` produces.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm and.comm.by
              (#concl (==> (and p q) (and q p)))
              (#by
                (intro h)
                (exact
                  (and-intro
                    (and-elim-r (assume (and p q)))
                    (and-elim-l (assume (and p q)))))))
            "#,
        );
        assert_eq!(thm.concl(), crate::init::logic::and_comm().concl());
    }

    #[test]
    fn by_intro_and_assumption() {
        // `intro` moves `p` into the context; `assumption` closes the goal.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm imp.refl.by
              (#concl (==> p p))
              (#by (intro h) (assumption)))
            "#,
        );
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_intro_over_forall() {
        // ∀-introduction in tactic mode, closed by `refl`: ⊢ ∀(x:nat). x = x.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm eq.refl.by
              (#concl (forall (x nat) (= x x)))
              (#by (intro x) (refl)))
            "#,
        );
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_have_brings_a_fact_into_context() {
        // `#have` proves an intermediate fact in (nested) tree mode and
        // makes it available; `assumption` then discharges the goal with it.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm dup.by
              (#concl (==> p (and p p)))
              (#by
                (intro h)
                (#have (and p p) (#proof (and-intro (assume p) (assume p))))
                (assumption)))
            "#,
        );
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_multi_intro_and_sym() {
        // `intro a b h` peels three binders at once; `sym` swaps the
        // equation goal; `assumption` closes it with the hypothesis.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm eq.sym.by
              (#concl (forall (a nat) (forall (b nat) (==> (= a b) (= b a)))))
              (#by (intro a b h) (sym) (assumption)))
            "#,
        );
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_not_intro() {
        // `not-intro` turns goal `¬F` into `F ⟹ F`.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm not.false.by
              (#concl (not false))
              (#by (not-intro) (intro h) (assumption)))
            "#,
        );
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn by_induct_on_nat() {
        // The `induct` tactic: ⊢ ∀(n:nat). n = n, base + step both by `refl`.
        // Exercises the kernel's `nat_induct` plus the β-conv bookkeeping.
        let thm = one(
            r#"
            (#import core)
            (#open core)
            (#thm nat.eq.refl.by
              (#concl (forall (n nat) (= n n)))
              (#by (induct n (#by (refl)) (#by (refl)))))
            "#,
        );
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
