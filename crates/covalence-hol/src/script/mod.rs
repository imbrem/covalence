//! Proof scripts — an S-expression authoring + replay layer over the
//! kernel, the bottom rung of the surface-syntax ladder
//! (`docs/surface-syntax.md`).
//!
//! A script file is a sequence of directives:
//!
//! ```text
//! (open core)                         ;; seed the name-resolution prelude
//!
//! (thm NAME
//!   (fix (p bool) (q bool))           ;; optional: typed free variables
//!   (concl  TERM)                     ;; the statement (a drift assertion)
//!   (proof  DRV))                     ;; the proof term, replayed by `check`
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
mod infer;
mod syntax;

pub use drv::{Drv, check, parse_drv};
pub use syntax::{ConstDef, Env, Scope, parse_term, parse_type};

use covalence_core::{Thm, Type};
use covalence_sexp::SExpr;

/// A replayed theory: the environment it produced (with all its lemmas,
/// `open`-able by other theories) plus the ordered list of theorems.
pub struct Theory {
    env: Env,
    pub thms: Vec<NamedThm>,
}

impl Theory {
    /// The environment this theory produced — pass it as an `(open NAME)`
    /// target when running a downstream script.
    pub fn env(&self) -> Env {
        self.env.clone()
    }

    /// Look up a proven lemma by name (panics if absent — for the
    /// `cov_theory!` accessor functions, which name lemmas statically).
    pub fn lemma(&self, name: &str) -> Thm {
        self.env
            .lemmas
            .get(name)
            .cloned()
            .unwrap_or_else(|| panic!("theory has no lemma `{name}`"))
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

/// Parse and replay a whole script. `(open NAME)` directives are resolved
/// by `resolver` (returning the `Env` to merge in); `(thm …)` directives
/// are checked and accumulate into the running environment so later
/// theorems can reference earlier ones — and any opened theory's lemmas —
/// via `(lemma NAME)`.
pub fn run(
    src: &str,
    resolver: impl Fn(&str) -> Option<Env>,
) -> Result<Theory, ScriptError> {
    let exprs =
        covalence_sexp::parse(src).map_err(|e| ScriptError::Syntax(format!("sexp: {e}")))?;
    let mut env = Env::empty();
    let mut thms = Vec::new();
    for e in &exprs {
        let ch = syntax::list(e, "directive")?;
        match syntax::head_sym(ch)? {
            "open" => {
                syntax::arity(ch, 2, "open")?;
                let name = syntax::sym(&ch[1], "environment name")?;
                let opened = resolver(name)
                    .ok_or_else(|| ScriptError::Unbound(format!("environment `{name}`")))?;
                env.open(&opened);
            }
            "thm" => {
                let nt = run_thm(ch, &env)?;
                env.lemmas.insert(nt.name.clone(), nt.thm.clone());
                thms.push(nt);
            }
            other => {
                return Err(ScriptError::Syntax(format!("unknown directive: {other}")));
            }
        }
    }
    Ok(Theory { env, thms })
}

/// Replay a script whose only available environment is the `core` prelude,
/// returning the theorems it proves.
pub fn run_str(src: &str) -> Result<Vec<NamedThm>, ScriptError> {
    Ok(run(src, |name| (name == "core").then(Env::core))?.thms)
}

/// Load a `.cov` proof script as a Rust module: run it once, lazily, with
/// the given `import`ed environments available for the script to `(open …)`
/// (or otherwise reference), then expose chosen lemmas as `fn() -> Thm`
/// accessors plus the resulting environment via `env()` (which downstream
/// theories can in turn `import`).
///
/// `import NAME = EXPR;` makes the environment `EXPR` *available* to the
/// script under `NAME`; the `.cov` decides what to do with it (today, an
/// `(open NAME)` directive merges it in — later it may bind it under a
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
            $( $lemma:literal => $lvis:vis fn $fn:ident ; )*
        }
    ) => {
        $(#[$meta])*
        $vis mod $modname {
            #[allow(unused_imports)]
            use super::*;

            static THEORY: ::std::sync::LazyLock<$crate::script::Theory> =
                ::std::sync::LazyLock::new(|| {
                    $crate::script::run(include_str!($src), |__name| match __name {
                        $( $oname => Some($oenv), )*
                        _ => None,
                    })
                    .unwrap_or_else(|__e| {
                        panic!("cov_theory `{}`: {}", stringify!($modname), __e)
                    })
                });

            /// The environment this theory produces (`open` it elsewhere).
            $vis fn env() -> $crate::script::Env {
                THEORY.env()
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
            "thm: expected (thm NAME [(fix …)] (concl …) (proof …))".into(),
        ));
    }
    let name = syntax::sym(&ch[1], "thm name")?.to_string();
    let mut idx = 2;

    // optional (fix x (y T) …) — annotations are optional; omitted types
    // (and omitted `fix` entirely) are inferred from the conclusion.
    let mut fix: Vec<(String, Option<Type>)> = Vec::new();
    if let SExpr::List(f) = &ch[idx]
        && f.first().and_then(|x| x.as_symbol()) == Some("fix")
    {
        for v in &f[1..] {
            fix.push(infer::parse_binder_spec(v)?);
        }
        idx += 1;
    }

    // Elaborate the conclusion: this infers the type of every free
    // variable, which then seeds the proof so both share one typing.
    let concl_ch = syntax::list(&ch[idx], "concl")?;
    let concl_payload = syntax::expect_head(concl_ch, "concl")?;
    let (expected, vars) = infer::elaborate_concl(concl_payload, &fix, env)?;
    let mut scope: Scope = vars;
    idx += 1;

    let proof_ch = syntax::list(&ch[idx], "proof")?;
    let proof_payload = syntax::expect_head(proof_ch, "proof")?;
    let drv = drv::parse_drv(proof_payload, &mut scope, env)?;

    let thm = drv::check(&drv, env)?;
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

    /// Replay a single `(thm …)` and return its checked theorem.
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
            (open core)
            (thm and.comm
              (fix (p bool) (q bool))
              (concl (==> (and p q) (and q p)))
              (proof
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
            (open core)
            (thm add.2.3
              (concl (= (nat.add 2 3) 5))
              (proof (reduce-prim (nat.add 2 3))))
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
            (open core)
            (thm imp.refl.auto
              (fix (p bool))
              (concl (==> p p))
              (proof (tauto (==> p p))))
            "#,
        );
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn excluded_middle_via_lem() {
        let thm = one(
            r#"
            (open core)
            (thm lem.p
              (fix (p bool))
              (concl (or p (not p)))
              (proof (lem p)))
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
            (open core)
            (thm rw.demo
              (fix (a nat) (b nat))
              (concl (= b b))
              (proof (rw (assume (= a b)) (refl a))))
            "#,
        );
        // carries the single hypothesis a = b
        assert_eq!(thm.hyps().len(), 1);
    }

    #[test]
    fn ports_logic_theory_implicitly() {
        // The checked-in `logic.cov` (implicit style: no `fix`, no binder
        // annotations) replays, and the closed theorems match the
        // hand-written Rust `init::logic` originals — the surface-syntax §8
        // golden-test discipline.
        let thms = run_str(include_str!("theories/logic.cov")).expect("logic.cov should replay");
        let get = |n: &str| {
            &thms
                .iter()
                .find(|t| t.name == n)
                .unwrap_or_else(|| panic!("missing thm {n}"))
                .thm
        };
        assert_eq!(get("truth").concl(), crate::init::logic::truth().concl());
        assert_eq!(get("and.comm").concl(), crate::init::logic::and_comm().concl());
        assert_eq!(get("or.comm").concl(), crate::init::logic::or_comm().concl());
        // lemma application: depends on the single hypothesis a ∧ b
        assert_eq!(get("and.comm.apply").hyps().len(), 1);
        // polymorphic lemma + its nat specialisation are hypothesis-free
        assert!(get("eq.refl.poly").hyps().is_empty());
        assert!(get("eq.refl.nat").hyps().is_empty());
    }

    #[test]
    fn infers_free_var_types_without_fix() {
        // No `fix`: p, q are inferred `bool` from their use under `and`.
        let thm = one(
            r#"
            (open core)
            (thm and.comm.implicit
              (concl (==> (and p q) (and q p)))
              (proof
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
        // A separate script `(open logic)`s the environment produced by the
        // `cov_theory!`-loaded `init::logic::cov`, and applies one of its
        // lemmas by name — demonstrating the exposed env + cross-theory
        // `(lemma …)` reference.
        let theory = run(
            r#"
            (open core)
            (open logic)
            (thm use.and.comm
              (concl (and b a))
              (proof
                (imp-elim
                  (inst p a (inst q b (lemma and.comm)))
                  (assume (and a b)))))
            "#,
            |name| match name {
                "core" => Some(Env::core()),
                "logic" => Some(crate::init::logic::cov::env()),
                _ => None,
            },
        )
        .expect("should replay against the opened `logic` env");
        assert_eq!(theory.thms.len(), 1);
        // {a ∧ b} ⊢ b ∧ a — carries the single hypothesis
        assert_eq!(theory.thms[0].thm.hyps().len(), 1);
    }

    #[test]
    fn conclusion_mismatch_is_caught() {
        let res = run_str(
            r#"
            (open core)
            (thm wrong
              (fix (p bool) (q bool))
              (concl (and p q))
              (proof (assume (and q p))))
            "#,
        );
        assert!(
            matches!(res, Err(ScriptError::ConclMismatch { .. })),
            "expected ConclMismatch, got {:?}",
            res.err()
        );
    }
}
