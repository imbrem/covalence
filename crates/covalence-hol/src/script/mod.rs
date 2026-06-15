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
mod syntax;

pub use drv::{Drv, check, parse_drv};
pub use syntax::{ConstDef, Env, Scope, parse_term, parse_type};

use covalence_core::Thm;
use covalence_sexp::SExpr;

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

/// Parse and replay a whole script, returning every `(thm …)` it proves.
/// Later theorems may reference earlier ones via `(lemma NAME)`.
pub fn run_str(src: &str) -> Result<Vec<NamedThm>, ScriptError> {
    let exprs =
        covalence_sexp::parse(src).map_err(|e| ScriptError::Syntax(format!("sexp: {e}")))?;
    let mut env = Env::core();
    let mut out = Vec::new();
    for e in &exprs {
        let ch = syntax::list(e, "directive")?;
        match syntax::head_sym(ch)? {
            "open" => {
                syntax::arity(ch, 2, "open")?;
                match syntax::sym(&ch[1], "prelude name")? {
                    "core" => env = Env::core(),
                    other => return Err(ScriptError::Unbound(format!("prelude `{other}`"))),
                }
            }
            "thm" => {
                let nt = run_thm(ch, &env)?;
                env.lemmas.insert(nt.name.clone(), nt.thm.clone());
                out.push(nt);
            }
            other => {
                return Err(ScriptError::Syntax(format!("unknown directive: {other}")));
            }
        }
    }
    Ok(out)
}

fn run_thm(ch: &[SExpr], env: &Env) -> Result<NamedThm, ScriptError> {
    if ch.len() < 4 {
        return Err(ScriptError::Syntax(
            "thm: expected (thm NAME [(fix …)] (concl …) (proof …))".into(),
        ));
    }
    let name = syntax::sym(&ch[1], "thm name")?.to_string();
    let mut scope: Scope = Vec::new();
    let mut idx = 2;

    // optional (fix (x T) …)
    if let SExpr::List(f) = &ch[idx]
        && f.first().and_then(|x| x.as_symbol()) == Some("fix")
    {
        for v in &f[1..] {
            scope.push(syntax::parse_var(v)?);
        }
        idx += 1;
    }

    let concl_ch = syntax::list(&ch[idx], "concl")?;
    let concl_payload = syntax::expect_head(concl_ch, "concl")?;
    let expected = syntax::parse_term(concl_payload, &mut scope, env)?;
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
