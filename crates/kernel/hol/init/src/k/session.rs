//! **`KSession` — the K narrow-waist API**, the peer of `MmSession` (Metamath)
//! and the Lisp `Session`. It holds a K definition (rewrite rules, from `.k`
//! source or KORE) and *reduces K programs* to hypothesis-free reduction
//! theorems:
//!
//! ```text
//!   MmSession : replay a proof     → ⊢ Derivable_DB ⌜S⌝
//!   KSession  : reduce a program   → ⊢ Reduces ⌜pgm⌝ ⌜normal form⌝
//! ```
//!
//! This is "K a first-class input format on par with Metamath and Lisp": parse a
//! definition, parse a program, reduce it — a kernel-checked theorem out. It
//! sits on the layered stack (`k::rewrite` → `metalogic::rewrite` →
//! `metalogic::binary` → HOL-omega); a `/k` REPL is a thin wrapper over it.
//!
//! Scope today (the first-order fragment — `notes/vibes/k/reduction-demo-scope.md`):
//! prefix-term rewrite rules (`rule sym(args…) => …`) with no cells, no `~>`, no
//! hooks, no binders. Enough for K tutorial Lesson 1.2 (`colorOf`/`contentsOfJar`)
//! and hand-written PEANO / boolean simplification.

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_k::fragment::RewriteRule;
use covalence_k::kdef::lower::module_rules;
use covalence_k::kdef::parse::{parse_definition, parse_term};

use super::encode::{encode_pattern, render};
use super::rewrite::{KReducer, LoweringReport};

fn session_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("k session: {}", msg.into()))
}

/// A reduction result: the normal form (encoded + rendered), the number of
/// certified steps, and `⊢ Reduces program normal_form`.
pub struct Reduction {
    /// The encoded normal-form `Φ`-term.
    pub normal_form: Term,
    /// The rendered normal form (readable K-ish text).
    pub rendered: String,
    /// `⊢ Reduces ⌜program⌝ ⌜normal_form⌝` — hypothesis-free for a closed program.
    pub thm: Thm,
    /// Whether reduction reached a normal form within the fuel (`false` = fuel ran
    /// out, so the theorem is a *partial* reduction, still valid).
    pub complete: bool,
}

/// A K definition loaded for reduction.
pub struct KSession {
    reducer: KReducer,
    default_fuel: usize,
}

impl KSession {
    /// Load a session from `.k` source: parse it, gather the rewrite rules across
    /// all modules, and build the reducer. Grammar/`syntax` declarations and
    /// unparseable sentences are ignored (this reduces via rules).
    pub fn from_source(src: &str) -> Result<KSession> {
        let def = parse_definition(src).map_err(|e| session_err(e.to_string()))?;
        let rules: Vec<RewriteRule> = def.modules.iter().flat_map(module_rules).collect();
        if rules.is_empty() {
            return Err(session_err("definition has no reducible rules"));
        }
        Ok(KSession::from_rules(&rules))
    }

    /// Build a session directly from KORE-extracted (or hand-built) rules.
    pub fn from_rules(rules: &[RewriteRule]) -> KSession {
        KSession {
            reducer: KReducer::new(rules),
            default_fuel: 10_000,
        }
    }

    /// The lowering report (rules lowered vs skipped).
    pub fn report(&self) -> &LoweringReport {
        self.reducer.report()
    }

    /// Set the default fuel bound used by [`reduce`](KSession::reduce).
    pub fn with_fuel(mut self, fuel: usize) -> KSession {
        self.default_fuel = fuel;
        self
    }

    /// Parse a program in the prefix-term fragment and encode it to a `Φ`-term.
    pub fn parse_program(&self, text: &str) -> Result<Term> {
        let term = parse_term(text).map_err(|e| session_err(e.to_string()))?;
        encode_pattern(&term.to_pattern())
    }

    /// **Reduce a program string** to its normal form + `⊢ Reduces` theorem
    /// (using the default fuel).
    pub fn reduce(&self, program: &str) -> Result<Reduction> {
        self.reduce_with_fuel(program, self.default_fuel)
    }

    /// [`reduce`](KSession::reduce) with an explicit fuel bound.
    pub fn reduce_with_fuel(&self, program: &str, fuel: usize) -> Result<Reduction> {
        let start = self.parse_program(program)?;
        self.reduce_term(&start, fuel)
    }

    /// Reduce an already-encoded program term.
    pub fn reduce_term(&self, start: &Term, fuel: usize) -> Result<Reduction> {
        let (nf, thm) = self.reducer.reduce(start, fuel)?;
        // Complete iff no redex remains (a further 1-fuel reduction is reflexive).
        let complete = {
            let (nf2, _) = self.reducer.reduce(&nf, 1)?;
            nf2 == nf
        };
        Ok(Reduction {
            rendered: render(&nf),
            normal_form: nf,
            thm,
            complete,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "reduction must be hypothesis-free");
    }

    const PEANO: &str = r#"
module PEANO
  syntax Nat ::= "z"
  rule plus(z(), N) => N
  rule plus(s(M), N) => s(plus(M, N))
  rule mult(z(), N) => z()
  rule mult(s(M), N) => plus(N, mult(M, N))
endmodule
"#;

    #[test]
    fn peano_session_reduces_a_program() {
        let k = KSession::from_source(PEANO).unwrap();
        assert_eq!(k.report().lowered, 4);

        // plus(s(s(z())), s(z())) →* s(s(s(z())))
        let r = k.reduce("plus(s(s(z())), s(z()))").unwrap();
        assert_genuine(&r.thm);
        assert!(r.complete);
        assert_eq!(r.rendered, "s(s(s(z)))");

        // 2 * 2 = 4 : mult(s(s(z())), s(s(z()))) →* s(s(s(s(z()))))
        let r2 = k.reduce("mult(s(s(z())), s(s(z())))").unwrap();
        assert_genuine(&r2.thm);
        assert_eq!(r2.rendered, "s(s(s(s(z))))");
    }

    const COLORS: &str = r#"
module COLORS
  rule colorOf(Banana()) => Yellow()
  rule colorOf(Blueberry()) => Blue()
  rule contentsOfJar(Jar(F)) => F
endmodule
"#;

    #[test]
    fn lesson_1_2_session() {
        let k = KSession::from_source(COLORS).unwrap();
        assert_eq!(k.reduce("colorOf(Banana())").unwrap().rendered, "Yellow");
        assert_eq!(k.reduce("colorOf(Blueberry())").unwrap().rendered, "Blue");
        assert_eq!(
            k.reduce("contentsOfJar(Jar(Kiwi()))").unwrap().rendered,
            "Kiwi"
        );
    }

    const BOOLSIMP: &str = r#"
module BOOLSIMP
  rule and(tt(), X) => X
  rule and(ff(), X) => ff()
  rule or(tt(), X) => tt()
  rule or(ff(), X) => X
  rule neg(tt()) => ff()
  rule neg(ff()) => tt()
endmodule
"#;

    #[test]
    fn boolsimp_session() {
        let k = KSession::from_source(BOOLSIMP).unwrap();
        // and(or(tt, ff), neg(ff)) →* tt
        let r = k.reduce("and(or(tt(), ff()), neg(ff()))").unwrap();
        assert_genuine(&r.thm);
        assert_eq!(r.rendered, "tt");
    }
}
