//! **Whole-`gram` lowering** — the CFG-stratum bridge, one stratum above the
//! single-symbol [`compile_sym`](super::compile_sym).
//!
//! [`spec_grammar_env`] takes root grammar names, resolves their dependency
//! closure over the bundled WASM 3.0 binary grammars, lowers them (under-
//! approximating; premise/parametric/`ListN` productions skip and report) into
//! a neutral [`covalence_grammar::cfg::Cfg<u8>`], and builds a
//! [`GrammarEnv`](crate::grammar::cfg::GrammarEnv) — the kernel-checked
//! `Derives_E` judgement. [`crate::grammar::cfg::tactic::prove_derives`] then
//! parses concrete bytes into a hypothesis-free `⊢ Derives_E ⌜nt⌝ w`.

use covalence_core::Result;
use covalence_spectec::cfg::{CfgReport, lower};
use covalence_spectec::grammar::wasm3_binary;

use crate::grammar::cfg::GrammarEnv;

/// Build a [`GrammarEnv`] from the dependency closure of `roots` over the
/// bundled WASM 3.0 binary grammars (`covalence_spectec::grammar::wasm3_binary`).
///
/// Returns the env plus the lowering [`CfgReport`] (which productions were
/// skipped and why). Every lowered clause under-approximates its SpecTec
/// grammar, so a `⊢ Derives_E ⌜nt⌝ w` proved against this env implies membership
/// in the true WASM byte language.
pub fn spec_grammar_env(roots: &[&str]) -> Result<(GrammarEnv, CfgReport)> {
    let grammars = wasm3_binary();
    let (cfg, report) = lower(&grammars, roots);
    let env = GrammarEnv::new(cfg)?;
    Ok((env, report))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn breftype_closure_env_builds() {
        // The Attr-stripped Var chain Breftype → Bheaptype → Babsheaptype.
        let (env, _report) = spec_grammar_env(&["Breftype"]).unwrap();
        assert!(env.nt("Breftype").is_some());
        assert!(env.nt("Babsheaptype").is_some());
        // At least the three named grammars became non-terminals.
        assert!(env.cfg().num_nts() >= 3);
    }
}
