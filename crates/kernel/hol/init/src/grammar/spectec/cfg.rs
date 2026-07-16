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
use covalence_spectec::cfg::{CfgReport, lower, lower_recognition};
use covalence_spectec::grammar::wasm3_binary;

use crate::grammar::cfg::GrammarEnv;

/// Build a [`GrammarEnv`] from the dependency closure of `roots` over the
/// bundled WASM 3.0 binary grammars (`covalence_spectec::grammar::wasm3_binary`).
///
/// Returns the env plus the lowering [`CfgReport`] (which productions were
/// skipped and why). Every lowered clause **under-approximates** its SpecTec
/// grammar (`L(Cfg) ⊆ L(SpecTec)`), so a `⊢ Derives_E ⌜nt⌝ w` proved against
/// this env implies membership in the true WASM byte language.
pub fn spec_grammar_env(roots: &[&str]) -> Result<(GrammarEnv, CfgReport)> {
    let grammars = wasm3_binary();
    let (cfg, report) = lower(&grammars, roots);
    let env = GrammarEnv::new(cfg)?;
    Ok((env, report))
}

/// As [`spec_grammar_env`] but using the **recognition-mode** lowering
/// ([`covalence_spectec::cfg::lower_recognition`]) — monomorphising parametric
/// grammars (so LEB128 `BuN`/`BsN`, `Bu32`/`Bu64`, and the `*idx` grammars
/// lower) and over-approximating value-range premises / `ListN` vectors.
///
/// The invariant flips: recognition-mode envs satisfy `L(SpecTec) ⊆ L(Cfg)`, so
/// a `⊢ Derives_E ⌜nt⌝ w` here means "`w` is a well-formed *recognition* of the
/// grammar's byte shape" — NOT that it encodes an in-range value. The
/// [`CfgReport`]'s `premises_dropped` / `listns_widened` / `mono_instances`
/// counters record the approximations. See
/// `notes/vibes/logics/cfg-stratum-design.md` §"M6 — Missing grammars".
pub fn spec_grammar_env_recognition(roots: &[&str]) -> Result<(GrammarEnv, CfgReport)> {
    let grammars = wasm3_binary();
    let (cfg, report) = lower_recognition(&grammars, roots);
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

#[cfg(test)]
mod recog_tests {
    use super::*;

    #[test]
    fn bu32_recognition_env_builds_with_leb128_instance() {
        // Bu32 = BuN(32); recognition mode monomorphises the parametric ref into
        // the instance NT `BuN@32`, lowered to the LEB128 regex terminal.
        let (env, report) = spec_grammar_env_recognition(&["Bu32"]).unwrap();
        assert!(env.nt("Bu32").is_some());
        let names: Vec<&str> = env.cfg().nts().iter().map(|d| d.name.as_str()).collect();
        assert!(
            names.contains(&"BuN@32"),
            "expected a monomorphised BuN@32 instance, got {names:?}"
        );
        // The recognition-mode approximation is recorded honestly.
        assert!(report.mono_instances >= 1);
    }
}
