//! **SpecTec grammars → byte predicates.** The grammar-aware layer on top of
//! the regular-expression core ([`crate::spectec::regex`]): it takes a SpecTec
//! grammar symbol ([`SpecTecSym`]) and routes it, through `covalence-spectec`'s
//! byte bridge, into the reified regex object logic.
//!
//! A SpecTec grammar is **more than a regex** — regular languages are only its
//! base case. The non-regular constructs (non-terminal references
//! [`SpecTecSym::Var`], captures, parametric-length iteration) return a typed
//! [`BridgeError`] here. Lifting those is the **CFG stratum**: our own
//! primitive notion of context-free grammar (reified non-terminals + a
//! `Derives` judgement, the way [`crate::init::regex`] is our primitive notion
//! of regular expression), at which point `Var` becomes a non-terminal symbol
//! rather than an error. See this module's `SKELETONS.md`.

use covalence_core::Term;

use super::regex::{Core, core_to_term, desugar};

pub use covalence_spectec::ast::SpecTecSym;
/// Why a [`SpecTecSym`] sits outside the regular fragment (a grammar
/// reference, capture, or parametric iteration).
pub use covalence_spectec::regex::BridgeError;

/// Desugar a [`SpecTecSym`] (read over **bytes**) to the regex [`Core`], via
/// `covalence-spectec`'s byte bridge.
pub fn sym_to_core(sym: &SpecTecSym) -> Result<Core, BridgeError> {
    covalence_spectec::regex::sym_to_regex_u8(sym).map(|r| desugar(&r))
}

/// Compile a [`SpecTecSym`] directly to the reified term `⌜r⌝ : regex u8`.
pub fn compile_sym(sym: &SpecTecSym) -> Result<Term, BridgeError> {
    sym_to_core(sym).map(|c| core_to_term(&c))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_sym_routes_through_byte_bridge() {
        // `(seq (num 0x61) (num 0x62))` -> reified `seq (lit a)(lit b)`.
        let sym = covalence_spectec::parse::parse_sym("(seq (num 0x61) (num 0x62))").unwrap();
        let term = compile_sym(&sym).unwrap();
        let expected = core_to_term(&Core::seq(Core::Lit(0x61), Core::Lit(0x62)));
        assert_eq!(term, expected);
    }

    #[test]
    fn compile_sym_rejects_grammar_reference() {
        let sym = covalence_spectec::parse::parse_sym("(var \"instr\")").unwrap();
        assert!(matches!(
            compile_sym(&sym),
            Err(BridgeError::GrammarRef { .. }),
        ));
    }
}
