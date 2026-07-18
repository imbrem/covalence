//! Typed access to the **grammar** definitions in a SpecTec AST, plus a
//! handful of small hand-written byte grammars for bootstrapping.
//!
//! A SpecTec grammar definition is `grammar X params : typ = | prod | …`,
//! carried by [`ast::SpecTecDef::Gram`]. WebAssembly's *binary* format is
//! specified as grammars whose names start with `B` (e.g. `Bvectype`); the
//! *text* format uses the `T`-prefixed ones. This module lifts those `Gram`
//! definitions out of the raw AST into the lighter [`Grammar`] view, and
//! exposes the bundled WebAssembly spec through [`wasm3`].
//!
//! # Available WASM versions
//!
//! Upstream (`wasm_spec_ast`) currently ships **only** the elaborated
//! WebAssembly **3.0** spec, so [`wasm3`] is the only concrete entry point.
//! `wasm1` / `wasm2` await separately-dumped ASTs — see this crate's
//! the generated open-work index. The shape of [`Grammar`] is version-independent, so adding
//! them later is purely a matter of supplying more embedded AST blobs.
//!
//! # Simple grammars
//!
//! [`simple`] holds a few small, self-contained byte grammars (the WASM
//! preamble, unsigned LEB128, ASCII runs) as [`Regex<u8>`](covalence_grammar::regex::Regex) values. They are
//! the easiest thing to point the grammar → bytes-predicate compiler at while
//! the full SpecTec lowering is built out, and double as worked examples.

use crate::ast;

/// One SpecTec grammar definition, `grammar name params : typ = prods`.
///
/// A thin owned view of [`ast::SpecTecDef::Gram`] — the same data, named so
/// callers don't have to pattern-match the catch-all `SpecTecDef` enum.
#[derive(Clone, Debug, PartialEq)]
pub struct Grammar {
    /// The grammar's name (e.g. `"Bvectype"`).
    pub name: String,
    /// Grammar parameters (`grammar X(p₁, …)`); empty for the common case.
    pub params: Vec<ast::SpecTecParam>,
    /// The grammar's result type.
    pub typ: ast::SpecTecTyp,
    /// The productions (alternatives), each `prod : symbol => expr` with
    /// optional premises.
    pub prods: Vec<ast::SpecTecProd>,
}

impl Grammar {
    /// The grammar symbol (right-hand side pattern) of each production.
    pub fn symbols(&self) -> impl Iterator<Item = &ast::SpecTecSym> {
        self.prods.iter().map(|p| {
            let ast::SpecTecProd::Prod { g, .. } = p;
            g
        })
    }

    /// `true` when this is a WebAssembly *binary*-format grammar (name starts
    /// with `B`) — the ones whose terminals are byte literals.
    pub fn is_binary(&self) -> bool {
        self.name.starts_with('B')
    }
}

/// Pull every `gram` definition out of a SpecTec AST, descending into `rec`
/// recursion groups (which is where some grammars are nested).
pub fn grammars(defs: &[ast::SpecTecDef]) -> Vec<Grammar> {
    let mut out = Vec::new();
    collect(defs, &mut out);
    out
}

fn collect(defs: &[ast::SpecTecDef], out: &mut Vec<Grammar>) {
    for def in defs {
        match def {
            ast::SpecTecDef::Gram { x, ps, t, prods } => out.push(Grammar {
                name: x.clone(),
                params: ps.clone(),
                typ: t.clone(),
                prods: prods.clone(),
            }),
            ast::SpecTecDef::Rec { ds } => collect(ds, out),
            _ => {}
        }
    }
}

/// All grammar definitions of the bundled WebAssembly **3.0** spec.
pub fn wasm3() -> Vec<Grammar> {
    grammars(&crate::wasm::get_wasm_spectec_ast())
}

/// The WebAssembly **3.0** *binary*-format grammars (the `B*` definitions) —
/// the subset whose terminals are byte literals and ranges, i.e. the part the
/// byte-grammar bridge ([`crate::regex::sym_to_regex_u8`]) targets.
pub fn wasm3_binary() -> Vec<Grammar> {
    wasm3().into_iter().filter(Grammar::is_binary).collect()
}

/// Small, self-contained byte grammars for bootstrapping, as [`Regex<u8>`](covalence_grammar::regex::Regex).
pub mod simple {
    use covalence_grammar::regex::{Regex, parse_regex_u8};

    /// The WebAssembly module preamble: the four magic bytes `\0asm` followed
    /// by the little-endian version `1` (`\x01\0\0\0`). Every valid `.wasm`
    /// binary starts with exactly these eight bytes.
    pub fn wasm_preamble() -> Regex<u8> {
        parse_regex_u8(r"\0asm\x01\0\0\0").expect("wasm preamble regex")
    }

    /// One unsigned LEB128-encoded integer: zero or more continuation bytes
    /// (high bit set, `0x80..=0xFF`) followed by one terminating byte (high
    /// bit clear, `0x00..=0x7F`). The byte-level shape, ignoring the value /
    /// minimal-encoding constraints.
    pub fn leb128_unsigned() -> Regex<u8> {
        parse_regex_u8(r"[\x80-\xFF]*[\x00-\x7F]").expect("leb128 unsigned regex")
    }

    /// A run of one or more ASCII decimal digits.
    pub fn ascii_digits() -> Regex<u8> {
        parse_regex_u8("[0-9]+").expect("ascii digits regex")
    }

    /// A C-style identifier byte pattern: a leading letter or underscore
    /// followed by letters, digits, or underscores.
    pub fn ident() -> Regex<u8> {
        parse_regex_u8("[A-Za-z_][A-Za-z0-9_]*").expect("ident regex")
    }

    /// The named simple grammars, for iteration / display.
    pub fn all() -> Vec<(&'static str, Regex<u8>)> {
        vec![
            ("wasm_preamble", wasm_preamble()),
            ("leb128_unsigned", leb128_unsigned()),
            ("ascii_digits", ascii_digits()),
            ("ident", ident()),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wasm3_has_grammars() {
        let gs = wasm3();
        assert!(!gs.is_empty(), "WASM 3.0 must expose grammar definitions");
        // The binary `Bvectype` grammar is part of the bundled spec.
        assert!(
            gs.iter().any(|g| g.name == "Bvectype"),
            "expected the Bvectype binary grammar"
        );
    }

    #[test]
    fn binary_grammars_are_b_prefixed() {
        for g in wasm3_binary() {
            assert!(g.is_binary(), "{} should be a binary grammar", g.name);
        }
        assert!(
            !wasm3_binary().is_empty(),
            "expected at least one B* binary grammar"
        );
    }

    #[test]
    fn binary_grammar_symbols_bridge_to_bytes() {
        // Every production symbol of a binary grammar should either bridge to
        // a byte regex or fail with a *typed* BridgeError (never panic).
        let mut bridged = 0usize;
        for g in wasm3_binary() {
            for sym in g.symbols() {
                if crate::regex::sym_to_regex_u8(sym).is_ok() {
                    bridged += 1
                }
            }
        }
        // At least some binary terminals are pure bytes that bridge cleanly.
        assert!(bridged > 0, "no binary grammar symbol bridged to bytes");
    }

    #[test]
    fn simple_grammars_build() {
        // Just exercise the builders + the named registry.
        assert_eq!(simple::all().len(), 4);
        let _ = simple::wasm_preamble();
        let _ = simple::leb128_unsigned();
    }
}
