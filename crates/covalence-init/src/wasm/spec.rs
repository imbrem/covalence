//! **The bundled WebAssembly spec** — load the real SpecTec AST and inventory /
//! measure coverage against it.
//!
//! [`covalence_spectec::wasm::get_wasm_spectec_ast`] ships the WebAssembly **3.0**
//! specification pre-elaborated as `Vec<SpecTecDef>`. This module is the grounding
//! harness (the analogue of the Metamath `import_hol_mm` / `scan_failures` tests):
//! it classifies the spec and reports how much of it the front end can currently
//! lower, so progress toward *importing the whole spec* is a live, measurable
//! number rather than a guess.
//!
//! There is no separately-bundled WASM 1.0/2.0 AST yet (see `covalence-spectec`'s
//! `SKELETONS.md`); "start with WASM 1" means working the **feature subset** —
//! e.g. a handful of numeric `*_ok` relations — out of the 3.0 dump first.

use covalence_spectec::ast::SpecTecDef;
use covalence_spectec::wasm::get_wasm_spectec_ast;

use super::relation;

/// The bundled WebAssembly 3.0 spec as a flat list of top-level definitions.
pub fn wasm_spec() -> Vec<SpecTecDef> {
    get_wasm_spectec_ast()
}

/// Counts of each kind of definition (recursively, flattening `rec` groups).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Inventory {
    pub types: usize,
    pub relations: usize,
    pub functions: usize,
    pub grammars: usize,
    pub rec_groups: usize,
}

/// Classify a definition list (descending into `rec` groups).
pub fn inventory(defs: &[SpecTecDef]) -> Inventory {
    fn go(d: &SpecTecDef, inv: &mut Inventory) {
        match d {
            SpecTecDef::Typ { .. } => inv.types += 1,
            SpecTecDef::Rel { .. } => inv.relations += 1,
            SpecTecDef::Dec { .. } => inv.functions += 1,
            SpecTecDef::Gram { .. } => inv.grammars += 1,
            SpecTecDef::Rec { ds } => {
                inv.rec_groups += 1;
                ds.iter().for_each(|x| go(x, inv));
            }
        }
    }
    let mut inv = Inventory::default();
    defs.iter().for_each(|d| go(d, &mut inv));
    inv
}

/// How many whole relations lower with [`relation::rule_set`] (every rule of the
/// relation expressible), out of the total relation count.
pub fn fully_lowered_relations(defs: &[SpecTecDef]) -> (usize, usize) {
    fn rels<'a>(d: &'a SpecTecDef, out: &mut Vec<&'a SpecTecDef>) {
        match d {
            SpecTecDef::Rel { .. } => out.push(d),
            SpecTecDef::Rec { ds } => ds.iter().for_each(|x| rels(x, out)),
            _ => {}
        }
    }
    let mut all = Vec::new();
    defs.iter().for_each(|d| rels(d, &mut all));
    let total = all.len();
    let ok = all.iter().filter(|d| relation::rule_set(d).is_ok()).count();
    (ok, total)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wasm_spec_loads_and_has_the_expected_shape() {
        let defs = wasm_spec();
        assert!(!defs.is_empty());
        let inv = inventory(&defs);
        // The 3.0 dump is large and relation-rich; guard the coarse shape so a
        // future dep bump that silently empties it fails loudly.
        assert!(inv.relations >= 100, "relations = {}", inv.relations);
        assert!(inv.types >= 100, "types = {}", inv.types);
        assert!(inv.functions >= 100, "functions = {}", inv.functions);
    }

    /// The live **coverage** metric: how many rules of the whole spec the
    /// combined rule set lowers, and how many whole relations are expressible.
    /// Printed with `--nocapture`; asserts only a non-regression floor so the
    /// number can climb without churning the test.
    #[test]
    fn coverage_report() {
        let defs = wasm_spec();
        let inv = inventory(&defs);
        let (rs, report) = relation::spec_rule_set(&defs);
        let clauses = rs.n_clauses().unwrap();
        let (full_ok, full_total) = fully_lowered_relations(&defs);

        println!("inventory: {inv:?}");
        println!(
            "combined rule set: {} clauses  ({} rules lowered / {} skipped)",
            clauses, report.lowered, report.skipped
        );
        println!("whole relations lowered: {full_ok} / {full_total}");
        println!("--- skip reasons ---");
        let mut v: Vec<_> = report.skips.iter().collect();
        v.sort_by_key(|(_, c)| std::cmp::Reverse(**c));
        for (k, c) in v.iter().take(15) {
            println!("  {c:>4}  {k}");
        }

        // Non-regression floors (raise as coverage grows). Current: 274 rules
        // lowered, 64/125 whole relations; the remaining skips are all
        // side-condition (`if`/`let`) and iterated premises — the denotational
        // (function) leg and list recursion, respectively.
        assert!(report.lowered >= 250, "rules lowered = {}", report.lowered);
        assert_eq!(clauses, report.lowered);
        assert!(full_ok >= 60, "whole relations lowered = {full_ok}");
    }
}
