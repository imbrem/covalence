//! Parameter-indexed SpecTec grammar identities in HOL.
//!
//! Each [`GrammarInstanceKey`] receives a distinct CFG non-terminal and
//! therefore a distinct `Derives_E` tag. Lowering is capability-based: the
//! built-in [`PremiseFreeRegexLowerer`] emits exactly the productions whose
//! symbols are byte regular expressions and whose premise lists are empty.
//! Every other source production remains visible in [`IndexedLoweringReport`].

use covalence_core::{Result, Term};
use covalence_grammar::cfg::{Cfg, NtId, Seg};
use covalence_spectec::ast::SpecTecProd;
use covalence_spectec::indexed::{GrammarInstanceKey, IndexedProduction, ParameterizedGrammarIr};
use covalence_spectec::regex::BridgeError;

use crate::grammar::cfg::GrammarEnv;

/// Why an indexed source production is outside an exact lowering capability.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndexedLoweringRefusal {
    /// Semantic premises require an indexed relation rather than a plain CFG
    /// clause.
    Premises { count: usize },
    /// The production symbol is outside the byte-regex fragment.
    Symbol(BridgeError),
}

/// One source production retained as an explicit lowering residual.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndexedLoweringResidual {
    pub instance_index: usize,
    pub source_index: usize,
    pub refusal: IndexedLoweringRefusal,
}

/// Auditable coverage of an indexed lowering run.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct IndexedLoweringReport {
    pub lowered: usize,
    pub residuals: Vec<IndexedLoweringResidual>,
}

impl IndexedLoweringReport {
    pub fn source_total(&self) -> usize {
        self.lowered + self.residuals.len()
    }

    pub fn is_complete(&self) -> bool {
        self.residuals.is_empty()
    }
}

/// Exact, independently replaceable lowering capability for one indexed
/// production.
///
/// Implementations must return only CFG segments with the same byte language
/// as the source production under `instance`. Refusal is coverage information,
/// not an error and emits no clause.
pub trait IndexedProductionLowerer {
    fn lower(
        &self,
        instance: &GrammarInstanceKey,
        production: &IndexedProduction,
        resolve: &dyn Fn(
            &GrammarInstanceKey,
            &str,
            &[covalence_spectec::ast::SpecTecArg],
        ) -> Option<NtId>,
    ) -> std::result::Result<Vec<Vec<Seg<u8>>>, IndexedLoweringRefusal>;
}

/// Exact lowering of premise-free, self-contained byte-regex productions.
#[derive(Clone, Copy, Debug, Default)]
pub struct PremiseFreeRegexLowerer;

impl IndexedProductionLowerer for PremiseFreeRegexLowerer {
    fn lower(
        &self,
        _instance: &GrammarInstanceKey,
        production: &IndexedProduction,
        resolve: &dyn Fn(
            &GrammarInstanceKey,
            &str,
            &[covalence_spectec::ast::SpecTecArg],
        ) -> Option<NtId>,
    ) -> std::result::Result<Vec<Vec<Seg<u8>>>, IndexedLoweringRefusal> {
        let SpecTecProd::Prod { g, prs, .. } = &production.production;
        if !prs.is_empty() {
            return Err(IndexedLoweringRefusal::Premises { count: prs.len() });
        }
        if let covalence_spectec::ast::SpecTecSym::Var { x, as1 } = g {
            return resolve(_instance, x, as1)
                .map(|nt| vec![vec![Seg::NonTerm(nt)]])
                .ok_or_else(|| {
                    IndexedLoweringRefusal::Symbol(BridgeError::GrammarRef { name: x.clone() })
                });
        }
        let regex =
            covalence_spectec::regex::sym_to_regex_u8(g).map_err(IndexedLoweringRefusal::Symbol)?;
        Ok(vec![vec![Seg::term(regex)]])
    }
}

/// HOL identities for a lossless parameter-indexed grammar IR.
pub struct IndexedGrammarEnv {
    ir: ParameterizedGrammarIr,
    env: GrammarEnv,
    instance_nts: Vec<NtId>,
    roots: Vec<NtId>,
    report: IndexedLoweringReport,
}

impl IndexedGrammarEnv {
    /// Allocate one distinct derivability tag per structurally distinct
    /// grammar instance and lower the exact premise-free byte-regex subset.
    // TODO(cov:wasm.spectec.indexed-grammar-lowering, major): Lower capture-sensitive reference arguments and semantic premises into the HOL relation.
    pub fn new(ir: ParameterizedGrammarIr) -> Result<Self> {
        Self::new_with(ir, &PremiseFreeRegexLowerer)
    }

    /// Construct with an explicit exact production-lowering capability.
    pub fn new_with(
        ir: ParameterizedGrammarIr,
        lowerer: &dyn IndexedProductionLowerer,
    ) -> Result<Self> {
        let mut cfg = Cfg::new();
        let instance_nts: Vec<NtId> = ir
            .instances()
            .iter()
            .enumerate()
            .map(|(index, instance)| {
                cfg.add_nt(format!("{}@indexed#{index}", instance.key.grammar))
            })
            .collect();
        let roots = ir
            .root_indices()
            .iter()
            .map(|index| instance_nts[*index])
            .collect();
        let mut report = IndexedLoweringReport::default();
        let resolve = |source: &GrammarInstanceKey,
                       grammar: &str,
                       args: &[covalence_spectec::ast::SpecTecArg]| {
            ir.resolve_reference(source, grammar, args)
                .and_then(|target| {
                    ir.instances()
                        .iter()
                        .position(|instance| instance.key == target.key)
                })
                .map(|index| instance_nts[index])
        };
        for (instance_index, instance) in ir.instances().iter().enumerate() {
            for production in &instance.productions {
                match lowerer.lower(&instance.key, production, &resolve) {
                    Ok(productions) => {
                        for segs in productions {
                            cfg.add_prod(instance_nts[instance_index], segs);
                        }
                        report.lowered += 1;
                    }
                    Err(refusal) => report.residuals.push(IndexedLoweringResidual {
                        instance_index,
                        source_index: production.source_index,
                        refusal,
                    }),
                }
            }
        }
        Ok(Self {
            ir,
            env: GrammarEnv::new(cfg)?,
            instance_nts,
            roots,
            report,
        })
    }

    pub fn ir(&self) -> &ParameterizedGrammarIr {
        &self.ir
    }

    pub fn env(&self) -> &GrammarEnv {
        &self.env
    }

    pub fn roots(&self) -> &[NtId] {
        &self.roots
    }

    pub fn report(&self) -> &IndexedLoweringReport {
        &self.report
    }

    /// Resolve the exact structural instance key carried by a derivability
    /// non-terminal.
    pub fn key(&self, nt: NtId) -> Option<&GrammarInstanceKey> {
        self.instance_nts
            .iter()
            .position(|candidate| *candidate == nt)
            .and_then(|index| self.ir.instances().get(index))
            .map(|instance| &instance.key)
    }

    /// The HOL `nat` tag occurring in `Derives_E nt word`.
    pub fn tag(&self, nt: NtId) -> Term {
        self.env.tag(nt)
    }

    /// Number of source productions exactly lowered to HOL closure clauses.
    pub fn lowered_clause_count(&self) -> usize {
        self.env.n_clauses()
    }
}

/// Build the identity-preserving indexed environment over bundled WASM 3.0.
pub fn wasm3_indexed_grammar_env(roots: &[GrammarInstanceKey]) -> Result<IndexedGrammarEnv> {
    let ir = ParameterizedGrammarIr::new(&covalence_spectec::grammar::wasm3(), roots)
        .map_err(|e| covalence_core::Error::ConnectiveRule(format!("indexed grammar: {e}")))?;
    IndexedGrammarEnv::new(ir)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_spectec::ast::{SpecTecArg, SpecTecExp};

    #[test]
    fn fixed_symbolic_contexts_have_distinct_derivability_identities() {
        let key = |context: &str| GrammarInstanceKey {
            grammar: "Tfunc_".into(),
            args: vec![SpecTecArg::Exp {
                e: SpecTecExp::Var { id: context.into() },
            }],
        };
        let indexed = wasm3_indexed_grammar_env(&[key("I_left"), key("I_right")]).unwrap();
        assert_ne!(indexed.roots()[0], indexed.roots()[1]);
        assert_ne!(
            indexed.tag(indexed.roots()[0]),
            indexed.tag(indexed.roots()[1])
        );
        assert_ne!(
            indexed.key(indexed.roots()[0]),
            indexed.key(indexed.roots()[1])
        );
        assert_eq!(
            indexed.ir().root(0).unwrap().productions.len(),
            indexed.ir().root(1).unwrap().productions.len()
        );
        assert_eq!(
            indexed.report().source_total(),
            indexed
                .ir()
                .instances()
                .iter()
                .map(|i| i.productions.len())
                .sum()
        );
        assert_eq!(indexed.lowered_clause_count(), indexed.report().lowered);
    }

    #[test]
    fn premise_free_regex_subset_lowers_and_residuals_stay_explicit() {
        use covalence_spectec::ast::{
            SpecTecParam, SpecTecPrem, SpecTecProd, SpecTecSym, SpecTecTyp,
        };
        use covalence_spectec::grammar::Grammar;

        let prod = |g, prs| SpecTecProd::Prod {
            ps: Vec::new(),
            g,
            e: SpecTecExp::Bool { b: true },
            prs,
        };
        let grammar = Grammar {
            name: "Bytes".into(),
            params: vec![SpecTecParam::Exp {
                x: "I".into(),
                t: SpecTecTyp::Var {
                    x: "nat".into(),
                    as1: Vec::new(),
                },
            }],
            typ: SpecTecTyp::Var {
                x: "byte".into(),
                as1: Vec::new(),
            },
            prods: vec![
                prod(SpecTecSym::Num { n: 0x2a }, Vec::new()),
                prod(
                    SpecTecSym::Num { n: 0x2b },
                    vec![SpecTecPrem::If {
                        e: SpecTecExp::Bool { b: true },
                    }],
                ),
                prod(
                    SpecTecSym::Var {
                        x: "Other".into(),
                        as1: Vec::new(),
                    },
                    Vec::new(),
                ),
            ],
        };
        let key = GrammarInstanceKey {
            grammar: "Bytes".into(),
            args: vec![SpecTecArg::Exp {
                e: SpecTecExp::Var { id: "ctx".into() },
            }],
        };
        let ir = ParameterizedGrammarIr::new(&[grammar], &[key]).unwrap();
        let indexed = IndexedGrammarEnv::new(ir).unwrap();

        assert_eq!(indexed.lowered_clause_count(), 1);
        assert_eq!(indexed.report().source_total(), 3);
        assert_eq!(
            indexed.report().residuals[0].refusal,
            IndexedLoweringRefusal::Premises { count: 1 }
        );
        assert!(matches!(
            indexed.report().residuals[1].refusal,
            IndexedLoweringRefusal::Symbol(BridgeError::GrammarRef { .. })
        ));
        assert_eq!(indexed.report().residuals[0].source_index, 1);
        assert_eq!(indexed.report().residuals[1].source_index, 2);
    }

    #[test]
    fn bundled_binary_literal_root_reaches_hol_clause() {
        let indexed = wasm3_indexed_grammar_env(&[GrammarInstanceKey {
            grammar: "Bmagic".into(),
            args: Vec::new(),
        }])
        .unwrap();

        assert_eq!(indexed.report().source_total(), 1);
        assert_eq!(indexed.lowered_clause_count(), 1);
        assert!(indexed.report().is_complete());
        assert_eq!(indexed.env().rule_set().n_clauses().unwrap(), 1);
    }

    #[test]
    fn nullary_reference_closure_lowers_to_a_real_nonterminal_edge() {
        use covalence_spectec::ast::{SpecTecProd, SpecTecSym, SpecTecTyp};
        use covalence_spectec::grammar::Grammar;

        let grammar = |name: &str, g| Grammar {
            name: name.into(),
            params: Vec::new(),
            typ: SpecTecTyp::Var {
                x: "byte".into(),
                as1: Vec::new(),
            },
            prods: vec![SpecTecProd::Prod {
                ps: Vec::new(),
                g,
                e: SpecTecExp::Bool { b: true },
                prs: Vec::new(),
            }],
        };
        let ir = ParameterizedGrammarIr::new(
            &[
                grammar(
                    "Root",
                    SpecTecSym::Var {
                        x: "Leaf".into(),
                        as1: Vec::new(),
                    },
                ),
                grammar("Leaf", SpecTecSym::Num { n: 0x2a }),
            ],
            &[GrammarInstanceKey {
                grammar: "Root".into(),
                args: Vec::new(),
            }],
        )
        .unwrap();
        assert_eq!(ir.instances().len(), 2, "dependency is materialised");

        let indexed = IndexedGrammarEnv::new(ir).unwrap();
        assert!(indexed.report().is_complete());
        assert_eq!(indexed.report().source_total(), 2);
        assert_eq!(indexed.lowered_clause_count(), 2);
        assert_eq!(indexed.key(indexed.roots()[0]).unwrap().grammar, "Root");
    }

    #[test]
    fn ground_parameter_reference_lowers_to_its_monomorphised_edge() {
        use covalence_spectec::ast::{
            SpecTecNum, SpecTecNumTyp, SpecTecParam, SpecTecProd, SpecTecSym, SpecTecTyp,
        };
        use covalence_spectec::grammar::Grammar;

        let parameter = SpecTecParam::Exp {
            x: "N".into(),
            t: SpecTecTyp::Num(SpecTecNumTyp::Nat),
        };
        let production = |g| SpecTecProd::Prod {
            ps: Vec::new(),
            g,
            e: SpecTecExp::Bool { b: true },
            prs: Vec::new(),
        };
        let grammars = [
            Grammar {
                name: "Root".into(),
                params: vec![parameter.clone()],
                typ: SpecTecTyp::Num(SpecTecNumTyp::Nat),
                prods: vec![production(SpecTecSym::Var {
                    x: "Leaf".into(),
                    as1: vec![SpecTecArg::Exp {
                        e: SpecTecExp::Var { id: "N".into() },
                    }],
                })],
            },
            Grammar {
                name: "Leaf".into(),
                params: vec![parameter],
                typ: SpecTecTyp::Num(SpecTecNumTyp::Nat),
                prods: vec![production(SpecTecSym::Num { n: 0x2a })],
            },
        ];
        let root = GrammarInstanceKey {
            grammar: "Root".into(),
            args: vec![SpecTecArg::Exp {
                e: SpecTecExp::Num {
                    n: SpecTecNum::Nat(32),
                },
            }],
        };
        let ir = ParameterizedGrammarIr::new(&grammars, &[root]).unwrap();
        assert_eq!(ir.instances().len(), 2);

        let indexed = IndexedGrammarEnv::new(ir).unwrap();
        assert!(indexed.report().is_complete());
        assert_eq!(indexed.report().source_total(), 2);
        assert_eq!(indexed.lowered_clause_count(), 2);
    }
}
