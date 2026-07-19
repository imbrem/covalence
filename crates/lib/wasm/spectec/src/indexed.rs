//! Lossless parameter-indexed grammar IR.
//!
//! The byte-CFG lowering intentionally cannot represent symbolic SpecTec
//! grammar parameters or semantic premises. This module supplies the layer
//! above it: instance identity contains the elaborated argument AST, and every
//! source production (including all premises) is retained verbatim. A later
//! lowering may discharge those premises into an indexed HOL relation; this
//! IR itself makes no production-coverage claim.

use std::collections::VecDeque;

use crate::ast::{SpecTecArg, SpecTecExp, SpecTecParam, SpecTecProd, SpecTecSym, SpecTecTyp};
use crate::grammar::Grammar;

/// Maximum reference depth materialised from one root. An absent deeper
/// instance remains a lowering residual; no edge is emitted to a guessed or
/// wildcard identity.
const MAX_REFERENCE_DEPTH: usize = 64;
const MAX_REFERENCE_INSTANCES: usize = 4096;

/// Canonical identity of one elaborated grammar instance.
///
/// `args` are the elaborated SpecTec AST, not rendered strings. Structural
/// equality therefore cannot collide distinct symbolic contexts. It may keep
/// semantically equivalent expressions as separate instances, which is safe.
#[derive(Clone, Debug, PartialEq)]
pub struct GrammarInstanceKey {
    pub grammar: String,
    pub args: Vec<SpecTecArg>,
}

/// One source production retained with its stable position.
#[derive(Clone, Debug, PartialEq)]
pub struct IndexedProduction {
    pub source_index: usize,
    pub production: SpecTecProd,
}

/// A parameter-indexed grammar definition.
#[derive(Clone, Debug, PartialEq)]
pub struct GrammarInstance {
    pub key: GrammarInstanceKey,
    pub params: Vec<SpecTecParam>,
    pub productions: Vec<IndexedProduction>,
}

/// Lossless indexed grammar roots, deduplicated by structural instance key.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ParameterizedGrammarIr {
    instances: Vec<GrammarInstance>,
    roots: Vec<usize>,
}

/// Refusal to construct an indexed instance.
#[derive(Clone, Debug, PartialEq, thiserror::Error)]
pub enum IndexedGrammarError {
    #[error("unknown grammar `{name}`")]
    Unknown { name: String },
    #[error("grammar `{name}` expects {expected} argument(s), got {actual}")]
    Arity {
        name: String,
        expected: usize,
        actual: usize,
    },
    #[error("argument {index} of grammar `{name}` has the wrong parameter kind")]
    ArgumentKind { name: String, index: usize },
}

impl ParameterizedGrammarIr {
    /// Construct a lossless IR for explicit instances and their exact ground
    /// reference dependency closure.
    ///
    /// Symbolic arguments are accepted and remain in [`GrammarInstanceKey`].
    /// No production is lowered, discarded, or approximated.
    pub fn new(
        grammars: &[Grammar],
        roots: &[GrammarInstanceKey],
    ) -> Result<Self, IndexedGrammarError> {
        let mut instances = Vec::new();
        let mut root_ids = Vec::with_capacity(roots.len());
        let mut pending: VecDeque<(GrammarInstanceKey, bool, usize)> =
            roots.iter().cloned().map(|key| (key, true, 0)).collect();
        while let Some((key, is_root, depth)) = pending.pop_front() {
            let grammar = grammars
                .iter()
                .find(|g| g.name == key.grammar)
                .ok_or_else(|| IndexedGrammarError::Unknown {
                    name: key.grammar.clone(),
                })?;
            if grammar.params.len() != key.args.len() {
                return Err(IndexedGrammarError::Arity {
                    name: key.grammar.clone(),
                    expected: grammar.params.len(),
                    actual: key.args.len(),
                });
            }
            for (index, (param, arg)) in grammar.params.iter().zip(&key.args).enumerate() {
                if !same_arg_kind(param, arg) {
                    return Err(IndexedGrammarError::ArgumentKind {
                        name: key.grammar.clone(),
                        index,
                    });
                }
            }
            let id = if let Some(id) = instances
                .iter()
                .position(|instance: &GrammarInstance| instance.key == key)
            {
                id
            } else {
                let id = instances.len();
                let productions: Vec<_> = grammar
                    .prods
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(source_index, production)| IndexedProduction {
                        source_index,
                        production,
                    })
                    .collect();
                instances.push(GrammarInstance {
                    key: key.clone(),
                    params: grammar.params.clone(),
                    productions,
                });
                let mut dependencies = Vec::new();
                for (source_index, production) in grammar.prods.iter().enumerate() {
                    let SpecTecProd::Prod { g, .. } = production;
                    collect_refs(g, &mut |name, args| {
                        if let Some(args) = substitute_args(&grammar.params, &key.args, args) {
                            dependencies.push((source_index, name.to_string(), args));
                        }
                    });
                }
                for (_, name, args) in dependencies {
                    if depth >= MAX_REFERENCE_DEPTH {
                        continue;
                    }
                    if let Some(target) = grammars.iter().find(|candidate| {
                        candidate.name == name
                            && candidate.params.len() == args.len()
                            && candidate
                                .params
                                .iter()
                                .zip(&args)
                                .all(|(param, arg)| same_arg_kind(param, arg))
                    }) {
                        let dependency = GrammarInstanceKey {
                            grammar: target.name.clone(),
                            args,
                        };
                        if !instances.iter().any(|instance| instance.key == dependency)
                            && !pending.iter().any(|(queued, _, _)| *queued == dependency)
                            && instances.len() + pending.len() < MAX_REFERENCE_INSTANCES
                        {
                            pending.push_back((dependency, false, depth + 1));
                        }
                    }
                }
                id
            };
            if is_root {
                root_ids.push(id);
            }
        }
        Ok(Self {
            instances,
            roots: root_ids,
        })
    }

    pub fn instances(&self) -> &[GrammarInstance] {
        &self.instances
    }

    pub fn root_indices(&self) -> &[usize] {
        &self.roots
    }

    pub fn root(&self, index: usize) -> Option<&GrammarInstance> {
        self.roots
            .get(index)
            .and_then(|instance| self.instances.get(*instance))
    }

    /// Resolve a source reference under an already materialised instance.
    ///
    /// This is exact syntactic substitution, not evaluation: every free
    /// occurrence of an enclosing parameter in the reference arguments is
    /// replaced by its structural argument AST. References with a remaining
    /// symbolic parameter, a shadowing iterator binder, or a kind mismatch
    /// fail closed.
    pub fn resolve_reference(
        &self,
        source: &GrammarInstanceKey,
        grammar: &str,
        args: &[SpecTecArg],
    ) -> Option<&GrammarInstance> {
        let source = self
            .instances
            .iter()
            .find(|instance| instance.key == *source)?;
        let args = substitute_args(&source.params, &source.key.args, args)?;
        self.instances
            .iter()
            .find(|instance| instance.key.grammar == grammar && instance.key.args == args)
    }
}

fn collect_refs(sym: &SpecTecSym, out: &mut impl FnMut(&str, &[SpecTecArg])) {
    match sym {
        SpecTecSym::Var { x, as1 } => out(x, as1),
        SpecTecSym::Num { .. } | SpecTecSym::Text { .. } | SpecTecSym::Eps => {}
        SpecTecSym::Seq { gs } | SpecTecSym::Alt { gs } => {
            for sym in gs {
                collect_refs(sym, out);
            }
        }
        SpecTecSym::Range { g1, g2 } => {
            collect_refs(g1, out);
            collect_refs(g2, out);
        }
        SpecTecSym::Iter { g1, .. } | SpecTecSym::Attr { g1, .. } => {
            collect_refs(g1, out);
        }
    }
}

fn substitute_args(
    params: &[SpecTecParam],
    values: &[SpecTecArg],
    args: &[SpecTecArg],
) -> Option<Vec<SpecTecArg>> {
    if params.len() != values.len()
        || !params
            .iter()
            .zip(values)
            .all(|(param, value)| same_arg_kind(param, value))
    {
        return None;
    }
    args.iter()
        .map(|arg| substitute_arg(params, values, arg))
        .collect()
}

fn substitute_arg(
    params: &[SpecTecParam],
    values: &[SpecTecArg],
    arg: &SpecTecArg,
) -> Option<SpecTecArg> {
    match arg {
        SpecTecArg::Exp { e } => Some(SpecTecArg::Exp {
            e: substitute_exp(params, values, e)?,
        }),
        SpecTecArg::Typ { t } => Some(SpecTecArg::Typ {
            t: substitute_typ(params, values, t)?,
        }),
        SpecTecArg::Def { x } => match lookup(params, values, x) {
            Some(SpecTecArg::Def { x }) => Some(SpecTecArg::Def { x: x.clone() }),
            Some(_) => None,
            None => Some(arg.clone()),
        },
        SpecTecArg::Gram { g } => {
            if let SpecTecSym::Var { x, as1 } = g
                && as1.is_empty()
            {
                match lookup(params, values, x) {
                    Some(SpecTecArg::Gram { g }) => {
                        return Some(SpecTecArg::Gram { g: g.clone() });
                    }
                    Some(_) => return None,
                    None => {}
                }
            }
            Some(SpecTecArg::Gram {
                g: substitute_sym(params, values, g)?,
            })
        }
    }
}

fn lookup<'a>(
    params: &[SpecTecParam],
    values: &'a [SpecTecArg],
    name: &str,
) -> Option<&'a SpecTecArg> {
    params
        .iter()
        .position(|param| param_name(param) == name)
        .and_then(|index| values.get(index))
}

fn param_name(param: &SpecTecParam) -> &str {
    match param {
        SpecTecParam::Exp { x, .. }
        | SpecTecParam::Typ { x }
        | SpecTecParam::Def { x, .. }
        | SpecTecParam::Gram { x, .. } => x,
    }
}

fn substitute_sym(
    params: &[SpecTecParam],
    values: &[SpecTecArg],
    sym: &SpecTecSym,
) -> Option<SpecTecSym> {
    use SpecTecSym::*;
    Some(match sym {
        Var { x, as1 } if as1.is_empty() => match lookup(params, values, x) {
            Some(SpecTecArg::Gram { g }) => return Some(g.clone()),
            Some(_) => return None,
            None => sym.clone(),
        },
        Var { x, as1 } => Var {
            x: x.clone(),
            as1: substitute_args(params, values, as1)?,
        },
        Num { .. } | Text { .. } | Eps => sym.clone(),
        Seq { gs } => Seq {
            gs: gs
                .iter()
                .map(|g| substitute_sym(params, values, g))
                .collect::<Option<_>>()?,
        },
        Alt { gs } => Alt {
            gs: gs
                .iter()
                .map(|g| substitute_sym(params, values, g))
                .collect::<Option<_>>()?,
        },
        Range { g1, g2 } => Range {
            g1: Box::new(substitute_sym(params, values, g1)?),
            g2: Box::new(substitute_sym(params, values, g2)?),
        },
        Iter { g1, it, xes } => {
            if xes.iter().any(|xe| {
                let crate::ast::SpecTecIterExp::Dom { x, .. } = xe;
                params.iter().any(|param| param_name(param) == x)
            }) {
                return None;
            }
            Iter {
                g1: Box::new(substitute_sym(params, values, g1)?),
                it: it.clone(),
                xes: xes
                    .iter()
                    .map(|xe| {
                        let crate::ast::SpecTecIterExp::Dom { x, e } = xe;
                        Some(crate::ast::SpecTecIterExp::Dom {
                            x: x.clone(),
                            e: substitute_exp(params, values, e)?,
                        })
                    })
                    .collect::<Option<_>>()?,
            }
        }
        Attr { e, g1 } => Attr {
            e: substitute_exp(params, values, e)?,
            g1: Box::new(substitute_sym(params, values, g1)?),
        },
    })
}

fn substitute_typ(
    params: &[SpecTecParam],
    values: &[SpecTecArg],
    typ: &SpecTecTyp,
) -> Option<SpecTecTyp> {
    use SpecTecTyp::*;
    Some(match typ {
        Var { x, as1 } if as1.is_empty() => match lookup(params, values, x) {
            Some(SpecTecArg::Typ { t }) => return Some(t.clone()),
            Some(_) => return None,
            None => typ.clone(),
        },
        Var { x, as1 } => Var {
            x: x.clone(),
            as1: substitute_args(params, values, as1)?,
        },
        Bool | Num(_) | Text => typ.clone(),
        Tup { ets } => Tup {
            ets: ets
                .iter()
                .map(|et| {
                    let crate::ast::SpecTecTypBind::Bind { id, typ } = et;
                    Some(crate::ast::SpecTecTypBind::Bind {
                        id: id.clone(),
                        typ: substitute_typ(params, values, typ)?,
                    })
                })
                .collect::<Option<_>>()?,
        },
        Iter { t1, it } => Iter {
            t1: Box::new(substitute_typ(params, values, t1)?),
            it: it.clone(),
        },
    })
}

/// Capture-free substitution over the ground argument fragment used by the
/// bundled grammars. Refusing other expression forms is deliberate: extending
/// this fragment cannot silently turn a symbolic dependency into a ground one.
fn substitute_exp(
    params: &[SpecTecParam],
    values: &[SpecTecArg],
    exp: &SpecTecExp,
) -> Option<SpecTecExp> {
    use SpecTecExp::*;
    Some(match exp {
        Var { id } => match lookup(params, values, id) {
            Some(SpecTecArg::Exp { e }) => return Some(e.clone()),
            Some(_) => return None,
            None => exp.clone(),
        },
        Bool { .. } | Num { .. } | Text { .. } => exp.clone(),
        Un { op, t, e2 } => Un {
            op: op.clone(),
            t: t.clone(),
            e2: Box::new(substitute_exp(params, values, e2)?),
        },
        Bin { op, t, e1, e2 } => Bin {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(substitute_exp(params, values, e1)?),
            e2: Box::new(substitute_exp(params, values, e2)?),
        },
        Call { x, as1 } if as1.is_empty() => match lookup(params, values, x) {
            Some(SpecTecArg::Exp { e }) => return Some(e.clone()),
            Some(_) => return None,
            None => exp.clone(),
        },
        Call { x, as1 } => Call {
            x: x.clone(),
            as1: substitute_args(params, values, as1)?,
        },
        Cvt { nt1, nt2, e1 } => Cvt {
            nt1: nt1.clone(),
            nt2: nt2.clone(),
            e1: Box::new(substitute_exp(params, values, e1)?),
        },
        // These forms do not occur in the bundled grammar-reference argument
        // fragment. Refuse instead of implementing an accidentally
        // capture-unsafe approximation.
        Cmp { .. }
        | Idx { .. }
        | Slice { .. }
        | Upd { .. }
        | Ext { .. }
        | Str { .. }
        | Dot { .. }
        | Comp { .. }
        | Mem { .. }
        | Len { .. }
        | Tup { .. }
        | Iter { .. }
        | Proj { .. }
        | Case { .. }
        | Uncase { .. }
        | Opt { .. }
        | Unopt { .. }
        | List { .. }
        | Lift { .. }
        | Cat { .. }
        | Sub { .. } => return None,
    })
}

fn same_arg_kind(param: &SpecTecParam, arg: &SpecTecArg) -> bool {
    matches!(
        (param, arg),
        (SpecTecParam::Exp { .. }, SpecTecArg::Exp { .. })
            | (SpecTecParam::Typ { .. }, SpecTecArg::Typ { .. })
            | (SpecTecParam::Def { .. }, SpecTecArg::Def { .. })
            | (SpecTecParam::Gram { .. }, SpecTecArg::Gram { .. })
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{SpecTecNum, SpecTecNumTyp, SpecTecOpTyp};

    #[test]
    fn symbolic_contexts_remain_distinct_and_premises_are_lossless() {
        let grammars = crate::grammar::wasm3();
        let key = |context: &str| GrammarInstanceKey {
            grammar: "Tfunc_".into(),
            args: vec![SpecTecArg::Exp {
                e: SpecTecExp::Var { id: context.into() },
            }],
        };
        let ir = ParameterizedGrammarIr::new(&grammars, &[key("I_left"), key("I_right")]).unwrap();
        assert!(
            ir.instances().len() >= 2,
            "the two roots plus their exact nullary dependency closure"
        );
        assert_ne!(ir.root(0).unwrap().key, ir.root(1).unwrap().key);

        let source = grammars.iter().find(|g| g.name == "Tfunc_").unwrap();
        assert!(source.prods.iter().any(|production| {
            let SpecTecProd::Prod { prs, .. } = production;
            !prs.is_empty()
        }));
        for root in [ir.root(0).unwrap(), ir.root(1).unwrap()] {
            assert_eq!(root.productions.len(), source.prods.len());
            assert!(
                root.productions
                    .iter()
                    .zip(&source.prods)
                    .all(|(indexed, source)| indexed.production == *source)
            );
        }
    }

    #[test]
    fn ground_parameters_materialise_referenced_instances() {
        let param = SpecTecParam::Exp {
            x: "N".into(),
            t: SpecTecTyp::Num(SpecTecNumTyp::Nat),
        };
        let prod = |g| SpecTecProd::Prod {
            ps: Vec::new(),
            g,
            e: SpecTecExp::Bool { b: true },
            prs: Vec::new(),
        };
        let grammars = vec![
            Grammar {
                name: "Root".into(),
                params: vec![param.clone()],
                typ: SpecTecTyp::Num(SpecTecNumTyp::Nat),
                prods: vec![prod(SpecTecSym::Var {
                    x: "Leaf".into(),
                    as1: vec![SpecTecArg::Exp {
                        e: SpecTecExp::Bin {
                            op: crate::ast::SpecTecBinOp::Add,
                            t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
                            e1: Box::new(SpecTecExp::Var { id: "N".into() }),
                            e2: Box::new(SpecTecExp::Num {
                                n: SpecTecNum::Nat(1),
                            }),
                        },
                    }],
                })],
            },
            Grammar {
                name: "Leaf".into(),
                params: vec![param],
                typ: SpecTecTyp::Num(SpecTecNumTyp::Nat),
                prods: vec![prod(SpecTecSym::Num { n: 0x2a })],
            },
        ];
        let root = GrammarInstanceKey {
            grammar: "Root".into(),
            args: vec![SpecTecArg::Exp {
                e: SpecTecExp::Num {
                    n: SpecTecNum::Nat(31),
                },
            }],
        };
        let ir = ParameterizedGrammarIr::new(&grammars, &[root.clone()]).unwrap();
        assert_eq!(ir.instances().len(), 2);
        let target = ir
            .resolve_reference(
                &root,
                "Leaf",
                &[SpecTecArg::Exp {
                    e: SpecTecExp::Bin {
                        op: crate::ast::SpecTecBinOp::Add,
                        t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
                        e1: Box::new(SpecTecExp::Var { id: "N".into() }),
                        e2: Box::new(SpecTecExp::Num {
                            n: SpecTecNum::Nat(1),
                        }),
                    },
                }],
            )
            .unwrap();
        assert_eq!(target.key.grammar, "Leaf");
        assert!(matches!(
            &target.key.args[0],
            SpecTecArg::Exp {
                e: SpecTecExp::Bin { e1, .. }
            } if matches!(e1.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(31) })
        ));
    }

    #[test]
    fn bundled_ground_recursive_instance_is_bounded_and_fail_closed() {
        let root = GrammarInstanceKey {
            grammar: "BuN".into(),
            args: vec![SpecTecArg::Exp {
                e: SpecTecExp::Num {
                    n: SpecTecNum::Nat(32),
                },
            }],
        };
        let ir = ParameterizedGrammarIr::new(&crate::grammar::wasm3(), &[root]).unwrap();

        assert!(
            ir.instances().len() > 1,
            "ground recursive dependencies are materialised"
        );
        assert!(
            ir.instances().len() <= MAX_REFERENCE_INSTANCES,
            "symbolic recursion is bounded rather than expanded forever"
        );
        assert_eq!(ir.root(0).unwrap().key.grammar, "BuN");
    }
}
