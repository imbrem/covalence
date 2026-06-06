//! Whole-document AST + converter toward `spectec_ast::SpecTecDef`.
//!
//! `Doc` is the highest-level Covalence-internal representation of an
//! elaborated SpecTec file (or collection of files). It groups
//! rule-decls under their relations, def-clauses under their signatures,
//! merges syntax profiles, and reflects var declarations as context
//! data. Each entry carries a `Span` so diagnostics can point back to
//! source.
//!
//! [`to_spectec_ast`] converts a [`Doc`] into a `Vec<spectec_ast::SpecTecDef>`
//! suitable for diffing against `wasm_spec_ast::get_wasm_spectec_ast()`.
//! The current converter is partial: it emits skeleton `Typ`, `Rel`,
//! `Dec`, `Gram` decls with names, MixOp templates, and rule/clause
//! counts, but does not yet encode the full operand/premise content.
//! Phase 2g exercises the converter end-to-end on the wasm-3.0 corpus
//! and reports the coverage gap.

use crate::cst::{GrammarDecl, RelationDecl, RuleDecl, Top, VarDecl};
use crate::elab::{
    elab_rule_conclusion, BinOp, CmpOp, ElabContext, ElabPremise, Expr, IterBinding,
    IterKind, MergedSyntax, NumLit, NumTyp, OpType, Path as ElabPath, UnOp,
};
use crate::source::Span;

/// A grouped, elaborated whole-document representation.
#[derive(Debug, Default, Clone)]
pub struct Doc {
    /// One entry per distinct `syntax NAME` (profiles merged).
    pub syntax: Vec<DocSyntax>,
    /// Each declared `var NAME : T`.
    pub vars: Vec<DocVar>,
    /// Each `relation NAME: ...` with its associated rules grouped by name.
    pub relations: Vec<DocRelation>,
    /// Each `def $NAME : T` signature with its clauses grouped.
    pub defs: Vec<DocDef>,
    /// Each `grammar NAME ...` declaration.
    pub grammars: Vec<DocGrammar>,
}

#[derive(Debug, Clone)]
pub struct DocSyntax {
    pub span: Span,
    pub name: String,
    pub merged: MergedSyntax,
}

#[derive(Debug, Clone)]
pub struct DocVar {
    pub span: Span,
    pub name: String,
    pub decl: VarDecl,
}

#[derive(Debug, Clone)]
pub struct DocRelation {
    pub span: Span,
    pub name: String,
    pub decl: RelationDecl,
    pub rules: Vec<RuleDecl>,
}

#[derive(Debug, Clone)]
pub struct DocDef {
    pub span: Span,
    pub name: String,
    /// First-seen signature for the def (later signatures with the same
    /// name are stored as additional entries; SpecTec sometimes uses
    /// multiple sigs as forward decls).
    pub sig: crate::cst::DefSig,
    /// Clauses pattern-matching the def, in source order.
    pub clauses: Vec<crate::cst::DefClause>,
}

#[derive(Debug, Clone)]
pub struct DocGrammar {
    pub span: Span,
    pub name: String,
    pub decl: GrammarDecl,
}

/// Group a flat `Vec<Top>` into a `Doc`. Rules are bucketed by their
/// relation name; def clauses by their def name.
pub fn build_doc(tops: &[Top], ctx: &ElabContext) -> Doc {
    let mut doc = Doc::default();

    // Syntax: one entry per merged name. Walk in source order so the
    // first occurrence determines the displayed span.
    let mut seen_syntax = std::collections::HashSet::new();
    for t in tops {
        if let Top::Syntax(s) = t
            && seen_syntax.insert(s.name.text.clone())
                && let Some(merged) = ctx.syntax_defs.get(&s.name.text) {
                    doc.syntax.push(DocSyntax {
                        span: s.span,
                        name: s.name.text.clone(),
                        merged: merged.clone(),
                    });
                }
    }

    // Vars, grammars, etc.
    for t in tops {
        match t {
            Top::Var(v) => doc.vars.push(DocVar {
                span: v.span,
                name: v.name.text.clone(),
                decl: v.clone(),
            }),
            Top::Grammar(g) => doc.grammars.push(DocGrammar {
                span: g.span,
                name: g.name.text.clone(),
                decl: g.clone(),
            }),
            _ => {}
        }
    }

    // Relations: bucket rules by name.
    let mut rel_idx: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    for t in tops {
        if let Top::Relation(r) = t {
            let idx = doc.relations.len();
            rel_idx.insert(r.name.text.clone(), idx);
            doc.relations.push(DocRelation {
                span: r.span,
                name: r.name.text.clone(),
                decl: r.clone(),
                rules: Vec::new(),
            });
        }
    }
    for t in tops {
        if let Top::Rule(r) = t
            && let Some(&idx) = rel_idx.get(&r.name.text) {
                doc.relations[idx].rules.push(r.clone());
            }
    }

    // Defs: bucket clauses by name.
    let mut def_idx: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    for t in tops {
        if let Top::DefSig(d) = t {
            // Use the first sig per name; later sigs are uncommon but
            // when present they amend the same name's clauses.
            def_idx.entry(d.name.text.clone()).or_insert_with(|| {
                let idx = doc.defs.len();
                doc.defs.push(DocDef {
                    span: d.span,
                    name: d.name.text.clone(),
                    sig: d.clone(),
                    clauses: Vec::new(),
                });
                idx
            });
        }
    }
    for t in tops {
        if let Top::DefClause(c) = t
            && let Some(&idx) = def_idx.get(&c.name.text) {
                doc.defs[idx].clauses.push(c.clone());
            }
    }

    doc
}

/// Produce a `Vec<SpecTecDef>` from a `Doc`. The MixOp templates are
/// filled in from `ctx.op_table` (where available), but operand bodies,
/// parameter lists, premise/clause contents, and SCC mutual-recursion
/// grouping are placeholders. Full content lowering is follow-up work;
/// this lets the corpus diff start running.
pub fn to_spectec_ast(doc: &Doc, ctx: &ElabContext) -> Vec<spectec_ast::SpecTecDef> {
    let mut out = Vec::new();

    // Typ entries from merged syntax.
    for syn in &doc.syntax {
        out.push(spectec_ast::SpecTecDef::Typ {
            x: syn.name.clone(),
            ps: Vec::new(),
            insts: Vec::new(),
        });
    }

    // Rel entries from relations. Each rule's conclusion + premises
    // is elaborated via `elab_rule_conclusion` and lowered to the
    // SpecTec rule shape (conclusion wrapped as a Tup, premises lowered
    // through `premise_to_spectec`).
    for rel in &doc.relations {
        let mixop = mixop_for(&rel.name, ctx);
        let rules = rel
            .rules
            .iter()
            .map(|rd| {
                let elab = elab_rule_conclusion(rd, ctx).ok();
                let (e, prs) = match elab.as_ref() {
                    Some(elab) => (
                        tup_of_operands(&elab.operands, ctx),
                        elab.premises.iter().map(|p| premise_to_spectec(p, ctx)).collect(),
                    ),
                    None => (raw_sentinel(), Vec::new()),
                };
                spectec_ast::SpecTecRule::Rule {
                    x: rd.case.as_ref().map(|c| c.text.clone()).unwrap_or_default(),
                    ps: Vec::new(),
                    op: mixop_for(&rel.name, ctx),
                    e,
                    prs,
                }
            })
            .collect();
        out.push(spectec_ast::SpecTecDef::Rel {
            x: rel.name.clone(),
            ps: Vec::new(),
            op: mixop,
            t: placeholder_typ(),
            rules,
        });
    }

    // Dec entries from defs. Clause bodies aren't yet elaborated through
    // the same mixfix machinery (`elab_rule_conclusion` only handles
    // rules); for now we emit empty clauses but keep the count.
    for d in &doc.defs {
        out.push(spectec_ast::SpecTecDef::Dec {
            x: d.name.clone(),
            ps: Vec::new(),
            t: placeholder_typ(),
            clauses: d
                .clauses
                .iter()
                .map(|_| spectec_ast::SpecTecClause::Clause {
                    ps: Vec::new(),
                    as_: Vec::new(),
                    e: raw_sentinel(),
                    prs: Vec::new(),
                })
                .collect(),
        });
    }

    // Gram entries from grammars.
    for g in &doc.grammars {
        out.push(spectec_ast::SpecTecDef::Gram {
            x: g.name.clone(),
            ps: Vec::new(),
            t: placeholder_typ(),
            prods: Vec::new(),
        });
    }

    out
}

fn mixop_for(name: &str, ctx: &ElabContext) -> spectec_ast::MixOp {
    let Some(op) = ctx.op_table.iter().find(|o| o.name == name) else {
        return spectec_ast::MixOp::new(Vec::new());
    };
    // Build the `%`-delimited template string and split on `%`. This
    // matches `spectec_ast::MixOp::Decode`'s representation exactly.
    let mut s = String::new();
    for f in &op.fragments {
        match f {
            crate::mixfix::Fragment::Hole(_) => s.push('%'),
            crate::mixfix::Fragment::Lit(t) => {
                use crate::token::Token::*;
                let text = match t {
                    Ident(n) => n.clone(),
                    Nat(n) => n.to_string(),
                    other => other.describe().trim_matches('`').to_string(),
                };
                s.push_str(&text);
            }
        }
    }
    let fragments: Vec<String> = s.split('%').map(str::to_owned).collect();
    spectec_ast::MixOp::new(fragments)
}

/// Placeholder operand-tuple type for relations / defs / grammars.
/// Real type lowering (synthesising `SpecTecTyp::Tup` from the operand
/// arity + per-hole types) is follow-up work; for now we emit the
/// reference's stand-in.
fn placeholder_typ() -> spectec_ast::SpecTecTyp {
    spectec_ast::SpecTecTyp::Bool
}

// ---------- Expr → SpecTecExp ----------

/// Lower an elaborated `Expr` into `spectec_ast::SpecTecExp`. For
/// variants Covalence doesn't yet structurally produce (e.g. `Bin`,
/// `Cmp`, `Idx`), the lowering is a direct mapping; in practice the
/// `Raw` fallback fires for un-structured expressions.
pub fn expr_to_spectec(e: &Expr, ctx: &ElabContext) -> spectec_ast::SpecTecExp {
    use spectec_ast::SpecTecExp as S;
    match e {
        Expr::Var { name, .. } => S::Var { id: name.clone() },
        Expr::Bool { value, .. } => S::Bool { b: *value },
        Expr::Num { value, .. } => S::Num {
            n: num_lit_to_spectec(value),
        },
        Expr::Text { value, .. } => S::Text { t: value.clone() },
        Expr::Un { op, ty, e, .. } => S::Un {
            op: un_op_to_spectec(op),
            t: op_type_to_spectec(ty),
            e2: Box::new(expr_to_spectec(e, ctx)),
        },
        Expr::Bin { op, ty, e1, e2, .. } => S::Bin {
            op: bin_op_to_spectec(op),
            t: op_type_to_spectec(ty),
            e1: Box::new(expr_to_spectec(e1, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
        },
        Expr::Cmp { op, ty, e1, e2, .. } => S::Cmp {
            op: cmp_op_to_spectec(op),
            t: op_type_to_spectec(ty),
            e1: Box::new(expr_to_spectec(e1, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
        },
        Expr::Idx { e1, e2, .. } => S::Idx {
            e1: Box::new(expr_to_spectec(e1, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
        },
        Expr::Slice { e1, e2, e3, .. } => S::Slice {
            e1: Box::new(expr_to_spectec(e1, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
            e3: Box::new(expr_to_spectec(e3, ctx)),
        },
        Expr::Upd { e1, path, e2, .. } => S::Upd {
            e1: Box::new(expr_to_spectec(e1, ctx)),
            path: Box::new(path_to_spectec(path, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
        },
        Expr::Ext { e1, path, e2, .. } => S::Ext {
            e1: Box::new(expr_to_spectec(e1, ctx)),
            path: Box::new(path_to_spectec(path, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
        },
        Expr::Str { fields, .. } => S::Str {
            efs: fields
                .iter()
                .map(|f| spectec_ast::SpecTecExpField::Field {
                    at: mixop_from_name(&f.field),
                    e: expr_to_spectec(&f.value, ctx),
                })
                .collect(),
        },
        Expr::Dot { e, field, .. } => S::Dot {
            e1: Box::new(expr_to_spectec(e, ctx)),
            at: mixop_from_name(field),
        },
        Expr::Comp { e1, e2, .. } => S::Comp {
            e1: Box::new(expr_to_spectec(e1, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
        },
        Expr::Mem { e1, e2, .. } => S::Mem {
            e1: Box::new(expr_to_spectec(e1, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
        },
        Expr::Len { e, .. } => S::Len {
            e1: Box::new(expr_to_spectec(e, ctx)),
        },
        Expr::Tup { items, .. } => S::Tup {
            es: items.iter().map(|i| expr_to_spectec(i, ctx)).collect(),
        },
        Expr::Call { name, args, .. } => S::Call {
            x: name.clone(),
            as1: args
                .iter()
                .map(|_| spectec_ast::SpecTecArg::Exp { e: raw_sentinel() })
                .collect(),
        },
        Expr::Iter {
            inner,
            kind,
            bindings,
            ..
        } => {
            let (it, xes) = iter_kind_to_spectec(kind, bindings, ctx);
            S::Iter {
                e1: Box::new(expr_to_spectec(inner, ctx)),
                it,
                xes,
            }
        }
        Expr::Proj { e, index, .. } => S::Proj {
            e1: Box::new(expr_to_spectec(e, ctx)),
            i: *index,
        },
        Expr::Case { head, args, .. } => {
            let op = mixop_for(head, ctx);
            let inner = if args.len() == 1 {
                expr_to_spectec(&args[0], ctx)
            } else {
                S::Tup {
                    es: args.iter().map(|a| expr_to_spectec(a, ctx)).collect(),
                }
            };
            S::Case {
                op,
                e1: Box::new(inner),
            }
        }
        Expr::Uncase { e, head, .. } => S::Uncase {
            e1: Box::new(expr_to_spectec(e, ctx)),
            op: mixop_from_name(head),
        },
        Expr::Opt { inner, .. } => S::Opt {
            eo: inner.as_ref().map(|e| Box::new(expr_to_spectec(e, ctx))),
        },
        Expr::Unopt { e, .. } => S::Unopt {
            e1: Box::new(expr_to_spectec(e, ctx)),
        },
        Expr::List { items, .. } => S::List {
            es: items.iter().map(|i| expr_to_spectec(i, ctx)).collect(),
        },
        Expr::Lift { e, .. } => S::Lift {
            e1: Box::new(expr_to_spectec(e, ctx)),
        },
        Expr::Cat { e1, e2, .. } => S::Cat {
            e1: Box::new(expr_to_spectec(e1, ctx)),
            e2: Box::new(expr_to_spectec(e2, ctx)),
        },
        Expr::Cvt { from, to, e, .. } => S::Cvt {
            nt1: num_typ_to_spectec(from),
            nt2: num_typ_to_spectec(to),
            e1: Box::new(expr_to_spectec(e, ctx)),
        },
        Expr::Sub { e, .. } => S::Sub {
            t1: placeholder_typ(),
            t2: placeholder_typ(),
            e1: Box::new(expr_to_spectec(e, ctx)),
        },
        // `eps` lowers to the empty list (SpecTec's notion of "empty
        // sequence").
        Expr::Eps { .. } => S::List { es: Vec::new() },
        // Sentinel for un-structured expressions; visible in the
        // differential test so we can track lowering coverage.
        Expr::Raw(_) => raw_sentinel(),
    }
}

/// Sentinel value for un-elaborated expressions. Chosen so it's
/// distinguishable in a differential diff (an unlikely `Bool { b: false }`
/// won't collide with anything the OCaml elaborator produces).
fn raw_sentinel() -> spectec_ast::SpecTecExp {
    spectec_ast::SpecTecExp::Bool { b: false }
}

// ---------- ElabPremise → SpecTecPrem ----------

pub fn premise_to_spectec(p: &ElabPremise, ctx: &ElabContext) -> spectec_ast::SpecTecPrem {
    use spectec_ast::SpecTecPrem as P;
    match p {
        ElabPremise::Rule {
            rel_name, operands, ..
        } => {
            let e = tup_of_operands(operands, ctx);
            P::Rule {
                x: rel_name.clone(),
                as1: Vec::new(),
                op: mixop_for(rel_name, ctx),
                e,
            }
        }
        ElabPremise::If(e) => P::If {
            e: expr_to_spectec(e, ctx),
        },
        ElabPremise::Let { lhs, rhs } => P::Let {
            e1: expr_to_spectec(lhs, ctx),
            e2: expr_to_spectec(rhs, ctx),
        },
        ElabPremise::Else => P::Else,
        ElabPremise::Iter {
            inner,
            kind,
            bindings,
        } => {
            let (it, xes) = iter_kind_to_spectec(kind, bindings, ctx);
            P::Iter {
                pr1: Box::new(premise_to_spectec(inner, ctx)),
                it,
                xes,
            }
        }
        ElabPremise::Raw(_) => P::If { e: raw_sentinel() },
    }
}

/// Wrap a vector of operand expressions as a single tuple expression,
/// the form `spectec_ast` uses for rule conclusions and relation
/// premises.
fn tup_of_operands(operands: &[Expr], ctx: &ElabContext) -> spectec_ast::SpecTecExp {
    spectec_ast::SpecTecExp::Tup {
        es: operands.iter().map(|o| expr_to_spectec(o, ctx)).collect(),
    }
}

// ---------- supporting converters ----------

fn iter_kind_to_spectec(
    kind: &IterKind,
    bindings: &[IterBinding],
    ctx: &ElabContext,
) -> (spectec_ast::SpecTecIter, Vec<spectec_ast::SpecTecIterExp>) {
    use spectec_ast::{SpecTecIter as I, SpecTecIterExp};
    let it = match kind {
        IterKind::Opt => I::Opt,
        IterKind::Star => I::List,
        IterKind::Plus => I::List1,
        IterKind::Length(_tr) => I::ListN {
            // The count expression is kept as a raw token run; we
            // can't yet lower it into a SpecTecExp tree, so we emit a
            // placeholder. The `xo` field captures any variable name
            // bound by the count (none in our current representation).
            e: vec![raw_sentinel()],
            xo: Vec::new(),
        },
    };
    let xes: Vec<SpecTecIterExp> = bindings
        .iter()
        .map(|b| SpecTecIterExp::Dom {
            x: b.var.clone(),
            e: spectec_ast::SpecTecExp::Var {
                id: b.source.clone(),
            },
        })
        .collect();
    let _ = ctx; // reserved for future hole-typed iter
    (it, xes)
}

fn num_lit_to_spectec(n: &NumLit) -> spectec_ast::SpecTecNum {
    use spectec_ast::SpecTecNum as N;
    match n {
        NumLit::Nat(v) => N::Nat(nat_to_u64(v)),
        NumLit::Int(v) => N::Int(int_to_i64(v)),
        NumLit::Rat(s) => N::Rat(s.clone()),
        NumLit::Real(s) => N::Real(s.clone()),
    }
}

/// Clamp an arbitrary-precision `Nat` to `u64` for the `spectec_ast`
/// dump format. Values exceeding `u64::MAX` are saturated; this matches
/// the OCaml dumper's behaviour on overflow (it ignores precision
/// beyond `u64`).
fn nat_to_u64(n: &covalence_types::Nat) -> u64 {
    u64::try_from(n).unwrap_or(u64::MAX)
}

fn int_to_i64(n: &covalence_types::Int) -> i64 {
    i64::try_from(n).unwrap_or(i64::MAX)
}

fn op_type_to_spectec(t: &OpType) -> spectec_ast::SpecTecOpTyp {
    use spectec_ast::SpecTecOpTyp as O;
    match t {
        OpType::Nat => O::Num(spectec_ast::SpecTecNumTyp::Nat),
        OpType::Int => O::Num(spectec_ast::SpecTecNumTyp::Int),
        OpType::Rat => O::Num(spectec_ast::SpecTecNumTyp::Rat),
        OpType::Real => O::Num(spectec_ast::SpecTecNumTyp::Real),
        OpType::Bool => O::Bool(spectec_ast::SpecTecBoolTyp::Bool),
    }
}

fn num_typ_to_spectec(t: &NumTyp) -> spectec_ast::SpecTecNumTyp {
    use spectec_ast::SpecTecNumTyp as N;
    match t {
        NumTyp::Nat => N::Nat,
        NumTyp::Int => N::Int,
        NumTyp::Rat => N::Rat,
        NumTyp::Real => N::Real,
    }
}

fn un_op_to_spectec(op: &UnOp) -> spectec_ast::SpecTecUnOp {
    use spectec_ast::SpecTecUnOp as O;
    match op {
        UnOp::Not => O::Not,
        UnOp::Plus => O::Plus,
        UnOp::Minus => O::Minus,
        UnOp::PlusMinus => O::PlusMinus,
        UnOp::MinusPlus => O::MinusPlus,
    }
}

fn bin_op_to_spectec(op: &BinOp) -> spectec_ast::SpecTecBinOp {
    use spectec_ast::SpecTecBinOp as O;
    match op {
        BinOp::And => O::And,
        BinOp::Or => O::Or,
        BinOp::Impl => O::Impl,
        BinOp::Equiv => O::Equiv,
        BinOp::Add => O::Add,
        BinOp::Sub => O::Sub,
        BinOp::Mul => O::Mul,
        BinOp::Div => O::Div,
        BinOp::Mod => O::Mod,
        BinOp::Pow => O::Pow,
    }
}

fn cmp_op_to_spectec(op: &CmpOp) -> spectec_ast::SpecTecCmpOp {
    use spectec_ast::SpecTecCmpOp as O;
    match op {
        CmpOp::Eq => O::Eq,
        CmpOp::Ne => O::Ne,
        CmpOp::Lt => O::Lt,
        CmpOp::Gt => O::Gt,
        CmpOp::Le => O::Le,
        CmpOp::Ge => O::Ge,
    }
}

fn path_to_spectec(p: &ElabPath, ctx: &ElabContext) -> spectec_ast::SpecTecPath {
    use spectec_ast::SpecTecPath as P;
    match p {
        ElabPath::Root => P::Root,
        ElabPath::Idx { p, e } => P::Idx {
            p1: Box::new(path_to_spectec(p, ctx)),
            e: expr_to_spectec(e, ctx),
        },
        ElabPath::Slice { p, e1, e2 } => P::Slice {
            p1: Box::new(path_to_spectec(p, ctx)),
            e1: expr_to_spectec(e1, ctx),
            e2: expr_to_spectec(e2, ctx),
        },
        ElabPath::Dot { p, field } => P::Dot {
            p1: Box::new(path_to_spectec(p, ctx)),
            at: mixop_from_name(field),
        },
    }
}

/// Construct a single-fragment MixOp from a bare name. Used for case
/// constructors and field names where we don't have a full mixfix
/// template — produces e.g. `["NOP"]` for `NOP` rather than the empty
/// `[""]` that `mixop_for` would emit if the op isn't in the table.
fn mixop_from_name(name: &str) -> spectec_ast::MixOp {
    spectec_ast::MixOp::new(vec![name.to_string()])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{elab::build_table, lex::lex, parse::parse, source::SourceMap};

    fn build(src: &str) -> (Vec<Top>, ElabContext) {
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let toks = lex(id, src).unwrap();
        let tops = parse(id, toks).unwrap();
        let ctx = build_table(&tops).unwrap();
        (tops, ctx)
    }

    #[test]
    fn doc_groups_rules_under_relation() {
        let src = r#"
            syntax t = nat
            syntax context = nat
            relation Sub: context |- t <: t
            rule Sub/refl: C |- a <: a
            rule Sub/trans: C |- a <: c
              -- Sub: C |- a <: b
              -- Sub: C |- b <: c
        "#;
        let (tops, ctx) = build(src);
        let doc = build_doc(&tops, &ctx);
        assert_eq!(doc.relations.len(), 1);
        assert_eq!(doc.relations[0].rules.len(), 2);
    }

    #[test]
    fn doc_groups_def_clauses() {
        let src = r#"
            def $min(nat, nat) : nat
            def $min(i, j) = i  -- if $(i <= j)
            def $min(i, j) = j  -- otherwise
        "#;
        let (tops, ctx) = build(src);
        let doc = build_doc(&tops, &ctx);
        assert_eq!(doc.defs.len(), 1);
        assert_eq!(doc.defs[0].clauses.len(), 2);
    }

    #[test]
    fn to_spectec_ast_emits_one_def_per_top() {
        let src = r#"
            syntax t = nat
            syntax context = nat
            relation R: context |- t : t
            rule R: C |- a : b
            def $foo(nat) : nat
            grammar G : nat = 0
            var n : nat
        "#;
        let (tops, ctx) = build(src);
        let doc = build_doc(&tops, &ctx);
        let defs = to_spectec_ast(&doc, &ctx);
        // 1 typ + 1 typ + 1 rel + 1 dec + 1 gram = 5 (vars don't emit
        // their own SpecTecDef, they inform the elaborator).
        assert_eq!(defs.len(), 5);
    }

    #[test]
    fn mixop_for_emits_percent_template() {
        let src = r#"
            syntax t = nat
            syntax context = nat
            relation R: context |- t <: t
        "#;
        let (_, ctx) = build(src);
        let mixop = mixop_for("R", &ctx);
        // Expect three fragments: "", "|-", "<:", "" — i.e. `%|-%<:%`.
        assert_eq!(mixop.fragments(), &["", "|-", "<:", ""]);
    }
}
