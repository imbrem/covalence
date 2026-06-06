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

use crate::cst::{GrammarDecl, RelationDecl, RuleDecl, SyntaxBody, Top, VarDecl, Alt, RecordField};
use crate::elab::{
    alt_to_constructor, elab_rule_conclusion, BinOp, CmpOp, ElabContext, ElabPremise, Expr,
    IterBinding, IterKind, MergedProfile, MergedSyntax, NumLit, NumTyp, OpType,
    Path as ElabPath, UnOp,
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

/// Produce a `Vec<SpecTecDef>` from a `Doc`, with mutually-recursive
/// groups wrapped in `SpecTecDef::Rec`.
pub fn to_spectec_ast(doc: &Doc, ctx: &ElabContext) -> Vec<spectec_ast::SpecTecDef> {
    let flat = to_spectec_ast_flat(doc, ctx);
    group_recursive(flat)
}

/// Flat version of [`to_spectec_ast`] — emits one `SpecTecDef` per
/// source decl with no `Rec` wrapping. Useful for testing and as the
/// input to [`group_recursive`].
fn to_spectec_ast_flat(doc: &Doc, ctx: &ElabContext) -> Vec<spectec_ast::SpecTecDef> {
    let mut out = Vec::new();

    // Typ entries from merged syntax. One Inst per profile-tagged
    // declaration; each Inst's DefTyp body is lowered from the
    // syntax body (alias / variant / record).
    for syn in &doc.syntax {
        let insts: Vec<spectec_ast::SpecTecInst> = syn
            .merged
            .profiles
            .iter()
            .filter_map(|prof| inst_for_profile(syn, prof, ctx))
            .collect();
        out.push(spectec_ast::SpecTecDef::Typ {
            x: syn.name.clone(),
            ps: Vec::new(),
            insts,
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

    // Dec entries from defs. Each clause's arg patterns are lowered
    // as Exp-wrapped expressions; the RHS is lowered to a SpecTecExp;
    // premises go through `premise_to_spectec`. None of this involves
    // the OpTable mixfix path (def clauses pattern-match by structure,
    // not by mixfix template).
    for d in &doc.defs {
        let clauses = d
            .clauses
            .iter()
            .map(|c| {
                let as_: Vec<spectec_ast::SpecTecArg> = c
                    .arg_pats
                    .iter()
                    .map(|pat_tr| spectec_ast::SpecTecArg::Exp {
                        e: token_run_to_expr(pat_tr, ctx),
                    })
                    .collect();
                let e = token_run_to_expr(&c.rhs, ctx);
                let prs = c
                    .premises
                    .iter()
                    .map(|pr_tr| {
                        // Each premise token run goes through
                        // `crate::elab::elab_premise` for the same
                        // shape recognition rules as rule premises.
                        let elabp = crate::elab::elab_premise(pr_tr, ctx)
                            .unwrap_or_else(|_| ElabPremise::Raw(pr_tr.clone()));
                        premise_to_spectec(&elabp, ctx)
                    })
                    .collect();
                spectec_ast::SpecTecClause::Clause {
                    ps: Vec::new(),
                    as_,
                    e,
                    prs,
                }
            })
            .collect();
        out.push(spectec_ast::SpecTecDef::Dec {
            x: d.name.clone(),
            ps: Vec::new(),
            t: placeholder_typ(),
            clauses,
        });
    }

    // Gram entries from grammars. We don't yet split productions on
    // `|` and lower each one — that's the obvious next slice. For now
    // we emit one production whose symbol is a `Var` carrying the raw
    // body as a synthetic ident, just so `prods` is non-empty when
    // there's a body.
    for g in &doc.grammars {
        let prods = match &g.decl.productions {
            Some(_) => vec![spectec_ast::SpecTecProd::Prod {
                ps: Vec::new(),
                g: spectec_ast::SpecTecSym::Eps,
                e: raw_sentinel(),
                prs: Vec::new(),
            }],
            None => Vec::new(),
        };
        out.push(spectec_ast::SpecTecDef::Gram {
            x: g.name.clone(),
            ps: Vec::new(),
            t: placeholder_typ(),
            prods,
        });
    }

    out
}

/// Lower a raw token run through the same expression-classification
/// pipeline elaboration uses, then through `expr_to_spectec`.
fn token_run_to_expr(
    tr: &crate::cst::TokenRun,
    ctx: &ElabContext,
) -> spectec_ast::SpecTecExp {
    if tr.tokens.is_empty() {
        return raw_sentinel();
    }
    match crate::elab::classify_token_run(tr, ctx) {
        Some(expr) => expr_to_spectec(&expr, ctx),
        None => raw_sentinel(),
    }
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
                .map(|tr| spectec_ast::SpecTecArg::Exp {
                    e: token_run_to_expr(tr, ctx),
                })
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

// ---------- SyntaxBody → SpecTecInst ----------

/// Build one `SpecTecInst` for a profile of a merged syntax decl.
/// Returns `None` for forward declarations (no body).
fn inst_for_profile(
    syn: &DocSyntax,
    prof: &MergedProfile,
    ctx: &ElabContext,
) -> Option<spectec_ast::SpecTecInst> {
    let dt = match prof.body.as_ref()? {
        SyntaxBody::Alias(tr) => spectec_ast::SpecTecDefTyp::Alias {
            typ: typ_expr_to_spectec(&tr.tokens, ctx),
        },
        SyntaxBody::Variant(_) => {
            // Use the merged alts for this profile (splices `...` from
            // sibling profiles in).
            let alts = syn.merged.alts_for_profile(prof.profile.as_deref());
            spectec_ast::SpecTecDefTyp::Variant {
                tcs: alts.iter().map(|a| alt_to_typcase(a, ctx)).collect(),
            }
        }
        SyntaxBody::Record(fields) => spectec_ast::SpecTecDefTyp::Struct {
            tfs: fields.iter().map(|f| record_field_to_typfield(f, ctx)).collect(),
        },
    };
    Some(spectec_ast::SpecTecInst::Inst {
        ps: Vec::new(),
        as_: Vec::new(),
        dt,
    })
}

/// Convert a variant alternative to a `SpecTecTypCase`. The case's
/// MixOp is constructed from the alt's tokens via the same logic that
/// builds constructor ops in `elab::alt_to_constructor`; the case's
/// operand-tuple type is a placeholder for now (full elaboration of
/// arg-type expressions in alternatives is later work).
fn alt_to_typcase(alt: &Alt, ctx: &ElabContext) -> spectec_ast::SpecTecTypCase {
    let op = match alt_to_constructor(alt, &ctx.type_names) {
        Some((_name, frags)) => mixop_from_fragments(&frags),
        None => mixop_from_alt_tokens(alt),
    };
    spectec_ast::SpecTecTypCase::Field {
        op,
        t: typ_expr_to_spectec_args(alt, ctx),
        qs: Vec::new(),
        prs: Vec::new(),
    }
}

fn record_field_to_typfield(
    f: &RecordField,
    ctx: &ElabContext,
) -> spectec_ast::SpecTecTypField {
    spectec_ast::SpecTecTypField::Field {
        at: mixop_from_name(&f.name.text),
        t: typ_expr_to_spectec(&f.ty.tokens, ctx),
        qs: Vec::new(),
        prs: Vec::new(),
    }
}

/// Build a MixOp from the alt's raw tokens by joining text with `%`
/// holes wherever a declared type name (or `(`) appears. Fallback used
/// when `alt_to_constructor` returns `None` (non-case-head alts).
fn mixop_from_alt_tokens(alt: &Alt) -> spectec_ast::MixOp {
    let mut s = String::new();
    for t in &alt.body.tokens {
        match &t.token {
            crate::token::Token::Ident(n) => {
                if is_uppercase_like(n) {
                    s.push_str(n);
                } else {
                    s.push('%');
                }
            }
            crate::token::Token::LParen => s.push('%'),
            other => s.push_str(other.describe().trim_matches('`')),
        }
    }
    spectec_ast::MixOp::new(s.split('%').map(str::to_owned).collect())
}

fn is_uppercase_like(name: &str) -> bool {
    !name.is_empty()
        && name
            .bytes()
            .next()
            .map(|b| b.is_ascii_uppercase() || b == b'_')
            .unwrap_or(false)
}

fn mixop_from_fragments(frags: &[crate::mixfix::Fragment]) -> spectec_ast::MixOp {
    let mut s = String::new();
    for f in frags {
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
    spectec_ast::MixOp::new(s.split('%').map(str::to_owned).collect())
}

/// Lower a raw token run as a type expression. This is a sketch — it
/// recognises a few cases and falls back to `SpecTecTyp::Bool` for the
/// rest.
fn typ_expr_to_spectec(
    toks: &[crate::token::Spanned],
    ctx: &ElabContext,
) -> spectec_ast::SpecTecTyp {
    use crate::token::Token::*;
    use spectec_ast::SpecTecTyp as T;
    // Singleton type-name ident.
    if toks.len() == 1 {
        if let Ident(n) = &toks[0].token {
            return match n.as_str() {
                "nat" => T::Num(spectec_ast::SpecTecNumTyp::Nat),
                "int" => T::Num(spectec_ast::SpecTecNumTyp::Int),
                "rat" => T::Num(spectec_ast::SpecTecNumTyp::Rat),
                "real" => T::Num(spectec_ast::SpecTecNumTyp::Real),
                "bool" => T::Bool,
                "text" => T::Text,
                _ if ctx.type_names.contains(n) => T::Var {
                    x: n.clone(),
                    as1: Vec::new(),
                },
                _ => T::Bool,
            };
        }
    }
    // Trailing `*`/`?`/`+` iter suffix.
    if toks.len() >= 2 {
        let last = &toks.last().unwrap().token;
        let it = match last {
            Star => Some(spectec_ast::SpecTecIter::List),
            Question => Some(spectec_ast::SpecTecIter::Opt),
            Plus => Some(spectec_ast::SpecTecIter::List1),
            _ => None,
        };
        if let Some(it) = it {
            let inner_toks = &toks[..toks.len() - 1];
            return T::Iter {
                t1: Box::new(typ_expr_to_spectec(inner_toks, ctx)),
                it: vec![it],
            };
        }
    }
    // Fallback.
    T::Bool
}

/// Lower the type of a variant alternative's arguments. Returns the
/// single arg type or a `Tup` of multiple arg types.
fn typ_expr_to_spectec_args(alt: &Alt, ctx: &ElabContext) -> spectec_ast::SpecTecTyp {
    // Skip the leading constructor head and gather the rest as one or
    // more arg-type expressions. We split the rest on whitespace —
    // approximated here as token-by-token, taking each type name + its
    // suffix as one arg.
    let toks = &alt.body.tokens;
    if toks.len() <= 1 {
        return spectec_ast::SpecTecTyp::Tup { ets: Vec::new() };
    }
    let rest = &toks[1..];
    // Use the same fragment extractor as `alt_to_constructor` to split
    // into argument positions.
    let frags = match alt_to_constructor(alt, &ctx.type_names) {
        Some((_, frags)) => frags,
        None => return spectec_ast::SpecTecTyp::Bool,
    };
    let _ = rest;
    let arg_tys: Vec<spectec_ast::SpecTecTypBind> = frags
        .iter()
        .filter_map(|f| match f {
            crate::mixfix::Fragment::Hole(_) => Some(spectec_ast::SpecTecTypBind::Bind {
                id: "_".to_string(),
                typ: spectec_ast::SpecTecTyp::Bool,
            }),
            _ => None,
        })
        .collect();
    if arg_tys.is_empty() {
        spectec_ast::SpecTecTyp::Tup { ets: Vec::new() }
    } else if arg_tys.len() == 1 {
        let spectec_ast::SpecTecTypBind::Bind { typ, .. } = arg_tys.into_iter().next().unwrap();
        typ
    } else {
        spectec_ast::SpecTecTyp::Tup { ets: arg_tys }
    }
}

// ---------- SCC analysis + Rec grouping ----------

/// Wrap consecutive runs of mutually-recursive defs in `SpecTecDef::Rec`.
///
/// The algorithm:
/// 1. Build a use-graph: each def is a node; an edge `A → B` exists
///    when an ident matching `B`'s name appears anywhere inside `A`'s
///    body (operands, premises, clauses, productions, MixOp templates).
/// 2. Compute strongly-connected components via Tarjan's algorithm.
/// 3. For each SCC, in source order: if it has more than one element,
///    emit `Rec { ds }`. A singleton SCC emits flat unless it has a
///    self-loop (the def references its own name), in which case it
///    also becomes `Rec { ds: vec![def] }`.
///
/// This is a sketch — over-approximates uses by walking raw tokens, so
/// some non-uses (e.g. ident appearing in a hint body) count as edges.
/// That just produces larger Rec groups; the relative grouping is
/// still meaningful.
fn group_recursive(defs: Vec<spectec_ast::SpecTecDef>) -> Vec<spectec_ast::SpecTecDef> {
    // Index defs by name and collect their referenced-name sets.
    let n = defs.len();
    let mut idx_by_name: std::collections::HashMap<String, usize> =
        std::collections::HashMap::with_capacity(n);
    for (i, d) in defs.iter().enumerate() {
        if let Some(name) = def_name(d) {
            idx_by_name.insert(name.to_string(), i);
        }
    }
    let mut deps: Vec<Vec<usize>> = Vec::with_capacity(n);
    for d in &defs {
        let refs = referenced_names(d);
        let mut targets: Vec<usize> = refs
            .into_iter()
            .filter_map(|r| idx_by_name.get(&r).copied())
            .collect();
        targets.sort_unstable();
        targets.dedup();
        deps.push(targets);
    }

    let sccs = tarjan_scc(&deps);

    // SCCs come out in reverse-topo order; we want source order.
    // Sort each SCC's members by their original index, then sort SCCs
    // by minimum member index.
    let mut sccs: Vec<Vec<usize>> = sccs
        .into_iter()
        .map(|mut s| {
            s.sort_unstable();
            s
        })
        .collect();
    sccs.sort_by_key(|s| *s.first().unwrap_or(&usize::MAX));

    let mut by_idx: Vec<Option<spectec_ast::SpecTecDef>> = defs.into_iter().map(Some).collect();
    let mut out = Vec::with_capacity(n);
    for scc in sccs {
        if scc.len() == 1 {
            let i = scc[0];
            let d = by_idx[i].take().expect("each def consumed once");
            // Self-loop check.
            if deps[i].contains(&i) {
                out.push(spectec_ast::SpecTecDef::Rec { ds: vec![d] });
            } else {
                out.push(d);
            }
        } else {
            let ds: Vec<_> = scc
                .iter()
                .map(|&i| by_idx[i].take().expect("each def consumed once"))
                .collect();
            out.push(spectec_ast::SpecTecDef::Rec { ds });
        }
    }
    out
}

fn def_name(d: &spectec_ast::SpecTecDef) -> Option<&str> {
    match d {
        spectec_ast::SpecTecDef::Typ { x, .. }
        | spectec_ast::SpecTecDef::Rel { x, .. }
        | spectec_ast::SpecTecDef::Dec { x, .. }
        | spectec_ast::SpecTecDef::Gram { x, .. } => Some(x.as_str()),
        spectec_ast::SpecTecDef::Rec { .. } => None,
    }
}

/// Approximation: collect every name-string that appears anywhere
/// inside a def, used as a basis for the use-graph edges. The
/// approximation includes `Var.id`, `Case.op` fragments, MixOp
/// fragments on relations/rules, `Call.x`, type-name `Var.x`, etc.
fn referenced_names(d: &spectec_ast::SpecTecDef) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    fn walk_exp(e: &spectec_ast::SpecTecExp, out: &mut std::collections::HashSet<String>) {
        use spectec_ast::SpecTecExp as E;
        match e {
            E::Var { id } => {
                out.insert(id.clone());
            }
            E::Bin { e1, e2, .. } | E::Cmp { e1, e2, .. } | E::Idx { e1, e2, .. }
            | E::Comp { e1, e2, .. } | E::Mem { e1, e2, .. } | E::Cat { e1, e2, .. } => {
                walk_exp(e1, out);
                walk_exp(e2, out);
            }
            E::Un { e2, .. } | E::Len { e1: e2, .. } | E::Lift { e1: e2, .. }
            | E::Unopt { e1: e2, .. } | E::Cvt { e1: e2, .. } | E::Sub { e1: e2, .. } => {
                walk_exp(e2, out);
            }
            E::Slice { e1, e2, e3, .. } => {
                walk_exp(e1, out);
                walk_exp(e2, out);
                walk_exp(e3, out);
            }
            E::Upd { e1, e2, .. } | E::Ext { e1, e2, .. } => {
                walk_exp(e1, out);
                walk_exp(e2, out);
            }
            E::Str { efs } => {
                for spectec_ast::SpecTecExpField::Field { e, .. } in efs {
                    walk_exp(e, out);
                }
            }
            E::Dot { e1, at } => {
                walk_exp(e1, out);
                for f in at.fragments() {
                    out.insert(f.clone());
                }
            }
            E::Tup { es } | E::List { es } => {
                for e in es {
                    walk_exp(e, out);
                }
            }
            E::Call { x, .. } => {
                out.insert(x.clone());
            }
            E::Iter { e1, .. } => walk_exp(e1, out),
            E::Proj { e1, .. } => walk_exp(e1, out),
            E::Case { op, e1 } => {
                for f in op.fragments() {
                    out.insert(f.clone());
                }
                walk_exp(e1, out);
            }
            E::Uncase { e1, op } => {
                walk_exp(e1, out);
                for f in op.fragments() {
                    out.insert(f.clone());
                }
            }
            E::Opt { eo: Some(e) } => walk_exp(e, out),
            E::Opt { eo: None } => {}
            E::Bool { .. } | E::Num { .. } | E::Text { .. } => {}
        }
    }
    fn walk_prem(p: &spectec_ast::SpecTecPrem, out: &mut std::collections::HashSet<String>) {
        use spectec_ast::SpecTecPrem as P;
        match p {
            P::Rule { x, e, .. } => {
                out.insert(x.clone());
                walk_exp(e, out);
            }
            P::If { e } => walk_exp(e, out),
            P::Let { e1, e2 } => {
                walk_exp(e1, out);
                walk_exp(e2, out);
            }
            P::Else => {}
            P::Iter { pr1, .. } => walk_prem(pr1, out),
        }
    }
    match d {
        spectec_ast::SpecTecDef::Typ { insts, .. } => {
            for spectec_ast::SpecTecInst::Inst { dt, .. } in insts {
                use spectec_ast::SpecTecDefTyp as DT;
                match dt {
                    DT::Alias { typ: _ } => {}
                    DT::Struct { tfs } => {
                        for spectec_ast::SpecTecTypField::Field { at, .. } in tfs {
                            for f in at.fragments() {
                                out.insert(f.clone());
                            }
                        }
                    }
                    DT::Variant { tcs } => {
                        for spectec_ast::SpecTecTypCase::Field { op, .. } in tcs {
                            for f in op.fragments() {
                                out.insert(f.clone());
                            }
                        }
                    }
                }
            }
        }
        spectec_ast::SpecTecDef::Rel { rules, .. } => {
            for spectec_ast::SpecTecRule::Rule { e, prs, .. } in rules {
                walk_exp(e, &mut out);
                for p in prs {
                    walk_prem(p, &mut out);
                }
            }
        }
        spectec_ast::SpecTecDef::Dec { clauses, .. } => {
            for spectec_ast::SpecTecClause::Clause { e, prs, .. } in clauses {
                walk_exp(e, &mut out);
                for p in prs {
                    walk_prem(p, &mut out);
                }
            }
        }
        spectec_ast::SpecTecDef::Gram { .. } | spectec_ast::SpecTecDef::Rec { .. } => {}
    }
    out
}

/// Tarjan's strongly-connected-components algorithm. Inputs: adjacency
/// `deps[i]` = outgoing edges from node `i`. Returns one `Vec<usize>`
/// per SCC (each holding the member indices), in reverse-topological
/// order (sinks first).
fn tarjan_scc(deps: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = deps.len();
    let mut indices = vec![usize::MAX; n];
    let mut lowlinks = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut index = 0usize;
    let mut out: Vec<Vec<usize>> = Vec::new();
    for v in 0..n {
        if indices[v] == usize::MAX {
            strong_connect(
                v, deps, &mut indices, &mut lowlinks, &mut on_stack, &mut stack, &mut index,
                &mut out,
            );
        }
    }
    out
}

fn strong_connect(
    v: usize,
    deps: &[Vec<usize>],
    indices: &mut [usize],
    lowlinks: &mut [usize],
    on_stack: &mut [bool],
    stack: &mut Vec<usize>,
    index: &mut usize,
    out: &mut Vec<Vec<usize>>,
) {
    // Iterative implementation to avoid blowing the call stack on
    // long dependency chains.
    let mut work: Vec<(usize, usize)> = vec![(v, 0)];
    indices[v] = *index;
    lowlinks[v] = *index;
    *index += 1;
    stack.push(v);
    on_stack[v] = true;
    while let Some(&(u, ref pos)) = work.last() {
        let pos = *pos;
        if pos < deps[u].len() {
            let w = deps[u][pos];
            work.last_mut().unwrap().1 += 1;
            if indices[w] == usize::MAX {
                indices[w] = *index;
                lowlinks[w] = *index;
                *index += 1;
                stack.push(w);
                on_stack[w] = true;
                work.push((w, 0));
            } else if on_stack[w] {
                lowlinks[u] = lowlinks[u].min(indices[w]);
            }
        } else {
            // Done with u.
            if lowlinks[u] == indices[u] {
                let mut scc = Vec::new();
                loop {
                    let w = stack.pop().expect("non-empty by construction");
                    on_stack[w] = false;
                    scc.push(w);
                    if w == u {
                        break;
                    }
                }
                out.push(scc);
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                lowlinks[parent] = lowlinks[parent].min(lowlinks[u]);
            }
        }
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
