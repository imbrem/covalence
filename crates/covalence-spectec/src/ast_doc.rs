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
use crate::elab::{ElabContext, MergedSyntax};
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

    // Rel entries from relations.
    for rel in &doc.relations {
        let mixop = mixop_for(&rel.name, ctx);
        out.push(spectec_ast::SpecTecDef::Rel {
            x: rel.name.clone(),
            ps: Vec::new(),
            op: mixop,
            t: dummy_typ(),
            rules: rel
                .rules
                .iter()
                .map(|rd| spectec_ast::SpecTecRule::Rule {
                    x: rd
                        .case
                        .as_ref()
                        .map(|c| c.text.clone())
                        .unwrap_or_default(),
                    ps: Vec::new(),
                    op: mixop_for(&rel.name, ctx),
                    e: dummy_exp(),
                    prs: Vec::new(),
                })
                .collect(),
        });
    }

    // Dec entries from defs.
    for d in &doc.defs {
        out.push(spectec_ast::SpecTecDef::Dec {
            x: d.name.clone(),
            ps: Vec::new(),
            t: dummy_typ(),
            clauses: d
                .clauses
                .iter()
                .map(|_| spectec_ast::SpecTecClause::Clause {
                    ps: Vec::new(),
                    as_: Vec::new(),
                    e: dummy_exp(),
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
            t: dummy_typ(),
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

fn dummy_typ() -> spectec_ast::SpecTecTyp {
    spectec_ast::SpecTecTyp::Bool
}

fn dummy_exp() -> spectec_ast::SpecTecExp {
    spectec_ast::SpecTecExp::Bool { b: true }
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
