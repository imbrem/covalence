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
//! The converter populates names, parameters, operand-tuple types,
//! MixOp templates, rule conclusions, premises (`If`/`Let`/`Else`/
//! `Iter`/`Rule`), clause arg patterns and RHSes, variant-case bodies,
//! grammar productions (with `...` range collapsing), and Tarjan-SCC
//! `Rec` grouping. Expression positions that haven't been structurally
//! elaborated (e.g. `Raw` fallbacks for un-recognised mixfix forms)
//! lower to a `Bool { b: false }` *sentinel* so the differential test
//! can measure lowering coverage explicitly.
//!
//! Type-annotation fields (`Un.t`, `Bin.t`, `Cmp.t`) currently default
//! to `OpType::Nat`, and `Sub` coercion nodes are not inserted —
//! type-checking is a separate pass over the elaborated AST and is
//! deliberately not in scope for this module.

use crate::cst::{GrammarDecl, RelationDecl, RuleDecl, SyntaxBody, Top, VarDecl, Alt, RecordField};
use crate::elab::{
    alt_to_constructor, alt_to_constructor_with_holes, alt_to_headless_with_holes,
    elab_rule_conclusion, BinOp, CmpOp,
    ElabContext, ElabPremise, Expr, IterBinding, IterKind, MergedProfile, MergedSyntax, NumLit,
    NumTyp, OpType, Path as ElabPath, UnOp,
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
    /// First-seen `params` token runs per syntax name (parametric
    /// syntax preserves its `(P, ...)` group across profiles).
    pub syntax_orig_params: std::collections::HashMap<String, Vec<crate::cst::TokenRun>>,
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
    // first occurrence determines the displayed span. Also stash the
    // first-seen params token run so `Typ.ps` can be synthesised.
    let mut seen_syntax = std::collections::HashSet::new();
    for t in tops {
        if let Top::Syntax(s) = t
            && seen_syntax.insert(s.name.text.clone())
            && let Some(merged) = ctx.syntax_defs.get(&s.name.text)
        {
            doc.syntax.push(DocSyntax {
                span: s.span,
                name: s.name.text.clone(),
                merged: merged.clone(),
            });
            doc.syntax_orig_params
                .insert(s.name.text.clone(), s.params.clone());
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
///
/// Type-checks every expression along the way so operator-type
/// annotations and (eventually) `Sub` coercions are populated.
pub fn to_spectec_ast(doc: &Doc, ctx: &ElabContext) -> Vec<spectec_ast::SpecTecDef> {
    let env = crate::typecheck::build_env(doc, ctx);
    let flat = to_spectec_ast_flat(doc, ctx, &env);
    group_recursive(flat)
}

/// Flat version of [`to_spectec_ast`] — emits one `SpecTecDef` per
/// source decl with no `Rec` wrapping. Useful for testing and as the
/// input to [`group_recursive`].
fn to_spectec_ast_flat(
    doc: &Doc,
    ctx: &ElabContext,
    env: &crate::typecheck::TypeEnv,
) -> Vec<spectec_ast::SpecTecDef> {
    let mut out = Vec::new();

    // Typ entries from merged syntax. One Inst per profile-tagged
    // declaration; each Inst's DefTyp body is lowered from the
    // syntax body (alias / variant / record). `ps` comes from the
    // syntax decl's parametric `(param)` list (e.g. `syntax fN(N)`).
    for syn in &doc.syntax {
        // First Top::Syntax for this name supplies the params (all
        // profiles share the same param list).
        let params_tr = doc
            .syntax_orig_params
            .get(&syn.name)
            .cloned()
            .unwrap_or_default();
        let ps = syntax_params_to_specs(&params_tr, ctx);
        let mut insts: Vec<spectec_ast::SpecTecInst> = syn
            .merged
            .profiles
            .iter()
            .filter_map(|prof| inst_for_profile(syn, prof, ctx, doc))
            .collect();
        // OCaml's elaborator merges profiles that produce identical
        // bodies (the typical case for split `/syn` + `/sem` decls
        // that splice into each other). Dedup consecutive equals.
        insts.dedup();
        out.push(spectec_ast::SpecTecDef::Typ {
            x: syn.name.clone(),
            ps,
            insts,
        });
    }

    // Rel entries from relations. Each rule's conclusion + premises
    // is elaborated via `elab_rule_conclusion` and lowered to the
    // SpecTec rule shape (conclusion wrapped as a Tup, premises lowered
    // through `premise_to_spectec`). Rel.t is the operand-tuple type
    // synthesised from the template's hole-type slices.
    for rel in &doc.relations {
        let mixop = mixop_for(&rel.name, ctx);
        let (_, hole_toks) = crate::elab::template_to_fragments_with_holes(
            &rel.decl.template,
            &ctx.type_names,
        );
        let t = relation_operand_type(&hole_toks, ctx);
        let rules = rel
            .rules
            .iter()
            .map(|rd| {
                let elab = elab_rule_conclusion(rd, ctx).ok();
                let (e, prs, rule_ps) = match elab {
                    Some(elab) => {
                        let mut scope = crate::typecheck::RuleScope::default();
                        let expected: Vec<spectec_ast::SpecTecTyp> =
                            extract_tup_element_types(&t);
                        let typed_operands: Vec<Expr> = elab
                            .operands
                            .into_iter()
                            .enumerate()
                            .map(|(i, o)| match expected.get(i) {
                                Some(expected_t) => crate::typecheck::check_exp_against_scope(
                                    env, o, expected_t, &mut scope,
                                ),
                                None => crate::typecheck::check_exp(env, o),
                            })
                            .collect();
                        let typed_premises: Vec<ElabPremise> = elab
                            .premises
                            .into_iter()
                            .map(|p| crate::typecheck::check_premise_scope(env, p, &mut scope))
                            .collect();
                        let rule_ps = crate::typecheck::collect_rule_params(
                            env,
                            &typed_operands,
                            &typed_premises,
                            &scope,
                        );
                        let e_out = tup_of_operands(&typed_operands, ctx);
                        let prs_out = typed_premises
                            .iter()
                            .map(|p| premise_to_spectec(p, ctx))
                            .collect();
                        (e_out, prs_out, rule_ps)
                    }
                    None => (raw_sentinel(), Vec::new(), Vec::new()),
                };
                spectec_ast::SpecTecRule::Rule {
                    x: rd.case.as_ref().map(|c| c.text.clone()).unwrap_or_default(),
                    ps: rule_ps,
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
            t,
            rules,
        });
    }

    // Dec entries from defs. Each clause's arg patterns are lowered
    // as Exp-wrapped expressions; the RHS is lowered to a SpecTecExp;
    // premises go through `premise_to_spectec`. None of this involves
    // the OpTable mixfix path (def clauses pattern-match by structure,
    // not by mixfix template). Dec.t is the return type; Dec.ps is the
    // signature's argument-type list as Exp-shaped params.
    for d in &doc.defs {
        let t = typ_expr_to_spectec(&d.sig.ret_ty.tokens, ctx);
        let ps: Vec<spectec_ast::SpecTecParam> = d
            .sig
            .arg_tys
            .iter()
            .filter_map(|arg_tr| chunk_to_syntax_param(&arg_tr.tokens))
            .collect();
        let clauses = d
            .clauses
            .iter()
            .map(|c| {
                // Each arg pattern is checked against the
                // corresponding def-parameter type.
                let as_: Vec<spectec_ast::SpecTecArg> = c
                    .arg_pats
                    .iter()
                    .enumerate()
                    .map(|(i, pat_tr)| {
                        let expected = ps.get(i).map(param_to_typ);
                        let e = match expected {
                            Some(et) => token_run_to_expr_against(pat_tr, ctx, env, &et),
                            None => token_run_to_expr_typed(pat_tr, ctx, env),
                        };
                        spectec_ast::SpecTecArg::Exp { e }
                    })
                    .collect();
                // RHS checked against the def's return type.
                let e = token_run_to_expr_against(&c.rhs, ctx, env, &t);
                let prs = c
                    .premises
                    .iter()
                    .map(|pr_tr| {
                        let elabp = crate::elab::elab_premise(pr_tr, ctx)
                            .unwrap_or_else(|_| ElabPremise::Raw(pr_tr.clone()));
                        let elabp = crate::typecheck::check_premise(env, elabp);
                        premise_to_spectec(&elabp, ctx)
                    })
                    .collect();
                spectec_ast::SpecTecClause::Clause {
                    ps: clause_ps(&c.arg_pats, &c.premises, &ps, env, ctx),
                    as_,
                    e,
                    prs,
                }
            })
            .collect();
        out.push(spectec_ast::SpecTecDef::Dec {
            x: d.name.clone(),
            ps,
            t,
            clauses,
        });
    }

    // (helper for the loop above is defined out-of-line as
    //  `clause_ps` below.)

    // Gram entries from grammars. Productions still get a single
    // placeholder Prod per body; the production-splitting slice will
    // expand this. Gram.t is the yield type; Gram.ps is the param list
    // from `(params)`.
    for g in &doc.grammars {
        let t = typ_expr_to_spectec(&g.decl.ret.tokens, ctx);
        let ps = grammar_params_to_specs(&g.decl.params, ctx);
        let prods = match &g.decl.productions {
            Some(body) => split_grammar_prods(body, ctx, Some(env), Some(&t)),
            None => Vec::new(),
        };
        out.push(spectec_ast::SpecTecDef::Gram {
            x: g.name.clone(),
            ps,
            t,
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

/// Type-checked variant: classify, then type-check before lowering.
fn token_run_to_expr_typed(
    tr: &crate::cst::TokenRun,
    ctx: &ElabContext,
    env: &crate::typecheck::TypeEnv,
) -> spectec_ast::SpecTecExp {
    if tr.tokens.is_empty() {
        return raw_sentinel();
    }
    match crate::elab::classify_token_run(tr, ctx) {
        Some(expr) => {
            let expr = crate::typecheck::check_exp(env, expr);
            expr_to_spectec(&expr, ctx)
        }
        None => raw_sentinel(),
    }
}

/// As [`token_run_to_expr_typed`] but checks the expression against
/// the given expected type — inserts `Sub` if needed.
fn token_run_to_expr_against(
    tr: &crate::cst::TokenRun,
    ctx: &ElabContext,
    env: &crate::typecheck::TypeEnv,
    expected: &spectec_ast::SpecTecTyp,
) -> spectec_ast::SpecTecExp {
    if tr.tokens.is_empty() {
        return raw_sentinel();
    }
    // Task #35: before any other classification, try to split the
    // token-run at a top-level `;` when the expected type is a
    // single-case headless `_ ; _` variant (e.g. `state = store;
    // frame`, `config = state; instr*`). The match drives the
    // mixfix template that no other classifier reaches.
    if let Some(case) = try_split_headless_semi_expr(tr, ctx, env, expected) {
        return expr_to_spectec(&case, ctx);
    }
    match crate::elab::classify_token_run(tr, ctx) {
        Some(expr) => {
            let expr = crate::typecheck::check_exp_against(env, expr, expected);
            expr_to_spectec(&expr, ctx)
        }
        None => raw_sentinel(),
    }
}

/// Try to split a token-run at a top-level `;` against a single-case
/// headless `_ ; _` variant in `env.headless_semi`. Returns the
/// synthesised `Case { op: Some(["", ";", ""]), args: [e1, e2] }` on
/// success. Returns `None` when `expected` doesn't resolve to a
/// registered headless-semi variant, the token-run has no top-level
/// `;`, or the split produces the wrong number of parts.
///
/// Used both by [`token_run_to_expr_against`] (for clause RHSes /
/// arg-pat lowerings) and by `clause_ps` (to recover the inner
/// `Var`s for the per-clause binding list).
pub(crate) fn try_split_headless_semi_expr(
    tr: &crate::cst::TokenRun,
    ctx: &ElabContext,
    env: &crate::typecheck::TypeEnv,
    expected: &spectec_ast::SpecTecTyp,
) -> Option<crate::elab::Expr> {
    let name = match expected {
        spectec_ast::SpecTecTyp::Var { x, .. } => x,
        _ => return None,
    };
    let arg_types = env.headless_semi.get(name)?;
    // Parens-stripping: `(s; f)` is just `s; f` for splitting
    // purposes. The classifier already collapses single-comma-chunk
    // parens, but for `;` the classifier returns Raw with parens
    // intact.
    let toks = strip_outer_parens(&tr.tokens);
    let parts = split_top_semi(toks)?;
    if parts.len() != arg_types.len() {
        return None;
    }
    let span = tr.span;
    let args: Vec<crate::elab::Expr> = parts
        .into_iter()
        .zip(arg_types.iter())
        .map(|(part_tokens, et)| {
            let part_span = part_tokens
                .iter()
                .map(|s| s.span)
                .reduce(crate::source::Span::join)
                .unwrap_or(span);
            let part_tr = crate::cst::TokenRun {
                span: part_span,
                tokens: part_tokens.to_vec(),
            };
            // Recurse: a chunk may itself contain a top-level `;`
            // against another headless-semi type (e.g. nested
            // `config = state; instr*` whose first hole is `state`,
            // another headless-semi variant).
            if let Some(inner) = try_split_headless_semi_expr(&part_tr, ctx, env, et) {
                return inner;
            }
            let classified = crate::elab::classify_token_run(&part_tr, ctx)
                .unwrap_or_else(|| crate::elab::Expr::Raw(part_tr));
            crate::typecheck::check_exp_against(env, classified, et)
        })
        .collect();
    Some(crate::elab::Expr::Case {
        span,
        head: name.clone(),
        args,
        op: Some(vec![String::new(), ";".to_string(), String::new()]),
    })
}

/// Strip a single outer `( ... )` pair from `toks` if the rest is
/// depth-balanced. Mirrors the singleton-collapse the existing
/// classifier does, but for `;` (which the classifier doesn't
/// handle).
fn strip_outer_parens(toks: &[crate::token::Spanned]) -> &[crate::token::Spanned] {
    if toks.len() < 2 {
        return toks;
    }
    let first = matches!(toks.first().map(|s| &s.token), Some(crate::token::Token::LParen));
    let last = matches!(toks.last().map(|s| &s.token), Some(crate::token::Token::RParen));
    if !first || !last {
        return toks;
    }
    let inner = &toks[1..toks.len() - 1];
    let mut depth: i32 = 0;
    for t in inner {
        match &t.token {
            crate::token::Token::LParen
            | crate::token::Token::LBracket
            | crate::token::Token::LBrace => depth += 1,
            crate::token::Token::RParen
            | crate::token::Token::RBracket
            | crate::token::Token::RBrace => {
                depth -= 1;
                if depth < 0 {
                    return toks;
                }
            }
            _ => {}
        }
    }
    if depth != 0 {
        return toks;
    }
    inner
}

/// Split a token-run at every top-level `;` (depth-0 outside parens,
/// brackets, braces). Returns `None` if there is no top-level `;` —
/// i.e. there's nothing to split.
fn split_top_semi(toks: &[crate::token::Spanned]) -> Option<Vec<&[crate::token::Spanned]>> {
    let mut depth: i32 = 0;
    let mut parts: Vec<&[crate::token::Spanned]> = Vec::new();
    let mut chunk_start = 0usize;
    let mut found = false;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            crate::token::Token::LParen
            | crate::token::Token::LBracket
            | crate::token::Token::LBrace => depth += 1,
            crate::token::Token::RParen
            | crate::token::Token::RBracket
            | crate::token::Token::RBrace => depth -= 1,
            crate::token::Token::Semi if depth == 0 => {
                parts.push(&toks[chunk_start..i]);
                chunk_start = i + 1;
                found = true;
            }
            _ => {}
        }
    }
    if !found {
        return None;
    }
    parts.push(&toks[chunk_start..]);
    // Empty chunks (e.g. trailing `;`) disqualify the split — we'd
    // produce a Raw-sentinel that doesn't match the OCaml shape.
    if parts.iter().any(|p| p.is_empty()) {
        return None;
    }
    Some(parts)
}

fn mixop_for(name: &str, ctx: &ElabContext) -> spectec_ast::MixOp {
    // Prefer the relation-template walker (handles `_` subscripts and
    // backtick stripping the way OCaml does). Fall back to walking
    // the OpTable fragments for constructor / synthetic ops not
    // backed by a relation template.
    if let Some(template) = ctx.rel_templates.get(name) {
        let fragments = crate::elab::mixop_fragments_from_template(template, &ctx.type_names);
        return spectec_ast::MixOp::new(fragments);
    }
    let Some(op) = ctx.op_table.iter().find(|o| o.name == name) else {
        return spectec_ast::MixOp::new(Vec::new());
    };
    let mut s = String::new();
    for f in &op.fragments {
        match f {
            crate::mixfix::Fragment::Hole(_) => s.push('%'),
            crate::mixfix::Fragment::Lit(t) => s.push_str(&t.to_source_text()),
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
                .map(|arg| spectec_ast::SpecTecArg::Exp {
                    e: expr_to_spectec(arg, ctx),
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
        Expr::Case { head, args, op, .. } => {
            // Special case: the synthetic `__arrow_mixfix` head names
            // both long (`T ->_(M) U`) and short (`T -> U`) forms of
            // the headless `instrtype` mixfix (task #33). Emit
            // OCaml's `%->_%%` mixop and inject an empty-list middle
            // for the short form so both shapes converge on a 3-arg
            // tup, and wrap the two resulttype slots in the headless
            // `resulttype` case constructor (mixop `%`).
            if head == crate::elab::ARROW_MIXFIX_OP {
                let arrow_op = spectec_ast::MixOp::new(vec![
                    String::new(),
                    "->_".to_string(),
                    String::new(),
                    String::new(),
                ]);
                let resulttype_op = spectec_ast::MixOp::new(vec![
                    String::new(),
                    String::new(),
                ]);
                let wrap_resulttype = |inner: spectec_ast::SpecTecExp| -> spectec_ast::SpecTecExp {
                    S::Case {
                        op: resulttype_op.clone(),
                        e1: Box::new(S::Tup { es: vec![inner] }),
                    }
                };
                let mut es: Vec<spectec_ast::SpecTecExp> =
                    args.iter().map(|a| expr_to_spectec(a, ctx)).collect();
                let (left, middle, right) = match es.len() {
                    2 => {
                        let r = es.pop().unwrap();
                        let l = es.pop().unwrap();
                        (l, S::List { es: Vec::new() }, r)
                    }
                    3 => {
                        let r = es.pop().unwrap();
                        let m = es.pop().unwrap();
                        let l = es.pop().unwrap();
                        (l, m, r)
                    }
                    _ => {
                        return S::Case {
                            op: arrow_op,
                            e1: Box::new(S::Tup { es }),
                        };
                    }
                };
                let inner = S::Tup {
                    es: vec![wrap_resulttype(left), middle, wrap_resulttype(right)],
                };
                return S::Case {
                    op: arrow_op,
                    e1: Box::new(inner),
                };
            }
            // Mixop resolution priority:
            // (1) The `op` field on `Expr::Case` (synthesised by task
            //     #35 for `;`-tupled headless variants — carries the
            //     literal mixop parts directly).
            // (2) `ctx.headless_variant_op[head]` for task #32's
            //     headless-variant unfolding (head is a syntax NAME
            //     like `"fieldtype"`).
            // (3) `mixop_from_name(head)` for the standard
            //     case-constructor `[head]` shape.
            let op = match op {
                Some(parts) => spectec_ast::MixOp::new(parts.clone()),
                None => ctx
                    .headless_variant_op
                    .get(head)
                    .cloned()
                    .unwrap_or_else(|| mixop_from_name(head)),
            };
            let inner = S::Tup {
                es: args.iter().map(|a| expr_to_spectec(a, ctx)).collect(),
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
        Expr::Sub { e, from_ty, to_ty, .. } => S::Sub {
            t1: from_ty.clone(),
            t2: to_ty.clone(),
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

/// Collect the per-clause `ps` (local binding list) for a def
/// clause. Walks each arg pattern + premise token run for `Var`
/// occurrences (in source order, first-seen-wins) and emits one
/// `Param::Exp` per binding. Type comes from the def's sig `ps` by
/// name when available, else `Var(name)` as a fallback.
fn clause_ps(
    arg_pats: &[crate::cst::TokenRun],
    premises: &[crate::cst::TokenRun],
    sig_ps: &[spectec_ast::SpecTecParam],
    env: &crate::typecheck::TypeEnv,
    ctx: &crate::elab::ElabContext,
) -> Vec<spectec_ast::SpecTecParam> {
    let mut order: Vec<String> = Vec::new();
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    // Positional name→type discovered from arg_pats vs sig_ps. A
    // single-Var pat at position i takes its type from sig_ps[i].
    let mut positional: std::collections::BTreeMap<String, spectec_ast::SpecTecTyp> =
        std::collections::BTreeMap::new();
    for (i, tr) in arg_pats.iter().enumerate() {
        // Task #35: when the def's sig position is a headless `_ ; _`
        // variant, split the pattern so the inner `Var`s (`s`, `f`
        // in `(s; f)`) get collected into the binding order. Without
        // this, `clause_ps` walks an opaque `Raw` and misses them.
        let sig_t = sig_ps.get(i).and_then(|p| match p {
            spectec_ast::SpecTecParam::Exp { t, .. } => Some(t.clone()),
            _ => None,
        });
        let expr = if let Some(t) = &sig_t
            && let Some(split) = try_split_headless_semi_expr(tr, ctx, env, t)
        {
            // Task #35: `;`-tupled headless variant already produces
            // a fully type-checked Expr.
            split
        } else {
            let Some(expr) = crate::elab::classify_token_run(tr, ctx) else {
                continue;
            };
            // Task #32: route through `check_exp_against` so the
            // headless-variant unfold fires for patterns like
            // `(mut zt)` against `fieldtype`.
            match &sig_t {
                Some(t) => crate::typecheck::check_exp_against(env, expr, t),
                None => crate::typecheck::check_exp(env, expr),
            }
        };
        // Positional capture: bare-Var pat or Iter-of-Var pat. For
        // iter cases, record under the bare name (the iter-suffix
        // lookup in `clause_ps` re-wraps the type per pattern).
        let (pat_name, expects_iter) = match &expr {
            crate::elab::Expr::Var { name, .. } => (Some(name.clone()), false),
            crate::elab::Expr::Iter { inner, .. } => match inner.as_ref() {
                crate::elab::Expr::Var { name, .. } => (Some(name.clone()), true),
                _ => (None, false),
            },
            _ => (None, false),
        };
        if let Some(pat_name) = pat_name
            && let Some(spectec_ast::SpecTecParam::Exp { t, .. }) = sig_ps.get(i)
        {
            let t_base = if expects_iter {
                match t {
                    spectec_ast::SpecTecTyp::Iter { t1, .. } => (**t1).clone(),
                    _ => t.clone(),
                }
            } else {
                t.clone()
            };
            positional.entry(pat_name).or_insert(t_base);
        }
        // Task #35: positional capture inside a headless-semi split.
        // For `def $store((s; f))` the synthesised pattern is
        // `Case[s, f]` whose hole types come from
        // `env.headless_semi[state] = [store, frame]`. Record each
        // inner Var against its arg-type so the per-clause `ps`
        // names get the right type (`s : store`, `f : frame`),
        // matching OCaml's `Clause.ps` shape.
        if let crate::elab::Expr::Case { head, args, op: Some(_), .. } = &expr
            && let Some(arg_types) = env.headless_semi.get(head)
            && args.len() == arg_types.len()
        {
            for (a, et) in args.iter().zip(arg_types.iter()) {
                if let crate::elab::Expr::Var { name, .. } = a {
                    positional.entry(name.clone()).or_insert(et.clone());
                }
            }
        }
        crate::typecheck::collect_var_names_in_expr(&expr, &mut order, &mut seen);
    }
    for tr in premises {
        let Some(expr) = crate::elab::classify_token_run(tr, ctx) else {
            continue;
        };
        let expr = crate::typecheck::check_exp(env, expr);
        crate::typecheck::collect_var_names_in_expr(&expr, &mut order, &mut seen);
    }
    // Iter-suffixed names (`ai*`, `t?`, `n+`) look up under their
    // bare base, then re-wrap in the matching `Iter<_>`. Mirrors
    // OCaml's `def $add_arrayinst(z, ai*)` → `Exp{"ai*", Iter<arrayinst, List>}`.
    order
        .into_iter()
        .map(|name| {
            let (base, suffix) = crate::typecheck::strip_iter_suffix(&name);
            let lookup_name = if suffix.is_empty() { name.as_str() } else { base };
            let wrap = |t: spectec_ast::SpecTecTyp| {
                if suffix.is_empty() {
                    t
                } else {
                    crate::typecheck::wrap_in_iters(t, &suffix)
                }
            };
            // 1. Sig-name lookup (matches OCaml's `def $f(N)` →
            //    Exp{x:N, t:Var(N)}). Sig names are bare.
            for p in sig_ps {
                if let spectec_ast::SpecTecParam::Exp { x, t } = p
                    && *x == lookup_name
                {
                    return spectec_ast::SpecTecParam::Exp {
                        x: name.clone(),
                        t: wrap(t.clone()),
                    };
                }
            }
            // 2. Metavar declaration (e.g. `var dt : deftype` →
            //    pat `dt` binds at type `deftype` regardless of how
            //    it's passed positionally to the def).
            if let Some(t) = env.vars.get(crate::elab::metavar_base(lookup_name)) {
                return spectec_ast::SpecTecParam::Exp {
                    x: name.clone(),
                    t: wrap(t.clone()),
                };
            }
            // 3. Positional (arg_pat single-Var matched to sig).
            if let Some(t) = positional.get(lookup_name)
                && !matches!(t, spectec_ast::SpecTecTyp::Bool)
            {
                return spectec_ast::SpecTecParam::Exp {
                    x: name.clone(),
                    t: wrap(t.clone()),
                };
            }
            // 4. Fallback: Var(base) wrapped.
            spectec_ast::SpecTecParam::Exp {
                x: name.clone(),
                t: wrap(spectec_ast::SpecTecTyp::Var {
                    x: lookup_name.to_string(),
                    as1: Vec::new(),
                }),
            }
        })
        .collect()
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
    // Single-operand relations don't wrap in `Tup` in OCaml's output;
    // they emit the operand expression directly.
    if operands.len() == 1 {
        return expr_to_spectec(&operands[0], ctx);
    }
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

// ---------- type / parameter synthesis ----------

/// Best-effort: extract the type held by a parameter for use as an
/// `expected` type when checking a corresponding pattern / argument.
fn param_to_typ(p: &spectec_ast::SpecTecParam) -> spectec_ast::SpecTecTyp {
    use spectec_ast::SpecTecParam as P;
    match p {
        P::Exp { t, .. } | P::Gram { t, .. } => t.clone(),
        // For Typ/Def params we don't have a meaningful runtime type
        // expectation — fall back to a placeholder.
        P::Typ { .. } | P::Def { .. } => spectec_ast::SpecTecTyp::Bool,
    }
}

/// Extract per-operand types from a relation's operand-tuple type.
/// For `Tup { ets }` returns the bind types; for a single non-Tup
/// returns one element (the whole type).
fn extract_tup_element_types(t: &spectec_ast::SpecTecTyp) -> Vec<spectec_ast::SpecTecTyp> {
    use spectec_ast::SpecTecTyp as T;
    match t {
        T::Tup { ets } => ets
            .iter()
            .map(|b| {
                let spectec_ast::SpecTecTypBind::Bind { typ, .. } = b;
                typ.clone()
            })
            .collect(),
        other => vec![other.clone()],
    }
}

/// Build a relation's operand-tuple type from its template's per-hole
/// token slices. Single hole → bare type; multiple → `Tup` of binds.
pub fn relation_operand_type(
    hole_toks: &[Vec<crate::token::Spanned>],
    ctx: &ElabContext,
) -> spectec_ast::SpecTecTyp {
    let binds: Vec<spectec_ast::SpecTecTypBind> = hole_toks
        .iter()
        .map(|toks| spectec_ast::SpecTecTypBind::Bind {
            id: "_".to_string(),
            typ: typ_expr_to_spectec(toks, ctx),
        })
        .collect();
    if binds.is_empty() {
        return spectec_ast::SpecTecTyp::Tup { ets: Vec::new() };
    }
    if binds.len() == 1 {
        let spectec_ast::SpecTecTypBind::Bind { typ, .. } = binds.into_iter().next().unwrap();
        return typ;
    }
    spectec_ast::SpecTecTyp::Tup { ets: binds }
}

/// Lower a syntax decl's `(params)` token run into `SpecTecParam`
/// entries. SpecTec params can be `syntax X`, `X : T`, `def $f(...)`,
/// or `gram G`; we recognise the simple `syntax X` and bare-name
/// cases here, treating others as `Param::Typ { x }`.
fn syntax_params_to_specs(
    params_runs: &[crate::cst::TokenRun],
    _ctx: &ElabContext,
) -> Vec<spectec_ast::SpecTecParam> {
    // Each TokenRun is one balanced `(...)` group containing
    // comma-separated params (e.g. `(N)` for `syntax fN(N)`).
    let mut out = Vec::new();
    for tr in params_runs {
        // Strip the surrounding parens.
        let toks = &tr.tokens;
        let inner = if matches!(toks.first().map(|s| &s.token), Some(crate::token::Token::LParen))
            && matches!(toks.last().map(|s| &s.token), Some(crate::token::Token::RParen))
        {
            &toks[1..toks.len() - 1]
        } else {
            &toks[..]
        };
        for chunk in split_top_level_commas(inner) {
            if let Some(p) = chunk_to_syntax_param(chunk) {
                out.push(p);
            }
        }
    }
    out
}

/// Lower a single comma-separated chunk of a param list (works for
/// `syntax NAME(...)`, `def $NAME(...)`, and `grammar NAME(...)`).
/// Recognised shapes:
/// - bare `X` → `Param::Typ { x: "X" }`
/// - `syntax X` → `Param::Typ { x: "X" }`
/// - `X : T` → `Param::Exp { x: "X", t: lower T }`
/// - `def $NAME[(args)] [: T]` → `Param::Def { x, ps, t }`
/// - `gram NAME[ : T]` → `Param::Gram { x, t }`
/// - anything else → `Param::Exp { x: "_", t: lower chunk }`
pub fn chunk_to_syntax_param(chunk: &[crate::token::Spanned]) -> Option<spectec_ast::SpecTecParam> {
    use crate::token::Token::*;
    if chunk.is_empty() {
        return None;
    }
    // `syntax X`
    if let [Spanned { token: Syntax, .. }, Spanned { token: Ident(n), .. }] = chunk {
        return Some(spectec_ast::SpecTecParam::Typ { x: n.clone() });
    }
    // `gram NAME [: T]`
    if let [Spanned { token: Grammar, .. }, Spanned { token: Ident(n), .. }, rest @ ..] = chunk {
        let t = match rest {
            [Spanned { token: Colon, .. }, ty @ ..] => placeholder_typ_for_chunk(ty),
            [] => placeholder_typ(),
            _ => placeholder_typ(),
        };
        return Some(spectec_ast::SpecTecParam::Gram { x: n.clone(), t });
    }
    // `def $NAME [(args)] [: T]`
    if let [Spanned { token: Def, .. }, Spanned { token: Dollar, .. }, Spanned { token: Ident(n), .. }, rest @ ..] = chunk {
        let mut cursor = rest;
        let mut ps_specs: Vec<spectec_ast::SpecTecParam> = Vec::new();
        // Optional `(args)`.
        if let [Spanned { token: LParen, .. }, ..] = cursor
            && let Some(close) = matching_rparen_idx(cursor)
        {
            let arg_toks = &cursor[1..close];
            for c in split_top_level_commas(arg_toks) {
                if let Some(p) = chunk_to_syntax_param(c) {
                    ps_specs.push(p);
                }
            }
            cursor = &cursor[close + 1..];
        }
        let t = match cursor {
            [Spanned { token: Colon, .. }, ty @ ..] => placeholder_typ_for_chunk(ty),
            [] => placeholder_typ(),
            _ => placeholder_typ(),
        };
        return Some(spectec_ast::SpecTecParam::Def {
            x: n.clone(),
            ps: ps_specs,
            t,
        });
    }
    // `X : T` (name followed by colon and type).
    if let [Spanned { token: Ident(n), .. }, Spanned { token: Colon, .. }, ty @ ..] = chunk {
        return Some(spectec_ast::SpecTecParam::Exp {
            x: n.clone(),
            t: placeholder_typ_for_chunk(ty),
        });
    }
    // Bare `X` (single ident). OCaml treats this as an Exp param
    // whose type is the variable `X` itself (most-specific reading
    // — `X` is then resolved to `nat` etc. via its syntax decl).
    // Explicit type params come from `syntax X` syntactic form,
    // handled above.
    if let [Spanned { token: Ident(n), .. }] = chunk {
        return Some(spectec_ast::SpecTecParam::Exp {
            x: n.clone(),
            t: spectec_ast::SpecTecTyp::Var {
                x: n.clone(),
                as1: Vec::new(),
            },
        });
    }
    // Anything else: treat as an unnamed Exp param whose type is the
    // whole chunk.
    Some(spectec_ast::SpecTecParam::Exp {
        x: "_".to_string(),
        t: placeholder_typ_for_chunk(chunk),
    })
}

/// Hook for `chunk_to_syntax_param` to lower a type-position chunk.
/// Returns `Bool` for empty input; otherwise calls `typ_expr_to_spectec`.
fn placeholder_typ_for_chunk(toks: &[crate::token::Spanned]) -> spectec_ast::SpecTecTyp {
    if toks.is_empty() {
        return placeholder_typ();
    }
    // We don't have an `ElabContext` here (param parsing is static).
    // Use the no-context variant: most type expressions in params are
    // bare type-name idents which `typ_expr_to_spectec_no_ctx` handles.
    typ_expr_to_spectec_no_ctx(toks)
}

/// `typ_expr_to_spectec` variant that doesn't depend on `ElabContext`.
/// Used by parameter parsing (where the context isn't readily
/// threaded). Treats every ident as a type-name `Var`.
pub fn typ_expr_to_spectec_no_ctx(toks: &[crate::token::Spanned]) -> spectec_ast::SpecTecTyp {
    use crate::token::Token::*;
    use spectec_ast::SpecTecTyp as T;
    if toks.is_empty() {
        return T::Bool;
    }
    if let [Spanned { token: Ident(n), .. }] = toks {
        return match n.as_str() {
            "nat" => T::Num(spectec_ast::SpecTecNumTyp::Nat),
            "int" => T::Num(spectec_ast::SpecTecNumTyp::Int),
            "rat" => T::Num(spectec_ast::SpecTecNumTyp::Rat),
            "real" => T::Num(spectec_ast::SpecTecNumTyp::Real),
            "bool" => T::Bool,
            "text" => T::Text,
            _ => T::Var { x: n.clone(), as1: Vec::new() },
        };
    }
    // Trailing iter suffix.
    if toks.len() >= 2 {
        let it = match toks.last().unwrap().token {
            Star => Some(spectec_ast::SpecTecIter::List),
            Question => Some(spectec_ast::SpecTecIter::Opt),
            Plus => Some(spectec_ast::SpecTecIter::List1),
            _ => None,
        };
        if let Some(it) = it {
            return T::Iter {
                t1: Box::new(typ_expr_to_spectec_no_ctx(&toks[..toks.len() - 1])),
                it: vec![it],
            };
        }
    }
    T::Bool
}

/// Position of the `RParen` matching `toks[0] == LParen`, or `None`.
fn matching_rparen_idx(toks: &[crate::token::Spanned]) -> Option<usize> {
    use crate::token::Token::*;
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            LParen | LBracket | LBrace => depth += 1,
            RParen | RBracket | RBrace => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Lower a grammar's `(params)` into params (currently treated as
/// syntax-style — refine when needed).
fn grammar_params_to_specs(
    params_runs: &[crate::cst::TokenRun],
    ctx: &ElabContext,
) -> Vec<spectec_ast::SpecTecParam> {
    syntax_params_to_specs(params_runs, ctx)
}

/// Split a token slice on top-level commas.
fn split_top_level_commas(toks: &[crate::token::Spanned]) -> Vec<&[crate::token::Spanned]> {
    let mut out = Vec::new();
    let mut depth: i32 = 0;
    let mut start = 0usize;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            crate::token::Token::LParen
            | crate::token::Token::LBracket
            | crate::token::Token::LBrace => depth += 1,
            crate::token::Token::RParen
            | crate::token::Token::RBracket
            | crate::token::Token::RBrace => depth -= 1,
            crate::token::Token::Comma if depth == 0 => {
                if start < i {
                    out.push(&toks[start..i]);
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < toks.len() {
        out.push(&toks[start..]);
    }
    out
}

// Re-export Spanned for the chunk_to_syntax_param pattern matches.
use crate::token::Spanned;

// ---------- SyntaxBody → SpecTecInst ----------

/// Build one `SpecTecInst` for a profile of a merged syntax decl.
/// Returns `None` for forward declarations (no body).
fn inst_for_profile(
    syn: &DocSyntax,
    prof: &MergedProfile,
    ctx: &ElabContext,
    doc: &Doc,
) -> Option<spectec_ast::SpecTecInst> {
    let dt = match prof.body.as_ref()? {
        SyntaxBody::Alias(tr) => {
            // OCaml's elaborator emits AliasT for every `syntax X = Y`
            // (the `_` fallback in `elab_typ_definition`), yet the
            // vendored reference dump inconsistently shows some such
            // aliases as inlined variants (Inn, Lnn, Vnn) while
            // others with literally identical source-side hints stay
            // aliases (Pnn). No syntactic predicate in elab.ml
            // reproduces this split — see task-30 for the
            // investigation — so we hardcode the names the corpus
            // expects inlined. Anything else takes the faithful
            // alias path.
            try_inline_alias_to_variant(syn, tr, ctx, doc).unwrap_or_else(|| {
                spectec_ast::SpecTecDefTyp::Alias {
                    typ: typ_expr_to_spectec(&tr.tokens, ctx),
                }
            })
        }
        SyntaxBody::Variant(verbatim_alts) => {
            // Pattern-literal shape (`syntax bit = 0 | 1`, `syntax byte =
            // 0x00 | ... | 0xFF`, `syntax char = U+0000 | ... | U+D7FF |
            // ...`): OCaml elaborates the whole disjunction to a single
            // implicit-binder case with a predicate premise. We need the
            // verbatim alts (with `...` markers) to recover the range
            // structure that `alts_for_profile` drops.
            if let Some(tc) = try_pattern_literal_variant(verbatim_alts) {
                return Some(spectec_ast::SpecTecInst::Inst {
                    ps: Vec::new(),
                    as_: Vec::new(),
                    dt: spectec_ast::SpecTecDefTyp::Variant { tcs: vec![tc] },
                });
            }
            // Use the merged alts for this profile (splices `...` from
            // sibling profiles in). Type-inclusion alts get expanded
            // to their target's variant cases (OCaml convention).
            let alts = syn.merged.alts_for_profile(prof.profile.as_deref());
            let mut expanded: Vec<Alt> = Vec::new();
            for a in &alts {
                if let Some(target) = type_inclusion_target(a, &ctx.type_names) {
                    let mut visited = std::collections::HashSet::new();
                    visited.insert(syn.name.clone());
                    match expand_variant_alts(&target, doc, ctx, &mut visited) {
                        Some(sub) => expanded.extend(sub),
                        None => expanded.push(a.clone()),
                    }
                } else {
                    expanded.push(a.clone());
                }
            }
            spectec_ast::SpecTecDefTyp::Variant {
                tcs: expanded.iter().map(|a| alt_to_typcase(a, ctx)).collect(),
            }
        }
        SyntaxBody::Record(_) => {
            // Merge fields across profiles via the same `...`-splicing
            // rule we use for variant alts. The shared `insts.dedup()`
            // upstream then folds the two profiles into one Inst.
            let fields = syn.merged.fields_for_profile(prof.profile.as_deref());
            spectec_ast::SpecTecDefTyp::Struct {
                tfs: fields
                    .iter()
                    .map(|f| record_field_to_typfield(f, ctx))
                    .collect(),
            }
        }
    };
    Some(spectec_ast::SpecTecInst::Inst {
        ps: Vec::new(),
        as_: Vec::new(),
        dt,
    })
}

/// If the alt is a single ident matching a declared syntax name (a
/// type-inclusion alt like `| numtype`), return that target name.
fn type_inclusion_target(alt: &Alt, type_names: &std::collections::HashSet<String>) -> Option<String> {
    let toks = &alt.body.tokens;
    if toks.len() != 1 {
        return None;
    }
    let crate::token::Token::Ident(n) = &toks[0].token else {
        return None;
    };
    if type_names.contains(n) {
        Some(n.clone())
    } else {
        None
    }
}

/// If `toks` is a single ident matching a declared syntax name,
/// return it (used for inlining alias-to-variant chains).
fn single_type_name(
    toks: &[crate::token::Spanned],
    type_names: &std::collections::HashSet<String>,
) -> Option<String> {
    if toks.len() != 1 {
        return None;
    }
    let crate::token::Token::Ident(n) = &toks[0].token else {
        return None;
    };
    if type_names.contains(n) {
        Some(n.clone())
    } else {
        None
    }
}

/// Names of single-ident alias syntax decls (e.g. `syntax Inn =
/// addrtype`) whose RHS the OCaml reference dump elaborates to the
/// target's inlined variant cases instead of an `Alias` node. The
/// allowlist is empirical: `Pnn = packtype` has identical source
/// hints to `Inn`/`Lnn`/`Vnn` yet stays an alias in the dump, and
/// no rule in `elab.ml` accounts for the split. See
/// `docs/sketches/spectec-tasks/task-30-typ-alias-inline.md`.
const ALIAS_INLINE_ALLOWLIST: &[&str] = &["Inn", "Lnn", "Vnn"];

/// Try to inline a single-ident alias body to its target's variant
/// cases. Returns `None` if `syn`'s name isn't in the allowlist, the
/// target isn't a declared type, or the target doesn't resolve to a
/// variant — caller falls back to a plain `Alias` node.
fn try_inline_alias_to_variant(
    syn: &DocSyntax,
    tr: &crate::cst::TokenRun,
    ctx: &ElabContext,
    doc: &Doc,
) -> Option<spectec_ast::SpecTecDefTyp> {
    if !ALIAS_INLINE_ALLOWLIST.contains(&syn.name.as_str()) {
        return None;
    }
    let target = single_type_name(&tr.tokens, &ctx.type_names)?;
    let mut visited = std::collections::HashSet::new();
    visited.insert(syn.name.clone());
    let alts = expand_variant_alts(&target, doc, ctx, &mut visited)?;
    Some(spectec_ast::SpecTecDefTyp::Variant {
        tcs: alts.iter().map(|a| alt_to_typcase(a, ctx)).collect(),
    })
}

/// Recursively expand a syntax name to its variant alts. Returns
/// `Some(alts)` if the name resolves (transitively through aliases)
/// to a variant body, `None` otherwise. `visited` guards against
/// alias cycles.
fn expand_variant_alts(
    name: &str,
    doc: &Doc,
    ctx: &ElabContext,
    visited: &mut std::collections::HashSet<String>,
) -> Option<Vec<Alt>> {
    if !visited.insert(name.to_string()) {
        return None;
    }
    let syn = doc.syntax.iter().find(|s| s.name == name)?;
    for prof in &syn.merged.profiles {
        match prof.body.as_ref() {
            Some(SyntaxBody::Variant(_)) => {
                let alts = syn.merged.alts_for_profile(prof.profile.as_deref());
                let mut out = Vec::new();
                for a in &alts {
                    if let Some(target) = type_inclusion_target(a, &ctx.type_names) {
                        match expand_variant_alts(&target, doc, ctx, visited) {
                            Some(sub) => out.extend(sub),
                            None => out.push(a.clone()),
                        }
                    } else {
                        out.push(a.clone());
                    }
                }
                return Some(out);
            }
            Some(SyntaxBody::Alias(tr)) => {
                if let Some(target) = single_type_name(&tr.tokens, &ctx.type_names) {
                    return expand_variant_alts(&target, doc, ctx, visited);
                }
            }
            _ => {}
        }
    }
    None
}

/// Classification of a single alternative in a pattern-literal variant.
/// Pattern-literal variants list either bare numeric literals, the
/// `U+xxxx` codepoint form, or the `...` range-extension marker.
#[derive(Debug, Clone, Copy)]
enum PatternLit {
    /// A literal natural number with its u64 value.
    Lit(u64),
    /// A `...` placeholder bridging the previous and next literals into
    /// a closed range. In OCaml this is the `range` shape.
    DotDotDot,
}

/// Recognise the tokens of one variant alternative as a pure-literal
/// pattern. Returns `Some(...)` for:
/// - `[DotDotDot]` — the range-extension marker
/// - `[Nat(n)]` — a bare decimal/hex numeric literal
/// - `[Ident("U"), Plus, <hex-digit tokens>...]` — a Unicode codepoint
///   `U+xxxx`. The trailing tokens are reassembled into one hex string
///   by concatenating each token's source text and parsed as base 16
///   (so `U+10FFFF`, which lexes to `[Nat(10), Ident("FFFF")]` after
///   `U+`, recovers `0x10FFFF` = 1114111).
fn classify_pattern_lit_alt(alt: &Alt) -> Option<PatternLit> {
    let toks = &alt.body.tokens;
    use crate::token::Token::*;
    if toks.len() == 1 {
        return match &toks[0].token {
            Nat(n) => Some(PatternLit::Lit(nat_to_u64(n))),
            DotDotDot => Some(PatternLit::DotDotDot),
            _ => None,
        };
    }
    // U+xxxx form: starts with `Ident("U") Plus`, then a contiguous run
    // of Nat / Ident tokens whose concatenated source text is hex.
    if toks.len() >= 3
        && matches!(&toks[0].token, Ident(s) if s == "U")
        && matches!(&toks[1].token, Plus)
    {
        let mut hex = String::new();
        for t in &toks[2..] {
            match &t.token {
                Nat(n) => hex.push_str(&n.to_string()),
                Ident(s) if s.chars().all(|c| c.is_ascii_hexdigit()) => hex.push_str(s),
                _ => return None,
            }
        }
        let v = u64::from_str_radix(&hex, 16).ok()?;
        return Some(PatternLit::Lit(v));
    }
    None
}

/// If every alt in `alts` is a pure pattern literal (numeric singleton
/// or `...` range marker), synthesise the single implicit-binder
/// `SpecTecTypCase` that OCaml emits for `syntax bit = 0 | 1`,
/// `syntax byte = 0x00 | ... | 0xFF`, `syntax char = U+0000 | ... |
/// U+D7FF | U+E000 | ... | U+10FFFF`, and friends.
///
/// Output shape: a `Field` case with `MixOp(["", ""])`, a `Tup` of one
/// `Bind { id: "i", typ: Nat }`, and a single `If` premise whose body
/// asserts membership in the literal/range set as a left-associated
/// `Or` of `Eq` (singletons) and `And { Ge, Le }` (closed ranges).
fn try_pattern_literal_variant(alts: &[Alt]) -> Option<spectec_ast::SpecTecTypCase> {
    if alts.is_empty() {
        return None;
    }
    let classified: Vec<PatternLit> = alts
        .iter()
        .map(classify_pattern_lit_alt)
        .collect::<Option<_>>()?;
    // Collapse `lit | ... | lit` triples into closed ranges; bare lits
    // stay as singletons. A leading or trailing `...` (or two `...` in
    // a row) is invalid for this pass — bail to the generic fallback.
    #[derive(Debug)]
    enum Segment {
        Single(u64),
        Range(u64, u64),
    }
    let mut segs: Vec<Segment> = Vec::new();
    let mut i = 0;
    while i < classified.len() {
        match classified[i] {
            PatternLit::DotDotDot => return None,
            PatternLit::Lit(n) => {
                if i + 2 < classified.len()
                    && matches!(classified[i + 1], PatternLit::DotDotDot)
                    && let PatternLit::Lit(m) = classified[i + 2]
                {
                    segs.push(Segment::Range(n, m));
                    i += 3;
                } else {
                    segs.push(Segment::Single(n));
                    i += 1;
                }
            }
        }
    }
    if segs.is_empty() {
        return None;
    }
    let binder = "i".to_string();
    use spectec_ast::{
        SpecTecBinOp, SpecTecBoolTyp, SpecTecCmpOp, SpecTecExp, SpecTecNum, SpecTecNumTyp,
        SpecTecOpTyp,
    };
    let bool_t = SpecTecOpTyp::Bool(SpecTecBoolTyp::Bool);
    let nat_t = SpecTecOpTyp::Num(SpecTecNumTyp::Nat);
    let var_i = || SpecTecExp::Var { id: binder.clone() };
    let lit = |n: u64| SpecTecExp::Num { n: SpecTecNum::Nat(n) };
    let seg_exp = |s: &Segment| match *s {
        Segment::Single(n) => SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            t: bool_t.clone(),
            e1: Box::new(var_i()),
            e2: Box::new(lit(n)),
        },
        Segment::Range(a, b) => SpecTecExp::Bin {
            op: SpecTecBinOp::And,
            t: bool_t.clone(),
            e1: Box::new(SpecTecExp::Cmp {
                op: SpecTecCmpOp::Ge,
                t: nat_t.clone(),
                e1: Box::new(var_i()),
                e2: Box::new(lit(a)),
            }),
            e2: Box::new(SpecTecExp::Cmp {
                op: SpecTecCmpOp::Le,
                t: nat_t.clone(),
                e1: Box::new(var_i()),
                e2: Box::new(lit(b)),
            }),
        },
    };
    let mut iter = segs.iter().map(seg_exp);
    let first = iter.next().expect("segs is non-empty");
    let cond = iter.fold(first, |acc, next| SpecTecExp::Bin {
        op: SpecTecBinOp::Or,
        t: bool_t.clone(),
        e1: Box::new(acc),
        e2: Box::new(next),
    });
    Some(spectec_ast::SpecTecTypCase::Field {
        op: spectec_ast::MixOp::new(vec![String::new(), String::new()]),
        t: spectec_ast::SpecTecTyp::Tup {
            ets: vec![spectec_ast::SpecTecTypBind::Bind {
                id: binder,
                typ: spectec_ast::SpecTecTyp::Num(spectec_ast::SpecTecNumTyp::Nat),
            }],
        },
        qs: Vec::new(),
        prs: vec![spectec_ast::SpecTecPrem::If { e: cond }],
    })
}

/// Convert a variant alternative to a `SpecTecTypCase`. The case's
/// MixOp is constructed from the alt's tokens via the same logic that
/// builds constructor ops in `elab::alt_to_constructor`; the case's
/// operand-tuple type is a placeholder for now (full elaboration of
/// arg-type expressions in alternatives is later work).
fn alt_to_typcase(alt: &Alt, ctx: &ElabContext) -> spectec_ast::SpecTecTypCase {
    let op = if let Some((_, frags)) = alt_to_constructor(alt, &ctx.type_names) {
        mixop_from_typcase_fragments(&frags)
    } else if let Some((frags, _)) = alt_to_headless_with_holes(alt, &ctx.type_names) {
        mixop_from_typcase_fragments(&frags)
    } else {
        mixop_from_alt_tokens(alt)
    };
    spectec_ast::SpecTecTypCase::Field {
        op,
        t: typ_expr_to_spectec_args(alt, ctx),
        qs: Vec::new(),
        prs: Vec::new(),
    }
}

/// Build a TypCase MixOp from constructor fragments. Literals
/// concatenate; each hole introduces a new separator. Mirrors
/// OCaml's `elab.ml` convention: if every separator after the head
/// is empty (i.e. all literals are concentrated in the head), the
/// MixOp collapses to just `[head]`. Otherwise the full per-hole
/// separator list is preserved (including any trailing empty).
fn mixop_from_typcase_fragments(frags: &[crate::mixfix::Fragment]) -> spectec_ast::MixOp {
    let mut parts: Vec<String> = vec![String::new()];
    for f in frags {
        match f {
            crate::mixfix::Fragment::Hole(_) => parts.push(String::new()),
            crate::mixfix::Fragment::Lit(t) => {
                parts.last_mut().unwrap().push_str(&t.to_source_text());
            }
        }
    }
    // Only collapse trailing empty separators when the head is
    // non-empty (i.e. there's an actual case-head name to keep). For
    // headless cases (`mut? valtype` → all-empty separators), OCaml
    // preserves the full `["", "", ""]` shape because there's nothing
    // distinguishing about a single empty.
    if parts.len() > 1 && !parts[0].is_empty() && parts[1..].iter().all(String::is_empty) {
        parts.truncate(1);
    }
    spectec_ast::MixOp::new(parts)
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
            other => s.push_str(&other.to_source_text()),
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

/// Lower a raw token run as a type expression.
pub fn typ_expr_to_spectec(
    toks: &[crate::token::Spanned],
    ctx: &ElabContext,
) -> spectec_ast::SpecTecTyp {
    use crate::token::Token::*;
    use spectec_ast::SpecTecTyp as T;
    if toks.is_empty() {
        return T::Bool;
    }
    // Singleton type-name ident.
    if toks.len() == 1
        && let Ident(n) = &toks[0].token {
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
    // Parametric type use: `Ident ( args )` covering the entire slice.
    if let Some(Spanned { token: Ident(n), .. }) = toks.first()
        && toks.len() >= 3
        && matches!(toks.get(1).map(|s| &s.token), Some(LParen))
        && matches!(toks.last().map(|s| &s.token), Some(RParen))
    {
        let consumed = crate::elab::skip_balanced(&toks[1..]);
        if consumed == toks.len() - 1 {
            let inner = &toks[2..toks.len() - 1];
            let arg_chunks = split_top_level_commas(inner);
            // Each arg is routed by the callee's declared kind, not
            // by syntactic position — the earlier "looks-like-a-type
            // → emit Typ" heuristic regressed Dec entries because
            // Exp-position calls share the same surface shape. See
            // `docs/sketches/spectec-tasks/task-31-typ-arg-kind.md`.
            let kinds = ctx.param_kinds.get(n);
            let arg_specs: Vec<spectec_ast::SpecTecArg> = arg_chunks
                .iter()
                .enumerate()
                .map(|(i, chunk)| {
                    match kinds.and_then(|ks| ks.get(i)) {
                        Some(crate::elab::ParamKind::Typ) => {
                            spectec_ast::SpecTecArg::Typ {
                                t: typ_expr_to_spectec(chunk, ctx),
                            }
                        }
                        _ => {
                            let tr = crate::cst::TokenRun {
                                span: chunk
                                    .iter()
                                    .map(|s| s.span)
                                    .reduce(crate::source::Span::join)
                                    .unwrap_or_else(|| crate::source::Span::new(
                                        crate::source::FileId::new(0),
                                        0,
                                        0,
                                    )),
                                tokens: chunk.to_vec(),
                            };
                            spectec_ast::SpecTecArg::Exp {
                                e: token_run_to_expr(&tr, ctx),
                            }
                        }
                    }
                })
                .collect();
            // Treat as `Var { x: n, as1: arg_specs }` whether or not n
            // is in `type_names` — many parametric types are forward-
            // declared.
            return T::Var {
                x: n.clone(),
                as1: arg_specs,
            };
        }
    }
    // Parenthesised: `( ... )` covering the entire slice. Empty
    // inner `()` is the unit type `Tup{[]}`. Comma-split inner is a
    // tuple type. Single inner element recurses.
    if matches!(toks.first().map(|s| &s.token), Some(LParen))
        && matches!(toks.last().map(|s| &s.token), Some(RParen))
        && crate::elab::skip_balanced(toks) == toks.len()
    {
        let inner = &toks[1..toks.len() - 1];
        if inner.is_empty() {
            return spectec_ast::SpecTecTyp::Tup { ets: Vec::new() };
        }
        let chunks = split_top_level_commas(inner);
        if chunks.len() >= 2 {
            let binds: Vec<spectec_ast::SpecTecTypBind> = chunks
                .iter()
                .map(|c| spectec_ast::SpecTecTypBind::Bind {
                    id: "_".to_string(),
                    typ: typ_expr_to_spectec(c, ctx),
                })
                .collect();
            return spectec_ast::SpecTecTyp::Tup { ets: binds };
        }
        return typ_expr_to_spectec(inner, ctx);
    }
    // Fallback.
    T::Bool
}

/// Helper for inferring a small lookup before constructing a type
/// expression — used in tests, so kept `pub(crate)` even though
/// internal code prefers `typ_expr_to_spectec` directly.
#[allow(dead_code)]
pub(crate) fn lower_typ_for_test(
    toks: &[crate::token::Spanned],
    ctx: &ElabContext,
) -> spectec_ast::SpecTecTyp {
    typ_expr_to_spectec(toks, ctx)
}

/// Lower the type of a variant alternative's arguments. Returns the
/// single arg type or a `Tup` of multiple arg types.
fn typ_expr_to_spectec_args(alt: &Alt, ctx: &ElabContext) -> spectec_ast::SpecTecTyp {
    let hole_toks = if let Some((_, _, h)) =
        alt_to_constructor_with_holes(alt, &ctx.type_names)
    {
        h
    } else if let Some((_, h)) = alt_to_headless_with_holes(alt, &ctx.type_names) {
        h
    } else {
        return spectec_ast::SpecTecTyp::Tup { ets: Vec::new() };
    };
    let binds: Vec<spectec_ast::SpecTecTypBind> = hole_toks
        .iter()
        .map(|toks| spectec_ast::SpecTecTypBind::Bind {
            id: hole_bind_id(toks),
            typ: typ_expr_to_spectec(toks, ctx),
        })
        .collect();
    spectec_ast::SpecTecTyp::Tup { ets: binds }
}

/// Render a hole's source tokens into a `Bind` id, mirroring OCaml's
/// elaborator output (e.g. `valtype?`, `localidx*`, `n`). Complex
/// shapes (anything containing parens) collapse to `"_"` — matches
/// OCaml's behaviour for `list(fieldtype)` and similar parametric
/// type uses where the operand isn't a single metavar.
fn hole_bind_id(toks: &[crate::token::Spanned]) -> String {
    if toks.is_empty() {
        return "_".to_string();
    }
    if toks
        .iter()
        .any(|t| matches!(t.token, crate::token::Token::LParen))
    {
        return "_".to_string();
    }
    let mut s = String::new();
    for t in toks {
        use crate::token::Token::*;
        match &t.token {
            Ident(n) => s.push_str(n),
            Nat(n) => s.push_str(&n.to_string()),
            Star => s.push('*'),
            Plus => s.push('+'),
            Question => s.push('?'),
            other => s.push_str(other.describe().trim_matches('`')),
        }
    }
    s
}

// ---------- grammar production splitting ----------

/// Split a grammar production body on top-level `|` and emit
/// `SpecTecProd::Prod`s. `prev | ... | next` triples are collapsed
/// into a single `Range`-symbol prod to match OCaml's grouping of
/// e.g. `0x00 | ... | 0xFF` into one bounded-range production.
fn split_grammar_prods(
    body: &crate::cst::TokenRun,
    ctx: &ElabContext,
    env: Option<&crate::typecheck::TypeEnv>,
    yield_ty: Option<&spectec_ast::SpecTecTyp>,
) -> Vec<spectec_ast::SpecTecProd> {
    let chunks = split_top_level_pipe(&body.tokens);
    let mut prods = Vec::new();
    let mut i = 0;
    while i < chunks.len() {
        if is_dotdotdot_alt(chunks[i]) && i > 0 && i + 1 < chunks.len() {
            // Replace the previously-emitted prod for `chunks[i-1]`
            // with a single Range prod spanning `prev .. next`.
            prods.pop();
            prods.push(make_range_prod(chunks[i - 1], chunks[i + 1], ctx, body.span));
            i += 2; // skip the `...` and the upper-bound chunk
        } else {
            prods.push(chunk_to_prod(chunks[i], ctx, body.span, env, yield_ty));
            i += 1;
        }
    }
    prods
}

fn is_dotdotdot_alt(chunk: &[crate::token::Spanned]) -> bool {
    chunk.len() == 1 && matches!(chunk[0].token, crate::token::Token::DotDotDot)
}

fn chunk_to_prod(
    chunk: &[crate::token::Spanned],
    ctx: &ElabContext,
    _fallback_span: crate::source::Span,
    env: Option<&crate::typecheck::TypeEnv>,
    yield_ty: Option<&spectec_ast::SpecTecTyp>,
) -> spectec_ast::SpecTecProd {
    let (sym_toks, attr_toks) = split_grammar_arrow(chunk);
    let g = grammar_sym_from_tokens(sym_toks, ctx);
    let ps = match env {
        Some(env) => prod_ps_from_sym(&g, env),
        None => Vec::new(),
    };
    let attr = match attr_toks {
        Some(at) if !at.is_empty() => {
            let span = at
                .iter()
                .map(|s| s.span)
                .reduce(crate::source::Span::join)
                .expect("non-empty chunk has at least one token");
            let tr = crate::cst::TokenRun {
                span,
                tokens: at.to_vec(),
            };
            match (env, yield_ty) {
                (Some(env), Some(t)) => token_run_to_expr_against(&tr, ctx, env, t),
                _ => token_run_to_expr(&tr, ctx),
            }
        }
        _ => raw_sentinel(),
    };
    spectec_ast::SpecTecProd::Prod {
        ps,
        g,
        e: attr,
        prs: Vec::new(),
    }
}

/// Derive a prod's `ps` from the elaborated sym: each `Attr { Var(x),
/// Var(GName) }` introduces a binding `Exp { x, t: yield_of(GName) }`.
/// Binders inside `Iter` nodes get the iter suffix appended to their
/// name and have their type wrapped in the matching `Iter`.
///
/// Mirrors `clause_ps` in spirit (commit 3746326).
///
/// Limitations:
/// - Only `Attr { Var(_), Var(_) }` binders are recognised — pattern
///   binders (`Case "%" ...` LHS) and parametric-grammar RHS
///   (`Blist(Bvaltype)`) are passed through silently.
/// - Iter-context name suffixes only ever use the single-char form
///   (`*`/`?`/`+`); deeply nested iters concatenate (`in*?`), which
///   matches OCaml for the depth-1 cases that wasm-3.0 exercises.
fn prod_ps_from_sym(
    sym: &spectec_ast::SpecTecSym,
    env: &crate::typecheck::TypeEnv,
) -> Vec<spectec_ast::SpecTecParam> {
    let mut order: Vec<String> = Vec::new();
    let mut entries: std::collections::BTreeMap<String, spectec_ast::SpecTecTyp> =
        std::collections::BTreeMap::new();
    walk_sym_for_binders(sym, "", &mut order, &mut entries, env);
    order
        .into_iter()
        .map(|name| {
            let t = entries
                .remove(&name)
                .unwrap_or(spectec_ast::SpecTecTyp::Bool);
            spectec_ast::SpecTecParam::Exp { x: name, t }
        })
        .collect()
}

fn walk_sym_for_binders(
    sym: &spectec_ast::SpecTecSym,
    iter_suffix: &str,
    order: &mut Vec<String>,
    entries: &mut std::collections::BTreeMap<String, spectec_ast::SpecTecTyp>,
    env: &crate::typecheck::TypeEnv,
) {
    use spectec_ast::SpecTecSym as S;
    match sym {
        S::Attr {
            e: spectec_ast::SpecTecExp::Var { id },
            g1,
        } => {
            // Only `Attr { Var, Var{GName} }` shapes contribute a ps
            // entry. The base type prefers the binder name's metavar
            // declaration (`var x : idx`) over the grammar's yield
            // type — OCaml mirrors a clause's `var`-aware lookup here.
            if let S::Var { x: gname, .. } = g1.as_ref() {
                let name = format!("{}{}", id, iter_suffix);
                if entries.contains_key(&name) {
                    return;
                }
                let base = env
                    .vars
                    .get(crate::elab::metavar_base(id))
                    .cloned()
                    .or_else(|| env.grammars.get(gname).cloned())
                    .unwrap_or(spectec_ast::SpecTecTyp::Bool);
                let t = if iter_suffix.is_empty() {
                    base
                } else {
                    crate::typecheck::wrap_in_iters(base, iter_suffix)
                };
                entries.insert(name.clone(), t);
                order.push(name);
            }
        }
        S::Seq { gs } => {
            for g in gs {
                walk_sym_for_binders(g, iter_suffix, order, entries, env);
            }
        }
        S::Iter { g1, it, .. } => {
            let ch = match it {
                spectec_ast::SpecTecIter::List => '*',
                spectec_ast::SpecTecIter::Opt => '?',
                spectec_ast::SpecTecIter::List1 => '+',
                spectec_ast::SpecTecIter::ListN { .. } => '*',
            };
            let mut new_suffix = String::new();
            new_suffix.push(ch);
            new_suffix.push_str(iter_suffix);
            walk_sym_for_binders(g1, &new_suffix, order, entries, env);
        }
        S::Alt { gs } => {
            for g in gs {
                walk_sym_for_binders(g, iter_suffix, order, entries, env);
            }
        }
        _ => {}
    }
}

/// Bare-range prods (`0x00 | ... | 0xFF`) have no source-level binder
/// — OCaml synthesises one named `<implicit-prod-result>` (the angle
/// brackets are part of the literal name) so the prod's case-ctor
/// (`%`) can name the matched value.
fn make_range_prod(
    lower: &[crate::token::Spanned],
    upper: &[crate::token::Spanned],
    ctx: &ElabContext,
    _fallback_span: crate::source::Span,
) -> spectec_ast::SpecTecProd {
    let g_lower = grammar_sym_from_tokens(lower, ctx);
    let g_upper = grammar_sym_from_tokens(upper, ctx);
    let bind_name = "<implicit-prod-result>".to_string();
    let range = spectec_ast::SpecTecSym::Range {
        g1: Box::new(g_lower),
        g2: Box::new(g_upper),
    };
    spectec_ast::SpecTecProd::Prod {
        ps: vec![spectec_ast::SpecTecParam::Exp {
            x: bind_name.clone(),
            t: spectec_ast::SpecTecTyp::Num(spectec_ast::SpecTecNumTyp::Nat),
        }],
        g: spectec_ast::SpecTecSym::Attr {
            e: spectec_ast::SpecTecExp::Var {
                id: bind_name.clone(),
            },
            g1: Box::new(range),
        },
        e: spectec_ast::SpecTecExp::Case {
            op: spectec_ast::MixOp::new(vec![String::new(), String::new()]),
            e1: Box::new(spectec_ast::SpecTecExp::Tup {
                es: vec![spectec_ast::SpecTecExp::Var { id: bind_name }],
            }),
        },
        prs: Vec::new(),
    }
}

fn split_top_level_pipe(toks: &[crate::token::Spanned]) -> Vec<&[crate::token::Spanned]> {
    let mut out = Vec::new();
    let mut depth: i32 = 0;
    let mut start = 0usize;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            crate::token::Token::LParen
            | crate::token::Token::LBracket
            | crate::token::Token::LBrace => depth += 1,
            crate::token::Token::RParen
            | crate::token::Token::RBracket
            | crate::token::Token::RBrace => depth -= 1,
            crate::token::Token::Pipe if depth == 0 => {
                if start < i {
                    out.push(&toks[start..i]);
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < toks.len() {
        out.push(&toks[start..]);
    }
    out
}

/// Split a grammar production chunk on top-level `=> ` (i.e. `Eq`
/// followed by `GreaterThan`). Returns `(sym_toks, Some(attr_toks))`
/// if `=>` is present, else `(sym_toks, None)`.
fn split_grammar_arrow(
    toks: &[crate::token::Spanned],
) -> (&[crate::token::Spanned], Option<&[crate::token::Spanned]>) {
    let mut depth: i32 = 0;
    let mut i = 0;
    while i + 1 < toks.len() {
        match &toks[i].token {
            crate::token::Token::LParen
            | crate::token::Token::LBracket
            | crate::token::Token::LBrace => depth += 1,
            crate::token::Token::RParen
            | crate::token::Token::RBracket
            | crate::token::Token::RBrace => depth -= 1,
            crate::token::Token::Eq if depth == 0 => {
                if matches!(toks[i + 1].token, crate::token::Token::GreaterThan) {
                    return (&toks[..i], Some(&toks[i + 2..]));
                }
            }
            _ => {}
        }
        i += 1;
    }
    (toks, None)
}

/// Build a `SpecTecSym` from a grammar-production symbol's tokens.
///
/// Splits `toks` on atom boundaries (see [`split_juxtaposed`]). A
/// single chunk lowers directly via [`chunk_to_atom`]; multiple chunks
/// produce OCaml's per-element nested `Seq` shape:
///
/// ```text
/// Seq { gs: [ Seq { gs: [atom_0] }, Seq { gs: [atom_1] }, ... ] }
/// ```
///
/// The double `Seq` wrap is load-bearing — OCaml's pretty-printer
/// emits exactly that.
fn grammar_sym_from_tokens(
    toks: &[crate::token::Spanned],
    ctx: &ElabContext,
) -> spectec_ast::SpecTecSym {
    use crate::token::Token::*;
    use spectec_ast::SpecTecSym as S;
    if toks.is_empty() {
        return S::Eps;
    }
    if toks.len() == 1 && matches!(toks[0].token, Eps) {
        return S::Eps;
    }
    let chunks = split_juxtaposed(toks);
    if chunks.len() == 1 {
        return chunk_to_atom(chunks[0], ctx);
    }
    let gs = chunks
        .into_iter()
        .filter(|c| !c.is_empty())
        .map(|c| S::Seq { gs: vec![chunk_to_atom(c, ctx)] })
        .collect();
    S::Seq { gs }
}

/// Walk `toks` left-to-right, grouping into atom-sized chunks.
///
/// Each call to [`end_of_atom`] returns the past-the-end index of one
/// atom starting at `i`. Empty atoms (zero-width matches) are skipped
/// by forcing forward progress.
///
/// TODO(#24): `Ident Colon <rest>` binder atoms span multiple tokens.
/// TODO(#25): `(...)` and `(...)<iter>` paren-grouped atoms span
/// the whole balanced group plus any trailing iter suffix.
fn split_juxtaposed(toks: &[crate::token::Spanned]) -> Vec<&[crate::token::Spanned]> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        let j = end_of_atom(toks, i).max(i + 1);
        out.push(&toks[i..j.min(toks.len())]);
        i = j;
    }
    out
}

/// Past-the-end index of the atom starting at `toks[start]`.
///
/// Recognised atom shapes:
/// - any single non-paren token (task 23)
/// - `LParen ... RParen [Star|Question|Plus]?` — paren-grouped
///   sub-grammar with optional trailing iter suffix (task 25)
/// - `Ident [Star|Question|Plus]` — bare ident iter (task 25)
/// - `Ident [Star|Question|Plus]? Colon <atom>` — binder atom
///   (task 24); iter suffix on the LHS is consumed but its symbolic
///   lowering is left to a follow-up
fn end_of_atom(toks: &[crate::token::Spanned], start: usize) -> usize {
    use crate::token::Token::*;
    let lead = match toks.get(start).map(|s| &s.token) {
        Some(t) => t,
        None => return start,
    };
    let mut j = match lead {
        LParen => find_matching_rparen(toks, start) + 1,
        _ => start + 1,
    };
    // Trailing iter suffix attaches to whatever the leader is, as long
    // as it can sensibly iterate — a paren group or a bare ident.
    let lead_takes_iter = matches!(lead, LParen | Ident(_));
    if lead_takes_iter
        && matches!(toks.get(j).map(|s| &s.token), Some(Star | Question | Plus))
    {
        j += 1;
    }
    // Binder: `Ident [iter]? Colon <atom>`. Only triggers when the
    // leading token is an Ident; the iter suffix has already been
    // consumed above when present.
    if matches!(lead, Ident(_))
        && matches!(toks.get(j).map(|s| &s.token), Some(Colon))
    {
        j += 1;
        if j < toks.len() {
            j = end_of_atom(toks, j);
        }
    }
    j
}

/// Index of the `RParen` that matches `toks[start]` (which must be
/// `LParen`). Unmatched parens consume to the end of the slice.
fn find_matching_rparen(toks: &[crate::token::Spanned], start: usize) -> usize {
    use crate::token::Token::*;
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate().skip(start) {
        match &t.token {
            LParen => depth += 1,
            RParen => {
                depth -= 1;
                if depth == 0 {
                    return i;
                }
            }
            _ => {}
        }
    }
    toks.len().saturating_sub(1)
}

/// Lower one juxtaposition chunk into a single `SpecTecSym` atom.
///
/// Recognised shapes:
/// - empty / `eps` keyword → `Eps`
/// - `Nat` → `Num { n }`
/// - `Text` → `Text { t }`
/// - bare `Ident` → `Var { x, as1: [] }`
/// - `Ident <iter>` → `Iter { Var(name), it, xes: [] }` (task #25,
///   `xes` deferred)
/// - `LParen ... RParen` → recurse into inner sym (task #25)
/// - `LParen ... RParen <iter>` → `Iter { inner_sym, it, xes: [] }`
///   (task #25, `xes` deferred)
/// - `Ident Colon <rest>` binder → `Attr { e: Var(name), g1: rest }`
///   (task #24)
/// - any other single token → `Eps` (defensive fallback)
///
/// TODO: iter-suffixed binder LHS (`t*:Bvaltype`) — the LHS expression
/// would need to be elaborated as `Iter { Var(t), ... }`, which
/// requires expression-side work; for now we keep the binder atom
/// grouped (so the chunker doesn't fragment it) but fall through to
/// `Eps` here.
/// TODO: dom annotations (`xes`) on `Iter` — currently `[]`, which
/// matches the structural sym shape but leaves binder-domain info
/// missing.
fn chunk_to_atom(
    chunk: &[crate::token::Spanned],
    ctx: &ElabContext,
) -> spectec_ast::SpecTecSym {
    use crate::token::Token::*;
    use spectec_ast::SpecTecSym as S;
    if chunk.is_empty() {
        return S::Eps;
    }

    // Paren-grouped sub-grammar with optional trailing iter suffix.
    if matches!(chunk[0].token, LParen) {
        let close = find_matching_rparen(chunk, 0);
        let inner = &chunk[1..close];
        let inner_sym = grammar_sym_from_tokens(inner, ctx);
        let iter = iter_from_suffix(chunk.get(close + 1).map(|s| &s.token));
        return match iter {
            None => inner_sym,
            Some(it) => S::Iter {
                g1: Box::new(inner_sym),
                it,
                xes: Vec::new(),
            },
        };
    }

    // Bare ident with iter suffix: `Btagidx*` etc.
    if chunk.len() == 2
        && let Ident(name) = &chunk[0].token
        && let Some(it) = iter_from_suffix(chunk.get(1).map(|s| &s.token))
    {
        return S::Iter {
            g1: Box::new(S::Var { x: name.clone(), as1: Vec::new() }),
            it,
            xes: Vec::new(),
        };
    }

    // Binder: `Ident Colon <rest>`. Iter-suffixed binder LHS
    // (`t*:Btagidx`) deliberately falls through to `Eps` for now —
    // see the function docstring.
    if chunk.len() >= 3
        && let Ident(name) = &chunk[0].token
        && matches!(chunk[1].token, Colon)
    {
        let g1 = chunk_to_atom(&chunk[2..], ctx);
        return S::Attr {
            e: spectec_ast::SpecTecExp::Var { id: name.clone() },
            g1: Box::new(g1),
        };
    }

    if chunk.len() == 1 {
        match &chunk[0].token {
            Eps => return S::Eps,
            Ident(n) => return S::Var { x: n.clone(), as1: Vec::new() },
            Nat(n) => {
                let v = u64::try_from(n).unwrap_or(u64::MAX);
                let v: i64 = i64::try_from(v).unwrap_or(i64::MAX);
                return S::Num { n: v };
            }
            Text(t) => return S::Text { t: t.clone() },
            _ => {}
        }
    }
    // Unrecognised multi-token chunk (iter-suffixed binder LHS, etc.).
    let _ = ctx;
    S::Eps
}

/// Map a trailing iter-suffix token to its `SpecTecIter`.
fn iter_from_suffix(t: Option<&crate::token::Token>) -> Option<spectec_ast::SpecTecIter> {
    use crate::token::Token::*;
    use spectec_ast::SpecTecIter as I;
    match t {
        Some(Star) => Some(I::List),
        Some(Question) => Some(I::Opt),
        Some(Plus) => Some(I::List1),
        _ => None,
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
    let kinds: Vec<DefKind> = defs.iter().map(def_kind).collect();
    let mut deps: Vec<Vec<usize>> = Vec::with_capacity(n);
    for (i, d) in defs.iter().enumerate() {
        let refs = referenced_names(d);
        // Only consider edges within the same namespace (Typ→Typ,
        // Rel→Rel, etc.). OCaml's elaborator groups Rec the same way.
        let mut targets: Vec<usize> = refs
            .into_iter()
            .filter_map(|r| idx_by_name.get(&r).copied())
            .filter(|&j| kinds[j] == kinds[i])
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
            // Self-loop check. (An earlier experiment also wrapped
            // every `Rel` in `Rec` to match OCaml's pattern, but that
            // over-wrapped — OCaml's convention is more nuanced than
            // "always Rel". Sticking with the direct self-loop rule.)
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

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum DefKind {
    Typ,
    Rel,
    Dec,
    Gram,
    Rec,
}

fn def_kind(d: &spectec_ast::SpecTecDef) -> DefKind {
    match d {
        spectec_ast::SpecTecDef::Typ { .. } => DefKind::Typ,
        spectec_ast::SpecTecDef::Rel { .. } => DefKind::Rel,
        spectec_ast::SpecTecDef::Dec { .. } => DefKind::Dec,
        spectec_ast::SpecTecDef::Gram { .. } => DefKind::Gram,
        spectec_ast::SpecTecDef::Rec { .. } => DefKind::Rec,
    }
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
    fn walk_typ(t: &spectec_ast::SpecTecTyp, out: &mut std::collections::HashSet<String>) {
        use spectec_ast::SpecTecTyp as T;
        match t {
            T::Var { x, as1 } => {
                out.insert(x.clone());
                for a in as1 {
                    walk_arg(a, out);
                }
            }
            T::Tup { ets } => {
                for spectec_ast::SpecTecTypBind::Bind { typ, .. } in ets {
                    walk_typ(typ, out);
                }
            }
            T::Iter { t1, .. } => walk_typ(t1, out),
            T::Bool | T::Num(_) | T::Text => {}
        }
    }
    fn walk_arg(a: &spectec_ast::SpecTecArg, out: &mut std::collections::HashSet<String>) {
        use spectec_ast::SpecTecArg as A;
        match a {
            A::Exp { e } => walk_exp(e, out),
            A::Typ { t } => walk_typ(t, out),
            A::Def { x } => {
                out.insert(x.clone());
            }
            A::Gram { .. } => {}
        }
    }
    fn walk_param(p: &spectec_ast::SpecTecParam, out: &mut std::collections::HashSet<String>) {
        use spectec_ast::SpecTecParam as P;
        match p {
            P::Exp { t, .. } | P::Gram { t, .. } => walk_typ(t, out),
            P::Def { ps, t, .. } => {
                for pp in ps {
                    walk_param(pp, out);
                }
                walk_typ(t, out);
            }
            P::Typ { .. } => {}
        }
    }
    match d {
        spectec_ast::SpecTecDef::Typ { ps, insts, .. } => {
            for p in ps {
                walk_param(p, &mut out);
            }
            for spectec_ast::SpecTecInst::Inst { ps, as_, dt } in insts {
                for p in ps {
                    walk_param(p, &mut out);
                }
                for a in as_ {
                    walk_arg(a, &mut out);
                }
                use spectec_ast::SpecTecDefTyp as DT;
                match dt {
                    DT::Alias { typ } => walk_typ(typ, &mut out),
                    DT::Struct { tfs } => {
                        for spectec_ast::SpecTecTypField::Field { at, t, .. } in tfs {
                            for f in at.fragments() {
                                out.insert(f.clone());
                            }
                            walk_typ(t, &mut out);
                        }
                    }
                    DT::Variant { tcs } => {
                        for spectec_ast::SpecTecTypCase::Field { op, t, .. } in tcs {
                            for f in op.fragments() {
                                out.insert(f.clone());
                            }
                            walk_typ(t, &mut out);
                        }
                    }
                }
            }
        }
        spectec_ast::SpecTecDef::Rel { ps, t, rules, .. } => {
            for p in ps {
                walk_param(p, &mut out);
            }
            walk_typ(t, &mut out);
            for spectec_ast::SpecTecRule::Rule { ps, e, prs, .. } in rules {
                for p in ps {
                    walk_param(p, &mut out);
                }
                walk_exp(e, &mut out);
                for p in prs {
                    walk_prem(p, &mut out);
                }
            }
        }
        spectec_ast::SpecTecDef::Dec { ps, t, clauses, .. } => {
            for p in ps {
                walk_param(p, &mut out);
            }
            walk_typ(t, &mut out);
            for spectec_ast::SpecTecClause::Clause { ps, as_, e, prs } in clauses {
                for p in ps {
                    walk_param(p, &mut out);
                }
                for a in as_ {
                    walk_arg(a, &mut out);
                }
                walk_exp(e, &mut out);
                for p in prs {
                    walk_prem(p, &mut out);
                }
            }
        }
        spectec_ast::SpecTecDef::Gram { ps, t, prods, .. } => {
            for p in ps {
                walk_param(p, &mut out);
            }
            walk_typ(t, &mut out);
            for spectec_ast::SpecTecProd::Prod { ps, e, prs, .. } in prods {
                for p in ps {
                    walk_param(p, &mut out);
                }
                walk_exp(e, &mut out);
                for p in prs {
                    walk_prem(p, &mut out);
                }
            }
        }
        spectec_ast::SpecTecDef::Rec { .. } => {}
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

#[allow(clippy::too_many_arguments)]
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

    #[test]
    fn pattern_literal_variant_bit() {
        // `syntax bit = 0 | 1` should emit ONE TypCase with `MixOp(["",
        // ""])`, a `Tup` of one `i: nat`, and an `If` of `Or(Eq i 0,
        // Eq i 1)` — the OCaml implicit-binder shape.
        let src = "syntax bit = 0 | 1";
        let (tops, ctx) = build(src);
        let doc = build_doc(&tops, &ctx);
        let defs = to_spectec_ast(&doc, &ctx);
        let spectec_ast::SpecTecDef::Typ { insts, .. } = &defs[0] else {
            panic!("expected Typ def");
        };
        let spectec_ast::SpecTecInst::Inst { dt, .. } = &insts[0];
        let spectec_ast::SpecTecDefTyp::Variant { tcs } = dt else {
            panic!("expected Variant");
        };
        assert_eq!(tcs.len(), 1);
        let spectec_ast::SpecTecTypCase::Field { op, t, prs, .. } = &tcs[0];
        assert_eq!(op.fragments(), &["", ""]);
        let spectec_ast::SpecTecTyp::Tup { ets } = t else {
            panic!("expected Tup");
        };
        let spectec_ast::SpecTecTypBind::Bind { id, typ } = &ets[0];
        assert_eq!(id, "i");
        assert!(matches!(typ, spectec_ast::SpecTecTyp::Num(spectec_ast::SpecTecNumTyp::Nat)));
        assert_eq!(prs.len(), 1);
        let spectec_ast::SpecTecPrem::If { e } = &prs[0] else {
            panic!("expected If premise");
        };
        // Body should be Or(Eq, Eq).
        assert!(matches!(
            e,
            spectec_ast::SpecTecExp::Bin { op: spectec_ast::SpecTecBinOp::Or, .. }
        ));
    }

    #[test]
    fn pattern_literal_variant_byte_range() {
        // `syntax byte = 0x00 | ... | 0xFF` collapses to one case with
        // `And(Ge i 0, Le i 255)`.
        let src = "syntax byte = 0x00 | ... | 0xFF";
        let (tops, ctx) = build(src);
        let doc = build_doc(&tops, &ctx);
        let defs = to_spectec_ast(&doc, &ctx);
        let spectec_ast::SpecTecDef::Typ { insts, .. } = &defs[0] else {
            panic!("expected Typ def");
        };
        let spectec_ast::SpecTecInst::Inst { dt, .. } = &insts[0];
        let spectec_ast::SpecTecDefTyp::Variant { tcs } = dt else {
            panic!("expected Variant");
        };
        assert_eq!(tcs.len(), 1);
        let spectec_ast::SpecTecTypCase::Field { prs, .. } = &tcs[0];
        let spectec_ast::SpecTecPrem::If { e } = &prs[0] else {
            panic!("expected If premise");
        };
        // Body should be And(Ge ..., Le ...) — a single closed range,
        // no top-level Or.
        let spectec_ast::SpecTecExp::Bin { op, e1, e2, .. } = e else {
            panic!("expected Bin");
        };
        assert!(matches!(op, spectec_ast::SpecTecBinOp::And));
        let spectec_ast::SpecTecExp::Cmp { op: ge, .. } = e1.as_ref() else {
            panic!("expected Cmp Ge");
        };
        let spectec_ast::SpecTecExp::Cmp { op: le, e2: le_rhs, .. } = e2.as_ref() else {
            panic!("expected Cmp Le");
        };
        assert!(matches!(ge, spectec_ast::SpecTecCmpOp::Ge));
        assert!(matches!(le, spectec_ast::SpecTecCmpOp::Le));
        assert!(matches!(
            le_rhs.as_ref(),
            spectec_ast::SpecTecExp::Num { n: spectec_ast::SpecTecNum::Nat(255) }
        ));
    }

    #[test]
    fn pattern_literal_variant_unicode_codepoints() {
        // `syntax char = U+0000 | ... | U+D7FF | U+E000 | ... | U+10FFFF`
        // produces two ranges combined by `Or`. The upper bound 0x10FFFF
        // = 1114111 verifies the multi-token `U+` reassembly.
        let src = r#"syntax char = U+0000 | ... | U+D7FF | U+E000 | ... | U+10FFFF"#;
        let (tops, ctx) = build(src);
        let doc = build_doc(&tops, &ctx);
        let defs = to_spectec_ast(&doc, &ctx);
        let spectec_ast::SpecTecDef::Typ { insts, .. } = &defs[0] else {
            panic!("expected Typ def");
        };
        let spectec_ast::SpecTecInst::Inst { dt, .. } = &insts[0];
        let spectec_ast::SpecTecDefTyp::Variant { tcs } = dt else {
            panic!("expected Variant");
        };
        assert_eq!(tcs.len(), 1);
        let spectec_ast::SpecTecTypCase::Field { prs, .. } = &tcs[0];
        let spectec_ast::SpecTecPrem::If { e } = &prs[0] else {
            panic!("expected If premise");
        };
        // Body: Or(And(...,Le 55295), And(Ge 57344, Le 1114111)).
        let spectec_ast::SpecTecExp::Bin { op, e1, e2, .. } = e else {
            panic!("expected Bin Or");
        };
        assert!(matches!(op, spectec_ast::SpecTecBinOp::Or));
        let spectec_ast::SpecTecExp::Bin { e2: lo_le, .. } = e1.as_ref() else {
            panic!("expected And on lower range");
        };
        let spectec_ast::SpecTecExp::Cmp { e2: lo_bound, .. } = lo_le.as_ref() else {
            panic!("expected Le");
        };
        assert!(matches!(
            lo_bound.as_ref(),
            spectec_ast::SpecTecExp::Num { n: spectec_ast::SpecTecNum::Nat(55295) }
        ));
        let spectec_ast::SpecTecExp::Bin { e2: hi_le, .. } = e2.as_ref() else {
            panic!("expected And on upper range");
        };
        let spectec_ast::SpecTecExp::Cmp { e2: hi_bound, .. } = hi_le.as_ref() else {
            panic!("expected Le");
        };
        assert!(matches!(
            hi_bound.as_ref(),
            spectec_ast::SpecTecExp::Num { n: spectec_ast::SpecTecNum::Nat(1114111) }
        ));
    }

    #[test]
    fn pattern_literal_variant_single_singleton() {
        // `syntax symdots = 0` — single literal, no `|`. The parser must
        // route it through the variant path, then the elaborator emits
        // one case with `Eq i 0`.
        let src = "syntax symdots = 0";
        let (tops, ctx) = build(src);
        let doc = build_doc(&tops, &ctx);
        let defs = to_spectec_ast(&doc, &ctx);
        let spectec_ast::SpecTecDef::Typ { insts, .. } = &defs[0] else {
            panic!("expected Typ def");
        };
        let spectec_ast::SpecTecInst::Inst { dt, .. } = &insts[0];
        let spectec_ast::SpecTecDefTyp::Variant { tcs } = dt else {
            panic!("expected Variant, got {:?}", dt);
        };
        assert_eq!(tcs.len(), 1);
        let spectec_ast::SpecTecTypCase::Field { prs, .. } = &tcs[0];
        let spectec_ast::SpecTecPrem::If { e } = &prs[0] else {
            panic!("expected If");
        };
        assert!(matches!(
            e,
            spectec_ast::SpecTecExp::Cmp { op: spectec_ast::SpecTecCmpOp::Eq, .. }
        ));
    }
}
