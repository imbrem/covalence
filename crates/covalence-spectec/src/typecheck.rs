//! Type-checking pass over the elaborated AST.
//!
//! Mirrors the structure of the OCaml SpecTec elaborator
//! (`spectec/src/frontend/elab.ml`) so the output matches the OCaml
//! dump shape. The pass:
//!
//! 1. Builds a [`TypeEnv`] from the elaboration context — maps every
//!    declared name (syntax, var, def, relation, grammar) to its
//!    types and parameters.
//! 2. Walks each rule conclusion + premises, refining the
//!    placeholder type annotations on `Un.t` / `Bin.t` / `Cmp.t`,
//!    looking up `Var` types, and inserting `Sub` coercions at
//!    subtyping boundaries.
//! 3. Same for `def` clause arg patterns and RHSes.
//!
//! Style: refine the existing `Expr` / `ElabPremise` enums in place
//! (returning new values from the walker rather than mutating
//! references). No new typed AST — the same data structure carries
//! both untyped (placeholders) and typed (refined) values.
//!
//! Status: **infrastructure only.** This file currently builds the
//! TypeEnv and provides a pass-through walker. Real refinement
//! (operator-type inference, var lookup, Sub insertion) is added in
//! subsequent commits.

use std::collections::BTreeMap;

use crate::ast_doc::Doc;
use crate::elab::{ElabContext, ElabPremise, Expr};

/// Type-checking environment, modelled on OCaml's `elab.ml::env`.
///
/// Stores resolved type information for every declared name in the
/// spec. Built once per `Doc` and threaded through the bidirectional
/// `check_exp` / `infer_exp` walkers.
#[derive(Debug, Default)]
pub struct TypeEnv {
    /// `var NAME : T` lookups, by base metavariable name (subscript
    /// and prime suffixes stripped during lookup, see
    /// [`elab::metavar_base`]).
    pub vars: BTreeMap<String, spectec_ast::SpecTecTyp>,
    /// `relation NAME: ...` operand-tuple types, by relation name.
    pub relations: BTreeMap<String, spectec_ast::SpecTecTyp>,
    /// `def $NAME(args) : T` return types, by def name.
    pub defs: BTreeMap<String, DefSig>,
    /// `grammar NAME : T` yield types, by grammar name.
    pub grammars: BTreeMap<String, spectec_ast::SpecTecTyp>,
}

#[derive(Debug, Clone)]
pub struct DefSig {
    pub params: Vec<spectec_ast::SpecTecParam>,
    pub ret: spectec_ast::SpecTecTyp,
}

/// Build the [`TypeEnv`] for a fully-elaborated `Doc`.
///
/// Walks each `DocVar` / `DocRelation` / `DocDef` / `DocGrammar`,
/// pulling out the type information already computed by the
/// converter helpers (`typ_expr_to_spectec`, `relation_operand_type`,
/// etc.). Doesn't mutate the Doc.
pub fn build_env(doc: &Doc, ctx: &ElabContext) -> TypeEnv {
    let mut env = TypeEnv::default();

    // Vars.
    for v in &doc.vars {
        let ty = crate::ast_doc::typ_expr_to_spectec_no_ctx(&v.decl.ty.tokens);
        env.vars.insert(v.name.clone(), ty);
    }

    // Relations.
    for rel in &doc.relations {
        let (_, hole_toks) = crate::elab::template_to_fragments_with_holes(
            &rel.decl.template,
            &ctx.type_names,
        );
        let t = crate::ast_doc::relation_operand_type(&hole_toks, ctx);
        env.relations.insert(rel.name.clone(), t);
    }

    // Defs.
    for d in &doc.defs {
        let ret = crate::ast_doc::typ_expr_to_spectec(&d.sig.ret_ty.tokens, ctx);
        let params: Vec<spectec_ast::SpecTecParam> = d
            .sig
            .arg_tys
            .iter()
            .filter_map(|arg_tr| crate::ast_doc::chunk_to_syntax_param(&arg_tr.tokens))
            .collect();
        env.defs.insert(d.name.clone(), DefSig { params, ret });
    }

    // Grammars.
    for g in &doc.grammars {
        let t = crate::ast_doc::typ_expr_to_spectec(&g.decl.ret.tokens, ctx);
        env.grammars.insert(g.name.clone(), t);
    }

    env
}

/// Type-check a single expression. Returns the refined expression
/// (with `Un.t` / `Bin.t` / `Cmp.t` populated, `Sub` coercions
/// inserted where needed, etc.).
///
/// Current implementation: pass-through. Real refinement follows in
/// subsequent commits.
pub fn check_exp(env: &TypeEnv, e: Expr) -> Expr {
    let _ = env;
    e
}

/// Type-check a premise.
pub fn check_premise(env: &TypeEnv, p: ElabPremise) -> ElabPremise {
    let _ = env;
    p
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast_doc::build_doc, elab::build_table, lex::lex, parse::parse, source::SourceMap};

    fn build(src: &str) -> (Doc, ElabContext) {
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let toks = lex(id, src).unwrap();
        let tops = parse(id, toks).unwrap();
        let ctx = build_table(&tops).unwrap();
        let doc = build_doc(&tops, &ctx);
        (doc, ctx)
    }

    #[test]
    fn env_records_var_types() {
        let src = r#"
            syntax t = nat
            var C : t
            var x : nat
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        assert!(env.vars.contains_key("C"));
        assert!(env.vars.contains_key("x"));
    }

    #[test]
    fn env_records_relation_operand_types() {
        let src = r#"
            syntax t = nat
            syntax context = nat
            relation R: context |- t : t
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        // R has 3 operands: context, t, t — should be a Tup type.
        let r = env.relations.get("R").unwrap();
        assert!(matches!(r, spectec_ast::SpecTecTyp::Tup { ets } if ets.len() == 3));
    }

    #[test]
    fn env_records_def_signatures() {
        let src = r#"
            def $min(nat, nat) : nat
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        let sig = env.defs.get("min").unwrap();
        assert_eq!(sig.params.len(), 2);
        assert!(matches!(sig.ret, spectec_ast::SpecTecTyp::Num(_)));
    }

    #[test]
    fn check_exp_is_passthrough_for_now() {
        let env = TypeEnv::default();
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let e = Expr::Var {
            span,
            name: "x".to_string(),
        };
        let result = check_exp(&env, e.clone());
        assert!(matches!(
            (e, result),
            (Expr::Var { name: ref a, .. }, Expr::Var { name: ref b, .. }) if a == b
        ));
    }
}
