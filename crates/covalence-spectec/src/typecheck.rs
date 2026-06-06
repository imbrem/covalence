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
use crate::elab::{BinOp, CmpOp, ElabContext, ElabPremise, Expr, OpType, UnOp};

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

/// Convenience alias for the type we use internally — directly the
/// `spectec_ast` form so the converter doesn't need any further
/// translation.
pub type Typ = spectec_ast::SpecTecTyp;

/// Type used as a placeholder when we can't infer (e.g. for `Raw`
/// fallbacks or sentinel values). Distinct from a literal `Bool`
/// type — callers should treat this as "unknown" and not try to
/// subtype against it.
pub fn unknown_typ() -> Typ {
    Typ::Bool
}

/// Type-check + infer the type of an expression. Returns the
/// (possibly refined) expression and its inferred type.
///
/// Mirrors OCaml's `infer_exp env e : Il.exp * Il.typ` pattern. The
/// returned `Expr` may have refined operator types, `Sub` coercions
/// inserted, etc., though the current implementation only covers
/// literal types and `Var` lookups; the rest is incremental.
pub fn infer_exp(env: &TypeEnv, e: Expr) -> (Expr, Typ) {
    use spectec_ast::SpecTecNumTyp;
    match e {
        Expr::Var { span, name } => {
            let t = lookup_var(env, &name);
            (Expr::Var { span, name }, t)
        }
        Expr::Bool { span, value } => (Expr::Bool { span, value }, Typ::Bool),
        Expr::Num { span, ref value } => {
            let t = match value {
                crate::elab::NumLit::Nat(_) => Typ::Num(SpecTecNumTyp::Nat),
                crate::elab::NumLit::Int(_) => Typ::Num(SpecTecNumTyp::Int),
                crate::elab::NumLit::Rat(_) => Typ::Num(SpecTecNumTyp::Rat),
                crate::elab::NumLit::Real(_) => Typ::Num(SpecTecNumTyp::Real),
            };
            let value = value.clone();
            (Expr::Num { span, value }, t)
        }
        Expr::Text { span, value } => (Expr::Text { span, value }, Typ::Text),
        Expr::Eps { span } => (
            Expr::Eps { span },
            Typ::Iter {
                t1: Box::new(unknown_typ()),
                it: vec![spectec_ast::SpecTecIter::List],
            },
        ),
        Expr::Tup { span, items } => {
            let mut new_items = Vec::with_capacity(items.len());
            let mut binds = Vec::with_capacity(items.len());
            for item in items {
                let (item, t) = infer_exp(env, item);
                new_items.push(item);
                binds.push(spectec_ast::SpecTecTypBind::Bind {
                    id: "_".to_string(),
                    typ: t,
                });
            }
            let t = Typ::Tup { ets: binds };
            (Expr::Tup { span, items: new_items }, t)
        }
        Expr::Un { span, op, ty: _, e } => {
            let (e, t_in) = infer_exp(env, *e);
            let (op_ty, t_out) = infer_unop(&op, &t_in);
            (
                Expr::Un {
                    span,
                    op,
                    ty: op_ty,
                    e: Box::new(e),
                },
                t_out,
            )
        }
        Expr::Bin { span, op, ty: _, e1, e2 } => {
            let (e1, t1) = infer_exp(env, *e1);
            let (e2, t2) = infer_exp(env, *e2);
            let (op_ty, t_out) = infer_binop(&op, &t1, &t2);
            (
                Expr::Bin {
                    span,
                    op,
                    ty: op_ty,
                    e1: Box::new(e1),
                    e2: Box::new(e2),
                },
                t_out,
            )
        }
        Expr::Cmp { span, op, ty: _, e1, e2 } => {
            let (e1, t1) = infer_exp(env, *e1);
            let (e2, t2) = infer_exp(env, *e2);
            let op_ty = infer_cmpop(&op, &t1, &t2);
            (
                Expr::Cmp {
                    span,
                    op,
                    ty: op_ty,
                    e1: Box::new(e1),
                    e2: Box::new(e2),
                },
                Typ::Bool,
            )
        }
        Expr::Iter { span, inner, kind, bindings } => {
            let (inner, t_inner) = infer_exp(env, *inner);
            let it = match &kind {
                crate::elab::IterKind::Opt => spectec_ast::SpecTecIter::Opt,
                crate::elab::IterKind::Star => spectec_ast::SpecTecIter::List,
                crate::elab::IterKind::Plus => spectec_ast::SpecTecIter::List1,
                crate::elab::IterKind::Length(_) => spectec_ast::SpecTecIter::List, // approx
            };
            let t = Typ::Iter {
                t1: Box::new(t_inner),
                it: vec![it],
            };
            (
                Expr::Iter {
                    span,
                    inner: Box::new(inner),
                    kind,
                    bindings,
                },
                t,
            )
        }
        Expr::Case { span, head, args } => {
            // Recurse on args, but we don't yet look up the
            // constructor's signature so the result type is unknown.
            let new_args = args.into_iter().map(|a| infer_exp(env, a).0).collect();
            (
                Expr::Case {
                    span,
                    head,
                    args: new_args,
                },
                unknown_typ(),
            )
        }
        // For the rest, pass through and report `unknown` for now.
        // Subsequent slices add real inference per variant.
        other => (other, unknown_typ()),
    }
}

/// Pick the result type for a unary operator given its operand
/// type. Mirrors OCaml's `infer_unop env op t1`.
fn infer_unop(op: &UnOp, t_in: &Typ) -> (OpType, Typ) {
    match op {
        UnOp::Not => (OpType::Bool, Typ::Bool),
        UnOp::Plus | UnOp::Minus | UnOp::PlusMinus | UnOp::MinusPlus => {
            let op_ty = typ_to_optyp(t_in).unwrap_or(OpType::Nat);
            (op_ty.clone(), optyp_to_typ(&op_ty))
        }
    }
}

/// Pick the operator + result type for a binary operator. Numeric
/// operators promote to the wider operand type
/// (`nat < int < rat < real`); logical operators are always `Bool`.
fn infer_binop(op: &BinOp, t1: &Typ, t2: &Typ) -> (OpType, Typ) {
    match op {
        BinOp::And | BinOp::Or | BinOp::Impl | BinOp::Equiv => {
            (OpType::Bool, Typ::Bool)
        }
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod | BinOp::Pow => {
            let op_ty = join_numeric(t1, t2);
            let result = optyp_to_typ(&op_ty);
            (op_ty, result)
        }
    }
}

/// Pick the operator type for a comparison. Result is always `Bool`
/// — that's handled by the caller.
fn infer_cmpop(op: &CmpOp, t1: &Typ, t2: &Typ) -> OpType {
    match op {
        // Equality / inequality work for any type pair; we report
        // `Bool` (since the result is Bool) but OCaml records the
        // operand type. Compromise: pick the operand type for `Eq`
        // / `Ne` if it's a recognised optype, else `Bool`.
        CmpOp::Eq | CmpOp::Ne => typ_to_optyp(t1).or_else(|| typ_to_optyp(t2)).unwrap_or(OpType::Bool),
        CmpOp::Lt | CmpOp::Gt | CmpOp::Le | CmpOp::Ge => join_numeric(t1, t2),
    }
}

/// Promote two numeric types to the wider one. If either side is
/// unknown / non-numeric, fall back to the other side or `Nat`.
fn join_numeric(t1: &Typ, t2: &Typ) -> OpType {
    let a = typ_to_optyp(t1);
    let b = typ_to_optyp(t2);
    match (a, b) {
        (Some(a), Some(b)) => widen(a, b),
        (Some(a), None) | (None, Some(a)) => a,
        (None, None) => OpType::Nat,
    }
}

fn widen(a: OpType, b: OpType) -> OpType {
    let rank = |t: &OpType| -> u8 {
        match t {
            OpType::Bool => 0,
            OpType::Nat => 1,
            OpType::Int => 2,
            OpType::Rat => 3,
            OpType::Real => 4,
        }
    };
    if rank(&a) >= rank(&b) { a } else { b }
}

fn typ_to_optyp(t: &Typ) -> Option<OpType> {
    match t {
        Typ::Bool => Some(OpType::Bool),
        Typ::Num(spectec_ast::SpecTecNumTyp::Nat) => Some(OpType::Nat),
        Typ::Num(spectec_ast::SpecTecNumTyp::Int) => Some(OpType::Int),
        Typ::Num(spectec_ast::SpecTecNumTyp::Rat) => Some(OpType::Rat),
        Typ::Num(spectec_ast::SpecTecNumTyp::Real) => Some(OpType::Real),
        _ => None,
    }
}

fn optyp_to_typ(o: &OpType) -> Typ {
    match o {
        OpType::Bool => Typ::Bool,
        OpType::Nat => Typ::Num(spectec_ast::SpecTecNumTyp::Nat),
        OpType::Int => Typ::Num(spectec_ast::SpecTecNumTyp::Int),
        OpType::Rat => Typ::Num(spectec_ast::SpecTecNumTyp::Rat),
        OpType::Real => Typ::Num(spectec_ast::SpecTecNumTyp::Real),
    }
}

/// Bidirectional check: infer `e`'s type, return the refined `Expr`.
/// In a later slice this'll also insert `Sub` coercion if needed.
pub fn check_exp(env: &TypeEnv, e: Expr) -> Expr {
    let (e, _t) = infer_exp(env, e);
    e
}

/// Look up a metavariable's declared type. Strips trailing primes
/// and `_<subscript>` suffixes per SpecTec convention (so `C_1` and
/// `C''` both resolve to the type declared by `var C : ...`).
fn lookup_var(env: &TypeEnv, name: &str) -> Typ {
    let base = metavar_base(name);
    env.vars
        .get(base)
        .cloned()
        .unwrap_or_else(unknown_typ)
}

/// Same algorithm as [`elab::metavar_base`], duplicated here so this
/// module doesn't depend on a private item.
fn metavar_base(name: &str) -> &str {
    let mut end = name.len();
    while end > 0 && name.as_bytes()[end - 1] == b'\'' {
        end -= 1;
    }
    let trimmed = &name[..end];
    if let Some(us) = trimmed.rfind('_') {
        let suffix = &trimmed[us + 1..];
        let is_subscript = !suffix.is_empty()
            && suffix
                .bytes()
                .all(|b| b.is_ascii_digit() || b.is_ascii_lowercase());
        if is_subscript {
            return &trimmed[..us];
        }
    }
    trimmed
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

    #[test]
    fn infer_var_uses_var_env() {
        let src = r#"
            syntax t = nat
            var C : t
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let (_, t) = infer_exp(
            &env,
            Expr::Var {
                span,
                name: "C".to_string(),
            },
        );
        assert!(matches!(t, spectec_ast::SpecTecTyp::Var { x, .. } if x == "t"));
    }

    #[test]
    fn infer_var_strips_subscript_and_prime() {
        let src = r#"
            syntax t = nat
            var C : t
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        for name in &["C_1", "C_n", "C'", "C''", "C_n'"] {
            let (_, t) = infer_exp(
                &env,
                Expr::Var {
                    span,
                    name: name.to_string(),
                },
            );
            assert!(
                matches!(&t, spectec_ast::SpecTecTyp::Var { x, .. } if x == "t"),
                "var {name} should resolve to type `t`"
            );
        }
    }

    #[test]
    fn infer_num_picks_num_typ() {
        let env = TypeEnv::default();
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let (_, t) = infer_exp(
            &env,
            Expr::Num {
                span,
                value: crate::elab::NumLit::Nat(covalence_types::Nat::from(7u64)),
            },
        );
        assert!(matches!(
            t,
            spectec_ast::SpecTecTyp::Num(spectec_ast::SpecTecNumTyp::Nat)
        ));
    }

    #[test]
    fn infer_tup_composes_types() {
        let src = r#"
            syntax t = nat
            var C : t
            var x : nat
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let (_, t) = infer_exp(
            &env,
            Expr::Tup {
                span,
                items: vec![
                    Expr::Var { span, name: "C".to_string() },
                    Expr::Var { span, name: "x".to_string() },
                ],
            },
        );
        let spectec_ast::SpecTecTyp::Tup { ets } = t else {
            panic!("expected Tup");
        };
        assert_eq!(ets.len(), 2);
    }

    #[test]
    fn infer_bin_promotes_to_widest_numeric() {
        let env = TypeEnv::default();
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let nat = Expr::Num {
            span,
            value: crate::elab::NumLit::Nat(covalence_types::Nat::from(2u64)),
        };
        let int_expr = Expr::Num {
            span,
            value: crate::elab::NumLit::Int(covalence_types::Int::from(-1i64)),
        };
        let (e, t) = infer_exp(
            &env,
            Expr::Bin {
                span,
                op: BinOp::Add,
                ty: OpType::Nat,
                e1: Box::new(nat),
                e2: Box::new(int_expr),
            },
        );
        // Both operands typecheck; widening picks Int.
        let Expr::Bin { ty, .. } = e else { panic!() };
        assert!(matches!(ty, OpType::Int));
        assert!(matches!(
            t,
            Typ::Num(spectec_ast::SpecTecNumTyp::Int)
        ));
    }

    #[test]
    fn infer_cmp_returns_bool() {
        let env = TypeEnv::default();
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let lhs = Expr::Num {
            span,
            value: crate::elab::NumLit::Nat(covalence_types::Nat::from(1u64)),
        };
        let rhs = Expr::Num {
            span,
            value: crate::elab::NumLit::Nat(covalence_types::Nat::from(2u64)),
        };
        let (_, t) = infer_exp(
            &env,
            Expr::Cmp {
                span,
                op: CmpOp::Le,
                ty: OpType::Nat,
                e1: Box::new(lhs),
                e2: Box::new(rhs),
            },
        );
        assert!(matches!(t, Typ::Bool));
    }

    #[test]
    fn infer_un_not_returns_bool() {
        let env = TypeEnv::default();
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let (e, t) = infer_exp(
            &env,
            Expr::Un {
                span,
                op: UnOp::Not,
                ty: OpType::Nat, // wrong, should be refined to Bool
                e: Box::new(Expr::Bool { span, value: true }),
            },
        );
        let Expr::Un { ty, .. } = e else { panic!() };
        assert!(matches!(ty, OpType::Bool));
        assert!(matches!(t, Typ::Bool));
    }

    #[test]
    fn infer_logical_bin_is_bool() {
        let env = TypeEnv::default();
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let (e, t) = infer_exp(
            &env,
            Expr::Bin {
                span,
                op: BinOp::And,
                ty: OpType::Nat, // wrong, should be refined
                e1: Box::new(Expr::Bool { span, value: true }),
                e2: Box::new(Expr::Bool { span, value: false }),
            },
        );
        let Expr::Bin { ty, .. } = e else { panic!() };
        assert!(matches!(ty, OpType::Bool));
        assert!(matches!(t, Typ::Bool));
    }

    #[test]
    fn unknown_var_returns_placeholder() {
        let env = TypeEnv::default();
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        let (_, t) = infer_exp(
            &env,
            Expr::Var {
                span,
                name: "missing".to_string(),
            },
        );
        // Falls back to unknown_typ (currently SpecTecTyp::Bool).
        assert!(matches!(t, spectec_ast::SpecTecTyp::Bool));
    }
}
