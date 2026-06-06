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

use spectec_ast as ast;

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
    pub vars: BTreeMap<String, ast::SpecTecTyp>,
    /// `relation NAME: ...` operand-tuple types, by relation name.
    pub relations: BTreeMap<String, ast::SpecTecTyp>,
    /// `def $NAME(args) : T` return types, by def name.
    pub defs: BTreeMap<String, DefSig>,
    /// `grammar NAME : T` yield types, by grammar name.
    pub grammars: BTreeMap<String, ast::SpecTecTyp>,
    /// Case constructor → containing syntax type, by constructor
    /// head name. For `syntax instr = | BLOCK ... | NOP ...`, maps
    /// `"BLOCK"`/`"NOP"` to `SpecTecTyp::Var { x: "instr", as1: [] }`.
    /// Duplicates (same head in multiple syntax defs) are resolved
    /// by first-seen wins.
    pub ctors: BTreeMap<String, ast::SpecTecTyp>,
    /// Variant subtype map (transitive). Each `T1 → {T2 names}`
    /// captures every type T1 is a subtype of via being one of T2's
    /// variant alternatives. E.g. for
    /// `syntax valtype = | numtype | reftype`, the map records
    /// `numtype → {valtype}` and `reftype → {valtype}` (plus any
    /// further outer types via transitivity).
    pub subtypes: BTreeMap<String, std::collections::BTreeSet<String>>,
}

#[derive(Debug, Clone)]
pub struct DefSig {
    pub params: Vec<ast::SpecTecParam>,
    pub ret: ast::SpecTecTyp,
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
        let params: Vec<ast::SpecTecParam> = d
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

    // Constructors AND variant subtypes: walk each merged syntax's
    // variant alts; case-headed alts register ctors, type-name alts
    // (`| numtype`) register subtype edges.
    let mut direct_sub: BTreeMap<String, std::collections::BTreeSet<String>> = BTreeMap::new();
    for syn in &doc.syntax {
        for prof in &syn.merged.profiles {
            if let Some(crate::cst::SyntaxBody::Variant(_)) = &prof.body {
                let alts = syn.merged.alts_for_profile(prof.profile.as_deref());
                for alt in &alts {
                    let toks = &alt.body.tokens;
                    let Some(crate::token::Spanned {
                        token: crate::token::Token::Ident(head),
                        ..
                    }) = toks.first()
                    else {
                        continue;
                    };
                    if is_case_head_str(head) {
                        env.ctors.entry(head.clone()).or_insert_with(|| Typ::Var {
                            x: syn.name.clone(),
                            as1: Vec::new(),
                        });
                    } else if toks.len() == 1 && ctx.type_names.contains(head) {
                        // Type-inclusion alt: head is the only token
                        // and it's a declared type → `head <: syn.name`.
                        direct_sub
                            .entry(head.clone())
                            .or_default()
                            .insert(syn.name.clone());
                    }
                }
            }
        }
    }

    // Transitive closure of `direct_sub`. Floyd-Warshall style.
    let mut closed = direct_sub.clone();
    loop {
        let mut grew = false;
        let snapshot = closed.clone();
        for (a, bs) in &snapshot {
            for b in bs {
                if let Some(b_subs) = snapshot.get(b) {
                    let entry = closed.entry(a.clone()).or_default();
                    for c in b_subs {
                        if entry.insert(c.clone()) {
                            grew = true;
                        }
                    }
                }
            }
        }
        if !grew {
            break;
        }
    }
    env.subtypes = closed;

    env
}

/// Match the heuristic in `elab::is_case_head`. Duplicated here so
/// `typecheck` doesn't depend on a private item.
fn is_case_head_str(name: &str) -> bool {
    if name.len() < 2 {
        return false;
    }
    let first = name.bytes().next().unwrap();
    if !(first.is_ascii_uppercase() || first == b'_') {
        return false;
    }
    let mut saw_letter = false;
    for b in name.bytes() {
        if b.is_ascii_alphabetic() {
            saw_letter = true;
            if b.is_ascii_lowercase() {
                return false;
            }
        }
    }
    saw_letter
}

/// Convenience alias for the type we use internally — directly the
/// `spectec_ast` form so the converter doesn't need any further
/// translation.
pub type Typ = ast::SpecTecTyp;

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
    use ast::SpecTecNumTyp;
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
                it: vec![ast::SpecTecIter::List],
            },
        ),
        Expr::Tup { span, items } => {
            let mut new_items = Vec::with_capacity(items.len());
            let mut binds = Vec::with_capacity(items.len());
            for item in items {
                let (item, t) = infer_exp(env, item);
                new_items.push(item);
                binds.push(ast::SpecTecTypBind::Bind {
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
                crate::elab::IterKind::Opt => ast::SpecTecIter::Opt,
                crate::elab::IterKind::Star => ast::SpecTecIter::List,
                crate::elab::IterKind::Plus => ast::SpecTecIter::List1,
                crate::elab::IterKind::Length(_) => ast::SpecTecIter::List, // approx
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
            let new_args = args.into_iter().map(|a| infer_exp(env, a).0).collect();
            let t = env.ctors.get(&head).cloned().unwrap_or_else(unknown_typ);
            (
                Expr::Case {
                    span,
                    head,
                    args: new_args,
                },
                t,
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
        Typ::Num(ast::SpecTecNumTyp::Nat) => Some(OpType::Nat),
        Typ::Num(ast::SpecTecNumTyp::Int) => Some(OpType::Int),
        Typ::Num(ast::SpecTecNumTyp::Rat) => Some(OpType::Rat),
        Typ::Num(ast::SpecTecNumTyp::Real) => Some(OpType::Real),
        _ => None,
    }
}

fn optyp_to_typ(o: &OpType) -> Typ {
    match o {
        OpType::Bool => Typ::Bool,
        OpType::Nat => Typ::Num(ast::SpecTecNumTyp::Nat),
        OpType::Int => Typ::Num(ast::SpecTecNumTyp::Int),
        OpType::Rat => Typ::Num(ast::SpecTecNumTyp::Rat),
        OpType::Real => Typ::Num(ast::SpecTecNumTyp::Real),
    }
}

/// Bidirectional check (no expected type): infer `e`'s type, return
/// the refined `Expr`. Use [`check_exp_against`] when you know the
/// position's expected type and want `Sub` coercion inserted on
/// subtype mismatch.
pub fn check_exp(env: &TypeEnv, e: Expr) -> Expr {
    let (e, _t) = infer_exp(env, e);
    e
}

/// Bidirectional check (with expected type): infer `e`'s type, then
/// either return `e` unchanged (when its type equiv-`expected`) or
/// wrap it in `Expr::Sub` (when `actual <: expected` but not
/// equivalent). Mirrors OCaml's `elab_exp env e expected_t`.
pub fn check_exp_against(env: &TypeEnv, e: Expr, expected: &Typ) -> Expr {
    let (e, actual) = infer_exp(env, e);
    let span = e.span();
    if is_unknown(&actual) || equiv_typ(&actual, expected) {
        return e;
    }
    if sub_typ(env, &actual, expected) {
        Expr::Sub {
            span,
            from_ty: actual,
            to_ty: expected.clone(),
            e: Box::new(e),
        }
    } else {
        // No subtype relation — return as-is (no coercion). A real
        // typechecker would diagnose; we stay lenient to keep the
        // pipeline producing output on the corpus.
        e
    }
}

/// `Typ::Bool` is the sentinel `unknown_typ` returns. Treat it as
/// "no information" for subtype-coercion purposes — otherwise every
/// unresolved `Var` would trigger a Bool-to-something coercion.
fn is_unknown(t: &Typ) -> bool {
    matches!(t, Typ::Bool)
}

/// Type equivalence. Mirrors OCaml's `equiv_typ`.
///
/// Currently structural equality. SpecTec has additional rules
/// (e.g. expanding type aliases) — those would land here when we
/// model type-alias unfolding.
pub fn equiv_typ(t1: &Typ, t2: &Typ) -> bool {
    t1 == t2
}

/// Subtype check. Mirrors OCaml's `sub_typ`.
///
/// Rules:
/// - reflexivity: `T <: T`
/// - numeric promotion: `Nat <: Int <: Rat <: Real`
/// - singleton lifts: `T <: T?`, `T <: T*`, `T <: T+`
/// - iteration lifts: `T+ <: T*` (a nonempty list is a list) and
///   `T <: T?` etc. extended to wrapping
/// - iteration covariance: `Iter T <: Iter T'` when `T <: T'` (same
///   iter)
///
/// Variant subtyping (`syntax a/syn = | numtype | reftype` lifting
/// `numtype <: a`) is left for the next slice once we thread the
/// `MergedSyntax` info through.
pub fn sub_typ(env: &TypeEnv, t1: &Typ, t2: &Typ) -> bool {
    if equiv_typ(t1, t2) {
        return true;
    }
    match (t1, t2) {
        // Numeric promotion.
        (Typ::Num(a), Typ::Num(b)) => num_promotes(a, b),
        // Variant subtype: `numtype <: valtype` etc., looked up in
        // the precomputed transitive-closure subtype map.
        (Typ::Var { x: a, .. }, Typ::Var { x: b, .. }) => env
            .subtypes
            .get(a)
            .is_some_and(|s| s.contains(b)),
        // T+ <: T* — a nonempty list is a list. Also T+ <: T?+ etc.
        // (any wider iter shape).
        (
            Typ::Iter { t1: t1_inner, it: it1 },
            Typ::Iter { t1: t2_inner, it: it2 },
        ) if it1.len() == 1 && it2.len() == 1 => {
            iter_widens(&it1[0], &it2[0]) && sub_typ(env, t1_inner, t2_inner)
        }
        // Singleton T lifts to T?, T*, T+ (when iter rank matches).
        (_, Typ::Iter { t1: t2_inner, it }) if it.len() == 1 => {
            matches!(
                it[0],
                ast::SpecTecIter::Opt | ast::SpecTecIter::List | ast::SpecTecIter::List1
            ) && sub_typ(env, t1, t2_inner)
        }
        _ => false,
    }
}

/// `iter_widens(from, to)`: when can a `from`-shaped iteration be
/// promoted to a `to`-shaped one? Currently `List1 <: List` (T+ <:
/// T*); other shapes only relate to themselves.
fn iter_widens(from: &ast::SpecTecIter, to: &ast::SpecTecIter) -> bool {
    use ast::SpecTecIter::*;
    match (from, to) {
        (a, b) if a == b => true,
        (List1, List) => true, // T+ <: T*
        _ => false,
    }
}

fn num_promotes(from: &ast::SpecTecNumTyp, to: &ast::SpecTecNumTyp) -> bool {
    use ast::SpecTecNumTyp::*;
    let rank = |t: &ast::SpecTecNumTyp| -> u8 {
        match t {
            Nat => 0,
            Int => 1,
            Rat => 2,
            Real => 3,
        }
    };
    rank(from) <= rank(to)
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

/// Type-check a premise. For `Rule { rel_name, operands }` premises,
/// each operand is checked against the corresponding hole-type of
/// the cited relation, inserting `Sub` coercions as needed.
pub fn check_premise(env: &TypeEnv, p: ElabPremise) -> ElabPremise {
    match p {
        ElabPremise::Rule {
            rel_name,
            op,
            operands,
        } => {
            // Look up the relation's operand-tuple type and check each
            // operand against the matching slot.
            let expected = env
                .relations
                .get(&rel_name)
                .map(extract_tup_types)
                .unwrap_or_default();
            let typed_operands: Vec<Expr> = operands
                .into_iter()
                .enumerate()
                .map(|(i, o)| match expected.get(i) {
                    Some(t) => check_exp_against(env, o, t),
                    None => check_exp(env, o),
                })
                .collect();
            ElabPremise::Rule {
                rel_name,
                op,
                operands: typed_operands,
            }
        }
        ElabPremise::If(e) => ElabPremise::If(check_exp_against(env, e, &Typ::Bool)),
        ElabPremise::Let { lhs, rhs } => ElabPremise::Let {
            // Symmetric: infer rhs, check lhs against rhs's type
            // (so pattern variables get the right type). Simplified
            // for now: check both, don't unify.
            lhs: check_exp(env, lhs),
            rhs: check_exp(env, rhs),
        },
        ElabPremise::Else => ElabPremise::Else,
        ElabPremise::Iter {
            inner,
            kind,
            bindings,
        } => ElabPremise::Iter {
            inner: Box::new(check_premise(env, *inner)),
            kind,
            bindings,
        },
        ElabPremise::Raw(tr) => ElabPremise::Raw(tr),
    }
}

/// Extract per-operand types from a `Tup` typ (or a single bare type
/// as a one-element vec). Same logic as `ast_doc::extract_tup_element_types`
/// but lives here to avoid a cross-module call cycle.
fn extract_tup_types(t: &Typ) -> Vec<Typ> {
    match t {
        Typ::Tup { ets } => ets
            .iter()
            .map(|b| {
                let ast::SpecTecTypBind::Bind { typ, .. } = b;
                typ.clone()
            })
            .collect(),
        other => vec![other.clone()],
    }
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
        assert!(matches!(r, ast::SpecTecTyp::Tup { ets } if ets.len() == 3));
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
        assert!(matches!(sig.ret, ast::SpecTecTyp::Num(_)));
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
        assert!(matches!(t, ast::SpecTecTyp::Var { x, .. } if x == "t"));
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
                matches!(&t, ast::SpecTecTyp::Var { x, .. } if x == "t"),
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
            ast::SpecTecTyp::Num(ast::SpecTecNumTyp::Nat)
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
        let ast::SpecTecTyp::Tup { ets } = t else {
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
            Typ::Num(ast::SpecTecNumTyp::Int)
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
    fn variant_subtype_recorded() {
        let src = r#"
            syntax numtype = | I32 | I64
            syntax reftype = nat
            syntax valtype = | numtype | reftype
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        let numtype = Typ::Var { x: "numtype".into(), as1: vec![] };
        let valtype = Typ::Var { x: "valtype".into(), as1: vec![] };
        assert!(sub_typ(&env, &numtype, &valtype));
        assert!(sub_typ(&env, &Typ::Var { x: "reftype".into(), as1: vec![] }, &valtype));
        // Reverse direction not a subtype.
        assert!(!sub_typ(&env, &valtype, &numtype));
    }

    #[test]
    fn variant_subtype_transitive() {
        let src = r#"
            syntax inner = | A
            syntax middle = | inner | B
            syntax outer = | middle | C
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        let inner = Typ::Var { x: "inner".into(), as1: vec![] };
        let outer = Typ::Var { x: "outer".into(), as1: vec![] };
        assert!(sub_typ(&env, &inner, &outer));
    }

    #[test]
    fn t_plus_lifts_to_t_star() {
        let env = TypeEnv::default();
        let t = Typ::Num(ast::SpecTecNumTyp::Nat);
        let plus = Typ::Iter {
            t1: Box::new(t.clone()),
            it: vec![ast::SpecTecIter::List1],
        };
        let star = Typ::Iter {
            t1: Box::new(t),
            it: vec![ast::SpecTecIter::List],
        };
        assert!(sub_typ(&env, &plus, &star));
        // T* doesn't lift to T+ (a possibly-empty list isn't a
        // nonempty list).
        assert!(!sub_typ(&env, &star, &plus));
    }

    #[test]
    fn check_exp_against_inserts_sub() {
        let src = r#"
            syntax numtype = | I32 | I64
            syntax reftype = nat
            syntax valtype = | numtype | reftype
        "#;
        let (doc, ctx) = build(src);
        let env = build_env(&doc, &ctx);
        let span = crate::source::Span::new(crate::source::FileId::new(0), 0, 0);
        // Pass I32 (numtype) where valtype expected.
        let e = Expr::Case {
            span,
            head: "I32".into(),
            args: vec![],
        };
        let expected = Typ::Var { x: "valtype".into(), as1: vec![] };
        let result = check_exp_against(&env, e, &expected);
        let Expr::Sub { from_ty, to_ty, .. } = &result else {
            panic!("expected Sub, got {result:?}");
        };
        assert!(matches!(from_ty, Typ::Var { x, .. } if x == "numtype"));
        assert!(matches!(to_ty, Typ::Var { x, .. } if x == "valtype"));
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
        assert!(matches!(t, ast::SpecTecTyp::Bool));
    }
}
