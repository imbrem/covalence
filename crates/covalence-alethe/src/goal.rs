//! Goal → SMT problem translation — the *inverse* of
//! [`crate::hol::HolAletheBridge`]'s term reader.
//!
//! To discharge a HOL goal `⊢ G` via an Alethe refutation we must first
//! hand an SMT solver (or a cached proof's checker) the problem whose
//! UNSAT *is* `⊢ G`: the single assertion `¬G`. [`goal_to_problem`]
//! renders `¬G` back to SMT-LIB2 over the fragment the bridge understands
//! (QF_UF + the linear-integer term layer), collecting every free
//! variable as an uninterpreted `declare-fun` and every `tfree` type as a
//! `declare-sort`.
//!
//! The round-trip is deliberately *narrow*: it covers exactly the shapes
//! [`crate::hol`] can read back (so a refutation of the emitted `¬G`
//! always replays). A goal outside that fragment (binders, non-`int`
//! literals, derived-type operations) is rejected with a precise
//! [`BridgeError`] rather than mistranslated — never silently trusted.

use std::collections::BTreeMap;

use covalence_core::{Term, TermKind, Type, TypeKind, defs};
use covalence_sexp::{SExp, SExpr};
use covalence_smt::SmtProblem;
use covalence_types::Int;

use crate::error::BridgeError;

type R<T> = Result<T, BridgeError>;

/// Build the SMT problem whose UNSAT certifies `⊢ goal`: assert `¬goal`,
/// declaring every free symbol and sort it mentions.
///
/// The chosen logic is `QF_UF` unless any `Int`-typed subterm appears, in
/// which case `QF_UFLIA` (cvc5 accepts the superset for the pure-`Bool`
/// case too, but the tighter logic keeps the solver honest).
pub fn goal_to_problem(goal: &Term) -> R<SmtProblem> {
    // Reject non-`bool` goals up front — a refutation only makes sense for
    // a formula.
    let ty = goal.type_of()?;
    if !ty.is_bool() {
        return Err(BridgeError::Malformed(format!(
            "smt goal `{goal}` has type {ty}, not bool"
        )));
    }

    let mut ctx = Collect::default();
    let body = ctx.render(goal)?;
    let not_body = SExp::List(vec![SExp::symbol("not"), body]);

    let mut problem = SmtProblem::new();
    problem.set_logic(if ctx.uses_int { "QF_UFLIA" } else { "QF_UF" });
    // Sorts in deterministic (declaration) order.
    for name in &ctx.sort_order {
        problem.declare_sort(name.clone(), 0);
    }
    // Funs in deterministic (first-seen) order.
    for name in &ctx.fun_order {
        let (params, sort) = &ctx.funs[name];
        problem.declare_fun(name.clone(), params.clone(), sort.clone());
    }
    problem.assert_term(not_body);
    Ok(problem)
}

/// Accumulates declarations while rendering a term to SMT-LIB.
#[derive(Default)]
struct Collect {
    /// sort name → unit; `sort_order` keeps declaration order.
    sorts: BTreeMap<String, ()>,
    sort_order: Vec<String>,
    /// fun name → (param sorts, result sort); `fun_order` keeps order.
    funs: BTreeMap<String, (Vec<SExpr>, SExpr)>,
    fun_order: Vec<String>,
    uses_int: bool,
}

impl Collect {
    /// Render a `bool`/`int`/uninterpreted term to an SMT-LIB S-expression,
    /// collecting the sorts and funs it references.
    fn render(&mut self, t: &Term) -> R<SExpr> {
        // Equality `(= a b)`.
        if let Some((l, r)) = t.as_eq() {
            let ls = self.render(l)?;
            let rs = self.render(r)?;
            return Ok(SExp::List(vec![SExp::symbol("="), ls, rs]));
        }
        match t.kind() {
            TermKind::Bool(b) => Ok(SExp::symbol(if *b { "true" } else { "false" })),
            TermKind::Int(n) => Ok(int_lit_sexpr(n)),
            TermKind::Free(v) => {
                self.declare_fun_from_type(v.name(), v.ty())?;
                Ok(SExp::symbol(v.name()))
            }
            // A spec-headed application: a connective or an int operator.
            TermKind::App(..) => self.render_app(t),
            other => Err(BridgeError::NotImplemented(format!(
                "smt goal: unsupported term `{t}` ({})",
                kind_name(other)
            ))),
        }
    }

    /// Render an application spine `(head a₁ … aₙ)`, recognising the
    /// connectives and int operators the bridge reads back, else treating
    /// the head as an uninterpreted function.
    fn render_app(&mut self, t: &Term) -> R<SExpr> {
        // Decompose the full spine: head + argument list (left to right).
        let mut args_rev = Vec::new();
        let mut cur = t;
        while let Some((f, a)) = cur.as_app() {
            args_rev.push(a);
            cur = f;
        }
        let head = cur;
        let args: Vec<&Term> = args_rev.into_iter().rev().collect();

        // Recognised spec head?
        if let Some((spec, _)) = head.as_spec() {
            // Connectives.
            for (sym, sp) in [
                ("not", defs::not_spec()),
                ("and", defs::and_spec()),
                ("or", defs::or_spec()),
                ("=>", defs::imp_spec()),
            ] {
                if spec.ptr_eq(&sp) {
                    return self.render_op(sym, &args);
                }
            }
            // Integer operators (binary unless noted).
            for (sym, opf) in [
                ("+", defs::int_add as fn() -> Term),
                ("-", defs::int_sub as fn() -> Term),
                ("*", defs::int_mul as fn() -> Term),
                ("<", defs::int_lt as fn() -> Term),
                ("<=", defs::int_le as fn() -> Term),
            ] {
                if let Some((opspec, _)) = opf().as_spec() {
                    if spec.ptr_eq(opspec) {
                        self.uses_int = true;
                        return self.render_op(sym, &args);
                    }
                }
            }
            // Unary integer negation.
            if let Some((negspec, _)) = defs::int_neg().as_spec() {
                if spec.ptr_eq(negspec) {
                    self.uses_int = true;
                    return self.render_op("-", &args);
                }
            }
            return Err(BridgeError::NotImplemented(format!(
                "smt goal: unsupported spec head in `{t}`"
            )));
        }

        // Uninterpreted application: the head must be a free symbol.
        if let TermKind::Free(v) = head.kind() {
            self.declare_fun_from_type(v.name(), v.ty())?;
            let mut out = vec![SExp::symbol(v.name())];
            for a in &args {
                out.push(self.render(a)?);
            }
            return Ok(SExp::List(out));
        }

        Err(BridgeError::NotImplemented(format!(
            "smt goal: unsupported application head in `{t}`"
        )))
    }

    /// Render `(sym a₁ … aₙ)` over already-recognised operator `sym`.
    fn render_op(&mut self, sym: &str, args: &[&Term]) -> R<SExpr> {
        let mut out = vec![SExp::symbol(sym)];
        for a in args {
            out.push(self.render(a)?);
        }
        Ok(SExp::List(out))
    }

    /// Declare a free symbol `name : ty`, decomposing an arrow type into
    /// `(declare-fun name (params…) cod)`. Idempotent; records first-seen
    /// order. Also declares any `tfree` sorts the type mentions.
    fn declare_fun_from_type(&mut self, name: &str, ty: &Type) -> R<()> {
        if self.funs.contains_key(name) {
            return Ok(());
        }
        // Peel the arrow spine: param₀ → param₁ → … → cod.
        let mut params = Vec::new();
        let mut cur = ty.clone();
        while let TypeKind::Fun(dom, cod) = cur.kind() {
            params.push(self.sort_sexpr(dom)?);
            cur = cod.clone();
        }
        let cod = self.sort_sexpr(&cur)?;
        self.funs.insert(name.to_string(), (params, cod));
        self.fun_order.push(name.to_string());
        Ok(())
    }

    /// Render a non-arrow type to its SMT sort, declaring a `tfree` sort
    /// the first time it appears. Rejects arrow/derived types (a fun's
    /// *argument* must be a base sort in QF_UF).
    fn sort_sexpr(&mut self, ty: &Type) -> R<SExpr> {
        match ty.kind() {
            TypeKind::Bool => Ok(SExp::symbol("Bool")),
            _ if *ty == Type::int() => {
                self.uses_int = true;
                Ok(SExp::symbol("Int"))
            }
            TypeKind::TFree(name) => {
                if !self.sorts.contains_key(name.as_str()) {
                    self.sorts.insert(name.to_string(), ());
                    self.sort_order.push(name.to_string());
                }
                Ok(SExp::symbol(name.as_str()))
            }
            _ => Err(BridgeError::NotImplemented(format!(
                "smt goal: unsupported sort `{ty}`"
            ))),
        }
    }
}

/// Serialize an integer literal as an SMT-LIB term: non-negatives bare,
/// negatives as `(- n)` (SMT-LIB has no negative numerals).
fn int_lit_sexpr(n: &Int) -> SExpr {
    if n.is_negative() {
        // `n.abs()` is the magnitude as a `Nat`, displayed bare.
        SExp::List(vec![SExp::symbol("-"), SExp::symbol(n.abs().to_string())])
    } else {
        SExp::symbol(n.to_string())
    }
}

fn kind_name(k: &TermKind) -> &'static str {
    match k {
        TermKind::Bound(_) => "bound",
        TermKind::Free(..) => "free",
        TermKind::Const(..) => "const",
        TermKind::App(..) => "app",
        TermKind::Abs(..) => "abs",
        TermKind::Blob(_) => "blob",
        TermKind::Nat(_) => "nat",
        TermKind::Int(_) => "int",
        TermKind::SmallInt(_) => "smallint",
        TermKind::Bool(_) => "bool",
        TermKind::Eq(_) => "eq",
        TermKind::Select(_) => "select",
        TermKind::Succ => "succ",
        TermKind::Spec(..) => "spec",
        TermKind::SpecAbs(..) => "specabs",
        TermKind::SpecRep(..) => "specrep",
        TermKind::Obs(..) => "obs",
        TermKind::Def(_) => "def",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol::HolLightCtx;

    #[test]
    fn renders_uf_goal() {
        // Goal: `p a` with `a : U`, `p : U → Bool`.
        let u = Type::tfree("U");
        let a = Term::free("a", u.clone());
        let p = Term::free("p", Type::fun(u.clone(), Type::bool()));
        let goal = Term::app(p, a);
        let problem = goal_to_problem(&goal).expect("translate");
        assert_eq!(problem.logic(), Some("QF_UF"));
        // U declared as a sort; a and p declared as funs.
        assert!(problem.sorts().iter().any(|s| s.name == "U"));
        assert!(problem.funs().iter().any(|f| f.name == "a"));
        assert!(problem.funs().iter().any(|f| f.name == "p"));
        // The assertion is `(not (p a))`.
        let assertion = &problem.assertions()[0];
        let list = assertion.as_list().unwrap();
        assert_eq!(list[0].as_symbol(), Some("not"));
    }

    #[test]
    fn renders_lia_goal() {
        // Goal: `(< x 0) ⟹ (< x 1)` — uses Int, picks QF_UFLIA.
        let int = Type::int();
        let x = Term::free("x", int.clone());
        let lt = |a: Term, b: Term| Term::app(Term::app(defs::int_lt(), a), b);
        let ctx = HolLightCtx::new();
        let goal = ctx.mk_imp(
            lt(x.clone(), Term::int_lit(0)),
            lt(x, Term::int_lit(1)),
        );
        let problem = goal_to_problem(&goal).expect("translate");
        assert_eq!(problem.logic(), Some("QF_UFLIA"));
        assert!(problem.funs().iter().any(|f| f.name == "x"));
    }

    #[test]
    fn rejects_non_bool_goal() {
        let goal = Term::int_lit(3);
        assert!(goal_to_problem(&goal).is_err());
    }
}
