//! **SpecTec expression → real typed HOL term** (leg B, the denotational leg).
//!
//! Where [`super::encode`] maps a `SpecTecExp` to an *uninterpreted* `nat`
//! algebra (syntactic; for `Derivable_R`), this renders it to a **genuine typed
//! HOL term over the [`crate::init`] catalogue** — SpecTec `1 + 2` becomes
//! `nat.add 1 2 : nat`, `(a, b)` a real `prod` pair, `[x, y]` a real `list`. This
//! is the "explicit HOL terms" half of the mirror: `SpecTec ⟶ HOL` directly, so
//! its result can be *computed with* and *reasoned about* in the kernel, and can
//! be cross-checked against leg A (Phase F).
//!
//! ## Scope (first slice: the value fragment)
//!
//! Closed value expressions over the catalogue: booleans, `nat`/`int` literals
//! and arithmetic/comparison (dispatched on the SpecTec operator *type*
//! annotation), tuples (→ right-nested `prod` pairs), non-empty lists, `some`,
//! and metavariables resolved through a caller-supplied type environment. This is
//! what SpecTec **functions** (`Dec`) and **side conditions** (`if`/`let`
//! premises) are built from — the foundation leg B needs before it can give those
//! meaning.
//!
//! Constructs needing types the catalogue doesn't yet have — SpecTec **variant**
//! types (`valtype`, `instr`, …) as real HOL datatypes, records, empty
//! collections without an element-type annotation — return a typed error until
//! the `Typ` → datatype layer (`wasm/syntax.rs`) lands. See `SKELETONS.md`.
//!
//! Unlike [`super::encode`], this is **not** total and **not** collision-free by
//! construction; it is an ordinary (untrusted) term builder, and the kernel
//! type-checks everything it produces.

use std::collections::BTreeMap;

use covalence_core::{Error, Result, Term, Type};
use covalence_spectec::ast::{
    SpecTecBinOp, SpecTecCmpOp, SpecTecExp, SpecTecNum, SpecTecNumTyp, SpecTecOpTyp, SpecTecUnOp,
};

use crate::init::ext::TermExt;
use crate::init::{int, list, nat};

/// A metavariable → HOL type environment (SpecTec variables carry no HOL type at
/// their use sites, so the caller supplies them).
pub type TypeEnv = BTreeMap<String, Type>;

fn denote_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("spectec denote: {}", msg.into()))
}

/// `f a b` — apply a curried binary catalogue constant.
fn apply2(f: Term, a: Term, b: Term) -> Result<Term> {
    f.apply(a)?.apply(b)
}

/// Render a closed value expression to a real typed HOL term over the catalogue.
/// `env` gives the HOL type of each free SpecTec metavariable.
pub fn denote(e: &SpecTecExp, env: &TypeEnv) -> Result<Term> {
    use SpecTecExp as E;
    match e {
        E::Bool { b } => Ok(Term::bool_lit(*b)),
        E::Num { n } => denote_num(n),
        E::Var { id } => match env.get(id) {
            Some(ty) => Ok(Term::free(id.clone(), ty.clone())),
            None => Err(denote_err(format!(
                "free metavariable `{id}` has no type in env"
            ))),
        },
        E::Bin { op, t, e1, e2 } => denote_bin(op, t, denote(e1, env)?, denote(e2, env)?),
        E::Cmp { op, t, e1, e2 } => denote_cmp(op, t, denote(e1, env)?, denote(e2, env)?),
        E::Un { op, e2, .. } => denote_un(op, denote(e2, env)?),
        E::Tup { es } => denote_tuple(es, env),
        E::List { es } => denote_list(es, env),
        E::Opt { eo } => match eo {
            Some(inner) => {
                let x = denote(inner, env)?;
                let ty = x.type_of()?;
                crate::init::option::some(ty).apply(x)
            }
            None => Err(denote_err(
                "empty option has no element type (needs a type annotation)",
            )),
        },
        _ => Err(denote_err(
            "constructor not in the value fragment yet (needs the datatype/function leg)",
        )),
    }
}

fn denote_num(n: &SpecTecNum) -> Result<Term> {
    match n {
        SpecTecNum::Nat(u) => Ok(Term::nat_lit(*u)),
        SpecTecNum::Int(i) => Ok(Term::int_lit(*i as i128)),
        SpecTecNum::Rat(_) | SpecTecNum::Real(_) => Err(denote_err(
            "rat/real literals not in the value fragment yet",
        )),
    }
}

/// The numeric type of an operator annotation, or `None` for `bool`.
fn numtype(t: &SpecTecOpTyp) -> Option<&SpecTecNumTyp> {
    match t {
        SpecTecOpTyp::Num(nt) => Some(nt),
        SpecTecOpTyp::Bool(_) => None,
    }
}

fn denote_bin(op: &SpecTecBinOp, t: &SpecTecOpTyp, a: Term, b: Term) -> Result<Term> {
    use SpecTecBinOp as B;
    // Logical connectives (bool-typed) go through the connective builders.
    match op {
        B::And => return a.and(b),
        B::Or => return a.or(b),
        B::Impl => return a.imp(b),
        B::Equiv => return a.iff(b),
        _ => {}
    }
    // Arithmetic: dispatch on the numeric operator type.
    let f = match (numtype(t), op) {
        (Some(SpecTecNumTyp::Nat), B::Add) => nat::nat_add(),
        (Some(SpecTecNumTyp::Nat), B::Sub) => nat::nat_sub(),
        (Some(SpecTecNumTyp::Nat), B::Mul) => nat::nat_mul(),
        (Some(SpecTecNumTyp::Nat), B::Div) => nat::nat_div(),
        (Some(SpecTecNumTyp::Nat), B::Mod) => nat::nat_mod(),
        (Some(SpecTecNumTyp::Int), B::Add) => int::int_add(),
        (Some(SpecTecNumTyp::Int), B::Sub) => int::int_sub(),
        (Some(SpecTecNumTyp::Int), B::Mul) => int::int_mul(),
        (Some(SpecTecNumTyp::Int), B::Div) => int::int_div(),
        (Some(SpecTecNumTyp::Int), B::Mod) => int::int_mod(),
        _ => {
            return Err(denote_err(format!(
                "binary op {op:?} at type {t:?} not in the value fragment yet"
            )));
        }
    };
    apply2(f, a, b)
}

fn denote_cmp(op: &SpecTecCmpOp, t: &SpecTecOpTyp, a: Term, b: Term) -> Result<Term> {
    use SpecTecCmpOp as C;
    match op {
        // Equality is generic (both sides already same type).
        C::Eq => return a.equals(b),
        C::Ne => return a.equals(b)?.not(),
        _ => {}
    }
    // Ordering: pick the (nat|int) constant and orient Gt/Ge by swapping.
    let nt = numtype(t).ok_or_else(|| denote_err("ordering compare on a non-numeric type"))?;
    let (lt, le) = match nt {
        SpecTecNumTyp::Nat => (nat::nat_lt(), nat::nat_le()),
        SpecTecNumTyp::Int => (int::int_lt(), int::int_le()),
        _ => {
            return Err(denote_err(format!(
                "ordering at {nt:?} not in the value fragment yet"
            )));
        }
    };
    match op {
        C::Lt => apply2(lt, a, b),
        C::Le => apply2(le, a, b),
        C::Gt => apply2(lt, b, a),
        C::Ge => apply2(le, b, a),
        C::Eq | C::Ne => unreachable!(),
    }
}

fn denote_un(op: &SpecTecUnOp, a: Term) -> Result<Term> {
    match op {
        SpecTecUnOp::Not => a.not(),
        SpecTecUnOp::Plus => Ok(a),
        SpecTecUnOp::Minus => int::int_neg().apply(a),
        other => Err(denote_err(format!(
            "unary op {other:?} not in the value fragment yet"
        ))),
    }
}

/// A tuple `(e₀, …, eₙ)` → right-nested `prod` pairs `pair e₀ (pair e₁ …)`.
fn denote_tuple(es: &[SpecTecExp], env: &TypeEnv) -> Result<Term> {
    match es {
        [] => Err(denote_err("empty tuple has no type")),
        [single] => denote(single, env),
        [head, rest @ ..] => {
            let a = denote(head, env)?;
            let b = denote_tuple(rest, env)?;
            let (ta, tb) = (a.type_of()?, b.type_of()?);
            apply2(crate::init::prod::pair(ta, tb), a, b)
        }
    }
}

/// A list `[e₀, …, eₙ]` → a real `list` value (element type from the first
/// element; the empty list needs an annotation we don't have here).
fn denote_list(es: &[SpecTecExp], env: &TypeEnv) -> Result<Term> {
    if es.is_empty() {
        return Err(denote_err(
            "empty list has no element type (needs an annotation)",
        ));
    }
    let elems = es
        .iter()
        .map(|e| denote(e, env))
        .collect::<Result<Vec<_>>>()?;
    let elem_ty = elems[0].type_of()?;
    list::list_of(&elem_ty, elems)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat_op_ty() -> SpecTecOpTyp {
        SpecTecOpTyp::Num(SpecTecNumTyp::Nat)
    }
    fn num(u: u64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Nat(u),
        }
    }
    fn empty() -> TypeEnv {
        TypeEnv::new()
    }

    #[test]
    fn nat_arithmetic_is_real_typed_hol() {
        // 1 + 2 : nat
        let e = SpecTecExp::Bin {
            op: SpecTecBinOp::Add,
            t: nat_op_ty(),
            e1: Box::new(num(1)),
            e2: Box::new(num(2)),
        };
        let t = denote(&e, &empty()).unwrap();
        assert_eq!(t.type_of().unwrap(), Type::nat());
    }

    /// The denotation is not just well-typed — it is genuinely *computable* HOL:
    /// the kernel reduces `⌜1 + 2⌝ = nat.add 1 2` to `3`. This is the payoff of
    /// leg B over leg A's uninterpreted `nat` algebra: real terms you can evaluate
    /// and reason about.
    #[test]
    fn denotation_is_computable() {
        use crate::init::ext::TermExt;
        let e = SpecTecExp::Bin {
            op: SpecTecBinOp::Add,
            t: nat_op_ty(),
            e1: Box::new(num(1)),
            e2: Box::new(num(2)),
        };
        let t = denote(&e, &empty()).unwrap();
        let thm = t.reduce().unwrap(); // ⊢ nat.add 1 2 = <nf>
        let rhs = thm.concl().as_eq().expect("an equation").1.clone();
        assert_eq!(rhs, Term::nat_lit(3u32));
    }

    #[test]
    fn comparison_is_bool_typed() {
        // 1 < 2 : bool
        let e = SpecTecExp::Cmp {
            op: SpecTecCmpOp::Lt,
            t: nat_op_ty(),
            e1: Box::new(num(1)),
            e2: Box::new(num(2)),
        };
        let t = denote(&e, &empty()).unwrap();
        assert_eq!(t.type_of().unwrap(), Type::bool());
    }

    #[test]
    fn logical_connective_is_bool() {
        let e = SpecTecExp::Bin {
            op: SpecTecBinOp::And,
            t: SpecTecOpTyp::Bool(covalence_spectec::ast::SpecTecBoolTyp::Bool),
            e1: Box::new(SpecTecExp::Bool { b: true }),
            e2: Box::new(SpecTecExp::Bool { b: false }),
        };
        let t = denote(&e, &empty()).unwrap();
        assert_eq!(t.type_of().unwrap(), Type::bool());
    }

    #[test]
    fn tuple_is_a_prod_pair() {
        // (1, 2) : prod nat nat
        let e = SpecTecExp::Tup {
            es: vec![num(1), num(2)],
        };
        let t = denote(&e, &empty()).unwrap();
        // well-typed and not a bare nat.
        let ty = t.type_of().unwrap();
        assert_ne!(ty, Type::nat());
    }

    #[test]
    fn nonempty_list_is_a_real_list() {
        let e = SpecTecExp::List {
            es: vec![num(1), num(2), num(3)],
        };
        let t = denote(&e, &empty()).unwrap();
        assert!(t.type_of().is_ok());
    }

    #[test]
    fn metavariable_resolves_through_env() {
        let mut env = empty();
        env.insert("x".into(), Type::nat());
        let e = SpecTecExp::Bin {
            op: SpecTecBinOp::Add,
            t: nat_op_ty(),
            e1: Box::new(SpecTecExp::Var { id: "x".into() }),
            e2: Box::new(num(1)),
        };
        let t = denote(&e, &env).unwrap();
        assert_eq!(t.type_of().unwrap(), Type::nat());
    }

    #[test]
    fn free_metavariable_without_env_errors() {
        let e = SpecTecExp::Var { id: "y".into() };
        assert!(denote(&e, &empty()).is_err());
    }
}
