//! **Side-condition discharge** — the sound, reusable core for lowering
//! `if`/`let` premises of SpecTec relation rules (the "mirror principle" for
//! ground instances).
//!
//! A rule like `Step_read/memory.fill-zero` fires only *when* a side condition
//! holds (`n = 0`). The relation engine's *judgement* encoding
//! ([`crate::wasm::encode`]) is uninterpreted (`Φ=nat` free algebra,
//! substitution = `all_elim`, no computation), but a side condition needs *real*
//! arithmetic, which lives in the *denotational* leg ([`crate::wasm::denote`]).
//! This module bridges them for a **ground** instance: given the condition
//! expression and concrete value-fragment bindings for its metavariables, it
//! *denotes* the closed condition and discharges it by kernel computation
//! ([`prove_true`](crate::init::ext::TermExt::prove_true)) — a real, oracle-free
//! `⊢ cond` theorem.
//!
//! **Soundness:** the discharge is a *decision procedure*, not a source of
//! judgements. It proves `⊢ cond` iff the closed condition reduces to `⌜T⌝`; a
//! false or non-computable condition fails. So it can only *refuse* to admit a
//! rule instance, never fabricate one — matching the front end's
//! faithfulness-not-soundness contract.
//!
//! **Scope (value fragment):** conditions over `Bool`/`Num`/`Var`/`Cmp`/`Bin`/`Un`
//! only. The flagship branch rules (`select`/`if`/`br_if`, condition
//! `Proj(Uncase c) ≠ 0`) need `Uncase`/`Proj` — the datatype/`Dec` leg — and are
//! out of scope here; see `notes/vibes/logics/spectec-fragment-api.md`.

use std::collections::BTreeMap;

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::mk_bool;
use covalence_spectec::ast::SpecTecExp;

use crate::init::ext::{TermExt, ThmExt};
use crate::wasm::denote::{DenoteCtx, TypeEnv, denote};

/// Whether `e` is in the value fragment this module can denote-and-decide:
/// booleans, numeric literals, metavariables, comparisons, arithmetic, and
/// unary ops — and nothing needing the datatype/function leg (`Uncase`, `Proj`,
/// `Call`, `Case`, iteration, …).
pub fn is_value_fragment(e: &SpecTecExp) -> bool {
    use SpecTecExp::*;
    match e {
        Bool { .. } | Num { .. } | Var { .. } => true,
        Un { e2, .. } => is_value_fragment(e2),
        Bin { e1, e2, .. } | Cmp { e1, e2, .. } => is_value_fragment(e1) && is_value_fragment(e2),
        _ => false,
    }
}

/// Substitute value-fragment `binds` (metavariable id → concrete expression)
/// through the value fragment of `e`.
fn subst(e: &SpecTecExp, binds: &BTreeMap<String, SpecTecExp>) -> SpecTecExp {
    use SpecTecExp::*;
    match e {
        Var { id } => binds.get(id).cloned().unwrap_or_else(|| e.clone()),
        Un { op, t, e2 } => Un {
            op: op.clone(),
            t: t.clone(),
            e2: Box::new(subst(e2, binds)),
        },
        Bin { op, t, e1, e2 } => Bin {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(subst(e1, binds)),
            e2: Box::new(subst(e2, binds)),
        },
        Cmp { op, t, e1, e2 } => Cmp {
            op: op.clone(),
            t: t.clone(),
            e1: Box::new(subst(e1, binds)),
            e2: Box::new(subst(e2, binds)),
        },
        _ => e.clone(),
    }
}

/// Prove `⊢ cond` for a value-fragment side condition whose metavariables are
/// bound to concrete value-fragment expressions by `binds`.
///
/// Errors if `cond` (or any binding) is outside the value fragment, if it does
/// not denote, or if it does not reduce to `⌜T⌝` (the condition is false for
/// these values — the instance is correctly refused).
pub fn prove_side_condition(
    cond: &SpecTecExp,
    binds: &BTreeMap<String, SpecTecExp>,
) -> Result<Thm> {
    if !is_value_fragment(cond) {
        return Err(Error::ConnectiveRule(
            "side condition: not in the value fragment (needs the datatype/function leg)".into(),
        ));
    }
    // Substitute the concrete bindings, then denote the closed condition.
    let closed = subst(cond, binds);
    // A closed value-fragment condition needs no free-variable types; any
    // residual `Var` (an unbound metavar) will fail to denote, which is correct.
    let ctx = DenoteCtx::values(TypeEnv::new());
    let term = denote(&closed, &ctx)?;
    debug_assert_eq!(term.type_of()?, Type::bool());
    // Discharge by kernel computation.
    prove_bool_true(&term)
}

/// `⊢ term` for a closed `bool` term that computes to a tautology: either it
/// reduces to `⌜T⌝` (via `eqt_elim`) — the `=`/`<`/`≤` conditions — or to `¬⌜F⌝`
/// (via the `⊢ ¬F` fact) — the `≠` conditions, which denote to `¬(a = b)` and
/// reduce to `¬F` (not literally `T`). Fails otherwise (the condition is false
/// for these values, or does not compute).
fn prove_bool_true(term: &Term) -> Result<Thm> {
    let red = term.reduce()?; // ⊢ term = v
    let v = red.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    if v.as_bool() == Some(true) {
        red.eqt_elim()
    } else if v == mk_bool(false).not()? {
        // v = ¬F ; from `⊢ term = ¬F` and `⊢ ¬F`, conclude `⊢ term`.
        red.sym()?.eq_mp(not_false()?)
    } else {
        Err(Error::ConnectiveRule(format!(
            "side condition: reduced to `{v}`, not a tautology"
        )))
    }
}

/// `⊢ ¬F` — false is not true (`¬p := p ⟹ F`, so `¬F = F ⟹ F`).
fn not_false() -> Result<Thm> {
    let f = mk_bool(false);
    Thm::assume(f.clone())?.imp_intro(&f)?.not_intro()
}

/// Convenience: bind a single metavariable and discharge (for one-variable
/// conditions like `n = 0`).
pub fn prove_side_condition_1(cond: &SpecTecExp, var: &str, val: SpecTecExp) -> Result<Thm> {
    let mut binds = BTreeMap::new();
    binds.insert(var.to_string(), val);
    prove_side_condition(cond, &binds)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_spectec::ast::{SpecTecCmpOp, SpecTecNum, SpecTecOpTyp};

    fn num(n: u64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Nat(n),
        }
    }
    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.to_string() }
    }
    fn cmp(op: SpecTecCmpOp, a: SpecTecExp, b: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Cmp {
            op,
            t: SpecTecOpTyp::Num(covalence_spectec::ast::SpecTecNumTyp::Nat),
            e1: Box::new(a),
            e2: Box::new(b),
        }
    }

    /// `n = 0` discharges for `n := 0`, and correctly REFUSES for `n := 5`.
    #[test]
    fn eq_zero_gates() {
        let cond = cmp(SpecTecCmpOp::Eq, var("n"), num(0));
        let ok = prove_side_condition_1(&cond, "n", num(0)).unwrap();
        assert!(ok.hyps().is_empty(), "discharge is hypothesis-free");
        // A false condition is refused — the discharge cannot fabricate.
        assert!(prove_side_condition_1(&cond, "n", num(5)).is_err());
    }

    /// `i < n` discharges for `2 < 5`, refuses for `5 < 5`.
    #[test]
    fn lt_gates() {
        let cond = cmp(SpecTecCmpOp::Lt, var("i"), var("n"));
        let mut ok = BTreeMap::new();
        ok.insert("i".to_string(), num(2));
        ok.insert("n".to_string(), num(5));
        assert!(prove_side_condition(&cond, &ok).unwrap().hyps().is_empty());

        let mut bad = BTreeMap::new();
        bad.insert("i".to_string(), num(5));
        bad.insert("n".to_string(), num(5));
        assert!(prove_side_condition(&cond, &bad).is_err());
    }

    /// `n ≤ k` (the `Limits_ok` shape) discharges for `3 ≤ 3`.
    #[test]
    fn le_gates() {
        let cond = cmp(SpecTecCmpOp::Le, var("n"), var("k"));
        let mut ok = BTreeMap::new();
        ok.insert("n".to_string(), num(3));
        ok.insert("k".to_string(), num(3));
        assert!(prove_side_condition(&cond, &ok).unwrap().hyps().is_empty());
        let mut bad = BTreeMap::new();
        bad.insert("n".to_string(), num(4));
        bad.insert("k".to_string(), num(3));
        assert!(prove_side_condition(&cond, &bad).is_err());
    }

    /// Arithmetic in the condition computes: `n = 2 + 3` holds for `n := 5`.
    #[test]
    fn arithmetic_condition() {
        let sum = SpecTecExp::Bin {
            op: covalence_spectec::ast::SpecTecBinOp::Add,
            t: SpecTecOpTyp::Num(covalence_spectec::ast::SpecTecNumTyp::Nat),
            e1: Box::new(num(2)),
            e2: Box::new(num(3)),
        };
        let cond = cmp(SpecTecCmpOp::Eq, var("n"), sum);
        assert!(
            prove_side_condition_1(&cond, "n", num(5))
                .unwrap()
                .hyps()
                .is_empty()
        );
        assert!(prove_side_condition_1(&cond, "n", num(6)).is_err());
    }

    /// `n ≠ 0` (the branch-rule condition shape, denoted as `¬(n=0)`) discharges
    /// for `n := 5` via the `¬F` fold, and REFUSES for `n := 0`.
    #[test]
    fn ne_zero_gates() {
        let cond = cmp(SpecTecCmpOp::Ne, var("n"), num(0));
        let ok = prove_side_condition_1(&cond, "n", num(5)).unwrap();
        assert!(ok.hyps().is_empty(), "discharge is hypothesis-free");
        // `0 ≠ 0` is false — refused.
        assert!(prove_side_condition_1(&cond, "n", num(0)).is_err());
    }

    /// A condition needing the datatype leg is rejected up front (not silently
    /// mis-decided).
    #[test]
    fn rejects_non_value_fragment() {
        let uncase = SpecTecExp::Uncase {
            e1: Box::new(var("c")),
            op: covalence_spectec::ast::MixOp::new(vec![String::new(), String::new()]),
        };
        let cond = cmp(SpecTecCmpOp::Ne, uncase, num(0));
        assert!(!is_value_fragment(&cond));
        assert!(prove_side_condition_1(&cond, "c", num(1)).is_err());
    }
}
