//! Shared helpers for the catalogue submodules.

use crate::hol;
use crate::term::{Term, Type};

use super::spec::TypeSpec;
use super::symbol::Symbol;

/// The "any" predicate `λ_:τ. T` for the carrier type τ. Used by
/// every `def name args := ty` (no `where pred`) catalogue entry.
pub(super) fn any(carrier: &Type) -> Term {
    Term::abs("_", carrier.clone(), Term::bool_lit(true))
}

/// Build `λS:car→bool. (∀x y. pred x y ⟹ S x ⟹ S y) ∧ (∃x. S x)`
/// — the selector predicate of `{ car } close pred`.
pub(super) fn close_predicate(car: Type, pred: Term) -> Term {
    let carrier = Type::fun(car.clone(), Type::bool());
    let s = Term::free("S", carrier.clone());

    let x = Term::free("x", car.clone());
    let y = Term::free("y", car.clone());
    let s_x = Term::app(s.clone(), x.clone());
    let s_y = Term::app(s.clone(), y.clone());
    let pred_xy = Term::app(Term::app(pred.clone(), x.clone()), y.clone());
    let closed_imp = hol::hol_imp(pred_xy, hol::hol_imp(s_x, s_y));
    let inner = hol::hol_forall("y", car.clone(), closed_imp);
    let closed_part = hol::hol_forall("x", car.clone(), inner);

    let x2 = Term::free("x", car.clone());
    let s_x2 = Term::app(s.clone(), x2);
    let nonempty_part = hol::hol_exists("x", car.clone(), s_x2);

    let body = hol::hol_and(closed_part, nonempty_part);
    hol::pub_abs("S", carrier, body)
}

/// `{ car } close pred` factory. Carrier is `car → bool`.
pub fn close_spec<S: Symbol>(symbol: S, car: Type, pred: Term) -> TypeSpec {
    let carrier = Type::fun(car.clone(), Type::bool());
    let tm = close_predicate(car, pred);
    TypeSpec::new(symbol, Some(carrier), Some(tm))
}

/// `car quot pred` factory — equivalent to `{ car } close (sym pred)`.
pub fn quot_spec<S: Symbol>(symbol: S, car: Type, pred: Term) -> TypeSpec {
    let x = Term::free("x", car.clone());
    let y = Term::free("y", car.clone());
    let pred_xy = Term::app(Term::app(pred.clone(), x.clone()), y.clone());
    let pred_yx = Term::app(Term::app(pred.clone(), y.clone()), x.clone());
    let disj = hol::hol_or(pred_xy, pred_yx);
    let lam_y = hol::pub_abs("y", car.clone(), disj);
    let sym_pred = hol::pub_abs("x", car.clone(), lam_y);
    close_spec(symbol, car, sym_pred)
}
