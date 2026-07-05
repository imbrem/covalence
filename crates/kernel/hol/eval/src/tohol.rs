//! The toHOL **symbolic-tier** driver (moved here from `covalence-core`'s
//! in-crate `proofs` module — the S4 first slice): a computation-backed
//! `IsThm` certificate whose numeral leaves are `toHOL` denotations, reified
//! through the admitted toHOL rules and transported with the base `eq_mp`,
//! landing as an [`EvalThm`] bit-for-bit equal to the fact the per-family cert
//! path mints. UNTRUSTED — composes gated mints only.
//!
//! This is the exemplar of the never-materialize pipeline (big values stay
//! symbolic; only the equations actually used ever exist). The bulk
//! reduction path in [`crate::reduce`] instead lands the per-family
//! certificates directly.

use covalence_pure::{CanonRule as _, Eqn, Expr, Thm as PThm, Val, apply, canon};
use covalence_pure_eval::NatAdd;
use covalence_types::Nat;

use covalence_core::seam::IsThm;
use covalence_core::{Ctx, Error, Result, Term, Type, defs};

use crate::lang::{CoreEval, EvalThm};
use crate::rules::{NatAddCert, PairVal, ToHolNatVal};
use crate::tohol_ops::{HolApp, HolAppE};

/// A pure theorem at the eval tier.
type PT<P> = PThm<CoreEval, P>;

/// A proven reification equation: `⊢ E = Val(t)` at the `Term` sort.
type Reified<E> = PT<Eqn<E, Val<Term>>>;

/// Lower a `covalence_pure` error into the core error type.
fn perr(e: covalence_pure::Error) -> Error {
    Error::Pure(format!("{e:?}"))
}

/// `⊢ nat.add ⌜a⌝ ⌜b⌝ = ⌜a + b⌝` as a kernel [`EvalThm`], computed **natively**
/// and landed through the toHOL seam — the end-to-end first slice, minting
/// the same conclusion as the legacy literal reduction of the application.
///
/// The pipeline (all steps gated or ungated-sound; none can forge):
/// 1. `NatAddCert` mints the symbolic-tier certificate
///    `⊢ IsThm(∅, ⌜nat.add (toHOL a) (toHOL b) = toHOL (a+b)⌝)`.
/// 2. `ToHolNatVal` (transitional) reifies each `toHOL` leaf to today's
///    literal-numeral `Term`, and `reify_app` pushes the equations up the
///    `HolApp` spine (`cong_pair` + `PairVal` + `cong_app` + `canon` +
///    `trans`) until the whole symbolic term expression equals a single
///    `Val<Term>`.
/// 3. The base `eq_mp` transports the `IsThm` proposition along the
///    reification equation (lifted through `cong_pair`/`cong_app(IsThm)`),
///    landing a genuine `CoreProp`.
/// 4. [`covalence_core::Thm::from_pure`] wraps it, re-running the sequent well-typedness
///    floor — indistinguishable from a rule-minted theorem.
pub fn nat_add_thm(a: Nat, b: Nat) -> Result<EvalThm> {
    // `NatAdd` is total (addition never refuses), so the `None` arm is
    // unreachable; refuse cleanly if it ever fires.
    let sum = NatAdd
        .eval(&(a.clone(), b.clone()))
        .ok_or_else(|| Error::Pure("nat.add: CanonRule refused a ground input".into()))?;

    // 1. The computation-backed certificate (symbolic tier).
    let cert = apply(CoreEval, NatAddCert, (a.clone(), b.clone())).map_err(perr)?;

    // 2. Reify the three toHOL leaves (transitional literal form) …
    let ta = apply(CoreEval, ToHolNatVal, a).map_err(perr)?;
    let tb = apply(CoreEval, ToHolNatVal, b).map_err(perr)?;
    let tc = apply(CoreEval, ToHolNatVal, sum).map_err(perr)?;

    // … and push them up the HolApp spine, innermost-first (the nesting must
    // mirror `tohol_ops::NatAddEqE` exactly for eq_mp's structural match).
    let add = PThm::refl(Val(defs::nat_add()), CoreEval);
    let lhs_partial = reify_app(add, ta)?; // ⊢ (nat.add (toHOL a)) = Val
    let lhs = reify_app(lhs_partial, tb)?; // ⊢ (nat.add (toHOL a) (toHOL b)) = Val
    let eq_op = PThm::refl(Val(Term::eq_op(Type::nat())), CoreEval);
    let eq_partial = reify_app(eq_op, lhs)?; // ⊢ ((=) lhs) = Val
    let full = reify_app(eq_partial, tc)?; // ⊢ E = Val(t_final)

    // 3. Transport IsThm(∅, E) along ⊢ E = Val(t_final), then wrap.
    let ctx = PThm::refl(Val(Ctx::new()), CoreEval);
    let pair = ctx.cong_pair(full).map_err(perr)?;
    let isthm_eq = pair.cong_app(IsThm);
    let landed = cert
        .eq_mp(isthm_eq)
        .ok_or_else(|| Error::Pure("eq_mp: reified lhs did not match the certificate".into()))?;
    EvalThm::from_pure(landed)
}

/// Reify one symbolic HOL application node: given `⊢ F = Val(f)` and
/// `⊢ X = Val(x)`, derive `⊢ HolApp(F, X) = Val(f x)`.
///
/// Steps: `cong_pair` (⊢ `(F, X) = (Val f, Val x)`), the admitted `PairVal`
/// fusion (⊢ `(Val f, Val x) = Val((f, x))`), `trans`, congruence under
/// `HolApp`, then the admitted `canon(HolApp)` evaluation
/// (⊢ `HolApp(Val((f, x))) = Val(f x)`) and a final `trans`.
fn reify_app<F, X>(f: Reified<F>, x: Reified<X>) -> Result<Reified<HolAppE<F, X>>>
where
    F: Expr<Ty = Term>,
    X: Expr<Ty = Term>,
{
    let fv = f.rhs().0.clone();
    let xv = x.rhs().0.clone();
    let pair = f.cong_pair(x).map_err(perr)?;
    let fused = apply(CoreEval, PairVal, (fv.clone(), xv.clone())).map_err(perr)?;
    let ground = pair.trans(fused).map_err(perr)?;
    let under_app = ground.cong_app(HolApp);
    let evaled = canon(HolApp, (fv, xv), CoreEval).map_err(perr)?;
    under_app.trans(evaled).map_err(perr)
}
