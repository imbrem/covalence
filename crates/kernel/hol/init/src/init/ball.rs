//! **Ball arithmetic groundwork** (stage F2c §3 — data only).
//!
//! A *ball* is a midpoint–radius interval `⟨c, r⟩ : f64 × f64` denoting the
//! real set `[c − r, c + r]` — the representation ball arithmetic (Arb-style)
//! computes with. This module defines the catalogue *data*: the `ball` type,
//! its constructor/accessors, and the outward-rounded `ball.add`, plus an
//! evaluation driver. **No enclosure theorems yet** — the containment
//! contract (`x ∈ X ∧ y ∈ Y ⟹ x + y ∈ ball.add X Y`) is the F4 follow-up
//! (see `SKELETONS.md`); until it is proved, the `ball.add` formula below is
//! *provisional* and may be revised to whatever the proof wants.
//!
//! ## The `ball.add` formula (recorded decision)
//!
//! `ball.add ⟨cx,rx⟩ ⟨cy,ry⟩ = ⟨c, r⟩` with, entirely in typed `f64` ops:
//!
//! ```text
//! c   = cx ⊕ cy                        (fl(cx + cy), round-to-nearest)
//! ulp = nextUp(|c|) ⊖ |c|              (an upper bound on the c-rounding error)
//! r   = nextUp((rx ⊕ ry) ⊕ ulp)        (radius sum, ulp bump, outward nudge)
//! ```
//!
//! where `nextUp(z) := fromBits(toBits(z) +₆₄ 1)` — the IEEE 754
//! monotone-bit-pattern trick (for non-negative finite `z`, incrementing the
//! bit pattern is exactly `nextUp`; `+₆₄` is the wrapping `u64.add`). The
//! rounding error of `c` is at most `½ ulp(c) ≤ ulp` and each radius `⊕`
//! rounds by at most `½ ulp` of its result, which the final `nextUp`
//! over-compensates for at the achievable precision; edge cases (overflow to
//! `∞`, NaN centers) degrade *conservatively* (infinite radius / unordered
//! comparisons), but none of this is *proved* yet — that is precisely F4.
//!
//! **Decision:** no `f64.ulpBits` bit-level constant was declared (the F2b
//! escape hatch the stage allowed): `nextUp` via `u64.add` on the coercion
//! images covers it with existing certified ops, keeping the F2b registry —
//! and the trusted base — untouched.
//!
//! ## Evaluation
//!
//! Concrete balls are `mk (fromBits ⌜c⌝) (fromBits ⌜r⌝)` in reduced form
//! ([`mk_ball`]). [`ball_eval`] normalises a closed ball expression by
//! iterating δ (the four `ball.*` symbols, through the twin registry) and
//! weak βι reduction ([`TermExt::reduce`] — typed `f64` ops, coercion
//! round-trips, and the proved product projections) to a fixpoint. Purely
//! compositional over kernel rules and the eval-tier certificates: it can
//! fail, but it cannot forge.

use std::sync::LazyLock;

use smol_str::SmolStr;

use covalence_core::{Error, IntTag, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs::{
    self, IntOp, TermSpec, TypeSpec, TypedF64, f64_from_bits, f64_op, f64_to_bits, f64_ty,
};
use covalence_hol_eval::{mk_f64, mk_u64};

use crate::init::ext::{TermExt, ThmExt};

// ============================================================================
// The `ball` type: a newtype over `prod f64 f64` (center, radius)
// ============================================================================

/// `ball := f64 × f64` — center–radius pairs, as an opaque newtype over
/// `prod f64 f64` (the same shape as the catalogue's other newtypes; the
/// kernel's witness-free abs/rep laws give the coercion round-trips).
pub fn ball_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| TypeSpec::newtype(SmolStr::from("ball"), defs::prod(f64_ty(), f64_ty())));
    LAZY.clone()
}

/// The `ball` type leaf.
pub fn ball_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(ball_spec(), vec![]));
    LAZY.clone()
}

/// `abs : prod f64 f64 → ball` — the newtype abstraction coercion.
fn ball_abs() -> Term {
    Term::spec_abs(ball_spec(), Vec::new())
}

/// `rep : ball → prod f64 f64` — the newtype representation coercion.
fn ball_rep() -> Term {
    Term::spec_rep(ball_spec(), Vec::new())
}

// ============================================================================
// Term builders
// ============================================================================

fn app2(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

/// `pair` at `f64 × f64`.
fn pair_f64() -> Term {
    defs::pair(f64_ty(), f64_ty())
}

/// Typed binary float op applied to two arguments.
fn fop2(op: TypedF64, a: Term, b: Term) -> Term {
    app2(f64_op(op), a, b)
}

/// `nextUp(z) := fromBits (u64.add (toBits z) ⌜1⌝)` — see the module docs.
fn next_up(z: Term) -> Term {
    let bump = app2(
        defs::int_op(IntTag::U64, IntOp::Add),
        Term::app(f64_to_bits(), z),
        mk_u64(1),
    );
    Term::app(f64_from_bits(), bump)
}

/// A concrete ball in **reduced form**: `abs (pair ⌜c⌝ ⌜r⌝)` over the two
/// `f64` literals — the normal form [`ball_eval`] lands on (and the shape
/// `ball.mk ⌜c⌝ ⌜r⌝` evaluates to).
pub fn mk_ball(c: f64, r: f64) -> Term {
    Term::app(ball_abs(), app2(pair_f64(), mk_f64(c), mk_f64(r)))
}

// ============================================================================
// The catalogue entries (let-style, monomorphic — twin-eligible)
// ============================================================================

/// `ball.mk : f64 → f64 → ball := λc r. abs (pair c r)`.
pub fn ball_mk_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let c = Term::free("c", f64_ty());
        let r = Term::free("r", f64_ty());
        let body = Term::app(ball_abs(), app2(pair_f64(), c, r));
        let lam_r = Term::abs(f64_ty(), subst::close(&body, "r"));
        let lam = Term::abs(f64_ty(), subst::close(&lam_r, "c"));
        let ty = Type::fun(f64_ty(), Type::fun(f64_ty(), ball_ty()));
        TermSpec::new(SmolStr::from("ball.mk"), Some(ty), Some(lam))
    });
    LAZY.clone()
}

/// `ball.mk` as a term.
pub fn ball_mk() -> Term {
    Term::term_spec(ball_mk_spec(), Vec::new())
}

/// Shared shape of the two accessors: `λb:ball. proj (rep b)`.
fn accessor(label: &str, first: bool) -> TermSpec {
    let b = Term::free("b", ball_ty());
    let proj = if first {
        defs::fst(f64_ty(), f64_ty())
    } else {
        defs::snd(f64_ty(), f64_ty())
    };
    let body = Term::app(proj, Term::app(ball_rep(), b));
    let lam = Term::abs(ball_ty(), subst::close(&body, "b"));
    let ty = Type::fun(ball_ty(), f64_ty());
    TermSpec::new(SmolStr::from(label), Some(ty), Some(lam))
}

/// `ball.center : ball → f64 := λb. fst (rep b)`.
pub fn ball_center_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| accessor("ball.center", true));
    LAZY.clone()
}

/// `ball.center` as a term.
pub fn ball_center() -> Term {
    Term::term_spec(ball_center_spec(), Vec::new())
}

/// `ball.radius : ball → f64 := λb. snd (rep b)`.
pub fn ball_radius_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| accessor("ball.radius", false));
    LAZY.clone()
}

/// `ball.radius` as a term.
pub fn ball_radius() -> Term {
    Term::term_spec(ball_radius_spec(), Vec::new())
}

/// `ball.add : ball → ball → ball` — the outward-rounded sum (see the
/// module docs for the formula and its provisional status).
pub fn ball_add_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let x = Term::free("x", ball_ty());
        let y = Term::free("y", ball_ty());
        let center = |b: &Term| Term::app(ball_center(), b.clone());
        let radius = |b: &Term| Term::app(ball_radius(), b.clone());
        // c = cx ⊕ cy   (duplicated below — HOL terms have no `let`).
        let c = fop2(TypedF64::Add, center(&x), center(&y));
        let abs_c = |c: &Term| Term::app(f64_op(TypedF64::Abs), c.clone());
        // ulp = nextUp(|c|) ⊖ |c|.
        let ulp = fop2(TypedF64::Sub, next_up(abs_c(&c)), abs_c(&c));
        // r = nextUp((rx ⊕ ry) ⊕ ulp).
        let r = next_up(fop2(
            TypedF64::Add,
            fop2(TypedF64::Add, radius(&x), radius(&y)),
            ulp,
        ));
        let body = app2(ball_mk(), c, r);
        let lam_y = Term::abs(ball_ty(), subst::close(&body, "y"));
        let lam = Term::abs(ball_ty(), subst::close(&lam_y, "x"));
        let ty = Type::fun(ball_ty(), Type::fun(ball_ty(), ball_ty()));
        TermSpec::new(SmolStr::from("ball.add"), Some(ty), Some(lam))
    });
    LAZY.clone()
}

/// `ball.add` as a term.
pub fn ball_add() -> Term {
    Term::term_spec(ball_add_spec(), Vec::new())
}

// ============================================================================
// Evaluation
// ============================================================================

/// `⊢ rep (abs v) = v` at the `ball` newtype — the coercion round-trip as
/// an opt-in evaluation step. Same derivation as the eval driver's
/// float-scoped collapse (the kernel's witness-free subtype law, the β of
/// the trivial selector, and `⊢ T`), assembled here because the generic
/// reducer deliberately scopes its collapse to the float newtypes (see
/// `covalence-hol-eval`'s driver docs). Purely composed of kernel rules.
fn ball_collapse_step(t: &Term) -> Option<Thm> {
    use covalence_core::TermKind;
    let (rep, arg) = t.as_app()?;
    let TermKind::SpecRep(spec, targs) = rep.kind() else {
        return None;
    };
    if !targs.is_empty() || !spec.ptr_eq(&ball_spec()) {
        return None;
    }
    let (abs, v) = arg.as_app()?;
    let TermKind::SpecAbs(abs_spec, abs_targs) = abs.kind() else {
        return None;
    };
    if !abs_targs.is_empty() || !spec.ptr_eq(abs_spec) {
        return None;
    }
    let derive = || -> Result<Thm> {
        // ⊢ P v ⟹ rep (abs v) = v, with P = λ_. T (the newtype selector).
        let fwd = Thm::spec_rep_abs_fwd(spec.clone(), Vec::new(), v.clone())?;
        let pred = spec.tm().ok_or(Error::NotASubtype)?.clone();
        let beta = Thm::beta_conv(Term::app(pred, v.clone()))?; // ⊢ P v = T
        let p_v = beta.sym()?.eq_mp(crate::init::logic::truth())?; // ⊢ P v
        fwd.imp_elim(p_v)
    };
    derive().ok()
}

/// The combined opt-in step [`ball_eval`] fires alongside the generic
/// reducer: proved product projections + the `ball` coercion round-trip.
fn ball_step(t: &Term) -> Option<Thm> {
    crate::init::ext::prod_proj_step(t).or_else(|| ball_collapse_step(t))
}

/// Normalise a closed ball expression: iterate *δ over the `ball.*` symbols*
/// (through [`TermExt::delta_all`], hence the twin registry), *weak βι
/// reduction* ([`TermExt::reduce`]), and the opt-in **ball step** (proved
/// `fst`/`snd`-of-`pair` projections + the `ball` coercion round-trip —
/// deliberately not part of the generic reducer, whose normal forms are
/// load-bearing elsewhere) until the right-hand side stops changing.
/// Returns `⊢ t = normal-form`; on concrete inputs the normal form of a
/// ball-valued expression is [`mk_ball`]'s shape.
pub fn ball_eval(t: &Term) -> Result<Thm> {
    let mut acc = Thm::refl(t.clone())?;
    loop {
        let before = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        for spec in [
            ball_add_spec(),
            ball_mk_spec(),
            ball_center_spec(),
            ball_radius_spec(),
        ] {
            acc = acc.rhs_conv(|u| u.delta_all(spec.symbol()))?;
        }
        acc = acc.rhs_conv(|u| u.reduce())?;
        acc = acc.rhs_conv(|u| crate::init::ext::fire_all(u, &ball_step))?;
        let after = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        if after == before {
            return Ok(acc);
        }
    }
}

/// Native mirror of the `ball.add` formula — the SAME operations in the
/// SAME order (Rust `f64` arithmetic is IEEE 754 round-to-nearest, matching
/// the WASM deterministic profile on non-NaN values; `wrapping_add` matches
/// the `u64.add` convention). Test oracle only.
pub fn ball_add_native(x: (f64, f64), y: (f64, f64)) -> (f64, f64) {
    let next_up = |z: f64| f64::from_bits(z.to_bits().wrapping_add(1));
    let c = x.0 + y.0;
    let ulp = next_up(c.abs()) - c.abs();
    let r = next_up((x.1 + y.1) + ulp);
    (c, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every ball catalogue entry is a well-typed monomorphic let-style
    /// definition (the twin-machinery criteria).
    #[test]
    fn ball_specs_are_let_style_and_well_typed() {
        for spec in [
            ball_mk_spec(),
            ball_center_spec(),
            ball_radius_spec(),
            ball_add_spec(),
        ] {
            let label = spec.symbol().label().to_string();
            let ty = spec.ty().expect("declares a type").clone();
            let body = spec.tm().expect("let-style");
            assert_eq!(body.type_of().expect("body type-checks"), ty, "{label}");
            assert!(ty.free_tvars().is_empty(), "{label} is monomorphic");
        }
        // And the twin registry accepts them (the stored defining theorems).
        for spec in [ball_mk_spec(), ball_add_spec()] {
            let twin = crate::init::twins::twin_for(&spec)
                .unwrap()
                .expect("ball specs twin");
            assert!(twin.def_thm.hyps().is_empty());
        }
    }

    /// The accessors compute: `center (mk_ball c r) = ⌜c⌝` and likewise for
    /// the radius, end to end through δ + the coercion round-trip + the
    /// proved projections.
    #[test]
    fn ball_accessors_compute() {
        let b = mk_ball(1.5, 0.25);
        let conv = ball_eval(&Term::app(ball_center(), b.clone())).unwrap();
        assert!(conv.hyps().is_empty());
        assert_eq!(conv.concl().as_eq().unwrap().1, &mk_f64(1.5));
        let conv = ball_eval(&Term::app(ball_radius(), b)).unwrap();
        assert_eq!(conv.concl().as_eq().unwrap().1, &mk_f64(0.25));
    }

    /// `ball.mk` on two concrete `f64`s evaluates to the reduced form.
    #[test]
    fn ball_mk_computes() {
        let t = app2(ball_mk(), mk_f64(3.0), mk_f64(0.5));
        let conv = ball_eval(&t).unwrap();
        assert_eq!(conv.concl().as_eq().unwrap().1, &mk_ball(3.0, 0.5));
    }

    /// **The stage acceptance test:** `ball.add` of two concrete balls
    /// computes, agreeing with the native mirror of the formula.
    #[test]
    fn ball_add_of_concrete_balls_computes() {
        let (bx, by) = ((1.5, 0.0078125), (2.25, 0.015625));
        let t = app2(ball_add(), mk_ball(bx.0, bx.1), mk_ball(by.0, by.1));
        let conv = ball_eval(&t).unwrap();
        assert!(conv.hyps().is_empty());
        let (lhs, rhs) = conv.concl().as_eq().unwrap();
        assert_eq!(lhs, &t);
        let (c, r) = ball_add_native(bx, by);
        assert_eq!(c, 3.75);
        assert!(r > 0.0078125 + 0.015625, "radius must be bumped outward");
        assert_eq!(rhs, &mk_ball(c, r));
    }

    /// A second sample with a zero-radius operand and a negative center —
    /// the formula (and its native mirror) must stay in lockstep.
    #[test]
    fn ball_add_more_samples() {
        for (bx, by) in [
            ((0.1, 0.0), (0.2, 0.0)),
            ((-1.0, 0.5), (1.0, 0.5)),
            ((1e300, 1.0), (1e300, 1.0)),
        ] {
            let t = app2(ball_add(), mk_ball(bx.0, bx.1), mk_ball(by.0, by.1));
            let conv = ball_eval(&t).unwrap();
            let (c, r) = ball_add_native(bx, by);
            assert_eq!(
                conv.concl().as_eq().unwrap().1,
                &mk_ball(c, r),
                "mismatch at {bx:?} + {by:?}"
            );
        }
    }
}
