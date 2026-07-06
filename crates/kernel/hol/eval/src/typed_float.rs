//! The **typed float reduction driver** (stage F2c) — untrusted.
//!
//! Layer 2 of the two-layer float architecture: the typed ops
//! (`f64.add : f64 → f64 → f64`, the [`TypedF64`] registry in
//! [`crate::defs`]) are ordinary let-style defined constants wrapping the
//! layer-1 bit constants in the `f64 := u64` coercions. This module makes
//! closed applications of them *reduce*, by composing already-gated steps —
//! it introduces **no new rule** and cannot forge:
//!
//! 1. **Definitional unfold + β** ([`crate::delta`] + `mk_comb`/`beta_conv`):
//!    `⊢ f64.op a₁ [a₂] = fromBits (opBits (toBits a₁) [(toBits a₂)])`
//!    (comparisons have no result coercion).
//! 2. **Coercion round-trip** ([`rep_abs_eq`]): each argument is the literal
//!    form `fromBits ⌜bits⌝`, and `⊢ toBits (fromBits v) = v` falls out of
//!    the kernel's witness-free subtype law [`covalence_core::Thm::spec_rep_abs_fwd`]
//!    with the newtype's trivial selector `λ_. T` discharged by β + `⊢ T`.
//! 3. **`FloatCert`** on the bit redex: `⊢ opBits ⌜b₁⌝ [⌜b₂⌝] = ⌜r⌝` (the
//!    layer-1 certificate — the only computation-bearing step).
//! 4. Congruence re-wraps arithmetic results under `fromBits`, landing on
//!    the canonical literal form [`crate::defs::mk_f64`] produces.
//!
//! [`rep_abs_eq`] doubles as the driver's `toBits (fromBits v) = v`
//! reduction step ([`collapse_step`]), scoped to the float newtypes — that
//! is what lets explicit coercions in downstream formulas (e.g. the
//! `ball.add` ulp bump in `covalence-init`) reduce through the same
//! pipeline. (See [`collapse_step`] on why it is not widened to every
//! newtype.)

use covalence_core::seam::Lit;
use covalence_core::{Error, Result, SmallIntLiteral, Term, TermKind, TypeSpec};

use crate::defs::{self, TypedF64};
use crate::derived::DerivedRules;
use crate::{EvalThm, rules};

/// The RHS of an equational conclusion.
fn rhs_of(thm: &EvalThm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// `⊢ rep (abs v) = v` for a **0-ary newtype** [`TypeSpec`] — the
/// carrier-side coercion round-trip, unconditional because the newtype
/// selector is the trivial `λ_. T`:
///
/// 1. [`covalence_core::Thm::spec_rep_abs_fwd`]: `⊢ P v ⟹ rep (abs v) = v`;
/// 2. `beta_conv`: `⊢ P v = T` (refuses unless the β-reduct is literally the
///    `T` literal — i.e. unless the spec really is a newtype);
/// 3. `⊢ T` (the cert-path truth) + `eq_mp` discharges `⊢ P v`;
/// 4. `imp_elim` concludes.
///
/// Every step is a kernel-gated rule: a non-newtype spec (or an ill-typed
/// `v`) makes some step refuse, never a wrong equation.
fn rep_abs_eq(spec: &TypeSpec, v: &Term) -> Result<EvalThm> {
    // ⊢ P v ⟹ rep (abs v) = v.
    let fwd = EvalThm::spec_rep_abs_fwd(spec.clone(), Vec::new(), v.clone())?;
    // β-discharge the trivial newtype selector.
    let pred = spec.tm().ok_or(Error::NotReducible)?.clone();
    let beta = EvalThm::beta_conv(Term::app(pred, v.clone()))?; // ⊢ P v = T
    if rhs_of(&beta)?.as_bool() != Some(true) {
        return Err(Error::NotReducible); // a genuine subtype, not a newtype
    }
    let p_v = beta.sym()?.eq_mp(crate::truth()?)?; // ⊢ P v
    fwd.imp_elim(p_v) // ⊢ rep (abs v) = v
}

/// The driver arm for a coercion round-trip node: `head` is a `rep` coercion
/// leaf and `arg` its (already-reduced) operand. Fires exactly on
/// `rep (abs v)` at one of the **float newtypes** (`f32`/`f64` — matched by
/// pointer identity against the canonical specs) with the two coercions on
/// the same handle, yielding `⊢ rep (abs v) = v` via [`rep_abs_eq`].
///
/// Deliberately scoped to the float specs even though the derivation is
/// sound for every newtype: `reduce`'s normal forms are load-bearing for
/// hand-assembled `trans` chains downstream (`covalence-init` derivations
/// over the `bytes`/`string` newtypes), so widening the reducer's catalogue
/// to *all* newtypes shifts proofs that predate it. Consumers that want the
/// general collapse assemble it from the same kernel law (the pattern is
/// `covalence-init`'s ball evaluator).
pub(crate) fn collapse_step(head: &Term, arg: &Term) -> Option<EvalThm> {
    let TermKind::SpecRep(spec, targs) = head.kind() else {
        return None;
    };
    if !targs.is_empty() || !(spec.ptr_eq(&defs::f64_spec()) || spec.ptr_eq(&defs::f32_spec())) {
        return None;
    }
    let (f, v) = arg.as_app()?;
    let TermKind::SpecAbs(abs_spec, abs_targs) = f.kind() else {
        return None;
    };
    if !spec.ptr_eq(abs_spec) || !abs_targs.is_empty() {
        return None;
    }
    rep_abs_eq(spec, v).ok()
}

/// The driver arm for a typed `f64` op applied to concrete `f64` literals:
/// `⊢ f64.op x₁ [x₂] = result` (an `f64` literal for arithmetic, a `bool`
/// literal for comparisons). Refuses (`None`) on wrong arity or any
/// non-literal argument.
pub(crate) fn typed_f64_step(
    op: TypedF64,
    spec: &crate::defs::TermSpec,
    args: &[Term],
) -> Option<EvalThm> {
    let arity = if op.is_unary() { 1 } else { 2 };
    if args.len() != arity {
        return None;
    }
    // Every argument must be the concrete literal form `fromBits ⌜bits⌝`.
    let bits: Vec<u64> = args.iter().map(defs::as_f64_bits).collect::<Option<_>>()?;
    drive(op, spec, args, &bits).ok()
}

/// The composite derivation behind [`typed_f64_step`] (see the module docs
/// for the four stages).
fn drive(
    op: TypedF64,
    spec: &crate::defs::TermSpec,
    args: &[Term],
    bits: &[u64],
) -> Result<EvalThm> {
    // (1) δ + β spine on the sample arguments.
    let head = Term::term_spec(spec.clone(), Vec::new());
    let mut acc = crate::delta(&head)?; // ⊢ f64.op = λa [b]. body
    for a in args {
        acc = acc.mk_comb(EvalThm::refl(a.clone())?)?;
        let cur = rhs_of(&acc)?;
        if let TermKind::App(f, _) = cur.kind()
            && matches!(f.kind(), TermKind::Abs(..))
        {
            acc = acc.trans(EvalThm::beta_conv(cur.clone())?)?;
        }
    }

    // (2) collapse each `toBits (fromBits ⌜bᵢ⌝)` to its bit literal.
    let f64spec = defs::f64_spec();
    let mut bits_eq = EvalThm::refl(defs::float_bits_op(op.bits_key()))?;
    for a in args {
        let (_, v) = a.as_app().ok_or(Error::NotReducible)?;
        bits_eq = bits_eq.mk_comb(rep_abs_eq(&f64spec, v)?)?;
    } // ⊢ opBits (toBits x₁) … = opBits ⌜b₁⌝ …

    // (3) FloatCert on the bit redex.
    let lits: Vec<Lit> = bits
        .iter()
        .map(|&b| Lit::Small(SmallIntLiteral::u64(b)))
        .collect();
    let cert = crate::mint(
        rules::FloatCert,
        (defs::float_bits_spec(op.bits_key()), lits),
    )
    .ok_or(Error::NotReducible)?; // ⊢ opBits ⌜b₁⌝ … = ⌜r⌝
    let chain = bits_eq.trans(cert)?;

    // (4) comparisons land in `bool`; arithmetic re-wraps under `fromBits`.
    let step = if op.is_cmp() {
        chain
    } else {
        EvalThm::refl(defs::f64_from_bits())?.mk_comb(chain)?
    };
    acc.trans(step)
}
