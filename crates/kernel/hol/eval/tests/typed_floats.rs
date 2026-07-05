//! Stage F2c acceptance: the **typed `f64` layer** (layer 2, untrusted).
//!
//! The typed ops are let-style coercion wrappers over the F2b bit constants;
//! the driver reduces closed applications by composing gated steps (δ/β +
//! coercion round-trip + `FloatCert`). Here: registry shape (let-style,
//! twin-eligible), the driver reduction against the base `CanonRule`s over
//! the adversarial operand bank (value-for-value, mirroring the F2b
//! differential style at the typed level), the coercion round-trip step, and
//! the shape refusals.

use covalence_core::{Term, TermKind, Type};
use covalence_hol_eval::defs::{
    self, TypedF64, f64_from_bits, f64_op, f64_op_spec, f64_to_bits, f64_ty,
};
use covalence_hol_eval::{as_f64_bits, mk_f64, mk_u64, reduce};
use covalence_pure::{CanonRule, F64};
use covalence_pure_eval as pe;

// ============================================================================
// Helpers + the operand bank (the F2b adversarial style)
// ============================================================================

/// f64 bit patterns: ±0, ±1, rounding ties, extremes, ±inf, NaNs.
const F64_BITS: &[u64] = &[
    0x0000_0000_0000_0000, // +0.0
    0x8000_0000_0000_0000, // -0.0
    0x3ff0_0000_0000_0000, // 1.0
    0xbff0_0000_0000_0000, // -1.0
    0x3fe0_0000_0000_0000, // 0.5
    0x3ff8_0000_0000_0000, // 1.5
    0xbff8_0000_0000_0000, // -1.5
    0x7fef_ffff_ffff_ffff, // max normal
    0x0000_0000_0000_0001, // smallest subnormal
    0x7ff0_0000_0000_0000, // +inf
    0xfff0_0000_0000_0000, // -inf
    0x7ff8_0000_0000_0000, // canonical qNaN
    0x7ff8_0000_1234_5678, // qNaN with payload
    0x3fbf_9add_3746_f65f, // 0.1234
];

/// The concrete `f64` literal form for raw bits (bit-exact — avoids any
/// native `f64` round-trip on NaN payloads).
fn lit(bits: u64) -> Term {
    Term::app(f64_from_bits(), mk_u64(bits))
}

fn app2(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

fn assert_reduces(t: Term, want: Term) {
    let thm = reduce(&t).unwrap_or_else(|| panic!("reduce refused {t:?}"));
    assert!(thm.hyps().is_empty(), "driver facts are hypothesis-free");
    let (lhs, rhs) = thm.concl().as_eq().expect("concl is an equation");
    assert_eq!(lhs, &t, "LHS mismatch for {t:?}");
    assert_eq!(rhs, &want, "value mismatch for {t:?}");
}

/// Expected result of a typed op — an independent transcription against the
/// base `CanonRule`s (unary ops ignore `b`).
fn expected(op: TypedF64, a: u64, b: u64) -> Term {
    let (x, y) = (F64::from_bits(a), F64::from_bits(b));
    let f = |v: Option<F64>| lit(v.expect("float ops are total").to_bits());
    let c = |v: Option<bool>| Term::bool_lit(v.expect("float cmps are total"));
    match op {
        TypedF64::Add => f(pe::F64Add.eval(&(x, y))),
        TypedF64::Sub => f(pe::F64Sub.eval(&(x, y))),
        TypedF64::Mul => f(pe::F64Mul.eval(&(x, y))),
        TypedF64::Div => f(pe::F64Div.eval(&(x, y))),
        TypedF64::Min => f(pe::F64Min.eval(&(x, y))),
        TypedF64::Max => f(pe::F64Max.eval(&(x, y))),
        TypedF64::Sqrt => f(pe::F64Sqrt.eval(&x)),
        TypedF64::Abs => f(pe::F64Abs.eval(&x)),
        TypedF64::Neg => f(pe::F64Neg.eval(&x)),
        TypedF64::Eq => c(pe::F64Eq.eval(&(x, y))),
        TypedF64::Lt => c(pe::F64Lt.eval(&(x, y))),
        TypedF64::Le => c(pe::F64Le.eval(&(x, y))),
    }
}

// ============================================================================
// Registry shape: let-style, twin-eligible, dotted labels, expected types
// ============================================================================

#[test]
fn typed_registry_is_let_style_with_expected_types() {
    for op in TypedF64::ALL {
        let spec = f64_op_spec(op);
        let label = spec.symbol().label().to_string();
        assert!(label.starts_with("f64."), "{op:?}: {label}");
        // Let-style + monomorphic: exactly the twin-machinery criteria
        // (`twin_for` in covalence-init) and the definitional-unfold shape.
        let ty = spec.ty().expect("typed op declares its type").clone();
        let body = spec.tm().expect("typed op is let-style (has a body)");
        assert_eq!(
            body.type_of().expect("body type-checks"),
            ty,
            "{op:?} body must have the declared type (let-style)"
        );
        assert!(ty.free_tvars().is_empty(), "{op:?} must be monomorphic");
        // Canonical handles are shared singletons; the 0-ary term agrees.
        assert!(spec.ptr_eq(&f64_op_spec(op)), "{op:?} not a singleton");
        assert_eq!(f64_op(op).type_of().unwrap(), ty);
    }

    // Spot-pin the documented signatures.
    let f = f64_ty();
    assert_eq!(f64_op_spec(TypedF64::Add).symbol().label(), "f64.add");
    assert_eq!(
        f64_op_spec(TypedF64::Add).ty().cloned().unwrap(),
        Type::fun(f.clone(), Type::fun(f.clone(), f.clone()))
    );
    assert_eq!(
        f64_op_spec(TypedF64::Sqrt).ty().cloned().unwrap(),
        Type::fun(f.clone(), f.clone())
    );
    assert_eq!(
        f64_op_spec(TypedF64::Le).ty().cloned().unwrap(),
        Type::fun(f.clone(), Type::fun(f, Type::bool()))
    );
}

#[test]
fn f64_literal_facade_round_trips() {
    for &b in F64_BITS {
        let t = lit(b);
        assert_eq!(t.type_of().unwrap(), f64_ty());
        assert_eq!(as_f64_bits(&t), Some(b), "bit-exact recognition");
    }
    // `mk_f64` builds the same form from a native value.
    assert_eq!(mk_f64(3.75), lit(3.75f64.to_bits()));
    // Non-literal shapes are rejected.
    assert_eq!(as_f64_bits(&Term::free("x", f64_ty())), None);
    assert_eq!(as_f64_bits(&mk_u64(1)), None);
}

// ============================================================================
// Driver reduction for every typed op, against the base CanonRules
// ============================================================================

#[test]
fn typed_ops_match_base_canon_rules() {
    for op in TypedF64::ALL {
        let head = f64_op(op);
        if op.is_unary() {
            for &a in F64_BITS {
                assert_reduces(Term::app(head.clone(), lit(a)), expected(op, a, 0));
            }
        } else {
            for &a in F64_BITS {
                for &b in F64_BITS {
                    assert_reduces(app2(head.clone(), lit(a), lit(b)), expected(op, a, b));
                }
            }
        }
    }
}

/// The stage acceptance sample, end-to-end at the `EvalThm` tier:
/// `⊢ f64.add 1.5 2.25 = 3.75`.
#[test]
fn f64_add_1_5_plus_2_25_is_3_75() {
    let redex = app2(f64_op(TypedF64::Add), mk_f64(1.5), mk_f64(2.25));
    assert_reduces(redex, mk_f64(3.75));
}

/// Documented semantics spot checks at the typed level: NaN unordered,
/// signed-zero equality, canonical-NaN arithmetic, sqrt.
#[test]
fn typed_spot_checks() {
    let nan = f64::NAN.to_bits();
    // NaN is unordered even against itself.
    assert_reduces(
        app2(f64_op(TypedF64::Eq), lit(nan), lit(nan)),
        Term::bool_lit(false),
    );
    // +0 = -0 at the float level (bit-distinct literals!).
    assert_reduces(
        app2(f64_op(TypedF64::Eq), mk_f64(0.0), mk_f64(-0.0)),
        Term::bool_lit(true),
    );
    // inf + -inf collapses to the canonical NaN.
    assert_reduces(
        app2(
            f64_op(TypedF64::Add),
            mk_f64(f64::INFINITY),
            mk_f64(f64::NEG_INFINITY),
        ),
        lit(nan),
    );
    // sqrt 2.25 = 1.5.
    assert_reduces(Term::app(f64_op(TypedF64::Sqrt), mk_f64(2.25)), mk_f64(1.5));
}

// ============================================================================
// The coercion round-trip step (`⊢ rep (abs v) = v`)
// ============================================================================

#[test]
fn coercion_round_trip_reduces() {
    // On a literal payload…
    let v = mk_u64(0x4012_0000_0000_0000);
    let t = Term::app(f64_to_bits(), Term::app(f64_from_bits(), v.clone()));
    assert_reduces(t, v);
    // …and on any well-typed carrier term (sound for every operand: the
    // newtype selector is trivially true).
    let x = Term::free("x", defs::u64_ty());
    let t = Term::app(f64_to_bits(), Term::app(f64_from_bits(), x.clone()));
    assert_reduces(t, x);
}

#[test]
fn coercion_round_trip_refusals() {
    // A bare `rep` on a non-`abs` operand does not reduce.
    let y = Term::free("y", f64_ty());
    assert!(reduce(&Term::app(f64_to_bits(), y)).is_none());
    // Mismatched specs: `rep_{f64}` over `abs_{f32}` is ill-typed anyway,
    // but even a well-typed forged pairing is refused by pointer identity.
    let f32_abs = Term::spec_abs(defs::f32_spec(), Vec::new());
    let t = Term::app(
        f64_to_bits(),
        Term::app(f32_abs, covalence_hol_eval::mk_u32(1)),
    );
    assert!(reduce(&t).is_none(), "ill-typed / mismatched coercion pair");
    // Scope pin: the collapse is deliberately restricted to the FLOAT
    // newtypes — a non-float 0-ary newtype (`string`) does not collapse in
    // the generic reducer (its normal forms are load-bearing downstream).
    let s = Term::free("s", defs::list(defs::char_ty()));
    let t = Term::app(
        Term::spec_rep(defs::string_spec(), Vec::new()),
        Term::app(Term::spec_abs(defs::string_spec(), Vec::new()), s),
    );
    assert!(reduce(&t).is_none(), "non-float newtypes stay untouched");
}

// ============================================================================
// Shape refusals (refuse, never a wrong equation)
// ============================================================================

#[test]
fn typed_refusals() {
    let add = f64_op(TypedF64::Add);
    // Partial application.
    assert!(reduce(&Term::app(add.clone(), mk_f64(1.0))).is_none());
    // Non-literal argument.
    let x = Term::free("x", f64_ty());
    assert!(reduce(&app2(add.clone(), mk_f64(1.0), x)).is_none());
    // Raw bit literals where f64 literals are expected: ill-typed, refused.
    assert!(reduce(&app2(add, mk_u64(1), mk_u64(2))).is_none());
    // A user-built spec sharing the label is a different Arc: never fires.
    let canonical = f64_op_spec(TypedF64::Add);
    let fake = covalence_core::TermSpec::new_untrusted(
        "f64.add",
        canonical.ty().cloned(),
        canonical.tm().cloned(),
    );
    assert!(defs::lookup_f64_op(&fake).is_none());
    let t = app2(Term::term_spec(fake, Vec::new()), mk_f64(1.5), mk_f64(2.25));
    assert!(reduce(&t).is_none(), "look-alike spec must not reduce");
}

/// The typed result form is itself in normal form: the driver's output
/// `fromBits ⌜bits⌝` is not an application the driver reduces again (no
/// loops), and it is exactly `mk_f64`'s shape.
#[test]
fn result_form_is_normal() {
    let out = mk_f64(3.75);
    assert!(reduce(&out).is_none(), "f64 literals are irreducible");
    match out.kind() {
        TermKind::App(f, _) => {
            assert!(matches!(f.kind(), TermKind::SpecAbs(..)));
        }
        _ => panic!("mk_f64 is an applied coercion"),
    }
}
