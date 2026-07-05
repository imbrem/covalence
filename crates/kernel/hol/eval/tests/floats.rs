//! Stage F2b acceptance: the **bit-level float layer**.
//!
//! For every declared bit-level float op (`defs::floats` registry), the
//! `FloatCert` cert-path reduction must agree value-for-value with the
//! trusted base `CanonRule` it claims to dispatch to — over adversarial
//! operand banks (NaN payloads, ±0, subnormals, infinities, saturation
//! boundaries; the differential-suite operand style). The expected values
//! here are an **independent transcription** of the op ↔ rule pairing, so a
//! transposed dispatch-table entry (e.g. `addBits` → `F32Sub`) or a wrong
//! literal rebuild is caught even though both sides bottom out in the same
//! base ops (whose own semantics are pinned bit-for-bit against wasmtime by
//! `covalence-pure-eval/tests/differential_float.rs`).
//!
//! Plus the tier-gating negatives (`FloatCert` is NOT admitted at `CoreLang`
//! — the pure-HOL tier keeps zero float axioms) and the adversarial shape
//! refusals (fake specs, wrong tags, wrong arity).

use covalence_core::seam::{CoreLang, Lit};
use covalence_core::{IntTag, SmallIntLiteral, Term, TermSpec, Type};
use covalence_hol_eval::defs::{
    self, FLOAT_CVT_TAGS, FloatKey, FloatOp, FloatWidth, float_bits_op, float_bits_spec,
};
use covalence_hol_eval::rules::FloatCert;
use covalence_hol_eval::{CoreEval, mk_u32, mk_u64, reduce};
use covalence_pure::{CanonRule, Error as PureError, F32, F64, apply};
use covalence_pure_eval as pe;

// ============================================================================
// Operand banks (raw bits — the differential-suite adversarial style)
// ============================================================================

/// f32 bit patterns: ±0, ±1, rounding ties, ±max-normal, subnormal extremes,
/// ±inf, canonical/signaling/payload NaNs, and int-saturation boundaries.
const F32_BITS: &[u32] = &[
    0x0000_0000, // +0.0
    0x8000_0000, // -0.0
    0x3f80_0000, // 1.0
    0xbf80_0000, // -1.0
    0x3f00_0000, // 0.5
    0x3fc0_0000, // 1.5
    0x4020_0000, // 2.5
    0xbfc0_0000, // -1.5 (nearest ties-to-even -> -2.0)
    0x7f7f_ffff, // max normal
    0xff7f_ffff, // -max normal
    0x0000_0001, // smallest subnormal
    0x007f_ffff, // largest subnormal
    0x8000_0001, // smallest negative subnormal
    0x7f80_0000, // +inf
    0xff80_0000, // -inf
    0x7fc0_0000, // canonical qNaN
    0x7f80_0001, // signaling NaN
    0x7fc0_1234, // qNaN with payload
    0xffc0_5678, // negative qNaN with payload
    0x4f00_0000, // 2^31  (> i32::MAX)
    0xcf00_0000, // -2^31 (= i32::MIN)
    0x4f80_0000, // 2^32  (> u32::MAX)
    0x5f80_0000, // 2^64
    0x42f6_e979, // 123.456
];

/// f64 bit patterns, analogous to [`F32_BITS`].
const F64_BITS: &[u64] = &[
    0x0000_0000_0000_0000, // +0.0
    0x8000_0000_0000_0000, // -0.0
    0x3ff0_0000_0000_0000, // 1.0
    0xbff0_0000_0000_0000, // -1.0
    0x3fe0_0000_0000_0000, // 0.5
    0x3ff8_0000_0000_0000, // 1.5
    0xbff8_0000_0000_0000, // -1.5 (nearest ties-to-even -> -2.0)
    0x7fef_ffff_ffff_ffff, // max normal
    0xffef_ffff_ffff_ffff, // -max normal
    0x0000_0000_0000_0001, // smallest subnormal
    0x000f_ffff_ffff_ffff, // largest subnormal
    0x7ff0_0000_0000_0000, // +inf
    0xfff0_0000_0000_0000, // -inf
    0x7ff8_0000_0000_0000, // canonical qNaN
    0x7ff0_0000_0000_0001, // signaling NaN
    0x7ff8_0000_1234_5678, // qNaN with payload
    0xfff8_0000_0abc_def0, // negative qNaN with payload
    0x41e0_0000_0000_0000, // 2^31
    0xc1e0_0000_0000_0000, // -2^31
    0x41f0_0000_0000_0000, // 2^32
    0x43e0_0000_0000_0000, // 2^63
    0x43f0_0000_0000_0000, // 2^64
    0x3fbf_9add_3746_f65f, // 0.1234
];

// ============================================================================
// Helpers
// ============================================================================

fn small(tag: IntTag, bits: u64) -> Term {
    Term::small_int(SmallIntLiteral::new(tag, bits))
}

fn apply_all(head: Term, args: &[Term]) -> Term {
    args.iter().fold(head, |f, a| Term::app(f, a.clone()))
}

/// Run the cert-path `reduce` and assert `⊢ t = want` (hyps empty, LHS = t).
fn assert_reduces(t: Term, want: Term) {
    let thm = reduce(&t).unwrap_or_else(|| panic!("reduce refused {t:?}"));
    assert!(thm.hyps().is_empty(), "cert facts are hypothesis-free");
    let (lhs, rhs) = thm.concl().as_eq().expect("concl is an equation");
    assert_eq!(lhs, &t, "LHS mismatch for {t:?}");
    assert_eq!(rhs, &want, "value mismatch for {t:?}");
}

fn assert_no_reduce(t: Term) {
    assert!(reduce(&t).is_none(), "reduce must refuse {t:?}");
}

// ============================================================================
// Expected values — an INDEPENDENT transcription of the op ↔ rule pairing
// ============================================================================

/// Expected result term of `FloatOp` at f32 (unary ops ignore `b`).
fn f32_expected(op: FloatOp, a: u32, b: u32) -> Term {
    let (x, y) = (F32::from_bits(a), F32::from_bits(b));
    let f = |v: Option<F32>| mk_u32(v.expect("float ops are total").to_bits());
    let c = |v: Option<bool>| Term::bool_lit(v.expect("float cmps are total"));
    match op {
        FloatOp::Add => f(pe::F32Add.eval(&(x, y))),
        FloatOp::Sub => f(pe::F32Sub.eval(&(x, y))),
        FloatOp::Mul => f(pe::F32Mul.eval(&(x, y))),
        FloatOp::Div => f(pe::F32Div.eval(&(x, y))),
        FloatOp::Min => f(pe::F32Min.eval(&(x, y))),
        FloatOp::Max => f(pe::F32Max.eval(&(x, y))),
        FloatOp::Copysign => f(pe::F32Copysign.eval(&(x, y))),
        FloatOp::Sqrt => f(pe::F32Sqrt.eval(&x)),
        FloatOp::Abs => f(pe::F32Abs.eval(&x)),
        FloatOp::Neg => f(pe::F32Neg.eval(&x)),
        FloatOp::Ceil => f(pe::F32Ceil.eval(&x)),
        FloatOp::Floor => f(pe::F32Floor.eval(&x)),
        FloatOp::Trunc => f(pe::F32Trunc.eval(&x)),
        FloatOp::Nearest => f(pe::F32Nearest.eval(&x)),
        FloatOp::Eq => c(pe::F32Eq.eval(&(x, y))),
        FloatOp::Ne => c(pe::F32Ne.eval(&(x, y))),
        FloatOp::Lt => c(pe::F32Lt.eval(&(x, y))),
        FloatOp::Gt => c(pe::F32Gt.eval(&(x, y))),
        FloatOp::Le => c(pe::F32Le.eval(&(x, y))),
        FloatOp::Ge => c(pe::F32Ge.eval(&(x, y))),
    }
}

/// Expected result term of `FloatOp` at f64 (unary ops ignore `b`).
fn f64_expected(op: FloatOp, a: u64, b: u64) -> Term {
    let (x, y) = (F64::from_bits(a), F64::from_bits(b));
    let f = |v: Option<F64>| mk_u64(v.expect("float ops are total").to_bits());
    let c = |v: Option<bool>| Term::bool_lit(v.expect("float cmps are total"));
    match op {
        FloatOp::Add => f(pe::F64Add.eval(&(x, y))),
        FloatOp::Sub => f(pe::F64Sub.eval(&(x, y))),
        FloatOp::Mul => f(pe::F64Mul.eval(&(x, y))),
        FloatOp::Div => f(pe::F64Div.eval(&(x, y))),
        FloatOp::Min => f(pe::F64Min.eval(&(x, y))),
        FloatOp::Max => f(pe::F64Max.eval(&(x, y))),
        FloatOp::Copysign => f(pe::F64Copysign.eval(&(x, y))),
        FloatOp::Sqrt => f(pe::F64Sqrt.eval(&x)),
        FloatOp::Abs => f(pe::F64Abs.eval(&x)),
        FloatOp::Neg => f(pe::F64Neg.eval(&x)),
        FloatOp::Ceil => f(pe::F64Ceil.eval(&x)),
        FloatOp::Floor => f(pe::F64Floor.eval(&x)),
        FloatOp::Trunc => f(pe::F64Trunc.eval(&x)),
        FloatOp::Nearest => f(pe::F64Nearest.eval(&x)),
        FloatOp::Eq => c(pe::F64Eq.eval(&(x, y))),
        FloatOp::Ne => c(pe::F64Ne.eval(&(x, y))),
        FloatOp::Lt => c(pe::F64Lt.eval(&(x, y))),
        FloatOp::Gt => c(pe::F64Gt.eval(&(x, y))),
        FloatOp::Le => c(pe::F64Le.eval(&(x, y))),
        FloatOp::Ge => c(pe::F64Ge.eval(&(x, y))),
    }
}

/// Expected `truncSatBits` result at (width, dst tag) for f32 bits `a`.
fn trunc_sat_expected_f32(dst: IntTag, a: u32) -> Term {
    let v = F32::from_bits(a);
    match dst {
        IntTag::U32 => Term::u32_lit(pe::U32TruncSatF32.eval(&v).unwrap()),
        IntTag::U64 => Term::u64_lit(pe::U64TruncSatF32.eval(&v).unwrap()),
        IntTag::S32 => Term::s32_lit(pe::I32TruncSatF32.eval(&v).unwrap()),
        IntTag::S64 => Term::s64_lit(pe::I64TruncSatF32.eval(&v).unwrap()),
        _ => unreachable!("only the WASM scalar tags are registered"),
    }
}

/// Expected `truncSatBits` result at (width, dst tag) for f64 bits `a`.
fn trunc_sat_expected_f64(dst: IntTag, a: u64) -> Term {
    let v = F64::from_bits(a);
    match dst {
        IntTag::U32 => Term::u32_lit(pe::U32TruncSatF64.eval(&v).unwrap()),
        IntTag::U64 => Term::u64_lit(pe::U64TruncSatF64.eval(&v).unwrap()),
        IntTag::S32 => Term::s32_lit(pe::I32TruncSatF64.eval(&v).unwrap()),
        IntTag::S64 => Term::s64_lit(pe::I64TruncSatF64.eval(&v).unwrap()),
        _ => unreachable!("only the WASM scalar tags are registered"),
    }
}

/// Integer operand bank per tag (as raw `SmallIntLiteral` payload bits).
fn int_bank(tag: IntTag) -> Vec<u64> {
    match tag {
        IntTag::U32 => vec![0, 1, 7, u32::MAX as u64, i32::MAX as u64, 0x8000_0000],
        IntTag::U64 => vec![0, 1, 7, u64::MAX, i64::MAX as u64, 1 << 63],
        // Signed payloads are sign-extended to 64 bits (the kernel literal
        // convention).
        IntTag::S32 => vec![
            0,
            1,
            (-1i64) as u64,
            i32::MAX as u64,
            i32::MIN as i64 as u64,
        ],
        IntTag::S64 => vec![0, 1, (-1i64) as u64, i64::MAX as u64, i64::MIN as u64],
        _ => unreachable!("only the WASM scalar tags are registered"),
    }
}

/// Expected `convertBits` result for f32 at src tag with payload bits `a`.
fn convert_expected_f32(src: IntTag, a: u64) -> Term {
    let r = match src {
        IntTag::U32 => pe::F32ConvertU32.eval(&(a as u32)),
        IntTag::U64 => pe::F32ConvertU64.eval(&a),
        IntTag::S32 => pe::F32ConvertI32.eval(&(a as i32)),
        IntTag::S64 => pe::F32ConvertI64.eval(&(a as i64)),
        _ => unreachable!(),
    };
    mk_u32(r.unwrap().to_bits())
}

/// Expected `convertBits` result for f64 at src tag with payload bits `a`.
fn convert_expected_f64(src: IntTag, a: u64) -> Term {
    let r = match src {
        IntTag::U32 => pe::F64ConvertU32.eval(&(a as u32)),
        IntTag::U64 => pe::F64ConvertU64.eval(&a),
        IntTag::S32 => pe::F64ConvertI32.eval(&(a as i32)),
        IntTag::S64 => pe::F64ConvertI64.eval(&(a as i64)),
        _ => unreachable!(),
    };
    mk_u64(r.unwrap().to_bits())
}

// ============================================================================
// Registry shape: declaration-only, dotted labels, expected types
// ============================================================================

#[test]
fn registry_is_declaration_only_with_expected_types() {
    let mut keys = vec![FloatKey::Promote, FloatKey::Demote];
    for &w in &FloatWidth::ALL {
        for op in FloatOp::ALL {
            keys.push(FloatKey::Op(w, op));
        }
        for &t in &FLOAT_CVT_TAGS {
            keys.push(FloatKey::TruncSat(w, t));
            keys.push(FloatKey::Convert(w, t));
        }
    }
    assert_eq!(
        keys.len(),
        58,
        "the F2b registry: 2·20 ops + 2·2·4 cvts + 2"
    );
    for &key in &keys {
        let spec = float_bits_spec(key);
        assert!(spec.tm().is_none(), "{key:?} must be declaration-only");
        assert!(
            spec.symbol().label().contains('.'),
            "{key:?} label must be dotted: {}",
            spec.symbol().label()
        );
        // The registered type is well-formed and matches the 0-ary term.
        let t = float_bits_op(key);
        assert_eq!(t.type_of().unwrap(), spec.ty().cloned().unwrap(), "{key:?}");
        // Canonical handles are shared singletons.
        assert!(
            spec.ptr_eq(&float_bits_spec(key)),
            "{key:?} not a singleton"
        );
    }

    // Spot-pin the documented signatures and labels.
    let u32t = defs::u32_ty();
    let u64t = defs::u64_ty();
    let add32 = float_bits_spec(FloatKey::Op(FloatWidth::F32, FloatOp::Add));
    assert_eq!(add32.symbol().label(), "f32.addBits");
    assert_eq!(
        add32.ty().cloned().unwrap(),
        Type::fun(u32t.clone(), Type::fun(u32t.clone(), u32t.clone()))
    );
    let le64 = float_bits_spec(FloatKey::Op(FloatWidth::F64, FloatOp::Le));
    assert_eq!(le64.symbol().label(), "f64.leBits");
    assert_eq!(
        le64.ty().cloned().unwrap(),
        Type::fun(u64t.clone(), Type::fun(u64t.clone(), Type::bool()))
    );
    let promote = float_bits_spec(FloatKey::Promote);
    assert_eq!(promote.symbol().label(), "f64.promoteBits");
    assert_eq!(
        promote.ty().cloned().unwrap(),
        Type::fun(u32t.clone(), u64t.clone())
    );
    let demote = float_bits_spec(FloatKey::Demote);
    assert_eq!(demote.symbol().label(), "f32.demoteBits");
    assert_eq!(
        demote.ty().cloned().unwrap(),
        Type::fun(u64t.clone(), u32t.clone())
    );
    let ts = float_bits_spec(FloatKey::TruncSat(FloatWidth::F64, IntTag::S32));
    assert_eq!(ts.symbol().label(), "s32.truncSatBits.f64");
    assert_eq!(
        ts.ty().cloned().unwrap(),
        Type::fun(u64t.clone(), IntTag::S32.ty())
    );
    let cv = float_bits_spec(FloatKey::Convert(FloatWidth::F32, IntTag::S64));
    assert_eq!(cv.symbol().label(), "f32.convertBits.s64");
    assert_eq!(cv.ty().cloned().unwrap(), Type::fun(IntTag::S64.ty(), u32t));
}

// ============================================================================
// Cert reductions for every declared op, against the base CanonRules
// ============================================================================

#[test]
fn f32_ops_match_base_canon_rules() {
    for op in FloatOp::ALL {
        let head = float_bits_op(FloatKey::Op(FloatWidth::F32, op));
        if op.is_unary() {
            for &a in F32_BITS {
                assert_reduces(
                    apply_all(head.clone(), &[mk_u32(a)]),
                    f32_expected(op, a, 0),
                );
            }
        } else {
            for &a in F32_BITS {
                for &b in F32_BITS {
                    assert_reduces(
                        apply_all(head.clone(), &[mk_u32(a), mk_u32(b)]),
                        f32_expected(op, a, b),
                    );
                }
            }
        }
    }
}

#[test]
fn f64_ops_match_base_canon_rules() {
    for op in FloatOp::ALL {
        let head = float_bits_op(FloatKey::Op(FloatWidth::F64, op));
        if op.is_unary() {
            for &a in F64_BITS {
                assert_reduces(
                    apply_all(head.clone(), &[mk_u64(a)]),
                    f64_expected(op, a, 0),
                );
            }
        } else {
            for &a in F64_BITS {
                for &b in F64_BITS {
                    assert_reduces(
                        apply_all(head.clone(), &[mk_u64(a), mk_u64(b)]),
                        f64_expected(op, a, b),
                    );
                }
            }
        }
    }
}

#[test]
fn promote_demote_match_base_canon_rules() {
    for &a in F32_BITS {
        let want = mk_u64(
            pe::F64PromoteF32
                .eval(&F32::from_bits(a))
                .unwrap()
                .to_bits(),
        );
        assert_reduces(Term::app(float_bits_op(FloatKey::Promote), mk_u32(a)), want);
    }
    for &a in F64_BITS {
        let want = mk_u32(pe::F32DemoteF64.eval(&F64::from_bits(a)).unwrap().to_bits());
        assert_reduces(Term::app(float_bits_op(FloatKey::Demote), mk_u64(a)), want);
    }
}

#[test]
fn trunc_sat_matches_base_canon_rules() {
    for &tag in &FLOAT_CVT_TAGS {
        for &a in F32_BITS {
            assert_reduces(
                Term::app(
                    float_bits_op(FloatKey::TruncSat(FloatWidth::F32, tag)),
                    mk_u32(a),
                ),
                trunc_sat_expected_f32(tag, a),
            );
        }
        for &a in F64_BITS {
            assert_reduces(
                Term::app(
                    float_bits_op(FloatKey::TruncSat(FloatWidth::F64, tag)),
                    mk_u64(a),
                ),
                trunc_sat_expected_f64(tag, a),
            );
        }
    }
}

#[test]
fn convert_matches_base_canon_rules() {
    for &tag in &FLOAT_CVT_TAGS {
        for a in int_bank(tag) {
            assert_reduces(
                Term::app(
                    float_bits_op(FloatKey::Convert(FloatWidth::F32, tag)),
                    small(tag, a),
                ),
                convert_expected_f32(tag, a),
            );
            assert_reduces(
                Term::app(
                    float_bits_op(FloatKey::Convert(FloatWidth::F64, tag)),
                    small(tag, a),
                ),
                convert_expected_f64(tag, a),
            );
        }
    }
}

// ============================================================================
// Documented spot checks: NaN canonicalization / payload bit ops / ±0 /
// subnormals / saturation (the WASM deterministic-profile commitments)
// ============================================================================

#[test]
fn spot_nan_zero_subnormal_saturation() {
    let canon32 = f32::NAN.to_bits();
    let op = |o| float_bits_op(FloatKey::Op(FloatWidth::F32, o));

    // Arithmetic NaN results collapse to the canonical NaN.
    assert_reduces(
        apply_all(
            op(FloatOp::Add),
            &[mk_u32(0x7f80_0000), mk_u32(0xff80_0000)],
        ), // inf + -inf
        mk_u32(canon32),
    );
    assert_reduces(
        apply_all(op(FloatOp::Div), &[mk_u32(0), mk_u32(0)]), // 0/0
        mk_u32(canon32),
    );
    assert_reduces(
        apply_all(op(FloatOp::Sqrt), &[mk_u32(0xbf80_0000)]), // sqrt(-1)
        mk_u32(canon32),
    );

    // abs/neg/copysign are pure bit ops — NaN payloads preserved.
    let payload = 0x7fc0_1234u32;
    assert_reduces(
        apply_all(op(FloatOp::Abs), &[mk_u32(payload | 0x8000_0000)]),
        mk_u32(payload),
    );
    assert_reduces(
        apply_all(op(FloatOp::Neg), &[mk_u32(payload)]),
        mk_u32(payload | 0x8000_0000),
    );
    assert_reduces(
        apply_all(
            op(FloatOp::Copysign),
            &[mk_u32(payload), mk_u32(0xbf80_0000)],
        ),
        mk_u32(payload | 0x8000_0000),
    );

    // Signed zero: min(+0, -0) = -0, max(+0, -0) = +0; eq(+0, -0) = T.
    assert_reduces(
        apply_all(op(FloatOp::Min), &[mk_u32(0), mk_u32(0x8000_0000)]),
        mk_u32(0x8000_0000),
    );
    assert_reduces(
        apply_all(op(FloatOp::Max), &[mk_u32(0), mk_u32(0x8000_0000)]),
        mk_u32(0),
    );
    assert_reduces(
        apply_all(op(FloatOp::Eq), &[mk_u32(0), mk_u32(0x8000_0000)]),
        Term::bool_lit(true),
    );
    // NaN is unordered: eq F, ne T.
    assert_reduces(
        apply_all(op(FloatOp::Eq), &[mk_u32(canon32), mk_u32(canon32)]),
        Term::bool_lit(false),
    );
    assert_reduces(
        apply_all(op(FloatOp::Ne), &[mk_u32(canon32), mk_u32(canon32)]),
        Term::bool_lit(true),
    );

    // Subnormal arithmetic stays exact: min_subnormal + min_subnormal.
    assert_reduces(
        apply_all(op(FloatOp::Add), &[mk_u32(1), mk_u32(1)]),
        mk_u32(2),
    );

    // trunc_sat saturation: NaN -> 0, +inf -> MAX, -2^31 exact.
    let ts = |t| float_bits_op(FloatKey::TruncSat(FloatWidth::F32, t));
    assert_reduces(
        Term::app(ts(IntTag::S32), mk_u32(canon32)),
        Term::s32_lit(0),
    );
    assert_reduces(
        Term::app(ts(IntTag::S32), mk_u32(0x7f80_0000)),
        Term::s32_lit(i32::MAX),
    );
    assert_reduces(
        Term::app(ts(IntTag::U32), mk_u32(0xbf80_0000)), // -1.0 -> 0 (unsigned)
        Term::u32_lit(0),
    );
}

// ============================================================================
// Tier gating: FloatCert is NOT admitted at CoreLang (pure-HOL keeps zero
// float axioms) — the pure_hol_units-style negative
// ============================================================================

fn sample_input() -> (TermSpec, Vec<Lit>) {
    (
        float_bits_spec(FloatKey::Op(FloatWidth::F32, FloatOp::Add)),
        vec![
            Lit::Small(SmallIntLiteral::u32(1.0f32.to_bits())),
            Lit::Small(SmallIntLiteral::u32(2.0f32.to_bits())),
        ],
    )
}

#[test]
fn float_cert_not_admitted_at_core_lang() {
    // The pure-HOL tier: `apply` gates on the rule's TypeId BEFORE `decide`
    // runs — `Thm<CoreLang>` can never contain a float-cert fact.
    assert!(matches!(
        apply(CoreLang, FloatCert, sample_input()),
        Err(PureError::NotAdmitted(_))
    ));
    // Nor the trivial language or the base Builtins canon.
    assert!(matches!(
        apply((), FloatCert, sample_input()),
        Err(PureError::NotAdmitted(_))
    ));
    assert!(matches!(
        apply(pe::Builtins, FloatCert, sample_input()),
        Err(PureError::NotAdmitted(_))
    ));
    // And IS admitted at the eval tier (1.0 + 2.0 = 3.0, on bits).
    assert!(apply(CoreEval, FloatCert, sample_input()).is_ok());
}

// ============================================================================
// Adversarial shape refusals (refuse, never a wrong equation)
// ============================================================================

#[test]
fn fake_spec_sharing_label_never_reduces() {
    // A user-built spec sharing `f32.addBits`'s label/type is a DIFFERENT
    // Arc: absent from the canonical registry, so neither the driver nor the
    // rule fires.
    let canonical = float_bits_spec(FloatKey::Op(FloatWidth::F32, FloatOp::Add));
    let fake = TermSpec::new_untrusted("f32.addBits", canonical.ty().cloned(), None);
    assert!(defs::lookup_float_op(&fake).is_none());
    let args = vec![
        Lit::Small(SmallIntLiteral::u32(1)),
        Lit::Small(SmallIntLiteral::u32(2)),
    ];
    assert!(apply(CoreEval, FloatCert, (fake.clone(), args)).is_err());
    assert_no_reduce(apply_all(
        Term::term_spec(fake, Vec::new()),
        &[mk_u32(1), mk_u32(2)],
    ));
}

#[test]
fn wrong_tag_arity_and_family_refuse() {
    let add32 = float_bits_op(FloatKey::Op(FloatWidth::F32, FloatOp::Add));
    // f64 bit literals fed to the f32 op: ill-typed, and the tag matcher
    // refuses even when fed straight to the rule.
    let (spec, _) = sample_input();
    let bad_args = vec![
        Lit::Small(SmallIntLiteral::u64(1)),
        Lit::Small(SmallIntLiteral::u64(2)),
    ];
    assert!(apply(CoreEval, FloatCert, (spec.clone(), bad_args)).is_err());
    // Wrong arity: partial application does not reduce.
    assert_no_reduce(Term::app(add32.clone(), mk_u32(1)));
    assert!(
        apply(
            CoreEval,
            FloatCert,
            (spec.clone(), vec![Lit::Small(SmallIntLiteral::u32(1))])
        )
        .is_err()
    );
    // Non-literal argument: no reduction.
    let x = Term::free("x", defs::u32_ty());
    assert_no_reduce(apply_all(add32, &[mk_u32(1), x]));
    // Wrong family: a float selector fed to another family's rule refuses.
    assert!(
        apply(
            CoreEval,
            covalence_hol_eval::rules::FixedWidthCert,
            sample_input()
        )
        .is_err()
    );
    // And a fixed-width selector fed to FloatCert refuses.
    let u32_add = defs::int_op_spec(IntTag::U32, defs::IntOp::Add);
    assert!(
        apply(
            CoreEval,
            FloatCert,
            (
                u32_add,
                vec![
                    Lit::Small(SmallIntLiteral::u32(1)),
                    Lit::Small(SmallIntLiteral::u32(2))
                ]
            )
        )
        .is_err()
    );
}
