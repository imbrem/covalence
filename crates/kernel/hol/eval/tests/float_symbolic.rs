//! The literal-endgame **never-materialize** proof-of-mechanism for the
//! bit-level `f32`/`f64` families (stage EG2 `float-unwall`; design:
//! `notes/vibes/literal-endgame-design.md` §7).
//!
//! Extends the int/bytes mechanism (`int_bytes_symbolic.rs`) to `f32.addBits` /
//! `f32.mulBits` and `f64.addBits` / `f64.mulBits`. Each symbolic lander carries
//! a `core::Thm` whose conclusion mentions `toHOL` floats that stay native
//! `F32`/`F64` bit-pattern leaves under the uninterpreted `ToHolF32`/`ToHolF64`
//! ops — no kernel `u32`/`u64` bit-pattern literal is materialized in the landed
//! conclusion, and its footprint is O(1) regardless of the bit pattern (NaN,
//! ±0, subnormal, ±inf all land the same size).
//!
//! Two obligations per family, both machine-checked:
//! - **never-materialize**: the symbolic conclusion's materialized-`Term`
//!   footprint is O(1) (2 nodes: the `=` head and the op head), independent of
//!   the operand bit patterns.
//! - **self-floor** (WAVE-1 audit): `from_pure_sym` skips `check_sequent`, so
//!   each symbolic lander is paired with a concrete floored sibling
//!   (`float_bits_thm` → `from_pure` → `check_sequent`) for the same input — the
//!   well-typedness witness.

use covalence_core::seam::Lit;
use covalence_core::{SmallIntLiteral, Term, TermKind};
use covalence_hol_eval::{
    F32BinEqE, F64BinEqE, HolApp, ToHolF32, ToHolF64, defs, f32_add_thm_symbolic,
    f32_mul_thm_symbolic, f64_add_thm_symbolic, f64_mul_thm_symbolic, float_bits_thm,
};
use covalence_pure::{App, F32, F64, Val};

/// Total `Term` node count (walks only `App`/`Abs` spines). A native
/// bit-pattern literal is a single leaf, so a materialized bit-tower would
/// explode this count. It never does.
fn term_nodes(t: &Term) -> usize {
    1 + match t.kind() {
        TermKind::App(f, x) => term_nodes(f) + term_nodes(x),
        TermKind::Abs(_, body) => term_nodes(body),
        _ => 0,
    }
}

// ===========================================================================
// f32.addBits / f32.mulBits — binary, `F32BinEqE`
// ===========================================================================

/// Destructure `f32.opBits (toHOL a) (toHOL b) = toHOL r` into its three native
/// `F32` leaves and its two operator `Term` constants, forcing nothing.
#[allow(clippy::type_complexity)]
fn destructure_f32_bin(concl: &F32BinEqE) -> (&F32, &F32, &F32, &Term, &Term) {
    let App(HolApp, (eq_applied, tohol_r)) = concl;
    let App(HolApp, (eq_op_leaf, lhs)) = eq_applied;
    let App(HolApp, (op_applied, tohol_b)) = lhs;
    let App(HolApp, (op_leaf, tohol_a)) = op_applied;
    let App(ToHolF32, Val(a)) = tohol_a;
    let App(ToHolF32, Val(b)) = tohol_b;
    let App(ToHolF32, Val(r)) = tohol_r;
    (a, b, r, &eq_op_leaf.0, &op_leaf.0)
}

fn f32_add_spec() -> Term {
    defs::float_bits_op(defs::FloatKey::Op(
        defs::FloatWidth::F32,
        defs::FloatOp::Add,
    ))
}

#[test]
fn f32_add_symbolic_lands_hyps_free() {
    let a = F32::new(1.5f32);
    let b = F32::new(2.25f32);
    let sum = a.add(b);

    let thm = f32_add_thm_symbolic(a, b).expect("symbolic f32.add");
    assert!(
        thm.sym_hyps().is_empty(),
        "certificates are hypothesis-free"
    );

    let (a_leaf, b_leaf, sum_leaf, eq_leaf, add_leaf) = destructure_f32_bin(thm.sym_concl());
    assert_eq!(a_leaf, &a, "toHOL leaf a is the native F32");
    assert_eq!(b_leaf, &b, "toHOL leaf b is the native F32");
    assert_eq!(sum_leaf, &sum, "toHOL leaf sum = a + b, WASM profile");

    // The `=` is at the `u32` bit sort (`f32 := u32`; `f32.addBits : u32 → u32
    // → u32`), and the op head is the canonical `f32.addBits` spec.
    assert_eq!(
        eq_leaf,
        &Term::eq_op(defs::u32_ty()),
        "materialized `= at u32`"
    );
    assert_eq!(add_leaf, &f32_add_spec(), "materialized `f32.addBits`");
    assert_eq!(
        term_nodes(eq_leaf) + term_nodes(add_leaf),
        2,
        "O(1) footprint"
    );
}

#[test]
fn f32_mul_symbolic_lands() {
    let a = F32::new(-6.0f32);
    let b = F32::new(7.0f32);
    let thm = f32_mul_thm_symbolic(a, b).expect("symbolic f32.mul");
    let (a_leaf, b_leaf, r_leaf, _, op) = destructure_f32_bin(thm.sym_concl());
    assert_eq!(a_leaf, &a);
    assert_eq!(b_leaf, &b);
    assert_eq!(r_leaf, &a.mul(b), "product computed on the WASM profile");
    assert_eq!(
        op,
        &defs::float_bits_op(defs::FloatKey::Op(
            defs::FloatWidth::F32,
            defs::FloatOp::Mul
        )),
        "materialized `f32.mulBits`"
    );
}

/// **Never-materialize / value-independence:** every edge bit pattern (NaN, ±0,
/// subnormal, ±inf) lands with the SAME O(1) footprint, holding the native
/// `F32` under `ToHolF32`. The materialized `Term` footprint (`=` head + op
/// head = 2 nodes) is independent of the operand value.
#[test]
fn f32_symbolic_never_materializes_edge_patterns() {
    let edges = [
        F32::from_bits(0x7fc0_0000), // canonical NaN
        F32::from_bits(0x7f80_0001), // signalling NaN payload
        F32::new(0.0f32),            // +0
        F32::from_bits(0x8000_0000), // -0
        F32::from_bits(0x0000_0001), // smallest subnormal
        F32::from_bits(0x7f80_0000), // +inf
        F32::from_bits(0xff80_0000), // -inf
    ];
    for &a in &edges {
        for &b in &edges {
            let thm = f32_add_thm_symbolic(a, b).expect("symbolic f32.add on edge bits");
            let (a_leaf, b_leaf, r_leaf, eq_leaf, op_leaf) = destructure_f32_bin(thm.sym_concl());
            assert_eq!(a_leaf, &a, "native F32 operand a held exactly");
            assert_eq!(b_leaf, &b, "native F32 operand b held exactly");
            assert_eq!(r_leaf, &a.add(b), "result is the WASM-profile sum");
            assert_eq!(
                term_nodes(eq_leaf) + term_nodes(op_leaf),
                2,
                "O(1) footprint, independent of the bit pattern"
            );
        }
    }
}

// ===========================================================================
// f64.addBits / f64.mulBits — binary, `F64BinEqE`
// ===========================================================================

#[allow(clippy::type_complexity)]
fn destructure_f64_bin(concl: &F64BinEqE) -> (&F64, &F64, &F64, &Term, &Term) {
    let App(HolApp, (eq_applied, tohol_r)) = concl;
    let App(HolApp, (eq_op_leaf, lhs)) = eq_applied;
    let App(HolApp, (op_applied, tohol_b)) = lhs;
    let App(HolApp, (op_leaf, tohol_a)) = op_applied;
    let App(ToHolF64, Val(a)) = tohol_a;
    let App(ToHolF64, Val(b)) = tohol_b;
    let App(ToHolF64, Val(r)) = tohol_r;
    (a, b, r, &eq_op_leaf.0, &op_leaf.0)
}

#[test]
fn f64_add_symbolic_lands_hyps_free() {
    let a = F64::new(1.5f64);
    let b = F64::new(2.25f64);
    let sum = a.add(b);

    let thm = f64_add_thm_symbolic(a, b).expect("symbolic f64.add");
    assert!(thm.sym_hyps().is_empty());

    let (a_leaf, b_leaf, sum_leaf, eq_leaf, add_leaf) = destructure_f64_bin(thm.sym_concl());
    assert_eq!(a_leaf, &a);
    assert_eq!(b_leaf, &b);
    assert_eq!(sum_leaf, &sum, "toHOL leaf sum = a + b, WASM profile");
    assert_eq!(
        eq_leaf,
        &Term::eq_op(defs::u64_ty()),
        "materialized `= at u64`"
    );
    assert_eq!(
        add_leaf,
        &defs::float_bits_op(defs::FloatKey::Op(
            defs::FloatWidth::F64,
            defs::FloatOp::Add
        )),
        "materialized `f64.addBits`"
    );
    assert_eq!(
        term_nodes(eq_leaf) + term_nodes(add_leaf),
        2,
        "O(1) footprint"
    );
}

#[test]
fn f64_mul_symbolic_lands() {
    let a = F64::new(-6.0f64);
    let b = F64::new(7.0f64);
    let thm = f64_mul_thm_symbolic(a, b).expect("symbolic f64.mul");
    let (a_leaf, b_leaf, r_leaf, _, op) = destructure_f64_bin(thm.sym_concl());
    assert_eq!(a_leaf, &a);
    assert_eq!(b_leaf, &b);
    assert_eq!(r_leaf, &a.mul(b), "product on the WASM profile");
    assert_eq!(
        op,
        &defs::float_bits_op(defs::FloatKey::Op(
            defs::FloatWidth::F64,
            defs::FloatOp::Mul
        )),
        "materialized `f64.mulBits`"
    );
}

#[test]
fn f64_symbolic_never_materializes_edge_patterns() {
    let edges = [
        F64::from_bits(0x7ff8_0000_0000_0000), // canonical NaN
        F64::from_bits(0x7ff0_0000_0000_0001), // signalling NaN payload
        F64::new(0.0f64),                      // +0
        F64::from_bits(0x8000_0000_0000_0000), // -0
        F64::from_bits(0x0000_0000_0000_0001), // smallest subnormal
        F64::from_bits(0x7ff0_0000_0000_0000), // +inf
        F64::from_bits(0xfff0_0000_0000_0000), // -inf
    ];
    for &a in &edges {
        for &b in &edges {
            let thm = f64_add_thm_symbolic(a, b).expect("symbolic f64.add on edge bits");
            let (a_leaf, b_leaf, r_leaf, eq_leaf, op_leaf) = destructure_f64_bin(thm.sym_concl());
            assert_eq!(a_leaf, &a);
            assert_eq!(b_leaf, &b);
            assert_eq!(r_leaf, &a.add(b));
            assert_eq!(
                term_nodes(eq_leaf) + term_nodes(op_leaf),
                2,
                "O(1) footprint, independent of the bit pattern"
            );
        }
    }
}

// ===========================================================================
// SELF-FLOOR witnesses (WAVE-1 audit obligation): a concrete floored sibling
// (`float_bits_thm` → from_pure → check_sequent) passing for the same input as
// the symbolic lander proves the symbolic conclusion is a well-typed HOL-bool
// sequent — i.e. each symbolic float lander self-floors.
// ===========================================================================

#[test]
fn f32_symbolic_landers_self_floor() {
    let vals = [
        F32::new(0.0f32),
        F32::new(3.5f32),
        F32::new(-2.0f32),
        F32::from_bits(0x7fc0_0000), // NaN
        F32::from_bits(0x7f80_0000), // +inf
    ];
    for &a in &vals {
        for &b in &vals {
            let sa = Lit::Small(SmallIntLiteral::u32(a.to_bits()));
            let sb = Lit::Small(SmallIntLiteral::u32(b.to_bits()));
            // f32.addBits
            float_bits_thm(
                defs::float_bits_spec(defs::FloatKey::Op(
                    defs::FloatWidth::F32,
                    defs::FloatOp::Add,
                )),
                vec![sa.clone(), sb.clone()],
            )
            .expect("concrete f32.addBits floors");
            f32_add_thm_symbolic(a, b).expect("symbolic f32.add");
            // f32.mulBits
            float_bits_thm(
                defs::float_bits_spec(defs::FloatKey::Op(
                    defs::FloatWidth::F32,
                    defs::FloatOp::Mul,
                )),
                vec![sa, sb],
            )
            .expect("concrete f32.mulBits floors");
            f32_mul_thm_symbolic(a, b).expect("symbolic f32.mul");
        }
    }
}

#[test]
fn f64_symbolic_landers_self_floor() {
    let vals = [
        F64::new(0.0f64),
        F64::new(3.5f64),
        F64::new(-2.0f64),
        F64::from_bits(0x7ff8_0000_0000_0000), // NaN
        F64::from_bits(0x7ff0_0000_0000_0000), // +inf
    ];
    for &a in &vals {
        for &b in &vals {
            let sa = Lit::Small(SmallIntLiteral::u64(a.to_bits()));
            let sb = Lit::Small(SmallIntLiteral::u64(b.to_bits()));
            // f64.addBits
            float_bits_thm(
                defs::float_bits_spec(defs::FloatKey::Op(
                    defs::FloatWidth::F64,
                    defs::FloatOp::Add,
                )),
                vec![sa.clone(), sb.clone()],
            )
            .expect("concrete f64.addBits floors");
            f64_add_thm_symbolic(a, b).expect("symbolic f64.add");
            // f64.mulBits
            float_bits_thm(
                defs::float_bits_spec(defs::FloatKey::Op(
                    defs::FloatWidth::F64,
                    defs::FloatOp::Mul,
                )),
                vec![sa, sb],
            )
            .expect("concrete f64.mulBits floors");
            f64_mul_thm_symbolic(a, b).expect("symbolic f64.mul");
        }
    }
}
