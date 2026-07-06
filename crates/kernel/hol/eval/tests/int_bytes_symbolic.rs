//! The literal-endgame **never-materialize** proof-of-mechanism for the
//! `int` and `bytes` families (stage EG2; design:
//! `notes/vibes/literal-endgame-design.md`).
//!
//! Extends the WAVE-1 nat mechanism (`nat_add_symbolic.rs`) to `int.add` /
//! `int.mul` / `int.neg` and `bytes.cat` / `bytes.len`. Each symbolic lander
//! carries a `core::Thm` whose conclusion mentions `toHOL` values that stay
//! native `Int`/`Bytes`/`Nat` leaves under the uninterpreted `ToHol*` ops — no
//! kernel literal is materialized in the landed conclusion, and a megabyte
//! bytestring stays a single native leaf (never a `cons`-tower — the
//! binary-substrate payoff).
//!
//! Two obligations per family, both machine-checked:
//! - **never-materialize**: the symbolic conclusion's materialized-`Term`
//!   footprint is O(1), independent of operand magnitude.
//! - **self-floor** (WAVE-1 audit): `from_pure_sym` skips `check_sequent`, so
//!   each symbolic lander is paired with a concrete floored sibling
//!   (`int_arith_thm` / `bytes_thm`) that passes `check_sequent` for the same
//!   input — the well-typedness witness.

use covalence_core::seam::Lit;
use covalence_core::{Term, TermKind, Type};
use covalence_hol_eval::{
    BytesCatEqE, BytesLenEqE, HolApp, IntBinEqE, IntUnEqE, ToHolBytes, ToHolInt, ToHolNat,
    bytes_cat_thm_symbolic, bytes_len_thm_symbolic, bytes_thm, defs, int_add_thm_symbolic,
    int_arith_thm, int_mul_thm_symbolic, int_neg_thm_symbolic,
};
use covalence_pure::{App, Val};
use covalence_types::{Bytes, Int, Nat};

/// Total `Term` node count (walks only `App`/`Abs` spines). A native literal —
/// whatever its magnitude — is a single leaf, so a materialized succ/cons tower
/// would explode this count. It never does.
fn term_nodes(t: &Term) -> usize {
    1 + match t.kind() {
        TermKind::App(f, x) => term_nodes(f) + term_nodes(x),
        TermKind::Abs(_, body) => term_nodes(body),
        _ => 0,
    }
}

// ===========================================================================
// int.add / int.mul — binary, `IntBinEqE`
// ===========================================================================

/// Destructure `int.op (toHOL a) (toHOL b) = toHOL r` into its three native
/// `Int` leaves and its two operator `Term` constants, forcing nothing.
#[allow(clippy::type_complexity)]
fn destructure_int_bin(concl: &IntBinEqE) -> (&Int, &Int, &Int, &Term, &Term) {
    let App(HolApp, (eq_applied, tohol_r)) = concl;
    let App(HolApp, (eq_op_leaf, lhs)) = eq_applied;
    let App(HolApp, (op_applied, tohol_b)) = lhs;
    let App(HolApp, (op_leaf, tohol_a)) = op_applied;
    let App(ToHolInt, Val(a)) = tohol_a;
    let App(ToHolInt, Val(b)) = tohol_b;
    let App(ToHolInt, Val(r)) = tohol_r;
    (a, b, r, &eq_op_leaf.0, &op_leaf.0)
}

#[test]
fn int_add_symbolic_never_materializes() {
    // A negative bignum whose eager numeral would be enormous.
    let a = Int::from(i128::MIN);
    let b = Int::from(-7i64);
    let sum = a.clone() + b.clone();

    let thm = int_add_thm_symbolic(a.clone(), b.clone()).expect("symbolic int.add");
    assert!(
        thm.sym_hyps().is_empty(),
        "certificates are hypothesis-free"
    );

    let (a_leaf, b_leaf, sum_leaf, eq_leaf, add_leaf) = destructure_int_bin(thm.sym_concl());
    assert_eq!(a_leaf, &a, "toHOL leaf a is the native Int");
    assert_eq!(b_leaf, &b, "toHOL leaf b is the native Int");
    assert_eq!(sum_leaf, &sum, "toHOL leaf sum = a + b, computed natively");

    assert_eq!(
        eq_leaf,
        &Term::eq_op(Type::int()),
        "materialized `= at int`"
    );
    assert_eq!(add_leaf, &defs::int_add(), "materialized `int.add`");
    assert_eq!(
        term_nodes(eq_leaf) + term_nodes(add_leaf),
        2,
        "O(1) footprint"
    );
}

#[test]
fn int_mul_symbolic_lands() {
    let thm = int_mul_thm_symbolic(Int::from(-6i64), Int::from(7i64)).expect("symbolic int.mul");
    let (a, b, r, _, op) = destructure_int_bin(thm.sym_concl());
    assert_eq!(a, &Int::from(-6i64));
    assert_eq!(b, &Int::from(7i64));
    assert_eq!(r, &Int::from(-42i64), "product computed natively");
    assert_eq!(op, &defs::int_mul(), "materialized `int.mul`");
}

// ===========================================================================
// int.neg — unary, `IntUnEqE`
// ===========================================================================

#[test]
fn int_neg_symbolic_lands() {
    let a = Int::from(i128::MIN);
    let thm = int_neg_thm_symbolic(a.clone()).expect("symbolic int.neg");

    let App(HolApp, (eq_applied, tohol_r)) = thm.sym_concl();
    let App(HolApp, (eq_op_leaf, lhs)) = eq_applied;
    let App(HolApp, (neg_leaf, tohol_a)) = lhs;
    let App(ToHolInt, Val(a_leaf)) = tohol_a;
    let App(ToHolInt, Val(r_leaf)) = tohol_r;

    assert_eq!(a_leaf, &a, "toHOL operand is the native Int");
    assert_eq!(r_leaf, &(-a.clone()), "negation computed natively");
    assert_eq!(&eq_op_leaf.0, &Term::eq_op(Type::int()));
    assert_eq!(&neg_leaf.0, &defs::int_neg(), "materialized `int.neg`");
    let _: &IntUnEqE = thm.sym_concl();
}

// ===========================================================================
// bytes.cat — binary, `BytesCatEqE` (the binary-substrate payoff)
// ===========================================================================

#[allow(clippy::type_complexity)]
fn destructure_bytes_cat(concl: &BytesCatEqE) -> (&Bytes, &Bytes, &Bytes, &Term, &Term) {
    let App(HolApp, (eq_applied, tohol_r)) = concl;
    let App(HolApp, (eq_op_leaf, lhs)) = eq_applied;
    let App(HolApp, (op_applied, tohol_b)) = lhs;
    let App(HolApp, (op_leaf, tohol_a)) = op_applied;
    let App(ToHolBytes, Val(a)) = tohol_a;
    let App(ToHolBytes, Val(b)) = tohol_b;
    let App(ToHolBytes, Val(r)) = tohol_r;
    (a, b, r, &eq_op_leaf.0, &op_leaf.0)
}

#[test]
fn bytes_cat_symbolic_megabyte_stays_a_native_leaf() {
    // A megabyte operand: the whole point is it stays a single native `Bytes`
    // leaf under `ToHolBytes`, never a cons-tower.
    let a = Bytes::from(vec![0xABu8; 1 << 20]);
    let b = Bytes::from(vec![0xCDu8; 1 << 20]);
    let mut cat_bytes = a.as_ref().to_vec();
    cat_bytes.extend_from_slice(b.as_ref());
    let cat = Bytes::from(cat_bytes);

    let thm = bytes_cat_thm_symbolic(a.clone(), b.clone()).expect("symbolic bytes.cat");
    assert!(thm.sym_hyps().is_empty());

    let (a_leaf, b_leaf, cat_leaf, eq_leaf, op_leaf) = destructure_bytes_cat(thm.sym_concl());
    assert_eq!(a_leaf, &a, "megabyte operand a is a native Bytes leaf");
    assert_eq!(b_leaf, &b, "megabyte operand b is a native Bytes leaf");
    assert_eq!(cat_leaf, &cat, "2 MB result is a native Bytes leaf");

    assert_eq!(
        eq_leaf,
        &Term::eq_op(Type::bytes()),
        "materialized `= at bytes`"
    );
    assert_eq!(op_leaf, &defs::bytes_cat(), "materialized `bytes.cat`");
    // The materialized-`Term` footprint is TWO nodes — independent of the 2 MB
    // of data held natively under `ToHolBytes`.
    assert_eq!(
        term_nodes(eq_leaf) + term_nodes(op_leaf),
        2,
        "O(1) footprint"
    );
}

// ===========================================================================
// bytes.len — mixed-sort, `BytesLenEqE` (ToHolBytes operand, ToHolNat result)
// ===========================================================================

#[test]
fn bytes_len_symbolic_mixed_sorts() {
    let bs = Bytes::from(vec![0u8; 1 << 20]);
    let thm = bytes_len_thm_symbolic(bs.clone()).expect("symbolic bytes.len");

    let App(HolApp, (eq_applied, tohol_len)) = thm.sym_concl();
    let App(HolApp, (eq_op_leaf, lhs)) = eq_applied;
    let App(HolApp, (len_leaf, tohol_bs)) = lhs;
    let App(ToHolBytes, Val(bs_leaf)) = tohol_bs;
    let App(ToHolNat, Val(len_leaf_val)) = tohol_len;

    assert_eq!(bs_leaf, &bs, "megabyte operand is a native Bytes leaf");
    assert_eq!(
        len_leaf_val,
        &Nat::from(1u32 << 20),
        "length computed natively (nat result)"
    );
    assert_eq!(
        &eq_op_leaf.0,
        &Term::eq_op(Type::nat()),
        "eq at the result sort `nat`"
    );
    assert_eq!(&len_leaf.0, &defs::bytes_len(), "materialized `bytes.len`");
    let _: &BytesLenEqE = thm.sym_concl();
}

// ===========================================================================
// SELF-FLOOR witnesses (WAVE-1 audit obligation): a concrete floored sibling
// (`int_arith_thm` / `bytes_thm` → from_pure → check_sequent) passing for the
// same input as the symbolic lander proves the symbolic conclusion is a
// well-typed HOL-bool sequent — i.e. each symbolic lander self-floors.
// ===========================================================================

#[test]
fn int_symbolic_landers_self_floor() {
    for (a, b) in [(0i64, 0i64), (5, -3), (-9, 4), (1_000_000, -7)] {
        let (a, b) = (Int::from(a), Int::from(b));
        // int.add
        int_arith_thm(
            defs::int_add_spec(),
            vec![Lit::Int(a.clone()), Lit::Int(b.clone())],
        )
        .expect("concrete int.add floors");
        int_add_thm_symbolic(a.clone(), b.clone()).expect("symbolic int.add");
        // int.mul
        int_arith_thm(
            defs::int_mul_spec(),
            vec![Lit::Int(a.clone()), Lit::Int(b.clone())],
        )
        .expect("concrete int.mul floors");
        int_mul_thm_symbolic(a.clone(), b.clone()).expect("symbolic int.mul");
        // int.neg
        int_arith_thm(defs::int_neg_spec(), vec![Lit::Int(a.clone())])
            .expect("concrete int.neg floors");
        int_neg_thm_symbolic(a.clone()).expect("symbolic int.neg");
    }
}

#[test]
fn bytes_symbolic_landers_self_floor() {
    for (a, b) in [
        (vec![], vec![]),
        (vec![1u8, 2, 3], vec![4u8, 5]),
        (vec![0xFFu8; 300], vec![0x00u8; 17]),
    ] {
        let (a, b) = (Bytes::from(a), Bytes::from(b));
        // bytes.cat
        bytes_thm(
            defs::bytes_cat_spec(),
            vec![Lit::Bytes(a.clone()), Lit::Bytes(b.clone())],
        )
        .expect("concrete bytes.cat floors");
        bytes_cat_thm_symbolic(a.clone(), b.clone()).expect("symbolic bytes.cat");
        // bytes.len
        bytes_thm(defs::bytes_len_spec(), vec![Lit::Bytes(a.clone())])
            .expect("concrete bytes.len floors");
        bytes_len_thm_symbolic(a.clone()).expect("symbolic bytes.len");
    }
}
