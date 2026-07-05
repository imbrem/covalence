//! Cert-path audit: closed-form computation via [`covalence_hol_eval::reduce`]
//! plus the surviving definitional unfolding (via [`delta`]), checked value-for-value against
//! the documented semantics of every op. This is the S8 port of the retired
//! in-kernel `covalence-core/tests/audit_reduce.rs` (which audited the
//! deleted legacy kernel reducer): the assertions are the SAME semantic
//! commitments — a
//! wrong reduction would mint a false equation, so a failing assert here is a
//! *soundness* finding against the family certificate rules / their
//! `covalence-pure-eval` computations.
//!
//! Coverage map (one or more tests each):
//!   nat: succ/pred(sat)/add/mul/sub(sat)/div(n/0=0)/mod(n%0=n)/
//!        pow(oversize-exp refusal)/le/lt/shl(oversize refusal, total on 0)/shr(total)/
//!        bitand/or/xor/to_int/to_bytes_{le,be}/from_bytes_{le,be}
//!   int: succ/pred/add/sub/mul/div(trunc, /0=0)/mod(%0=x)/neg/abs/
//!        sgn/le/lt
//!   bytes: cat/cons_nat(mod 256)/len/at(OOB=0)/slice(saturating)
//!   small int (uN/sN): add/sub/mul wrap, div/rem (signed & unsigned,
//!        /0=0), shl/shr (logical vs arithmetic, mod-width shift),
//!        and/or/xor/not/neg, cmp (signed vs unsigned), zext/sext,
//!        wrap, to_nat/to_int/from_nat/from_int
//!   HOL `=`: bool/nat/int/blob/small-int true & false; cross-kind and
//!        non-literal => refuse
//!   negative space: partial application / non-literal arg / wrong
//!        arity / wrong small-int tag => refuse
//!   delta (definitional unfolding): let-style => body; def-style => SpecIsDefStyle;
//!        declaration-only => SpecHasNoBody; non-spec => NotASpec
//!   ADVERSARIAL cert audit: wrong-shaped inputs fed straight to the
//!        admitted rules (fake specs, wrong families, mixed literal
//!        kinds) must not mint.

use covalence_core::seam::Lit;
use covalence_core::{IntTag, Term, TermKind, Type};
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::IntOp;
use covalence_hol_eval::rules::{BytesCert, FixedWidthCert, IntArithCert, LitEqCert, NatArithCert};
use covalence_hol_eval::{CoreEval, EvalThm as Thm, delta, mk_blob, mk_int, mk_nat, reduce};
use covalence_pure::apply;
use covalence_types::Nat;

// ============================================================================
// Helpers
// ============================================================================

fn nat(n: u64) -> Term {
    mk_nat(Nat::from(n))
}

fn nat_big(n: Nat) -> Term {
    mk_nat(n)
}

fn int(n: i64) -> Term {
    mk_int(n as i128)
}

fn blob(bytes: Vec<u8>) -> Term {
    mk_blob(bytes)
}

fn app1(f: Term, a: Term) -> Term {
    Term::app(f, a)
}

fn app2(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

fn app3(f: Term, a: Term, b: Term, c: Term) -> Term {
    Term::app(Term::app(Term::app(f, a), b), c)
}

/// Run the cert-path `reduce` and assert it yields `⊢ t = want` (HOL eq).
fn assert_reduces(t: Term, want: Term) {
    let thm = reduce(&t).unwrap_or_else(|| panic!("reduce refused {t:?}"));
    assert!(thm.hyps().is_empty(), "cert facts are hypothesis-free");
    let TermKind::App(eq_lhs_app, rhs) = thm.concl().kind() else {
        panic!("concl is not an App: {:?}", thm.concl());
    };
    let TermKind::App(eq_op, lhs) = eq_lhs_app.kind() else {
        panic!("concl LHS is not an App: {:?}", thm.concl());
    };
    assert!(
        matches!(eq_op.kind(), TermKind::Eq(_)),
        "concl head is not HOL =: {:?}",
        thm.concl()
    );
    assert_eq!(lhs, &t, "LHS mismatch for {t:?}");
    assert_eq!(rhs, &want, "RHS mismatch for {t:?}");
}

/// Assert the cert path refuses to reduce `t`.
fn assert_no_reduce(t: Term) {
    assert!(
        reduce(&t).is_none(),
        "expected NO reduction for {t:?}, but it reduced"
    );
}

/// HOL `=` op applied to two terms, with `α` inferred from `lhs`.
fn hol_eq(lhs: Term, rhs: Term) -> Term {
    let alpha = lhs.type_of().expect("hol_eq lhs must be well-typed");
    Term::app(Term::app(Term::eq_op(alpha), lhs), rhs)
}

// ============================================================================
// nat: constructors & saturation
// ============================================================================

#[test]
fn nat_succ() {
    assert_reduces(app1(defs::nat_succ(), nat(0)), nat(1));
    assert_reduces(app1(defs::nat_succ(), nat(41)), nat(42));
    // The primitive `succ` leaf reduces too (SuccCert).
    assert_reduces(app1(Term::succ(), nat(7)), nat(8));
}

#[test]
fn nat_pred_saturates_at_zero() {
    assert_reduces(app1(defs::nat_pred(), nat(0)), nat(0));
    assert_reduces(app1(defs::nat_pred(), nat(1)), nat(0));
    assert_reduces(app1(defs::nat_pred(), nat(100)), nat(99));
}

// ============================================================================
// nat: arithmetic
// ============================================================================

#[test]
fn nat_add() {
    assert_reduces(app2(defs::nat_add(), nat(0), nat(0)), nat(0));
    assert_reduces(app2(defs::nat_add(), nat(3), nat(4)), nat(7));
    assert_reduces(app2(defs::nat_add(), nat(0), nat(9)), nat(9));
}

#[test]
fn nat_mul() {
    assert_reduces(app2(defs::nat_mul(), nat(0), nat(99)), nat(0));
    assert_reduces(app2(defs::nat_mul(), nat(6), nat(7)), nat(42));
}

#[test]
fn nat_sub_saturates() {
    assert_reduces(app2(defs::nat_sub(), nat(10), nat(3)), nat(7));
    assert_reduces(app2(defs::nat_sub(), nat(3), nat(3)), nat(0));
    // Saturation: 2 - 5 = 0 (NOT a wrap to a huge nat).
    assert_reduces(app2(defs::nat_sub(), nat(2), nat(5)), nat(0));
    assert_reduces(app2(defs::nat_sub(), nat(0), nat(1)), nat(0));
}

#[test]
fn nat_div_zero_is_zero() {
    // n / 0 = 0 (kernel convention).
    assert_reduces(app2(defs::nat_div(), nat(10), nat(0)), nat(0));
    assert_reduces(app2(defs::nat_div(), nat(0), nat(0)), nat(0));
    // Truncating division.
    assert_reduces(app2(defs::nat_div(), nat(17), nat(5)), nat(3));
    assert_reduces(app2(defs::nat_div(), nat(20), nat(4)), nat(5));
}

#[test]
fn nat_mod_by_zero_is_identity() {
    // n % 0 = n (Euclidean convention). This value is FORCED by
    // soundness: `nat.mod` has a let-style body `λn m. n - (n/m)*m`,
    // which at m=0 (with n/0=0) is `n - 0 = n`. If the certificate gave
    // 0 here, definitional unfolding + the cert path would derive `n = 0`
    // for any n. See `audit_reduce_matches_body` for the regression guard.
    assert_reduces(app2(defs::nat_mod(), nat(10), nat(0)), nat(10));
    assert_reduces(app2(defs::nat_mod(), nat(0), nat(0)), nat(0));
    assert_reduces(app2(defs::nat_mod(), nat(17), nat(5)), nat(2));
    assert_reduces(app2(defs::nat_mod(), nat(20), nat(4)), nat(0));
}

#[test]
fn nat_div_reduction_satisfies_its_selector_predicate() {
    // SOUNDNESS GUARD for the def-style `nat.div`. `nat.div` carries the
    // selector predicate
    //   λd. ∀n m. (m=0 ⟹ d n m = 0) ∧
    //             (¬(m=0) ⟹ d n m * m ≤ n ∧ n < S(d n m) * m)
    // and `spec_ax` only stays consistent with the certificate reduction
    // if the *reduction itself* satisfies that predicate (otherwise the
    // kernel has no model — nat.div cannot be both the floor and a
    // predicate-satisfier). Here we evaluate each predicate clause on the
    // reduced `q = n / m` and assert it holds, across a wide range of
    // (n, m) — every quotient/divisor shape including the boundaries
    // n < m, n = q*m exactly, and m = 0.
    let red = |t: Term| rhs_of(&reduce(&t).expect("reduces"));
    let t = || Term::bool_lit(true);
    let mut probes: Vec<(u64, u64)> = Vec::new();
    for n in [0u64, 1, 2, 3, 5, 7, 10, 16, 17, 23, 24, 100, 255, 1000] {
        for m in [0u64, 1, 2, 3, 4, 5, 7, 8, 16, 100, 256] {
            probes.push((n, m));
        }
    }
    for (n, m) in probes {
        let q = red(app2(defs::nat_div(), nat(n), nat(m)));
        if m == 0 {
            // clause 1: m = 0 ⟹ d n m = 0.
            assert_eq!(q, nat(0), "n/0 must reduce to 0 (n={n})");
            continue;
        }
        // clause 2a: q * m ≤ n.
        let lower = red(app2(
            defs::nat_le(),
            red(app2(defs::nat_mul(), q.clone(), nat(m))),
            nat(n),
        ));
        assert_eq!(lower, t(), "q*m ≤ n fails at n={n}, m={m} (q={q:?})");
        // clause 2b: n < S(q) * m.
        let sq = red(app1(defs::nat_succ(), q.clone()));
        let sq_m = red(app2(defs::nat_mul(), sq, nat(m)));
        let upper = red(app2(defs::nat_lt(), nat(n), sq_m));
        assert_eq!(upper, t(), "n < S(q)*m fails at n={n}, m={m} (q={q:?})");
    }
}

#[test]
fn nat_div_mod_satisfy_euclidean_law() {
    // The div/mod certificate reductions must jointly satisfy the Euclidean
    // division law: for all n, m,  n = (n / m) * m + (n mod m),  and for
    // m > 0 the remainder is bounded, 0 ≤ n mod m < m. This is exactly
    // the def-style selector predicate `nat_div_predicate` characterises,
    // checked here on the closed-literal reduction.
    let red = |t: Term| rhs_of(&reduce(&t).expect("reduces"));
    for (n, m) in [
        (0u64, 0u64),
        (0, 1),
        (1, 0),
        (17, 5),
        (20, 4),
        (3, 7),
        (1, 1),
        (100, 7),
        (255, 16),
        (42, 1),
    ] {
        let q = red(app2(defs::nat_div(), nat(n), nat(m))); // n / m
        let r = red(app2(defs::nat_mod(), nat(n), nat(m))); // n mod m
        // (n/m)*m + (n mod m)  ==  n   (reduce innermost-first; one step each)
        let qm = red(app2(defs::nat_mul(), q, nat(m)));
        let recombined = red(app2(defs::nat_add(), qm, r.clone()));
        assert_eq!(
            recombined,
            nat(n),
            "Euclidean identity fails at n={n}, m={m}"
        );
        // m > 0 ⟹ n mod m < m.
        if m != 0 {
            let bounded = red(app2(defs::nat_lt(), r, nat(m)));
            assert_eq!(
                bounded,
                Term::bool_lit(true),
                "remainder not < divisor at n={n}, m={m}"
            );
        }
    }
}

#[test]
fn nat_pow() {
    assert_reduces(app2(defs::nat_pow(), nat(2), nat(0)), nat(1));
    assert_reduces(app2(defs::nat_pow(), nat(0), nat(0)), nat(1));
    assert_reduces(app2(defs::nat_pow(), nat(2), nat(10)), nat(1024));
    assert_reduces(app2(defs::nat_pow(), nat(0), nat(5)), nat(0));
    assert_reduces(app2(defs::nat_pow(), nat(5), nat(1)), nat(5));
}

#[test]
fn nat_pow_oversize_exponent_refuses() {
    // Exponent that does not fit in a single u32 digit: must NOT reduce
    // (would otherwise produce an astronomically large literal / panic).
    let huge_exp = Nat::from_inner((u64::from(u32::MAX) + 1).into());
    assert_no_reduce(app2(defs::nat_pow(), nat(2), nat_big(huge_exp)));
}

#[test]
fn nat_le_lt() {
    assert_reduces(app2(defs::nat_le(), nat(3), nat(5)), Term::bool_lit(true));
    assert_reduces(app2(defs::nat_le(), nat(5), nat(5)), Term::bool_lit(true));
    assert_reduces(app2(defs::nat_le(), nat(7), nat(5)), Term::bool_lit(false));
    assert_reduces(app2(defs::nat_lt(), nat(3), nat(5)), Term::bool_lit(true));
    assert_reduces(app2(defs::nat_lt(), nat(5), nat(5)), Term::bool_lit(false));
    assert_reduces(app2(defs::nat_lt(), nat(7), nat(5)), Term::bool_lit(false));
}

// ============================================================================
// nat: bitwise / shifts
// ============================================================================

#[test]
fn nat_shl_shr() {
    assert_reduces(app2(defs::nat_shl(), nat(1), nat(0)), nat(1));
    assert_reduces(app2(defs::nat_shl(), nat(1), nat(4)), nat(16));
    assert_reduces(app2(defs::nat_shl(), nat(3), nat(2)), nat(12));
    assert_reduces(app2(defs::nat_shr(), nat(16), nat(2)), nat(4));
    assert_reduces(app2(defs::nat_shr(), nat(1), nat(4)), nat(0));
    assert_reduces(app2(defs::nat_shr(), nat(255), nat(0)), nat(255));
}

#[test]
fn nat_shl_oversize_shift_refuses() {
    // Shift count exceeding one u64 digit on a NON-ZERO operand: the true
    // result needs ≥ 2^64 bits (unrepresentable), so the cert REFUSES (`None`)
    // rather than clamp/truncate the shift.
    let huge_shift = Nat::from_inner((u128::from(u64::MAX) + 1).into());
    assert_no_reduce(app2(defs::nat_shl(), nat(1), nat_big(huge_shift)));
}

#[test]
fn nat_shl_zero_and_shr_are_total_over_oversize_shift() {
    // No cert clamps a `Nat`: `0 << huge = 0` and `a >> huge = 0` are the
    // true answers, so they REDUCE (never refuse) even for an over-usize
    // shift — the total counterpart of the `shl` refusal above.
    let huge_shift = Nat::from_inner((u128::from(u64::MAX) + 1).into());
    assert_reduces(
        app2(defs::nat_shl(), nat(0), nat_big(huge_shift.clone())),
        nat(0),
    );
    assert_reduces(app2(defs::nat_shr(), nat(5), nat_big(huge_shift)), nat(0));
}

#[test]
fn nat_shl_cert_refuses_or_reduces_by_representability() {
    // Straight to the admitted `NatArithCert`: an oversize LEFT shift on a
    // non-zero operand REFUSES (unrepresentable), but the same shift on `0`
    // now SUCCEEDS (`0 << s = 0` is total) — the base-TCB fallibility change.
    let huge = Nat::from(u64::MAX) + Nat::from(1u32);
    let shl = defs::nat_shl_spec();
    assert!(
        apply(
            CoreEval,
            NatArithCert,
            (shl.clone(), vec![lnat(1), Lit::Nat(huge.clone())])
        )
        .is_err(),
        "1 << huge is unrepresentable ⇒ cert must refuse"
    );
    assert!(
        apply(CoreEval, NatArithCert, (shl, vec![lnat(0), Lit::Nat(huge)])).is_ok(),
        "0 << huge = 0 is total ⇒ cert must succeed"
    );
}

#[test]
fn nat_bitwise() {
    assert_reduces(
        app2(defs::nat_bit_and(), nat(0b1100), nat(0b1010)),
        nat(0b1000),
    );
    assert_reduces(
        app2(defs::nat_bit_or(), nat(0b1100), nat(0b1010)),
        nat(0b1110),
    );
    assert_reduces(
        app2(defs::nat_bit_xor(), nat(0b1100), nat(0b1010)),
        nat(0b0110),
    );
    assert_reduces(app2(defs::nat_bit_and(), nat(0xFF), nat(0)), nat(0));
}

// ============================================================================
// nat <-> int / bytes
// ============================================================================

#[test]
fn nat_to_int() {
    assert_reduces(app1(defs::nat_to_int(), nat(0)), int(0));
    assert_reduces(app1(defs::nat_to_int(), nat(42)), int(42));
}

#[test]
fn nat_to_bytes_round_trips() {
    // 0 -> a single zero byte (BigUint::to_bytes_* convention: zero
    // encodes as [0], not the empty string). Not a soundness issue:
    // from_bytes_le([0]) round-trips back to 0.
    assert_reduces(app1(defs::nat_to_bytes_le(), nat(0)), blob(vec![0]));
    assert_reduces(app1(defs::nat_to_bytes_be(), nat(0)), blob(vec![0]));
    // 256 = 0x0100: LE = [0,1], BE = [1,0].
    assert_reduces(app1(defs::nat_to_bytes_le(), nat(256)), blob(vec![0, 1]));
    assert_reduces(app1(defs::nat_to_bytes_be(), nat(256)), blob(vec![1, 0]));
    // from_bytes inverse.
    assert_reduces(app1(defs::nat_from_bytes_le(), blob(vec![0, 1])), nat(256));
    assert_reduces(app1(defs::nat_from_bytes_be(), blob(vec![1, 0])), nat(256));
    // Empty blob decodes to 0.
    assert_reduces(app1(defs::nat_from_bytes_le(), blob(vec![])), nat(0));
    assert_reduces(app1(defs::nat_from_bytes_be(), blob(vec![])), nat(0));
}

// ============================================================================
// int arithmetic
// ============================================================================

#[test]
fn int_succ_pred() {
    assert_reduces(app1(defs::int_succ(), int(-1)), int(0));
    assert_reduces(app1(defs::int_succ(), int(5)), int(6));
    assert_reduces(app1(defs::int_pred(), int(0)), int(-1));
    assert_reduces(app1(defs::int_pred(), int(-5)), int(-6));
}

#[test]
fn int_add_sub_mul() {
    assert_reduces(app2(defs::int_add(), int(-3), int(4)), int(1));
    assert_reduces(app2(defs::int_add(), int(-3), int(-4)), int(-7));
    assert_reduces(app2(defs::int_sub(), int(3), int(7)), int(-4));
    assert_reduces(app2(defs::int_sub(), int(-3), int(-7)), int(4));
    assert_reduces(app2(defs::int_mul(), int(-2), int(-3)), int(6));
    assert_reduces(app2(defs::int_mul(), int(-2), int(3)), int(-6));
    assert_reduces(app2(defs::int_mul(), int(0), int(99)), int(0));
}

#[test]
fn int_div_truncates_toward_zero_and_zero_divisor() {
    assert_reduces(app2(defs::int_div(), int(17), int(5)), int(3));
    // Truncation toward zero, not floor.
    assert_reduces(app2(defs::int_div(), int(-17), int(5)), int(-3));
    assert_reduces(app2(defs::int_div(), int(17), int(-5)), int(-3));
    assert_reduces(app2(defs::int_div(), int(-17), int(-5)), int(3));
    // /0 = 0.
    assert_reduces(app2(defs::int_div(), int(17), int(0)), int(0));
    assert_reduces(app2(defs::int_div(), int(-17), int(0)), int(0));
}

#[test]
fn int_mod_and_zero_divisor() {
    assert_reduces(app2(defs::int_mod(), int(17), int(5)), int(2));
    // Sign of remainder follows the dividend (truncating rem).
    assert_reduces(app2(defs::int_mod(), int(-17), int(5)), int(-2));
    assert_reduces(app2(defs::int_mod(), int(17), int(-5)), int(2));
    // x mod 0 = x (Euclidean identity, matching `int.mod`'s body; see
    // `audit_reduce_matches_body`). A result of 0 would contradict the body
    // `x − (x/y)·y`.
    assert_reduces(app2(defs::int_mod(), int(17), int(0)), int(17));
    assert_reduces(app2(defs::int_mod(), int(-17), int(0)), int(-17));
}

#[test]
fn int_neg_abs_sgn() {
    assert_reduces(app1(defs::int_neg(), int(7)), int(-7));
    assert_reduces(app1(defs::int_neg(), int(-7)), int(7));
    assert_reduces(app1(defs::int_neg(), int(0)), int(0));
    // abs : int -> nat.
    assert_reduces(app1(defs::int_abs(), int(-12)), nat(12));
    assert_reduces(app1(defs::int_abs(), int(12)), nat(12));
    assert_reduces(app1(defs::int_abs(), int(0)), nat(0));
    // sgn : int -> int.
    assert_reduces(app1(defs::int_sgn(), int(-9)), int(-1));
    assert_reduces(app1(defs::int_sgn(), int(0)), int(0));
    assert_reduces(app1(defs::int_sgn(), int(9)), int(1));
}

#[test]
fn int_le_lt() {
    assert_reduces(app2(defs::int_le(), int(-3), int(2)), Term::bool_lit(true));
    assert_reduces(app2(defs::int_le(), int(2), int(2)), Term::bool_lit(true));
    assert_reduces(app2(defs::int_le(), int(2), int(-3)), Term::bool_lit(false));
    assert_reduces(app2(defs::int_lt(), int(-3), int(2)), Term::bool_lit(true));
    assert_reduces(app2(defs::int_lt(), int(2), int(2)), Term::bool_lit(false));
}

// ============================================================================
// bytes
// ============================================================================

#[test]
fn bytes_cat() {
    assert_reduces(
        app2(defs::bytes_cat(), blob(vec![1, 2]), blob(vec![3, 4, 5])),
        blob(vec![1, 2, 3, 4, 5]),
    );
    assert_reduces(
        app2(defs::bytes_cat(), blob(vec![]), blob(vec![9])),
        blob(vec![9]),
    );
    assert_reduces(
        app2(defs::bytes_cat(), blob(vec![9]), blob(vec![])),
        blob(vec![9]),
    );
}

#[test]
fn bytes_cons_nat_mod_256() {
    // Byte operand reduced mod 256.
    assert_reduces(
        app2(defs::bytes_cons_nat(), nat(0), blob(vec![9])),
        blob(vec![0, 9]),
    );
    assert_reduces(
        app2(defs::bytes_cons_nat(), nat(255), blob(vec![])),
        blob(vec![255]),
    );
    // 256 mod 256 = 0.
    assert_reduces(
        app2(defs::bytes_cons_nat(), nat(256), blob(vec![9])),
        blob(vec![0, 9]),
    );
    // 257 mod 256 = 1.
    assert_reduces(
        app2(defs::bytes_cons_nat(), nat(257), blob(vec![9])),
        blob(vec![1, 9]),
    );
    // Large nat reduced mod 256: 0x12345 & 0xFF = 0x45.
    assert_reduces(
        app2(defs::bytes_cons_nat(), nat(0x12345), blob(vec![])),
        blob(vec![0x45]),
    );
}

#[test]
fn bytes_len() {
    assert_reduces(app1(defs::bytes_len(), blob(vec![])), nat(0));
    assert_reduces(app1(defs::bytes_len(), blob(vec![1, 2, 3])), nat(3));
}

#[test]
fn bytes_at_in_bounds_and_oob() {
    assert_reduces(app2(defs::bytes_at(), blob(vec![7, 8, 9]), nat(0)), nat(7));
    assert_reduces(app2(defs::bytes_at(), blob(vec![7, 8, 9]), nat(2)), nat(9));
    // Out of bounds index => 0.
    assert_reduces(app2(defs::bytes_at(), blob(vec![7, 8, 9]), nat(3)), nat(0));
    assert_reduces(app2(defs::bytes_at(), blob(vec![7, 8, 9]), nat(99)), nat(0));
    // Index beyond usize (multi-digit nat) => MAX => OOB => 0.
    let huge = Nat::from_inner((u128::from(u64::MAX) + 1).into());
    assert_reduces(
        app2(defs::bytes_at(), blob(vec![7, 8, 9]), nat_big(huge)),
        nat(0),
    );
    // Empty blob, any index => 0.
    assert_reduces(app2(defs::bytes_at(), blob(vec![]), nat(0)), nat(0));
}

#[test]
fn bytes_slice_saturates() {
    let bs = || blob(vec![10, 20, 30, 40, 50]);
    assert_reduces(
        app3(defs::bytes_slice(), bs(), nat(1), nat(3)),
        blob(vec![20, 30, 40]),
    );
    // Length runs past end: saturates to remaining bytes.
    assert_reduces(
        app3(defs::bytes_slice(), bs(), nat(3), nat(100)),
        blob(vec![40, 50]),
    );
    // Start at/past end: empty.
    assert_reduces(
        app3(defs::bytes_slice(), bs(), nat(5), nat(3)),
        blob(vec![]),
    );
    assert_reduces(
        app3(defs::bytes_slice(), bs(), nat(99), nat(3)),
        blob(vec![]),
    );
    // Zero length: empty.
    assert_reduces(
        app3(defs::bytes_slice(), bs(), nat(1), nat(0)),
        blob(vec![]),
    );
    // Whole thing.
    assert_reduces(
        app3(defs::bytes_slice(), bs(), nat(0), nat(5)),
        blob(vec![10, 20, 30, 40, 50]),
    );
}

// ============================================================================
// Fixed-width integer ops
// ============================================================================

fn intop(tag: IntTag, op: IntOp) -> Term {
    defs::int_op(tag, op)
}

#[test]
fn small_int_add_sub_mul_wrap() {
    use IntOp::*;
    // u8: 200 + 100 = 300 = 44 (mod 256).
    assert_reduces(
        app2(intop(IntTag::U8, Add), Term::u8_lit(200), Term::u8_lit(100)),
        Term::u8_lit(44),
    );
    // u8: 5 - 8 = -3 = 253 (mod 256).
    assert_reduces(
        app2(intop(IntTag::U8, Sub), Term::u8_lit(5), Term::u8_lit(8)),
        Term::u8_lit(253),
    );
    // u8: 20 * 20 = 400 = 144 (mod 256).
    assert_reduces(
        app2(intop(IntTag::U8, Mul), Term::u8_lit(20), Term::u8_lit(20)),
        Term::u8_lit(144),
    );
    // s8: signed wrap on overflow: 127 + 1 = -128.
    assert_reduces(
        app2(intop(IntTag::S8, Add), Term::s8_lit(127), Term::s8_lit(1)),
        Term::s8_lit(-128),
    );
    // u16 / u32 / u64 wrap.
    assert_reduces(
        app2(
            intop(IntTag::U16, Add),
            Term::u16_lit(0xFFFF),
            Term::u16_lit(1),
        ),
        Term::u16_lit(0),
    );
    assert_reduces(
        app2(
            intop(IntTag::U32, Add),
            Term::u32_lit(u32::MAX),
            Term::u32_lit(1),
        ),
        Term::u32_lit(0),
    );
    assert_reduces(
        app2(
            intop(IntTag::U64, Mul),
            Term::u64_lit(u64::MAX),
            Term::u64_lit(2),
        ),
        Term::u64_lit(u64::MAX.wrapping_mul(2)),
    );
}

#[test]
fn small_int_div_rem_unsigned() {
    use IntOp::*;
    assert_reduces(
        app2(intop(IntTag::U8, Div), Term::u8_lit(200), Term::u8_lit(7)),
        Term::u8_lit(28),
    );
    assert_reduces(
        app2(intop(IntTag::U8, Rem), Term::u8_lit(200), Term::u8_lit(7)),
        Term::u8_lit(4),
    );
    // Div by zero => 0; Rem by zero => the dividend (Euclidean `x rem 0 =
    // x`, matching the let-style body — see `audit_reduce_matches_body`).
    assert_reduces(
        app2(intop(IntTag::U8, Div), Term::u8_lit(5), Term::u8_lit(0)),
        Term::u8_lit(0),
    );
    assert_reduces(
        app2(intop(IntTag::U8, Rem), Term::u8_lit(5), Term::u8_lit(0)),
        Term::u8_lit(5),
    );
}

#[test]
fn small_int_div_rem_signed() {
    use IntOp::*;
    // -7 / 2 = -3 (truncating toward zero).
    assert_reduces(
        app2(intop(IntTag::S8, Div), Term::s8_lit(-7), Term::s8_lit(2)),
        Term::s8_lit(-3),
    );
    // -7 % 2 = -1 (truncating rem; sign of dividend).
    assert_reduces(
        app2(intop(IntTag::S8, Rem), Term::s8_lit(-7), Term::s8_lit(2)),
        Term::s8_lit(-1),
    );
    assert_reduces(
        app2(intop(IntTag::S8, Div), Term::s8_lit(7), Term::s8_lit(-2)),
        Term::s8_lit(-3),
    );
    // Signed div by zero => 0; rem by zero => the dividend.
    assert_reduces(
        app2(intop(IntTag::S8, Div), Term::s8_lit(-5), Term::s8_lit(0)),
        Term::s8_lit(0),
    );
    assert_reduces(
        app2(intop(IntTag::S8, Rem), Term::s8_lit(-5), Term::s8_lit(0)),
        Term::s8_lit(-5),
    );
}

#[test]
fn small_int_shifts() {
    use IntOp::*;
    // Unsigned logical right shift: 0x80 >> 1 = 0x40.
    assert_reduces(
        app2(intop(IntTag::U8, Shr), Term::u8_lit(0x80), Term::u8_lit(1)),
        Term::u8_lit(0x40),
    );
    // Signed arithmetic right shift: -8 >> 1 = -4.
    assert_reduces(
        app2(intop(IntTag::S8, Shr), Term::s8_lit(-8), Term::s8_lit(1)),
        Term::s8_lit(-4),
    );
    // -1 >> 7 = -1 (sign bit replicated).
    assert_reduces(
        app2(intop(IntTag::S8, Shr), Term::s8_lit(-1), Term::s8_lit(7)),
        Term::s8_lit(-1),
    );
    // Left shift wraps within width: u8 1 << 8 -> shift count is taken
    // mod width (8 % 8 = 0), so result is 1.
    assert_reduces(
        app2(intop(IntTag::U8, Shl), Term::u8_lit(1), Term::u8_lit(8)),
        Term::u8_lit(1),
    );
    // 1 << 7 = 0x80.
    assert_reduces(
        app2(intop(IntTag::U8, Shl), Term::u8_lit(1), Term::u8_lit(7)),
        Term::u8_lit(0x80),
    );
}

#[test]
fn small_int_bitwise() {
    use IntOp::*;
    assert_reduces(
        app2(
            intop(IntTag::U8, And),
            Term::u8_lit(0b1100),
            Term::u8_lit(0b1010),
        ),
        Term::u8_lit(0b1000),
    );
    assert_reduces(
        app2(
            intop(IntTag::U8, Or),
            Term::u8_lit(0b1100),
            Term::u8_lit(0b1010),
        ),
        Term::u8_lit(0b1110),
    );
    assert_reduces(
        app2(
            intop(IntTag::U8, Xor),
            Term::u8_lit(0b1100),
            Term::u8_lit(0b1010),
        ),
        Term::u8_lit(0b0110),
    );
    // Unary not / neg.
    assert_reduces(
        app1(intop(IntTag::U8, Not), Term::u8_lit(0)),
        Term::u8_lit(255),
    );
    assert_reduces(
        app1(intop(IntTag::U8, Neg), Term::u8_lit(1)),
        Term::u8_lit(255),
    );
    // Signed neg with overflow: -(-128) wraps to -128 in s8.
    assert_reduces(
        app1(intop(IntTag::S8, Neg), Term::s8_lit(-128)),
        Term::s8_lit(-128),
    );
}

#[test]
fn small_int_compare_signed_vs_unsigned() {
    use IntOp::*;
    // unsigned: 200 < 100 is false.
    assert_reduces(
        app2(intop(IntTag::U8, Lt), Term::u8_lit(200), Term::u8_lit(100)),
        Term::bool_lit(false),
    );
    // signed: -1 < 1 is true (same bits as 0xFF < 0x01, false unsigned).
    assert_reduces(
        app2(intop(IntTag::S8, Lt), Term::s8_lit(-1), Term::s8_lit(1)),
        Term::bool_lit(true),
    );
    assert_reduces(
        app2(intop(IntTag::U8, Le), Term::u8_lit(5), Term::u8_lit(5)),
        Term::bool_lit(true),
    );
    assert_reduces(
        app2(intop(IntTag::U8, Gt), Term::u8_lit(200), Term::u8_lit(100)),
        Term::bool_lit(true),
    );
    assert_reduces(
        app2(intop(IntTag::S8, Ge), Term::s8_lit(-1), Term::s8_lit(0)),
        Term::bool_lit(false),
    );
}

#[test]
fn small_int_zext_sext_wrap() {
    // zext u8 -> u32 (zero extend).
    assert_reduces(
        app1(defs::int_zext(IntTag::U8, IntTag::U32), Term::u8_lit(200)),
        Term::u32_lit(200),
    );
    // zext as wrap (narrowing): u32 0x1FF -> u8 0xFF.
    assert_reduces(
        app1(
            defs::int_zext(IntTag::U32, IntTag::U8),
            Term::u32_lit(0x1FF),
        ),
        Term::u8_lit(0xFF),
    );
    // sext s8 -> s32 of a negative.
    assert_reduces(
        app1(defs::int_sext(IntTag::S8, IntTag::S32), Term::s8_lit(-1)),
        Term::s32_lit(-1),
    );
    assert_reduces(
        app1(defs::int_sext(IntTag::S8, IntTag::S32), Term::s8_lit(-128)),
        Term::s32_lit(-128),
    );
}

#[test]
fn small_int_nat_int_casts() {
    // toNat (unsigned value of bits).
    assert_reduces(
        app1(defs::int_to_nat(IntTag::U8), Term::u8_lit(200)),
        nat(200),
    );
    // toNat on signed reads the *unsigned* bit value: s8 -1 = 0xFF = 255.
    assert_reduces(
        app1(defs::int_to_nat(IntTag::S8), Term::s8_lit(-1)),
        nat(255),
    );
    // toInt (signed value for sN).
    assert_reduces(
        app1(defs::int_to_int(IntTag::S8), Term::s8_lit(-5)),
        int(-5),
    );
    assert_reduces(
        app1(defs::int_to_int(IntTag::U8), Term::u8_lit(200)),
        int(200),
    );
    // fromNat wraps mod 2^width.
    assert_reduces(
        app1(defs::int_from_nat(IntTag::U8), nat(300)),
        Term::u8_lit(44),
    );
    assert_reduces(
        app1(defs::int_from_nat(IntTag::U8), nat(255)),
        Term::u8_lit(255),
    );
    // fromInt two's complement.
    assert_reduces(
        app1(defs::int_from_int(IntTag::S8), int(-1)),
        Term::s8_lit(-1),
    );
    assert_reduces(
        app1(defs::int_from_int(IntTag::U8), int(-1)),
        Term::u8_lit(255),
    );
    assert_reduces(
        app1(defs::int_from_int(IntTag::S8), int(-128)),
        Term::s8_lit(-128),
    );
    // fromInt wrap of an out-of-range positive: 256 -> 0 (u8).
    assert_reduces(
        app1(defs::int_from_int(IntTag::U8), int(256)),
        Term::u8_lit(0),
    );
}

#[test]
fn small_int_wrong_tag_refuses() {
    use IntOp::*;
    // u8.add applied to u16 literals: tag mismatch => no reduction.
    assert_no_reduce(app2(
        intop(IntTag::U8, Add),
        Term::u16_lit(1),
        Term::u16_lit(2),
    ));
    // Mixed tags.
    assert_no_reduce(app2(
        intop(IntTag::U8, Add),
        Term::u8_lit(1),
        Term::u16_lit(2),
    ));
    // u8.toNat applied to s8 literal: src tag mismatch.
    assert_no_reduce(app1(defs::int_to_nat(IntTag::U8), Term::s8_lit(1)));
    // zext src tag mismatch.
    assert_no_reduce(app1(
        defs::int_zext(IntTag::U8, IntTag::U32),
        Term::u16_lit(1),
    ));
}

// ============================================================================
// HOL `=` on closed literals
// ============================================================================

#[test]
fn hol_eq_bool() {
    assert_reduces(
        hol_eq(Term::bool_lit(true), Term::bool_lit(true)),
        Term::bool_lit(true),
    );
    assert_reduces(
        hol_eq(Term::bool_lit(false), Term::bool_lit(false)),
        Term::bool_lit(true),
    );
    assert_reduces(
        hol_eq(Term::bool_lit(true), Term::bool_lit(false)),
        Term::bool_lit(false),
    );
}

#[test]
fn hol_eq_nat() {
    assert_reduces(hol_eq(nat(5), nat(5)), Term::bool_lit(true));
    assert_reduces(hol_eq(nat(0), nat(0)), Term::bool_lit(true));
    assert_reduces(hol_eq(nat(0), nat(5)), Term::bool_lit(false));
}

#[test]
fn hol_eq_int() {
    assert_reduces(hol_eq(int(-3), int(-3)), Term::bool_lit(true));
    assert_reduces(hol_eq(int(-3), int(3)), Term::bool_lit(false));
    assert_reduces(hol_eq(int(0), int(0)), Term::bool_lit(true));
}

#[test]
fn hol_eq_blob() {
    assert_reduces(
        hol_eq(blob(vec![1, 2]), blob(vec![1, 2])),
        Term::bool_lit(true),
    );
    assert_reduces(hol_eq(blob(vec![]), blob(vec![])), Term::bool_lit(true));
    assert_reduces(
        hol_eq(blob(vec![1, 2]), blob(vec![3])),
        Term::bool_lit(false),
    );
}

#[test]
fn hol_eq_small_int() {
    assert_reduces(
        hol_eq(Term::u8_lit(200), Term::u8_lit(200)),
        Term::bool_lit(true),
    );
    assert_reduces(
        hol_eq(Term::u8_lit(200), Term::u8_lit(201)),
        Term::bool_lit(false),
    );
    assert_reduces(
        hol_eq(Term::s64_lit(-1), Term::s64_lit(-1)),
        Term::bool_lit(true),
    );
}

#[test]
fn hol_eq_non_literal_refuses() {
    // RHS is a free variable.
    let n = Term::free("n", Type::nat());
    assert_no_reduce(hol_eq(nat(5), n));
    // Both sides non-literal.
    let a = Term::free("a", Type::nat());
    let b = Term::free("b", Type::nat());
    assert_no_reduce(hol_eq(a, b));
}

#[test]
fn hol_eq_ill_typed_operands_refuse_without_panic() {
    // `Eq(nat)` applied to two `bool` literals is ILL-TYPED (the eq
    // operator wants `nat` operands). The `Lit` recognizer matches the
    // `(Bool, Bool)` shape, so without the `type_of` guard in `reduce`
    // the cert path would rebuild a *repaired* equation instead of
    // mirroring the ill-typed one. It must refuse cleanly.
    let t = Term::app(
        Term::app(Term::eq_op(Type::nat()), Term::bool_lit(true)),
        Term::bool_lit(false),
    );
    assert_no_reduce(t);
    // Symmetric: `Eq(bool)` over two `nat` literals.
    let t2 = Term::app(Term::app(Term::eq_op(Type::bool()), nat(1)), nat(2));
    assert_no_reduce(t2);
}

#[test]
fn hol_eq_partial_application_refuses() {
    // `= ` applied to only one argument (the eq op applied to one term).
    let partial = Term::app(Term::eq_op(Type::nat()), nat(5));
    assert_no_reduce(partial);
    // The bare eq operator on its own.
    assert_no_reduce(Term::eq_op(Type::nat()));
}

// ============================================================================
// Negative space: partial / wrong-arity / non-literal / non-spec heads
// ============================================================================

#[test]
fn partial_applications_refuse() {
    // Bare op (zero args).
    assert_no_reduce(defs::nat_add());
    // One arg of a binary op.
    assert_no_reduce(app1(defs::nat_add(), nat(1)));
    // One arg of a ternary op.
    assert_no_reduce(app1(defs::bytes_slice(), blob(vec![1, 2])));
    assert_no_reduce(app2(defs::bytes_slice(), blob(vec![1, 2]), nat(0)));
}

#[test]
fn non_literal_args_refuse() {
    // Second arg is a free var.
    assert_no_reduce(app2(defs::nat_add(), nat(1), Term::free("x", Type::nat())));
    // First arg is a free var.
    assert_no_reduce(app2(defs::nat_add(), Term::free("x", Type::nat()), nat(1)));
    // Unary op with a free arg.
    assert_no_reduce(app1(defs::nat_succ(), Term::free("x", Type::nat())));
    // Bytes op with a non-blob arg.
    assert_no_reduce(app2(defs::bytes_cat(), nat(1), blob(vec![2])));
}

#[test]
fn mixed_incompatible_literal_kinds_refuse() {
    // nat_add applied to int literals (wrong literal kind).
    assert_no_reduce(app2(defs::nat_add(), int(1), int(2)));
    // int_add applied to nat literals.
    assert_no_reduce(app2(defs::int_add(), nat(1), nat(2)));
    // bytes_cons_nat with the operands of the wrong kind (blob, nat).
    assert_no_reduce(app2(defs::bytes_cons_nat(), blob(vec![1]), nat(2)));
    // nat_add applied to small-int literals.
    assert_no_reduce(app2(defs::nat_add(), Term::u8_lit(1), Term::u8_lit(2)));
}

#[test]
fn non_spec_head_refuses() {
    // Head is an ordinary const, not a spec / Eq.
    let f = Term::const_("f", Type::fun(Type::nat(), Type::nat()));
    assert_no_reduce(app1(f, nat(5)));
    // Head is a free var.
    let g = Term::free("g", Type::fun(Type::nat(), Type::nat()));
    assert_no_reduce(app1(g, nat(5)));
    // A bare nat literal (no application at all).
    assert_no_reduce(nat(5));
}

#[test]
fn over_application_refuses() {
    // A binary op applied to THREE args (extra trailing arg): arity
    // mismatch => no reduction.
    assert_no_reduce(app3(defs::nat_add(), nat(1), nat(2), nat(3)));
    // A unary op applied to two args.
    assert_no_reduce(app2(defs::nat_succ(), nat(1), nat(2)));
}

// ============================================================================
// Adversarial cert audit: wrong-shaped inputs fed straight to the admitted
// rules must not mint (the rules derive their whole conclusion, so the only
// attack surface is the selector/args input — probe it directly).
// ============================================================================

/// Native `Lit` args for the direct rule probes.
fn lnat(n: u64) -> Lit {
    Lit::Nat(Nat::from(n))
}

#[test]
fn fake_spec_does_not_mint_via_any_family_rule() {
    // A user-built spec sharing `nat.add`'s label/type/body is a DIFFERENT
    // `Arc`: absent from every canonical-handle table, so no family rule
    // fires — even when the fake is fed straight to `apply`.
    let canonical = defs::nat_add_spec();
    let fake = covalence_core::TermSpec::new_untrusted(
        "natAdd",
        canonical.ty().cloned(),
        canonical.tm().cloned(),
    );
    let args = vec![lnat(1), lnat(2)];
    assert!(apply(CoreEval, NatArithCert, (fake.clone(), args.clone())).is_err());
    assert!(apply(CoreEval, IntArithCert, (fake.clone(), args.clone())).is_err());
    assert!(apply(CoreEval, BytesCert, (fake.clone(), args.clone())).is_err());
    assert!(apply(CoreEval, FixedWidthCert, (fake.clone(), args)).is_err());
    // And through the driver.
    assert_no_reduce(app2(Term::term_spec(fake, Vec::new()), nat(1), nat(2)));
}

#[test]
fn wrong_family_or_arity_does_not_mint() {
    // The right op fed to the WRONG family rule refuses (each family's own
    // table is the gate, not the shared `Lit` currency).
    let nat_add = defs::nat_add_spec();
    assert!(
        apply(
            CoreEval,
            IntArithCert,
            (nat_add.clone(), vec![lnat(1), lnat(2)])
        )
        .is_err()
    );
    assert!(
        apply(
            CoreEval,
            BytesCert,
            (nat_add.clone(), vec![lnat(1), lnat(2)])
        )
        .is_err()
    );
    // Wrong arity refuses.
    assert!(apply(CoreEval, NatArithCert, (nat_add.clone(), vec![lnat(1)])).is_err());
    assert!(
        apply(
            CoreEval,
            NatArithCert,
            (nat_add.clone(), vec![lnat(1), lnat(2), lnat(3)])
        )
        .is_err()
    );
    // Wrong literal kind refuses.
    assert!(
        apply(
            CoreEval,
            NatArithCert,
            (nat_add, vec![Lit::Int(1.into()), Lit::Int(2.into())])
        )
        .is_err()
    );
}

#[test]
fn lit_eq_cert_mixed_kinds_do_not_mint() {
    // Mixed literal kinds must refuse (the equation would be ill-typed).
    assert!(apply(CoreEval, LitEqCert, (lnat(1), Lit::Int(1.into()))).is_err());
    assert!(apply(CoreEval, LitEqCert, (Lit::Bool(true), lnat(1))).is_err());
    // Mixed fixed-width TAGS must refuse too (same-kind, different type).
    let u8v = Lit::Small(covalence_core::SmallIntLiteral::new(IntTag::U8, 1));
    let u16v = Lit::Small(covalence_core::SmallIntLiteral::new(IntTag::U16, 1));
    assert!(apply(CoreEval, LitEqCert, (u8v, u16v)).is_err());
}

#[test]
fn lit_eq_cert_non_canonical_payloads_agree() {
    // Regression (audit wave-2 critical): a non-canonical fixed-width payload
    // must NOT let LitEqCert mint a false disequality. `SmallIntLiteral::new`
    // canonicalizes to the tag width, so `256_u8` and `0_u8` are the SAME
    // literal (both denote the zero u8) — LitEqCert on them mints an
    // *equality*, never `(256_u8 = 0_u8) = F`.
    use covalence_core::SmallIntLiteral;
    let a = SmallIntLiteral::new(IntTag::U8, 256);
    let z = SmallIntLiteral::new(IntTag::U8, 0);
    assert_eq!(a, z, "256_u8 must canonicalize to 0_u8");
    assert_eq!(a.bits(), 0);
    let neg_raw = SmallIntLiteral::new(IntTag::S8, 0xFF);
    let neg = SmallIntLiteral::s8(-1);
    assert_eq!(neg_raw, neg, "0xFF_s8 must canonicalize to -1_s8");
    // The cert admits on the canonicalized (now equal) pair — it cannot
    // witness them apart, so no false `(a = z) = F` is derivable.
    apply(CoreEval, LitEqCert, (Lit::Small(a), Lit::Small(z)))
        .expect("LitEqCert on equal (canonicalized) literals");
}

// ============================================================================
// delta (definitional unfolding — the kernel unfold rule via the driver)
// ============================================================================

#[test]
fn unfold_let_style_yields_body() {
    // `nat_add` is a let-style spec (its `tm` is the body and has the
    // spec's declared type). Unfolding yields `⊢ natAdd = body`.
    let t = defs::nat_add();
    let thm = delta(&t).expect("let-style spec should unfold");
    // Conclusion is a HOL eq with the spec on the LHS.
    let TermKind::App(eq_lhs_app, rhs) = thm.concl().kind() else {
        panic!("unfold concl is not App: {:?}", thm.concl());
    };
    let TermKind::App(eq_op, lhs) = eq_lhs_app.kind() else {
        panic!("unfold concl LHS is not App: {:?}", thm.concl());
    };
    assert!(matches!(eq_op.kind(), TermKind::Eq(_)));
    assert_eq!(lhs, &t, "unfold LHS should be the original spec term");
    // RHS is the spec's body (same type as the spec).
    assert_eq!(
        rhs.type_of().unwrap(),
        t.type_of().unwrap(),
        "unfolded body must share the spec's type"
    );
    // And it must equal the recorded body.
    if let TermKind::Spec(spec, _) = t.kind() {
        assert_eq!(rhs, spec.tm().expect("let-style spec has a body"));
    } else {
        panic!("nat_add() is not a Spec leaf");
    }
}

#[test]
fn unfold_def_style_errs() {
    // `nat_le` is a def-style (ε selector predicate) spec: its `tm` has
    // type `(declared_ty -> bool)`, so unfold must refuse.
    let t = defs::nat_le();
    let err = delta(&t).expect_err("def-style spec must not unfold");
    assert!(
        matches!(err, covalence_core::Error::SpecIsDefStyle),
        "expected SpecIsDefStyle, got {err:?}"
    );
}

#[test]
fn unfold_declaration_only_errs() {
    // `nat.bitAnd` is declaration-only (`tm = None`): unfold => SpecHasNoBody.
    // (`nat.div` and `cond`, by contrast, carry let-style bodies — div the
    // explicit course-of-values recursion fixpoint, cond the HOL Light `COND`
    // let-body — see `defs::nat_div_body` / `defs::cond`.)
    let t = defs::nat_bit_and();
    let err = delta(&t).expect_err("declaration-only spec must not unfold");
    assert!(
        matches!(err, covalence_core::Error::SpecHasNoBody),
        "expected SpecHasNoBody, got {err:?}"
    );
    // `nat.div` is now a let-style def (the recursive fixpoint): unfold succeeds,
    // yielding `nat.div = body`.
    let eq = delta(&defs::nat_div()).expect("nat.div is let-style, must unfold");
    assert_eq!(
        eq.concl().as_eq().expect("unfold yields an equation").0,
        &defs::nat_div(),
        "nat.div unfold LHS should be nat.div"
    );
    // The fixed-width *conversions* (toNat/toInt/fromNat/fromInt) stay
    // declaration-only — they are the primitive reducible interface.
    let conv = defs::int_to_nat(IntTag::U8);
    let err = delta(&conv).expect_err("conversion spec must not unfold");
    assert!(
        matches!(err, covalence_core::Error::SpecHasNoBody),
        "expected SpecHasNoBody for conversion, got {err:?}"
    );
}

#[test]
fn defined_fixed_width_ops_unfold_to_their_bodies() {
    // The ring ops (add/sub/mul/neg) now have let-style bodies — unfold
    // succeeds and yields `⊢ op = body` with the spec on the LHS.
    for op in [IntOp::Add, IntOp::Sub, IntOp::Mul, IntOp::Neg] {
        let t = defs::int_op(IntTag::U8, op);
        let thm = delta(&t).expect("defined op unfolds");
        assert!(thm.hyps().is_empty());
        let TermKind::App(eq_lhs, _) = thm.concl().kind() else {
            panic!("unfold concl not an application");
        };
        let TermKind::App(eq_head, lhs) = eq_lhs.kind() else {
            panic!("unfold concl LHS not an application");
        };
        assert!(matches!(eq_head.kind(), TermKind::Eq(_)));
        assert_eq!(lhs, &t, "unfold LHS is the op itself");
    }
}

#[test]
fn unfold_non_spec_errs() {
    // A plain application is not a spec leaf.
    let err = delta(&nat(5)).expect_err("non-spec must not unfold");
    assert!(
        matches!(err, covalence_core::Error::NotASpec),
        "expected NotASpec, got {err:?}"
    );
    // An Eq op is not a spec.
    let err = delta(&Term::eq_op(Type::nat())).expect_err("eq op is not a spec");
    assert!(matches!(err, covalence_core::Error::NotASpec));
}

// ============================================================================
// cert path ↔ definitional-unfolding consistency (the nat.mod soundness class)
//
// A spec reachable by BOTH the certificate rules and definitional unfolding
// commits the kernel to two facts about it: `spec lit… = reduce(spec lit…)`
// and `spec = body`. If the body, evaluated on the same literals, disagrees
// with the certificate, the theory is INCONSISTENT (`⊢ litₐ = lit_b` for
// distinct literals, hence `⊢ F`).
//
// The risk is *derivable* (and thus testable here) only when the body
// bottoms out in cert-reducible sub-ops, so the body itself reduces to a
// literal. That is the case for `nat.mod` (`n − (n/m)·m`) and `int.div`
// / `int.mod` (built from `intSgn`/`intAbs`/`intMul`/`intSub` + `natDiv`/
// `natToInt`). The Grothendieck / `iter` ops (`nat.add`, `int.add`, …)
// bottom out at `ε` (`natRec`, `abs`/`rep`) and are STUCK — sound by the
// model alone, with no derivable contradiction to guard (see
// `iter_based_bodies_are_stuck` for that distinction).
//
// `body_eval` FORCES the unfold path at the root (so the cert path cannot
// short-circuit it), then reduces the resulting body via cert reduction of
// its inner ops; comparing that to cert-reduction-at-the-root is the real
// check.
// ============================================================================

/// The RHS of a `⊢ lhs = rhs` theorem.
fn rhs_of(thm: &Thm) -> Term {
    let TermKind::App(f, rhs) = thm.concl().kind() else {
        panic!("not an equation: {}", thm.concl());
    };
    let TermKind::App(_, _) = f.kind() else {
        panic!("not an equation: {}", thm.concl());
    };
    rhs.clone()
}

/// Spine of an application: `(head, [arg1, …, argn])`.
fn spine(t: &Term) -> (Term, Vec<Term>) {
    let mut head = t.clone();
    let mut args = Vec::new();
    while let TermKind::App(f, x) = head.kind() {
        args.push(x.clone());
        head = f.clone();
    }
    args.reverse();
    (head, args)
}

/// `true` iff `t` is a concrete closed literal leaf (any kind).
fn is_literal(t: &Term) -> bool {
    Lit::from_term(t).is_some()
}

/// Prove `⊢ t = v` (a literal) for a term whose every application node is a
/// cert-reducible op applied to (recursively) literal args.
/// Call-by-value via congruence + `reduce`. Returns `None` if some node
/// is not reducible (e.g. a bare `natRec`/`succ` spec leaf reached through an
/// `iter`-based body) — used to distinguish reducible from stuck bodies.
fn eval(t: &Term) -> Option<Thm> {
    if is_literal(t) {
        return Some(Thm::refl(t.clone()).unwrap());
    }
    match t.kind() {
        TermKind::App(..) => {
            let (head, args) = spine(t);
            // Thread congruence so `cur : ⊢ t = head v1 … vn`.
            let mut cur = Thm::refl(head).unwrap();
            for a in &args {
                cur = cur.mk_comb(eval(a)?).ok()?;
            }
            let applied = rhs_of(&cur);
            let red = reduce(&applied)?;
            cur.trans(red).ok()
        }
        _ => None,
    }
}

/// Prove `⊢ (spec lit…) = v` by FORCING the spec's body: unfold the head
/// spec, β-reduce the spine, then `eval` the body (its inner ops reduce by
/// the cert path). Returns `None` if the head is not let-style or the body
/// does not reduce to a literal.
fn body_eval(applied: &Term) -> Option<Thm> {
    let (head, args) = spine(applied);
    let unf = delta(&head).ok()?; // ⊢ head = body
    let mut cong = unf;
    for a in &args {
        cong = cong.mk_comb(Thm::refl(a.clone()).unwrap()).ok()?;
    }
    let beta = beta_spine(&rhs_of(&cong)); // ⊢ body v… = normal
    let normal = rhs_of(&beta);
    cong.trans(beta).unwrap().trans(eval(&normal)?).ok()
}

/// Prove `⊢ t = t'` where `t'` contracts every β-redex on `t`'s left spine.
fn beta_spine(t: &Term) -> Thm {
    match t.kind() {
        TermKind::App(f, x) => {
            let f_eq = beta_spine(f);
            let f_norm = rhs_of(&f_eq);
            let app_eq = f_eq.mk_comb(Thm::refl(x.clone()).unwrap()).unwrap();
            if let TermKind::Abs(..) = f_norm.kind() {
                let contracted = Thm::beta_conv(rhs_of(&app_eq)).unwrap();
                app_eq.trans(contracted).unwrap()
            } else {
                app_eq
            }
        }
        _ => Thm::refl(t.clone()).unwrap(),
    }
}

/// For every op with a reducible body, `reduce(op lits)` MUST equal the
/// value obtained by forcing op's unfolded body. A mismatch is a soundness
/// hole (the kernel could then prove `litₐ = lit_b`). Covers `nat.mod` (the
/// historical hole) and the defined `int.div` / `int.mod`, exercising
/// the div/mod-by-zero and all four sign quadrants.
#[test]
fn audit_reduce_matches_body() {
    let mut probes: Vec<Term> = Vec::new();
    for (n, m) in [(5, 0), (10, 0), (0, 0), (17, 5), (20, 4), (3, 7), (1, 1)] {
        probes.push(app2(defs::nat_mod(), nat(n), nat(m)));
    }
    for (x, y) in [
        (7, 3),
        (-7, 3),
        (7, -3),
        (-7, -3),
        (7, 0),
        (-7, 0),
        (0, 5),
        (0, 0),
        (20, 4),
        (-20, -4),
        (1, 1),
    ] {
        probes.push(app2(defs::int_div(), int(x), int(y)));
        probes.push(app2(defs::int_mod(), int(x), int(y)));
    }
    // Fixed-width ring ops (add/sub/mul/neg) — sign-uniform, with overflow
    // and the neg-of-min edge. Both unsigned (uN) and signed (sN) tags, so
    // both `toInt` interpretations are exercised.
    let u8 = |v: u8| Term::u8_lit(v);
    let s8 = |v: i8| Term::s8_lit(v);
    for (a, b) in [(200u8, 100u8), (5, 8), (0, 0), (20, 20), (255, 1)] {
        probes.push(app2(defs::int_op(IntTag::U8, IntOp::Add), u8(a), u8(b)));
        probes.push(app2(defs::int_op(IntTag::U8, IntOp::Sub), u8(a), u8(b)));
        probes.push(app2(defs::int_op(IntTag::U8, IntOp::Mul), u8(a), u8(b)));
    }
    for v in [0u8, 1, 127, 128, 255] {
        probes.push(app1(defs::int_op(IntTag::U8, IntOp::Neg), u8(v)));
    }
    for (a, b) in [(100i8, 50i8), (-100, 50), (-3, 4), (127, 1), (-128, -1)] {
        probes.push(app2(defs::int_op(IntTag::S8, IntOp::Add), s8(a), s8(b)));
        probes.push(app2(defs::int_op(IntTag::S8, IntOp::Sub), s8(a), s8(b)));
        probes.push(app2(defs::int_op(IntTag::S8, IntOp::Mul), s8(a), s8(b)));
    }
    for v in [0i8, 1, -1, 127, -128] {
        probes.push(app1(defs::int_op(IntTag::S8, IntOp::Neg), s8(v)));
    }
    // A wider tag, to catch any width-specific masking error.
    probes.push(app2(
        defs::int_op(IntTag::U32, IntOp::Mul),
        Term::u32_lit(100_000),
        Term::u32_lit(100_000),
    ));
    probes.push(app2(
        defs::int_op(IntTag::S32, IntOp::Sub),
        Term::s32_lit(i32::MIN),
        Term::s32_lit(1),
    ));
    // Bitwise / comparison / shift / div / rem. UNSIGNED tag (u8): every
    // defined binary op (incl. logical `shr`); plus unary `not`.
    {
        use IntOp::*;
        let u8_pairs = [
            (0xCCu8, 0xAA),
            (0, 255),
            (255, 255),
            (200, 7),
            (5, 0), // div/rem by zero
            (0, 5),
            (1, 4),
            (1, 8),   // shift == width  (→ amount 0)
            (1, 100), // shift > width   (→ amount mod width)
            (5, 5),
            (200, 100),
            (100, 200),
        ];
        for op in [And, Or, Xor, Div, Rem, Shl, Shr, Lt, Le, Gt, Ge] {
            for (a, b) in u8_pairs {
                probes.push(app2(defs::int_op(IntTag::U8, op), u8(a), u8(b)));
            }
        }
        for v in [0u8, 1, 128, 255] {
            probes.push(app1(defs::int_op(IntTag::U8, Not), u8(v)));
        }
        // SIGNED tag (s8): every defined op EXCEPT arithmetic `shr` (still
        // declaration-only — it has no body, so it is not in this guard).
        let s8_pairs = [
            (-1i8, 1i8),
            (1, -1),
            (-128, 127),
            (-7, 2),
            (7, -2),
            (-5, 0),    // div/rem by zero
            (-128, -1), // div overflow edge
            (5, 5),
            (-50, 50),
        ];
        for op in [And, Or, Xor, Div, Rem, Shl, Lt, Le, Gt, Ge] {
            for (a, b) in s8_pairs {
                probes.push(app2(defs::int_op(IntTag::S8, op), s8(a), s8(b)));
            }
        }
        for v in [0i8, -1, 127, -128] {
            probes.push(app1(defs::int_op(IntTag::S8, Not), s8(v)));
        }
    }
    for t in probes {
        let via_reduce = rhs_of(&reduce(&t).unwrap());
        let via_body = rhs_of(
            &body_eval(&t).unwrap_or_else(|| panic!("{t}: body did not reduce to a literal")),
        );
        assert_eq!(
            via_reduce, via_body,
            "{t}: cert path={via_reduce} but unfolded body={via_body} \
             — these MUST agree or the kernel is inconsistent"
        );
    }
}

/// The contrasting case: the `iter`/Grothendieck ops have bodies that are
/// STUCK at `ε` (they cannot be reduced to a literal), so there is no
/// derivable unfold-vs-reduce contradiction — they are sound by the model
/// only. `body_eval` returns `None` for them, confirming they are outside
/// the testable coupling class above.
#[test]
fn iter_based_bodies_are_stuck() {
    for t in [
        app2(defs::nat_add(), nat(3), nat(4)),
        app2(defs::nat_mul(), nat(6), nat(7)),
        app2(defs::int_add(), int(3), int(4)),
        app1(defs::nat_to_int(), nat(5)),
    ] {
        // The cert path still decides it…
        assert!(reduce(&t).is_some(), "{t} should cert-reduce");
        // …but the body cannot be driven to a literal by the kernel.
        assert!(
            body_eval(&t).is_none(),
            "{t}: body unexpectedly reduced to a literal (it should be stuck at ε)"
        );
    }
}

/// A SECOND coupling, introduced by `Thm::spec_ax`: it exposes a def-style
/// spec's *predicate* as a kernel fact (`(pred w) ⟹ pred(t)`). For a
/// def-style spec that is ALSO cert-reducible — only `nat.le` and `nat.lt`
/// — the predicate's solutions must agree with the certificate, or
/// `spec_ax` + the cert path are jointly inconsistent (the theory has no
/// model). Their predicates are the four defining recursion equations,
/// which pin down a UNIQUE solution, so it suffices that the certificate
/// *satisfies* those equations (uniqueness is by construction). See
/// `kernel-design.md` §9.
#[test]
fn audit_reduced_def_specs_satisfy_their_predicate() {
    fn reduce_bool(t: Term) -> bool {
        let rhs = rhs_of(&reduce(&t).unwrap());
        match rhs.as_bool() {
            Some(b) => b,
            None => panic!("{t}: reduced to non-bool {rhs:?}"),
        }
    }
    // (accessor, cmp 0 0, cmp 0 (S m), cmp (S n) 0) — the three base clauses
    // of `nat_cmp_predicate`; the fourth (recursion) is checked below.
    type CmpCase = (fn() -> Term, bool, bool, bool);
    let cases: &[CmpCase] = &[
        (defs::nat_le as fn() -> Term, true, true, false),
        (defs::nat_lt, false, true, false),
    ];
    for &(cmp, zz, zs, sz) in cases {
        assert_eq!(reduce_bool(app2(cmp(), nat(0), nat(0))), zz, "cmp 0 0");
        for m in [0u64, 1, 5, 42] {
            assert_eq!(
                reduce_bool(app2(cmp(), nat(0), nat(m + 1))),
                zs,
                "cmp 0 (S m)"
            );
            assert_eq!(
                reduce_bool(app2(cmp(), nat(m + 1), nat(0))),
                sz,
                "cmp (S n) 0"
            );
        }
        // Recursion clause: `cmp (S n) (S m) = cmp n m`.
        for (n, m) in [(0u64, 0u64), (3, 5), (5, 3), (2, 2), (7, 0), (0, 7)] {
            assert_eq!(
                reduce_bool(app2(cmp(), nat(n + 1), nat(m + 1))),
                reduce_bool(app2(cmp(), nat(n), nat(m))),
                "cmp (S n) (S m) = cmp n m at ({n},{m})"
            );
        }
    }
}
