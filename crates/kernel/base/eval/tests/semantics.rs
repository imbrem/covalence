//! Direct unit tests of the FORCED edge-case conventions and the op
//! semantics — the successor of the S3 differential suite (which pinned the
//! `Builtins` CanonRules value-for-value against the kernel's legacy
//! `Thm::reduce_*` reducer until the latter was deleted in S8). These pin
//! the semantics this crate is committed to, standalone: a wrong value here
//! would flow through the covalence-core family certificate rules and mint
//! a false equation, so a failing assert is a *soundness* finding.

use covalence_pure::CanonRule;
use covalence_pure_eval::*;
use covalence_types::{Bytes, Int, Nat};

fn n(v: u128) -> Nat {
    Nat::from(v)
}
fn z(v: i128) -> Int {
    Int::from(v)
}
fn bs(v: &[u8]) -> Bytes {
    Bytes::from(v.to_vec())
}

#[test]
fn nat_div_mod_zero_conventions() {
    // n / 0 = 0 and n mod 0 = n (FORCED — see the crate docs).
    assert_eq!(NatDiv.eval(&(n(10), n(0))), Some(n(0)));
    assert_eq!(NatMod.eval(&(n(10), n(0))), Some(n(10)));
    assert_eq!(NatDiv.eval(&(n(17), n(5))), Some(n(3)));
    assert_eq!(NatMod.eval(&(n(17), n(5))), Some(n(2)));
}

#[test]
fn nat_saturation() {
    assert_eq!(NatPred.eval(&n(0)), Some(n(0)));
    assert_eq!(NatPred.eval(&n(7)), Some(n(6)));
    assert_eq!(NatSub.eval(&(n(2), n(5))), Some(n(0)));
    assert_eq!(NatSub.eval(&(n(10), n(3))), Some(n(7)));
}

#[test]
fn int_div_mod_zero_conventions() {
    // x / 0 = 0 and x mod 0 = x; truncating division, remainder takes the
    // dividend's sign.
    assert_eq!(IntDiv.eval(&(z(10), z(0))), Some(z(0)));
    assert_eq!(IntMod.eval(&(z(-10), z(0))), Some(z(-10)));
    assert_eq!(IntDiv.eval(&(z(-17), z(5))), Some(z(-3)));
    assert_eq!(IntMod.eval(&(z(-17), z(5))), Some(z(-2)));
}

#[test]
fn fixed_width_div_rem_zero_conventions() {
    // x / 0 = 0 and x rem 0 = x, signed and unsigned.
    assert_eq!(FwDiv::<u8>::new().eval(&(5, 0)), Some(0));
    assert_eq!(FwRem::<u8>::new().eval(&(5, 0)), Some(5));
    assert_eq!(FwDiv::<i8>::new().eval(&(-5, 0)), Some(0));
    assert_eq!(FwRem::<i8>::new().eval(&(-5, 0)), Some(-5));
    // MIN / -1 wraps (two's complement), MIN rem -1 = 0.
    assert_eq!(FwDiv::<i8>::new().eval(&(i8::MIN, -1)), Some(i8::MIN));
    assert_eq!(FwRem::<i8>::new().eval(&(i8::MIN, -1)), Some(0));
}

#[test]
fn fixed_width_wrap_and_shift() {
    assert_eq!(FwAdd::<u8>::new().eval(&(200, 100)), Some(44));
    assert_eq!(FwMul::<u8>::new().eval(&(20, 20)), Some(144));
    // Shift amounts are mod width; sN >> is arithmetic, uN >> logical.
    assert_eq!(FwShl::<u8>::new().eval(&(1, 12)), Some(16)); // 12 mod 8 = 4
    assert_eq!(FwShr::<i8>::new().eval(&(-8, 1)), Some(-4));
    assert_eq!(FwShr::<u8>::new().eval(&(0x80, 1)), Some(0x40));
}

#[test]
fn casts() {
    // zext ignores the source type's signedness (unsigned bit value)...
    assert_eq!(Zext::<i8, u32>::new().eval(&-1), Some(0xFF));
    // ...sext sign-extends the bits regardless of the source type.
    assert_eq!(Sext::<u8, u32>::new().eval(&0xFF), Some(u32::MAX));
    assert_eq!(Sext::<i8, i32>::new().eval(&-1), Some(-1));
    // Narrowing wraps.
    assert_eq!(Zext::<u32, u8>::new().eval(&0x1FF), Some(0xFF));
    // fromNat / fromInt wrap; toNat / toInt read per the type.
    assert_eq!(FwFromNat::<u8>::new().eval(&n(300)), Some(44));
    assert_eq!(FwFromInt::<u8>::new().eval(&z(-1)), Some(255));
    assert_eq!(FwToNat::<i8>::new().eval(&-1), Some(n(255)));
    assert_eq!(FwToInt::<i8>::new().eval(&-5), Some(z(-5)));
}

#[test]
fn oversize_pow_and_shl_refuse_shr_is_total() {
    // The fallibility rule (crate docs, "Refusal vs. totality vs. OOM"):
    // an op computes the true answer where representable, REFUSES (`None`)
    // where the answer is detectably unrepresentable, and never clamps or
    // truncates an arbitrary-precision operand.
    let huge_exp = n(1u128 << 32);
    // base ≥ 2, oversize exponent: unrepresentable ⇒ None.
    assert_eq!(NatPow.eval(&(n(2), huge_exp.clone())), None);
    // base ∈ {0, 1}: total even for oversize exponents (true value known).
    assert_eq!(NatPow.eval(&(n(0), huge_exp.clone())), Some(n(0)));
    assert_eq!(NatPow.eval(&(n(1), huge_exp)), Some(n(1)));

    let huge_shift = n(1u128 << 64);
    // a ≠ 0, shift beyond usize: result needs ≥ 2^64 bits ⇒ None.
    assert_eq!(NatShl.eval(&(n(1), huge_shift.clone())), None);
    // a = 0: total (0 · 2^s = 0).
    assert_eq!(NatShl.eval(&(n(0), huge_shift.clone())), Some(n(0)));
    // shr returns 0 exactly when the shift ≥ bits(a) — compared against the
    // operand's ACTUAL bit-length, target-independent (NOT the usize boundary,
    // which is 2^32 on wasm32 and would mint a false `a >> s = 0`).
    assert_eq!(NatShr.eval(&(n(1), huge_shift.clone())), Some(n(0)));
    let big = NatShl.eval(&(n(0xFFFF), n(1000))).unwrap();
    assert_eq!(NatShr.eval(&(big, huge_shift)), Some(n(0)));
}

#[test]
fn shr_keys_off_bit_length_not_usize() {
    // Regression (audit: 32-bit/wasm32 ⊢False). `a = 2^100` has 101 bits.
    let a = NatShl.eval(&(n(1), n(100))).unwrap(); // 2^100
    // s < bits(a): the true nonzero value, computed.
    assert_eq!(NatShr.eval(&(a.clone(), n(98))), Some(n(4))); // 2^100 >> 98 = 4
    assert_eq!(NatShr.eval(&(a.clone(), n(99))), Some(n(2))); // 2^100 >> 99 = 2
    assert_eq!(NatShr.eval(&(a.clone(), n(100))), Some(n(1))); // = 1
    // s == bits(a) and s > bits(a): exactly 0 (the boundary the fix keys on).
    assert_eq!(NatShr.eval(&(a.clone(), n(101))), Some(n(0)));
    assert_eq!(NatShr.eval(&(a.clone(), n(200))), Some(n(0)));
    // Oversize shift (> usize on 64-bit) still 0 because it exceeds bits(a).
    assert_eq!(NatShr.eval(&(a, n(1u128 << 64))), Some(n(0)));
    // a = 0 → 0 for any shift (bits(0) = 0).
    assert_eq!(NatShr.eval(&(n(0), n(1u128 << 64))), Some(n(0)));
}

// ============================================================================
// Op semantics ported from the retired kernel audit suite (S8): the same
// value commitments, asserted directly on the CanonRules.
// ============================================================================

#[test]
fn nat_pow_values() {
    assert_eq!(NatPow.eval(&(n(2), n(0))), Some(n(1)));
    assert_eq!(NatPow.eval(&(n(0), n(0))), Some(n(1)));
    assert_eq!(NatPow.eval(&(n(2), n(10))), Some(n(1024)));
    assert_eq!(NatPow.eval(&(n(0), n(5))), Some(n(0)));
    assert_eq!(NatPow.eval(&(n(5), n(1))), Some(n(5)));
}

#[test]
fn nat_shift_and_bitwise_values() {
    assert_eq!(NatShl.eval(&(n(1), n(0))), Some(n(1)));
    assert_eq!(NatShl.eval(&(n(1), n(4))), Some(n(16)));
    assert_eq!(NatShl.eval(&(n(3), n(2))), Some(n(12)));
    assert_eq!(NatShr.eval(&(n(16), n(2))), Some(n(4)));
    assert_eq!(NatShr.eval(&(n(1), n(4))), Some(n(0)));
    assert_eq!(NatShr.eval(&(n(255), n(0))), Some(n(255)));
    assert_eq!(NatBitAnd.eval(&(n(0b1100), n(0b1010))), Some(n(0b1000)));
    assert_eq!(NatBitOr.eval(&(n(0b1100), n(0b1010))), Some(n(0b1110)));
    assert_eq!(NatBitXor.eval(&(n(0b1100), n(0b1010))), Some(n(0b0110)));
    assert_eq!(NatBitAnd.eval(&(n(0xFF), n(0))), Some(n(0)));
}

#[test]
fn nat_comparisons() {
    assert_eq!(NatLe.eval(&(n(3), n(5))), Some(true));
    assert_eq!(NatLe.eval(&(n(5), n(5))), Some(true));
    assert_eq!(NatLe.eval(&(n(7), n(5))), Some(false));
    assert_eq!(NatLt.eval(&(n(3), n(5))), Some(true));
    assert_eq!(NatLt.eval(&(n(5), n(5))), Some(false));
    assert_eq!(NatLt.eval(&(n(7), n(5))), Some(false));
}

#[test]
fn int_unary_values() {
    assert_eq!(IntSucc.eval(&z(-1)), Some(z(0)));
    assert_eq!(IntSucc.eval(&z(5)), Some(z(6)));
    assert_eq!(IntPred.eval(&z(0)), Some(z(-1)));
    assert_eq!(IntPred.eval(&z(-5)), Some(z(-6)));
    assert_eq!(IntNeg.eval(&z(7)), Some(z(-7)));
    assert_eq!(IntNeg.eval(&z(-7)), Some(z(7)));
    assert_eq!(IntNeg.eval(&z(0)), Some(z(0)));
    // abs : int -> nat.
    assert_eq!(IntAbs.eval(&z(-12)), Some(n(12)));
    assert_eq!(IntAbs.eval(&z(12)), Some(n(12)));
    assert_eq!(IntAbs.eval(&z(0)), Some(n(0)));
    // sgn : int -> int.
    assert_eq!(IntSgn.eval(&z(-9)), Some(z(-1)));
    assert_eq!(IntSgn.eval(&z(0)), Some(z(0)));
    assert_eq!(IntSgn.eval(&z(9)), Some(z(1)));
}

#[test]
fn int_comparisons() {
    assert_eq!(IntLe.eval(&(z(-3), z(2))), Some(true));
    assert_eq!(IntLe.eval(&(z(2), z(2))), Some(true));
    assert_eq!(IntLe.eval(&(z(2), z(-3))), Some(false));
    assert_eq!(IntLt.eval(&(z(-3), z(2))), Some(true));
    assert_eq!(IntLt.eval(&(z(2), z(2))), Some(false));
}

#[test]
fn nat_coercions_and_bytes_round_trips() {
    assert_eq!(NatToInt.eval(&n(0)), Some(z(0)));
    assert_eq!(NatToInt.eval(&n(42)), Some(z(42)));
    // 0 encodes as a single zero byte (BigUint convention: [0], not empty).
    assert_eq!(NatToBytesLe.eval(&n(0)), Some(bs(&[0])));
    assert_eq!(NatToBytesBe.eval(&n(0)), Some(bs(&[0])));
    // 256 = 0x0100: LE = [0,1], BE = [1,0].
    assert_eq!(NatToBytesLe.eval(&n(256)), Some(bs(&[0, 1])));
    assert_eq!(NatToBytesBe.eval(&n(256)), Some(bs(&[1, 0])));
    // from_bytes inverse; the empty blob decodes to 0.
    assert_eq!(NatFromBytesLe.eval(&bs(&[0, 1])), Some(n(256)));
    assert_eq!(NatFromBytesBe.eval(&bs(&[1, 0])), Some(n(256)));
    assert_eq!(NatFromBytesLe.eval(&bs(&[])), Some(n(0)));
    assert_eq!(NatFromBytesBe.eval(&bs(&[])), Some(n(0)));
}

#[test]
fn bytes_semantics() {
    // cat
    assert_eq!(
        BytesCat.eval(&(bs(&[1, 2]), bs(&[3, 4, 5]))),
        Some(bs(&[1, 2, 3, 4, 5]))
    );
    assert_eq!(BytesCat.eval(&(bs(&[]), bs(&[9]))), Some(bs(&[9])));
    // consNat reduces the nat operand mod 256.
    assert_eq!(BytesConsNat.eval(&(n(0), bs(&[9]))), Some(bs(&[0, 9])));
    assert_eq!(BytesConsNat.eval(&(n(256), bs(&[9]))), Some(bs(&[0, 9])));
    assert_eq!(BytesConsNat.eval(&(n(257), bs(&[9]))), Some(bs(&[1, 9])));
    assert_eq!(BytesConsNat.eval(&(n(0x12345), bs(&[]))), Some(bs(&[0x45])));
    // len
    assert_eq!(BytesLen.eval(&bs(&[])), Some(n(0)));
    assert_eq!(BytesLen.eval(&bs(&[1, 2, 3])), Some(n(3)));
    // at: in-bounds, out-of-bounds (reads 0), beyond-usize index (reads 0).
    assert_eq!(BytesAt.eval(&(bs(&[7, 8, 9]), n(0))), Some(n(7)));
    assert_eq!(BytesAt.eval(&(bs(&[7, 8, 9]), n(2))), Some(n(9)));
    assert_eq!(BytesAt.eval(&(bs(&[7, 8, 9]), n(99))), Some(n(0)));
    let huge = Nat::from(u128::from(u64::MAX) + 1);
    assert_eq!(BytesAt.eval(&(bs(&[7, 8, 9]), huge.clone())), Some(n(0)));
    // slice saturates on both start and len.
    let b = bs(&[10, 20, 30, 40, 50]);
    assert_eq!(
        BytesSlice.eval(&(b.clone(), n(1), n(3))),
        Some(bs(&[20, 30, 40]))
    );
    assert_eq!(
        BytesSlice.eval(&(b.clone(), n(3), n(100))),
        Some(bs(&[40, 50]))
    );
    assert_eq!(BytesSlice.eval(&(b.clone(), n(5), n(3))), Some(bs(&[])));
    assert_eq!(
        BytesSlice.eval(&(b.clone(), huge.clone(), n(3))),
        Some(bs(&[]))
    );
    // Over-usize LEN is total too: takes to the end of the real buffer.
    assert_eq!(
        BytesSlice.eval(&(b.clone(), n(1), huge)),
        Some(bs(&[20, 30, 40, 50]))
    );
    assert_eq!(BytesSlice.eval(&(b.clone(), n(1), n(0))), Some(bs(&[])));
    assert_eq!(
        BytesSlice.eval(&(b.clone(), n(0), n(5))),
        Some(bs(&[10, 20, 30, 40, 50]))
    );
}
