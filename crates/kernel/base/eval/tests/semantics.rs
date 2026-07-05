//! Direct unit tests of the FORCED edge-case conventions. These survive the
//! deletion of the legacy kernel reducer (unlike `tests/differential.rs`) — they
//! pin the semantics this crate is committed to independently of the legacy
//! kernel path.

use covalence_pure::CanonRule;
use covalence_pure_eval::*;
use covalence_types::{Int, Nat};

fn n(v: u128) -> Nat {
    Nat::from(v)
}
fn z(v: i128) -> Int {
    Int::from(v)
}

#[test]
fn nat_div_mod_zero_conventions() {
    // n / 0 = 0 and n mod 0 = n (FORCED — see the crate docs).
    assert_eq!(NatDiv.eval(&(n(10), n(0))), n(0));
    assert_eq!(NatMod.eval(&(n(10), n(0))), n(10));
    assert_eq!(NatDiv.eval(&(n(17), n(5))), n(3));
    assert_eq!(NatMod.eval(&(n(17), n(5))), n(2));
}

#[test]
fn nat_saturation() {
    assert_eq!(NatPred.eval(&n(0)), n(0));
    assert_eq!(NatPred.eval(&n(7)), n(6));
    assert_eq!(NatSub.eval(&(n(2), n(5))), n(0));
    assert_eq!(NatSub.eval(&(n(10), n(3))), n(7));
}

#[test]
fn int_div_mod_zero_conventions() {
    // x / 0 = 0 and x mod 0 = x; truncating division, remainder takes the
    // dividend's sign.
    assert_eq!(IntDiv.eval(&(z(10), z(0))), z(0));
    assert_eq!(IntMod.eval(&(z(-10), z(0))), z(-10));
    assert_eq!(IntDiv.eval(&(z(-17), z(5))), z(-3));
    assert_eq!(IntMod.eval(&(z(-17), z(5))), z(-2));
}

#[test]
fn fixed_width_div_rem_zero_conventions() {
    // x / 0 = 0 and x rem 0 = x, signed and unsigned.
    assert_eq!(FwDiv::<u8>::new().eval(&(5, 0)), 0);
    assert_eq!(FwRem::<u8>::new().eval(&(5, 0)), 5);
    assert_eq!(FwDiv::<i8>::new().eval(&(-5, 0)), 0);
    assert_eq!(FwRem::<i8>::new().eval(&(-5, 0)), -5);
    // MIN / -1 wraps (two's complement), MIN rem -1 = 0.
    assert_eq!(FwDiv::<i8>::new().eval(&(i8::MIN, -1)), i8::MIN);
    assert_eq!(FwRem::<i8>::new().eval(&(i8::MIN, -1)), 0);
}

#[test]
fn fixed_width_wrap_and_shift() {
    assert_eq!(FwAdd::<u8>::new().eval(&(200, 100)), 44);
    assert_eq!(FwMul::<u8>::new().eval(&(20, 20)), 144);
    // Shift amounts are mod width; sN >> is arithmetic, uN >> logical.
    assert_eq!(FwShl::<u8>::new().eval(&(1, 12)), 16); // 12 mod 8 = 4
    assert_eq!(FwShr::<i8>::new().eval(&(-8, 1)), -4);
    assert_eq!(FwShr::<u8>::new().eval(&(0x80, 1)), 0x40);
}

#[test]
fn casts() {
    // zext ignores the source type's signedness (unsigned bit value)...
    assert_eq!(Zext::<i8, u32>::new().eval(&-1), 0xFF);
    // ...sext sign-extends the bits regardless of the source type.
    assert_eq!(Sext::<u8, u32>::new().eval(&0xFF), u32::MAX);
    assert_eq!(Sext::<i8, i32>::new().eval(&-1), -1);
    // Narrowing wraps.
    assert_eq!(Zext::<u32, u8>::new().eval(&0x1FF), 0xFF);
    // fromNat / fromInt wrap; toNat / toInt read per the type.
    assert_eq!(FwFromNat::<u8>::new().eval(&n(300)), 44);
    assert_eq!(FwFromInt::<u8>::new().eval(&z(-1)), 255);
    assert_eq!(FwToNat::<i8>::new().eval(&-1), n(255));
    assert_eq!(FwToInt::<i8>::new().eval(&-5), z(-5));
}

#[test]
fn oversize_pow_and_shift_refuse_by_panic() {
    // builtins.rs refuses (None) exponents/shifts beyond u32/u64; eval is
    // total-or-abort, so the same cases panic — nothing is minted either way.
    let huge_exp = n(1u128 << 32);
    let r = std::panic::catch_unwind(|| NatPow.eval(&(n(2), huge_exp)));
    assert!(r.is_err(), "oversize exponent must refuse");
    let huge_shift = n(1u128 << 64);
    let r = std::panic::catch_unwind(|| NatShl.eval(&(n(1), huge_shift)));
    assert!(r.is_err(), "oversize shift must refuse");
    let huge_shift = n(1u128 << 64);
    let r = std::panic::catch_unwind(|| NatShr.eval(&(n(1), huge_shift)));
    assert!(r.is_err(), "oversize shift must refuse");
}
