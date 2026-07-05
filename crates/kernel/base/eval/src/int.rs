//! `int` builtins: arbitrary-precision signed-integer ops over
//! [`covalence_types::Int`].
//!
//! Every body transcribes the matching arm of `covalence-core`'s
//! `builtins.rs::eval_prim` exactly. Division truncates toward zero and the
//! remainder takes the dividend's sign; `a / 0 = 0` and `a mod 0 = a` are
//! FORCED (exactly as for `nat.mod` — `int.div`/`int.mod` have let-style
//! bodies built from reducible sub-ops, so these are the bodies' values at
//! `b = 0`).

use covalence_types::{Int, Nat, Sign};

use crate::NamedRule;

canon_op! {
    /// `int.succ`.
    IntSucc("int.succ"): Int => Int,
    |a| a + &Int::one()
}

canon_op! {
    /// `int.pred`.
    IntPred("int.pred"): Int => Int,
    |a| a - &Int::one()
}

canon_op! {
    /// `int.neg`.
    IntNeg("int.neg"): Int => Int,
    |a| -a
}

canon_op! {
    /// `int.abs` — absolute value, landing in `nat`.
    IntAbs("int.abs"): Int => Nat,
    |a| a.abs()
}

canon_op! {
    /// `int.sgn` — sign as `-1 | 0 | 1`.
    IntSgn("int.sgn"): Int => Int,
    |a| match a.sign() {
        Sign::Negative => Int::from_sign_nat(Sign::Negative, Nat::one()),
        Sign::Zero => Int::zero(),
        Sign::Positive => Int::from_sign_nat(Sign::Positive, Nat::one()),
    }
}

canon_op! {
    /// `int.add`.
    IntAdd("int.add"): (Int, Int) => Int,
    |(a, b)| a + b
}

canon_op! {
    /// `int.mul`.
    IntMul("int.mul"): (Int, Int) => Int,
    |(a, b)| a * b
}

canon_op! {
    /// `int.sub`.
    IntSub("int.sub"): (Int, Int) => Int,
    |(a, b)| a - b
}

canon_op! {
    /// `int.div` — truncating division toward zero; `a / 0 = 0` (paired
    /// with `a mod 0 = a` on [`IntMod`], both FORCED by the let-style
    /// catalogue bodies).
    IntDiv("int.div"): (Int, Int) => Int,
    |(a, b)| if b.is_zero() { Int::zero() } else { a / b }
}

canon_op! {
    /// `int.mod` — remainder with the dividend's sign; `a mod 0 = a`
    /// (NOT 0), FORCED exactly as for `nat.mod`.
    IntMod("int.mod"): (Int, Int) => Int,
    |(a, b)| if b.is_zero() { a.clone() } else { a % b }
}

canon_op! {
    /// `int.le`.
    IntLe("int.le"): (Int, Int) => bool,
    |(a, b)| a <= b
}

canon_op! {
    /// `int.lt`.
    IntLt("int.lt"): (Int, Int) => bool,
    |(a, b)| a < b
}
