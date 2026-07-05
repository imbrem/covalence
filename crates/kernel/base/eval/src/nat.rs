//! `nat` builtins: arbitrary-precision natural-number ops over
//! [`covalence_types::Nat`].
//!
//! Every body transcribes the matching arm of `covalence-core`'s
//! `builtins.rs::eval_prim` exactly. Edge-case conventions that bear on
//! soundness (all FORCED — see the crate docs):
//!
//! - saturating predecessor and subtraction (`pred 0 = 0`, `a - b = 0` when
//!   `b > a`);
//! - `a / 0 = 0` and `a mod 0 = a` (NOT 0): `nat.mod`'s let-style body
//!   `λn m. n - (n/m)*m` evaluates to `n - 0 = n` at `m = 0`, so any other
//!   value would let definitional unfolding and this rule derive `n = 0` for
//!   every `n`;
//! - `nat.pow` / `nat.shl` / `nat.shr` REFUSE (panic) oversize exponents /
//!   shift amounts rather than truncate them, mirroring `builtins.rs`'s
//!   `None` refusal.

use covalence_types::{Bytes, Int, Nat, Sign};

use crate::NamedRule;

/// Shift amount as `usize`; REFUSES (panics) shifts that do not fit in one
/// `u64` digit / in `usize`, mirroring `builtins.rs::reduce_nat_shift`'s
/// `None` (truncating an unbounded exponent would be unsound).
fn shift_amount(shift: &Nat) -> usize {
    let digits = shift.as_inner().to_u64_digits();
    assert!(
        digits.len() <= 1,
        "nat shift: oversize shift amount (refusing to evaluate)"
    );
    usize::try_from(digits.first().copied().unwrap_or(0))
        .expect("nat shift: shift amount exceeds usize (refusing to evaluate)")
}

canon_op! {
    /// `nat.pred` — saturating predecessor: `pred 0 = 0`.
    NatPred("nat.pred"): Nat => Nat,
    |n| n.checked_sub(&Nat::one()).unwrap_or_else(Nat::zero)
}

canon_op! {
    /// `nat.add`.
    NatAdd("nat.add"): (Nat, Nat) => Nat,
    |(a, b)| a + b
}

canon_op! {
    /// `nat.mul`.
    NatMul("nat.mul"): (Nat, Nat) => Nat,
    |(a, b)| a * b
}

canon_op! {
    /// `nat.sub` — saturating: `a - b = 0` when `b > a`.
    NatSub("nat.sub"): (Nat, Nat) => Nat,
    |(a, b)| a.checked_sub(b).unwrap_or_else(Nat::zero)
}

canon_op! {
    /// `nat.div` — `a / 0 = 0` (paired with `a mod 0 = a` on [`NatMod`]).
    NatDiv("nat.div"): (Nat, Nat) => Nat,
    |(a, b)| if b.is_zero() { Nat::zero() } else { a / b }
}

canon_op! {
    /// `nat.mod` — `n mod 0 = n` (NOT 0), FORCED for soundness: `nat.mod`
    /// has a let-style body `λn m. n - (n/m)*m`, which at `m = 0` (with
    /// `n/0 = 0`) evaluates to `n - 0 = n`. Returning 0 here would derive
    /// `n = 0` for any `n`. `n mod 0 = n` also satisfies
    /// `n = (n/m)*m + (n mod m)` and matches Lean/Coq.
    NatMod("nat.mod"): (Nat, Nat) => Nat,
    |(a, b)| if b.is_zero() { a.clone() } else { a % b }
}

canon_op! {
    /// `nat.pow`. REFUSES (panics) an exponent that does not fit in `u32`
    /// rather than truncate it (mirrors `builtins.rs`'s `None`).
    NatPow("nat.pow"): (Nat, Nat) => Nat,
    |(base, exp)| {
        let digits = exp.as_inner().to_u32_digits();
        assert!(
            digits.len() <= 1,
            "nat.pow: oversize exponent (refusing to evaluate)"
        );
        base.pow(digits.first().copied().unwrap_or(0))
    }
}

canon_op! {
    /// `nat.shl` — left shift; the shift amount must fit `u64`/`usize`
    /// (else REFUSES by panic).
    NatShl("nat.shl"): (Nat, Nat) => Nat,
    |(a, s)| Nat::from_inner(a.as_inner() << shift_amount(s))
}

canon_op! {
    /// `nat.shr` — right shift; the shift amount must fit `u64`/`usize`
    /// (else REFUSES by panic).
    NatShr("nat.shr"): (Nat, Nat) => Nat,
    |(a, s)| Nat::from_inner(a.as_inner() >> shift_amount(s))
}

canon_op! {
    /// `nat.bitAnd`.
    NatBitAnd("nat.bitAnd"): (Nat, Nat) => Nat,
    |(a, b)| Nat::from_inner(a.as_inner() & b.as_inner())
}

canon_op! {
    /// `nat.bitOr`.
    NatBitOr("nat.bitOr"): (Nat, Nat) => Nat,
    |(a, b)| Nat::from_inner(a.as_inner() | b.as_inner())
}

canon_op! {
    /// `nat.bitXor`.
    NatBitXor("nat.bitXor"): (Nat, Nat) => Nat,
    |(a, b)| Nat::from_inner(a.as_inner() ^ b.as_inner())
}

canon_op! {
    /// `nat.le`.
    NatLe("nat.le"): (Nat, Nat) => bool,
    |(a, b)| a <= b
}

canon_op! {
    /// `nat.lt`.
    NatLt("nat.lt"): (Nat, Nat) => bool,
    |(a, b)| a < b
}

canon_op! {
    /// `nat.toInt` — the canonical embedding `nat → int`.
    NatToInt("nat.toInt"): Nat => Int,
    |n| {
        let sign = if n.is_zero() { Sign::Zero } else { Sign::Positive };
        Int::from_sign_nat(sign, n.clone())
    }
}

canon_op! {
    /// `nat.toBytesLe` — minimal little-endian byte encoding.
    NatToBytesLe("nat.toBytesLe"): Nat => Bytes,
    |n| Bytes::from(n.to_bytes_le())
}

canon_op! {
    /// `nat.toBytesBe` — minimal big-endian byte encoding.
    NatToBytesBe("nat.toBytesBe"): Nat => Bytes,
    |n| Bytes::from(n.to_bytes_be())
}

canon_op! {
    /// `nat.fromBytesLe`.
    NatFromBytesLe("nat.fromBytesLe"): Bytes => Nat,
    |b| Nat::from_bytes_le(b.as_ref())
}

canon_op! {
    /// `nat.fromBytesBe`.
    NatFromBytesBe("nat.fromBytesBe"): Bytes => Nat,
    |b| Nat::from_bytes_be(b.as_ref())
}
