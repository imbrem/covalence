//! `nat` builtins: arbitrary-precision natural-number ops over
//! [`covalence_types::Nat`].
//!
//! Every body transcribes the matching arm of `covalence-core`'s
//! `builtins.rs::eval_prim` exactly. Edge-case / totality conventions that
//! bear on soundness (all FORCED — see the crate docs); note that no `Nat` is
//! ever clamped to `usize`:
//!
//! - saturating predecessor and subtraction (`pred 0 = 0`, `a - b = 0` when
//!   `b > a`);
//! - `a / 0 = 0` and `a mod 0 = a` (NOT 0): `nat.mod`'s let-style body
//!   `λn m. n - (n/m)*m` evaluates to `n - 0 = n` at `m = 0`, so any other
//!   value would let definitional unfolding and this rule derive `n = 0` for
//!   every `n`;
//! - `nat.shl` (`a·2^s`) computes the true product where `s` fits `usize`
//!   (OOM-panic on a huge-but-representable result); it is `0` for `a = 0`, and
//!   REFUSES (`None`) when `a ≠ 0` and `s` exceeds `usize` (result ≥ 2^64 bits);
//! - `nat.shr` (`⌊a/2^s⌋`) is **total**: `0` for any `s ≥ 2^64` (any
//!   representable `a` has bit-length ≪ 2^64), so it never refuses;
//! - `nat.pow` (`base^exp`) is `0`/`1` for `base ∈ {0, 1}`, the true power where
//!   `exp` fits `u32` (OOM-panic acceptable), and REFUSES (`None`) when `exp`
//!   exceeds `u32`.

use covalence_types::{Bytes, Int, Nat, Sign};

use crate::NamedRule;

/// The shift amount as `usize`, or `None` if it exceeds `usize` (more than one
/// `u64` digit, or a single digit above `usize::MAX`). Never clamps — the caller
/// decides whether an over-`usize` shift means refuse (`shl`) or is trivially
/// out-of-range (`shr`).
fn shift_usize(shift: &Nat) -> Option<usize> {
    let digits = shift.as_inner().to_u64_digits();
    if digits.len() > 1 {
        return None;
    }
    usize::try_from(digits.first().copied().unwrap_or(0)).ok()
}

canon_op! {
    /// `nat.succ` — the successor (the kernel's primitive `succ` on a closed
    /// literal: `succ n = n + 1`, transcribing the succ arm of
    /// `builtins.rs`).
    NatSucc("nat.succ"): Nat => Nat,
    |n| n + &Nat::one()
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

canon_op_partial! {
    /// `nat.pow` (`base^exp`). Total for `base ∈ {0, 1}`; otherwise computes the
    /// true power where `exp` fits `u32` (may OOM-panic on a huge-but-representable
    /// result) and REFUSES (`None`) when `exp` exceeds `u32`. Never truncates.
    NatPow("nat.pow"): (Nat, Nat) => Nat,
    |(base, exp)| {
        if base.is_zero() {
            Some(if exp.is_zero() { Nat::one() } else { Nat::zero() })
        } else if *base == Nat::one() {
            Some(Nat::one())
        } else {
            let digits = exp.as_inner().to_u32_digits();
            if digits.len() > 1 {
                None
            } else {
                Some(base.pow(digits.first().copied().unwrap_or(0)))
            }
        }
    }
}

canon_op_partial! {
    /// `nat.shl` (`a·2^s`). `0` for `a = 0`; the true product where `s` fits `usize`
    /// (may OOM-panic on a huge-but-representable result); REFUSES (`None`) when
    /// `a ≠ 0` and `s` exceeds `usize` (result would need ≥ 2^64 bits). Never
    /// truncates.
    NatShl("nat.shl"): (Nat, Nat) => Nat,
    |(a, s)| {
        if a.is_zero() {
            Some(Nat::zero())
        } else {
            shift_usize(s).map(|s| Nat::from_inner(a.as_inner() << s))
        }
    }
}

canon_op_partial! {
    /// `nat.shr` (`⌊a/2^s⌋`) — **total**. Any `s` that exceeds `usize` is `≥ 2^64`,
    /// which is larger than the bit-length of any representable `a`, so the result is
    /// `0`; num-bigint drops limbs for a large in-`usize` `s`, so that is cheap too.
    NatShr("nat.shr"): (Nat, Nat) => Nat,
    |(a, s)| Some(match shift_usize(s) {
        Some(s) => Nat::from_inner(a.as_inner() >> s),
        None => Nat::zero(),
    })
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
