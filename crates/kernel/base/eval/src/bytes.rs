//! `bytes` builtins: flat byte-string ops over [`covalence_types::Bytes`],
//! computing through [`covalence_types::blob`] (the same single, tested
//! implementation `covalence-core`'s `builtins.rs` dispatches to).
//!
//! Conventions (transcribed from `builtins.rs::eval_prim`): the `consNat`
//! operand is reduced mod 256 to a single byte; an out-of-bounds `at` index
//! reads as 0; `slice` takes `(start, len)` and saturates to the buffer.
//! Oversize `nat` indices (beyond `u64`/`usize`) clamp to `usize::MAX` and
//! are then clipped by the `blob` ops — same as the kernel's convention.

use covalence_types::{Bytes, Nat, blob};

use crate::NamedRule;

/// `n mod 256` as a byte — transcribes `builtins.rs::nat_mod_256`.
fn nat_mod_256(n: &Nat) -> u8 {
    let modded = n.as_inner() % 256u32;
    // `BigUint % 256u32` fits in a single u32; pull the LSB.
    let digits = modded.to_u32_digits();
    digits.first().copied().unwrap_or(0) as u8
}

/// A `Nat` as `usize`, mapping out-of-range values to `usize::MAX` (which
/// the `blob` ops clip) — transcribes `builtins.rs::nat_to_usize` composed
/// with its callers' `unwrap_or(usize::MAX)`.
fn nat_to_usize_clamped(n: &Nat) -> usize {
    let digits = n.as_inner().to_u64_digits();
    if digits.len() > 1 {
        return usize::MAX;
    }
    let v = digits.first().copied().unwrap_or(0);
    usize::try_from(v).unwrap_or(usize::MAX)
}

canon_op! {
    /// `bytes.cat` — concatenation.
    BytesCat("bytes.cat"): (Bytes, Bytes) => Bytes,
    |(a, b)| blob::cat(a.as_ref(), b.as_ref())
}

canon_op! {
    /// `bytes.consNat` — prepend a byte; the `nat` operand is reduced
    /// mod 256.
    BytesConsNat("bytes.consNat"): (Nat, Bytes) => Bytes,
    |(n, bs)| blob::cons(nat_mod_256(n), bs.as_ref())
}

canon_op! {
    /// `bytes.len`.
    BytesLen("bytes.len"): Bytes => Nat,
    |bs| Nat::from(bs.len())
}

canon_op! {
    /// `bytes.at` — byte at index, or 0 out of bounds.
    BytesAt("bytes.at"): (Bytes, Nat) => Nat,
    |(bs, i)| Nat::from(u32::from(blob::at(bs.as_ref(), nat_to_usize_clamped(i))))
}

canon_op! {
    /// `bytes.slice` — the sub-string `(start, len)`, saturating to the
    /// buffer.
    BytesSlice("bytes.slice"): (Bytes, Nat, Nat) => Bytes,
    |(bs, start, len)| blob::slice(
        bs.as_ref(),
        nat_to_usize_clamped(start),
        nat_to_usize_clamped(len),
    )
}
