//! `bytes` builtins: flat byte-string ops over [`covalence_types::Bytes`],
//! computing through [`covalence_types::blob`] (the same single, tested
//! implementation `covalence-core`'s `builtins.rs` dispatches to).
//!
//! Conventions: the `consNat` operand is reduced mod 256 to a single byte;
//! `at`/`slice` are **total** over `Nat` indices/lengths — no op clamps a `Nat`
//! to `usize`. An out-of-range `at` index reads as 0; `slice` takes `(start, len)`
//! and yields the subslice `[min(start,len), …]` of the *real* buffer (an
//! over-range `start` gives empty, an over-long `len` stops at the end). Because
//! every index that reaches a `blob` op is `≤ bs.len() ≤ usize::MAX`, the `Nat →
//! usize` conversions are exact. `cat`/`consNat` may OOM-panic on allocation only.

use covalence_types::{Bytes, Nat, blob};

use crate::NamedRule;

/// `n mod 256` as a byte — transcribes `builtins.rs::nat_mod_256`.
fn nat_mod_256(n: &Nat) -> u8 {
    let modded = n.as_inner() % 256u32;
    // `BigUint % 256u32` fits in a single u32; pull the LSB.
    let digits = modded.to_u32_digits();
    digits.first().copied().unwrap_or(0) as u8
}

/// A `Nat` as `usize`, or `None` when it exceeds `usize` (more than one `u64`
/// digit, or a single digit above `usize::MAX`). **Never clamps** — callers only
/// convert indices already known to be `≤ bs.len() ≤ usize::MAX`, so the `expect`
/// at those sites is unreachable.
fn nat_to_usize(n: &Nat) -> Option<usize> {
    let digits = n.as_inner().to_u64_digits();
    if digits.len() > 1 {
        return None;
    }
    usize::try_from(digits.first().copied().unwrap_or(0)).ok()
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
    /// `bytes.at` — byte at index, or 0 out of bounds. **Total**: an index `≥`
    /// the buffer length reads as 0; otherwise the index is `< len ≤ usize::MAX`,
    /// so it fits `usize` exactly.
    BytesAt("bytes.at"): (Bytes, Nat) => Nat,
    |(bs, i)| {
        if *i >= Nat::from(bs.len()) {
            Nat::zero()
        } else {
            let idx = nat_to_usize(i).expect("index below buffer length fits usize");
            Nat::from(u32::from(blob::at(bs.as_ref(), idx)))
        }
    }
}

canon_op! {
    /// `bytes.slice` — the sub-string `(start, len)`. **Total**: clamped against
    /// the *real* length `n = |bs|` — `effective_start = min(start, n)`,
    /// `take = min(len, n − effective_start)`. Both are `≤ n ≤ usize::MAX`, so the
    /// `usize` conversions are exact and the result is always a subslice of `bs`.
    BytesSlice("bytes.slice"): (Bytes, Nat, Nat) => Bytes,
    |(bs, start, len)| {
        let n = Nat::from(bs.len());
        let effective_start = (*start).clone().min(n.clone());
        let avail = &n - &effective_start;
        let take = (*len).clone().min(avail);
        let start_usize = nat_to_usize(&effective_start).expect("start ≤ len fits usize");
        let take_usize = nat_to_usize(&take).expect("take ≤ len fits usize");
        blob::slice(bs.as_ref(), start_usize, take_usize)
    }
}
