//! Property tests for the `Builtins` CanonRules — totality / refusal
//! boundaries and algebraic cross-checks over the FULL claimed domain,
//! with adversarial value generators (stage P2 of the kernel property
//! campaign; the example-based commitments live in `semantics.rs`).
//!
//! What is checked, per the crate-doc contract ("Refusal vs. totality
//! vs. OOM"):
//!
//! - **Totality claims**: `nat.shr`, `bytes.at`, `bytes.slice` NEVER
//!   refuse — asserted with `.expect(...)` over generators that include
//!   huge (multi-`u64`-digit) shift amounts / indices / lengths.
//! - **Refusal claims**: `nat.shl` / `nat.pow` refuse EXACTLY where
//!   documented (`a ≠ 0 ∧ s > usize` / `base ≥ 2 ∧ exp ≥ 2^32`) and
//!   compute everywhere else we can afford to evaluate (the
//!   in-between region — representable but astronomically large — is
//!   the documented OOM-acceptable domain and is deliberately NOT
//!   evaluated here).
//! - **Algebraic cross-checks** against independent reference
//!   computations: ring laws, the div/mod invariant `a = (a/b)·b + a%b`
//!   under the FORCED `b = 0` conventions, shift/pow/div consistency,
//!   byte-wise references for the bitwise ops, encode/decode round
//!   trips.
//! - **Target independence** (the wasm32 `nat.shr` lesson): the
//!   `shr = 0` boundary is asserted as a pure bit-length property
//!   (`result = 0 ⟺ s ≥ bits(a)`), which is the cfg-independent form
//!   of the fix, plus a source tripwire pinning that the guard is
//!   written against `bits()` and not a `usize` conversion.
//! - **Fixed-width ops**: every `u8…u64`/`s8…s64` family member and the
//!   full 8×8 `zext`/`sext` cast grid, cross-checked against native
//!   Rust integer semantics (an independent implementation of the same
//!   WebAssembly-style spec).
//!
//! The `expect`-guarded `Nat → usize` conversions inside `bytes.at` /
//! `bytes.slice` (see `src/bytes.rs::nat_to_usize`) are exercised over
//! this adversarial domain, pinning their panic-free envelope.
//!
//! Case counts use proptest defaults (env-overridable via
//! `PROPTEST_CASES`); the big-buffer suites set a smaller default via
//! [`covalence_proptest::cases`] for CI cost — a hard-coded `cases:`
//! would override the env var and silently defeat high-count sweeps.

use covalence_proptest::cases;
use covalence_proptest::proptest::collection::vec as pvec;
use covalence_proptest::proptest::prelude::*;
use covalence_proptest::proptest::sample::select;
use covalence_pure::CanonRule;
use covalence_pure_eval::*;
use covalence_types::{Bytes, Int, Nat, Sign};

// ===========================================================================
// Helpers
// ===========================================================================

/// `n` as `u128`, or `None` if it does not fit — via the little-endian byte
/// encoding, independent of `usize` and of the ops under test.
fn nat_to_u128(n: &Nat) -> Option<u128> {
    let b = n.to_bytes_le();
    if b.iter().skip(16).any(|&x| x != 0) {
        return None;
    }
    let mut v: u128 = 0;
    for (i, &byte) in b.iter().take(16).enumerate() {
        v |= (byte as u128) << (8 * i);
    }
    Some(v)
}

/// Byte-wise reference for the `nat` bitwise ops, computed on the LE
/// encodings — an implementation independent of `num-bigint`'s limb ops.
fn bytewise(a: &Nat, b: &Nat, f: impl Fn(u8, u8) -> u8) -> Nat {
    let (x, y) = (a.to_bytes_le(), b.to_bytes_le());
    let n = x.len().max(y.len());
    let mut out = vec![0u8; n];
    for (i, o) in out.iter_mut().enumerate() {
        *o = f(*x.get(i).unwrap_or(&0), *y.get(i).unwrap_or(&0));
    }
    Nat::from_bytes_le(&out)
}

// ===========================================================================
// Generators — adversarial by construction
// ===========================================================================

/// Boundary values around the `u32` / `u64` / `usize` representation
/// edges (the class both prior ⊢False bugs lived in).
fn nat_boundary() -> impl Strategy<Value = Nat> {
    let vals: Vec<u128> = vec![
        0,
        1,
        2,
        (1u128 << 32) - 1,
        1u128 << 32,
        (1u128 << 32) + 1,
        (1u128 << 64) - 1,
        1u128 << 64,
        (1u128 << 64) + 1,
        usize::MAX as u128,
        usize::MAX as u128 + 1,
        u128::MAX,
    ];
    select(vals).prop_map(Nat::from)
}

/// Bit-length-ramped `Nat`: a random little-endian payload whose byte
/// length ramps from 0 to 4 KiB (up to ~32k bits).
fn nat_ramp() -> impl Strategy<Value = Nat> {
    (0usize..=4096)
        .prop_flat_map(|len| pvec(any::<u8>(), len..=len))
        .prop_map(|bytes| Nat::from_bytes_le(&bytes))
}

/// The full adversarial `Nat` domain: small, boundary, and huge.
fn nat_any() -> impl Strategy<Value = Nat> {
    prop_oneof![
        3 => any::<u64>().prop_map(Nat::from),
        2 => nat_boundary(),
        2 => nat_ramp(),
    ]
}

/// The full adversarial `Int` domain: both signs over [`nat_any`].
fn int_any() -> impl Strategy<Value = Int> {
    (any::<bool>(), nat_any()).prop_map(|(neg, mag)| {
        if mag.is_zero() {
            Int::zero()
        } else {
            let sign = if neg { Sign::Negative } else { Sign::Positive };
            Int::from_sign_nat(sign, mag)
        }
    })
}

/// Bytes: empty through ~64 KiB. The large branch fills via a cheap LCG
/// (shrinks on `(len, seed)`, not element-wise). Megabyte-shaped buffers
/// are exercised in the deterministic `megabyte_buffer_edges` test.
fn bytes_any() -> impl Strategy<Value = Bytes> {
    let lcg = |(len, seed): (usize, u64)| {
        let mut x = seed | 1;
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            x = x
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            v.push((x >> 56) as u8);
        }
        Bytes::from(v)
    };
    prop_oneof![
        4 => pvec(any::<u8>(), 0..=64).prop_map(Bytes::from),
        2 => (64usize..=4096, any::<u64>()).prop_map(lcg),
        1 => (4096usize..=65536, any::<u64>()).prop_map(lcg),
    ]
}

/// Adversarial index/length domain: dense small values plus the full
/// boundary/huge `Nat` domain.
fn nat_index() -> impl Strategy<Value = Nat> {
    prop_oneof![
        3 => (0u64..=70000).prop_map(Nat::from),
        2 => nat_any(),
    ]
}

// ===========================================================================
// nat — ring laws, saturation, the FORCED div/mod conventions
// ===========================================================================

proptest! {
    /// Commutativity / associativity / distributivity of `nat.add` /
    /// `nat.mul`, cross-checked against direct `num-bigint` arithmetic.
    #[test]
    fn nat_ring_laws(a in nat_any(), b in nat_any(), c in nat_any()) {
        let add = |x: &Nat, y: &Nat| NatAdd.eval(&(x.clone(), y.clone())).unwrap();
        let mul = |x: &Nat, y: &Nat| NatMul.eval(&(x.clone(), y.clone())).unwrap();
        // reference agreement (num-bigint via the wrapper's value ops)
        prop_assert_eq!(add(&a, &b), &a + &b);
        prop_assert_eq!(mul(&a, &b), &a * &b);
        // commutativity
        prop_assert_eq!(add(&a, &b), add(&b, &a));
        prop_assert_eq!(mul(&a, &b), mul(&b, &a));
        // associativity
        prop_assert_eq!(add(&add(&a, &b), &c), add(&a, &add(&b, &c)));
        prop_assert_eq!(mul(&mul(&a, &b), &c), mul(&a, &mul(&b, &c)));
        // distributivity
        prop_assert_eq!(mul(&a, &add(&b, &c)), add(&mul(&a, &b), &mul(&a, &c)));
        // identities
        prop_assert_eq!(add(&a, &Nat::zero()), a.clone());
        prop_assert_eq!(mul(&a, &Nat::one()), a.clone());
        prop_assert_eq!(mul(&a, &Nat::zero()), Nat::zero());
    }

    /// `nat.sub` saturates; `nat.succ`/`nat.pred` are inverse where defined.
    #[test]
    fn nat_sub_succ_pred(a in nat_any(), b in nat_any()) {
        let s = NatSub.eval(&(a.clone(), b.clone())).unwrap();
        if a >= b {
            prop_assert_eq!(&s + &b, a.clone(), "a ∸ b + b = a when b ≤ a");
        } else {
            prop_assert!(s.is_zero(), "a ∸ b = 0 when b > a");
        }
        let sa = NatSucc.eval(&a).unwrap();
        prop_assert_eq!(&sa, &(&a + &Nat::one()));
        prop_assert_eq!(NatPred.eval(&sa).unwrap(), a.clone());
        prop_assert_eq!(NatPred.eval(&Nat::zero()).unwrap(), Nat::zero());
    }

    /// The Euclidean invariant `a = (a/b)·b + a mod b` holds on the WHOLE
    /// domain — including `b = 0` under the FORCED conventions
    /// (`a/0 = 0`, `a mod 0 = a`), which is exactly why those conventions
    /// are the sound pair. For `b ≠ 0` the remainder is strictly below `b`.
    #[test]
    fn nat_divmod_invariant(a in nat_any(), b in nat_any()) {
        let d = NatDiv.eval(&(a.clone(), b.clone())).unwrap();
        let m = NatMod.eval(&(a.clone(), b.clone())).unwrap();
        prop_assert_eq!(&(&d * &b) + &m, a.clone(), "a = (a/b)*b + a%b");
        if b.is_zero() {
            prop_assert!(d.is_zero(), "a / 0 = 0");
            prop_assert_eq!(&m, &a);
        } else {
            prop_assert!(m < b, "a mod b < b for b ≠ 0");
            prop_assert_eq!(d, &a / &b);
        }
    }

    /// `nat.le` / `nat.lt` agree with the value order and with each other.
    #[test]
    fn nat_comparisons_are_the_order(a in nat_any(), b in nat_any()) {
        let le = NatLe.eval(&(a.clone(), b.clone())).unwrap();
        let lt = NatLt.eval(&(a.clone(), b.clone())).unwrap();
        prop_assert_eq!(le, a <= b);
        prop_assert_eq!(lt, a < b);
        prop_assert_eq!(lt, le && a != b);
    }

    /// Bitwise ops match an independent byte-wise reference on the LE
    /// encodings, plus the classical identities.
    #[test]
    fn nat_bitops_bytewise_reference(a in nat_any(), b in nat_any()) {
        let and = NatBitAnd.eval(&(a.clone(), b.clone())).unwrap();
        let or = NatBitOr.eval(&(a.clone(), b.clone())).unwrap();
        let xor = NatBitXor.eval(&(a.clone(), b.clone())).unwrap();
        prop_assert_eq!(&and, &bytewise(&a, &b, |x, y| x & y));
        prop_assert_eq!(&or, &bytewise(&a, &b, |x, y| x | y));
        prop_assert_eq!(&xor, &bytewise(&a, &b, |x, y| x ^ y));
        // (a & b) + (a | b) = a + b
        prop_assert_eq!(&and + &or, &a + &b);
        // xor involution: (a ^ b) ^ b = a
        prop_assert_eq!(NatBitXor.eval(&(xor, b.clone())).unwrap(), a.clone());
    }
}

// ===========================================================================
// nat — shift / pow totality and refusal boundaries
// ===========================================================================

proptest! {
    /// TOTALITY + target independence: `nat.shr` never refuses, and its
    /// zero boundary is a pure bit-length property — `⌊a/2^s⌋ = 0 ⟺
    /// s ≥ bits(a)` — with no `usize` in the statement (the wasm32
    /// ⊢False lesson, asserted cfg-independently).
    #[test]
    fn nat_shr_total_and_bitlength_keyed(a in nat_any(), s in nat_any()) {
        let r = NatShr
            .eval(&(a.clone(), s.clone()))
            .expect("nat.shr is TOTAL: it must never refuse");
        let bits = Nat::from(a.as_inner().bits());
        prop_assert_eq!(
            r.is_zero(),
            s >= bits,
            "shr is zero exactly when the shift ≥ the operand's bit-length"
        );
    }

    /// `nat.shr` value agreement with direct `num-bigint` shifting, and
    /// path consistency `a >> s = a / 2^s` (shr vs pow+div).
    #[test]
    fn nat_shr_matches_reference(a in nat_any(), s in 0u32..=600) {
        let sn = Nat::from(u64::from(s));
        let r = NatShr.eval(&(a.clone(), sn.clone())).unwrap();
        prop_assert_eq!(&r, &Nat::from_inner(a.as_inner() >> (s as usize)));
        let p = NatPow.eval(&(Nat::from(2u64), sn)).unwrap();
        prop_assert_eq!(r, NatDiv.eval(&(a, p)).unwrap());
    }

    /// `nat.shl` at `a = 0` is total: `0 · 2^s = 0` for EVERY `s`,
    /// including multi-digit shifts.
    #[test]
    fn nat_shl_zero_operand_total(s in nat_any()) {
        prop_assert_eq!(NatShl.eval(&(Nat::zero(), s)), Some(Nat::zero()));
    }

    /// REFUSAL boundary: for `s > usize::MAX` (strictly above the
    /// documented boundary) `nat.shl` refuses exactly when `a ≠ 0` —
    /// never computes a truncated value, never refuses the `a = 0` case.
    #[test]
    fn nat_shl_refuses_exactly_oversize(a in nat_any(), extra in nat_any()) {
        let s = &Nat::from(usize::MAX) + &(&Nat::one() + &extra);
        let r = NatShl.eval(&(a.clone(), s));
        if a.is_zero() {
            prop_assert_eq!(r, Some(Nat::zero()));
        } else {
            prop_assert_eq!(r, None, "a ≠ 0 with an over-usize shift must REFUSE");
        }
    }

    /// `nat.shl` value agreement (`a·2^s` via direct `num-bigint`), plus
    /// consistency across paths: `shl(a,s) = a · 2^s = mul(a, pow(2,s))`
    /// and `shr(shl(a,s), s) = a`.
    #[test]
    fn nat_shl_matches_reference(a in nat_any(), s in 0u32..=600) {
        let sn = Nat::from(u64::from(s));
        let r = NatShl.eval(&(a.clone(), sn.clone())).expect("in-range shl computes");
        prop_assert_eq!(&r, &Nat::from_inner(a.as_inner() << (s as usize)));
        let p = NatPow.eval(&(Nat::from(2u64), sn.clone())).unwrap();
        prop_assert_eq!(&r, &NatMul.eval(&(a.clone(), p)).unwrap());
        prop_assert_eq!(NatShr.eval(&(r, sn)).unwrap(), a);
    }

    /// REFUSAL boundary: for `exp ≥ 2^32` (the documented `u32` edge,
    /// hit exactly at `extra = 0`) `nat.pow` refuses UNLESS the base is
    /// `0`/`1`, where the true value is known for every exponent.
    #[test]
    fn nat_pow_refuses_exactly_oversize(base in nat_any(), extra in nat_any()) {
        let exp = &Nat::from(u32::MAX) + &(&Nat::one() + &extra); // = 2^32 + extra
        let r = NatPow.eval(&(base.clone(), exp.clone()));
        if base.is_zero() {
            prop_assert_eq!(r, Some(Nat::zero()), "0^(huge ≥ 1) = 0");
        } else if base.is_one() {
            prop_assert_eq!(r, Some(Nat::one()));
        } else {
            prop_assert_eq!(r, None, "base ≥ 2 with exp ≥ 2^32 must REFUSE");
        }
    }

    /// `nat.pow` value agreement with iterated multiplication (an
    /// independent reference), on the affordable exponent range.
    #[test]
    fn nat_pow_matches_iterated_mul(base in nat_any(), exp in 0u32..=24) {
        let mut acc = Nat::one();
        for _ in 0..exp {
            acc = &acc * &base;
        }
        prop_assert_eq!(NatPow.eval(&(base, Nat::from(u64::from(exp)))).unwrap(), acc);
    }
}

/// Just below the `u32` boundary (`exp = 2^32 − 1`) the trivial bases
/// still compute — the boundary is exact, not approximate. (Bases ≥ 2
/// there are the documented OOM-acceptable domain: representable, not
/// evaluated.)
#[test]
fn nat_pow_below_boundary_trivial_bases_compute() {
    let exp = Nat::from(u32::MAX);
    assert_eq!(NatPow.eval(&(Nat::zero(), exp.clone())), Some(Nat::zero()));
    assert_eq!(NatPow.eval(&(Nat::one(), exp)), Some(Nat::one()));
}

/// Source tripwire for target independence (the wasm32 `nat.shr` lesson):
/// the `shr = 0` guard must be expressed against the operand's actual
/// bit-length (`bits()`, a `u64` fact about the VALUE), never through a
/// `usize`-flavoured conversion whose meaning changes per target.
#[test]
fn nat_shr_guard_is_written_against_bit_length() {
    let src = include_str!("../src/nat.rs");
    let shr = src
        .split("NatShr(\"nat.shr\")")
        .nth(1)
        .expect("NatShr op present in src/nat.rs");
    let body = &shr[..shr.find("canon_op").unwrap_or(shr.len())];
    let bits_at = body
        .find(".bits()")
        .expect("nat.shr's zero guard must compare against the operand's bit-length");
    // The usize-flavoured conversion (`shift_usize`, refusal plumbing only)
    // must come strictly AFTER the bit-length guard — clamping the shift
    // through usize before deciding the zero case is the wasm32 ⊢False shape.
    let usize_at = body
        .find("shift_usize")
        .expect("the computing branch converts the in-range shift via shift_usize");
    assert!(
        bits_at < usize_at,
        "nat.shr must decide the zero boundary via bit-length BEFORE any \
         usize conversion of the shift (the wasm32 ⊢False bug shape)"
    );
}

// ===========================================================================
// nat — coercions and byte encodings
// ===========================================================================

proptest! {
    /// LE/BE encode/decode round trips, BE = reverse(LE), and high-zero
    /// padding invariance of decoding.
    #[test]
    fn nat_bytes_roundtrips(n0 in nat_any(), pad in 0usize..4) {
        let le = NatToBytesLe.eval(&n0).unwrap();
        let be = NatToBytesBe.eval(&n0).unwrap();
        prop_assert_eq!(NatFromBytesLe.eval(&le).unwrap(), n0.clone());
        prop_assert_eq!(NatFromBytesBe.eval(&be).unwrap(), n0.clone());
        let mut rev = le.as_ref().to_vec();
        rev.reverse();
        prop_assert_eq!(be.as_ref(), &rev[..]);
        // decoding ignores high-zero padding (LE: trailing, BE: leading)
        let mut padded_le = le.as_ref().to_vec();
        padded_le.extend(std::iter::repeat_n(0u8, pad));
        prop_assert_eq!(NatFromBytesLe.eval(&Bytes::from(padded_le)).unwrap(), n0.clone());
        let mut padded_be = vec![0u8; pad];
        padded_be.extend_from_slice(be.as_ref());
        prop_assert_eq!(NatFromBytesBe.eval(&Bytes::from(padded_be)).unwrap(), n0);
    }

    /// `nat.toInt` is the order-preserving non-negative embedding.
    #[test]
    fn nat_to_int_embedding(a in nat_any(), b in nat_any()) {
        let ia = NatToInt.eval(&a).unwrap();
        let ib = NatToInt.eval(&b).unwrap();
        prop_assert_eq!(ia.abs(), a.clone());
        prop_assert!(!ia.is_negative());
        prop_assert_eq!(ia.is_zero(), a.is_zero());
        prop_assert_eq!(ia <= ib, a <= b);
    }
}

// ===========================================================================
// int — ring laws, the FORCED div/mod conventions, abs/sgn
// ===========================================================================

proptest! {
    /// Ring laws for `int`, cross-checked against direct `num-bigint`
    /// arithmetic; `sub = add ∘ neg`; succ/pred inverses.
    #[test]
    fn int_ring_laws(a in int_any(), b in int_any(), c in int_any()) {
        let add = |x: &Int, y: &Int| IntAdd.eval(&(x.clone(), y.clone())).unwrap();
        let mul = |x: &Int, y: &Int| IntMul.eval(&(x.clone(), y.clone())).unwrap();
        prop_assert_eq!(add(&a, &b), &a + &b);
        prop_assert_eq!(mul(&a, &b), &a * &b);
        prop_assert_eq!(add(&a, &b), add(&b, &a));
        prop_assert_eq!(mul(&a, &b), mul(&b, &a));
        prop_assert_eq!(add(&add(&a, &b), &c), add(&a, &add(&b, &c)));
        prop_assert_eq!(mul(&mul(&a, &b), &c), mul(&a, &mul(&b, &c)));
        prop_assert_eq!(mul(&a, &add(&b, &c)), add(&mul(&a, &b), &mul(&a, &c)));
        // neg / sub
        let na = IntNeg.eval(&a).unwrap();
        prop_assert_eq!(IntNeg.eval(&na).unwrap(), a.clone());
        prop_assert!(add(&a, &na).is_zero());
        prop_assert_eq!(IntSub.eval(&(a.clone(), b.clone())).unwrap(), add(&a, &IntNeg.eval(&b).unwrap()));
        // succ / pred
        let sa = IntSucc.eval(&a).unwrap();
        prop_assert_eq!(IntPred.eval(&sa).unwrap(), a.clone());
        prop_assert_eq!(IntSucc.eval(&IntPred.eval(&a).unwrap()).unwrap(), a.clone());
    }

    /// `a = (a/b)·b + a%b` on the WHOLE domain (`a/0 = 0`, `a%0 = a`
    /// FORCED); for `b ≠ 0`: truncation toward zero, `|a%b| < |b|`, and
    /// the remainder takes the dividend's sign.
    #[test]
    fn int_divmod_invariant(a in int_any(), b in int_any()) {
        let d = IntDiv.eval(&(a.clone(), b.clone())).unwrap();
        let m = IntMod.eval(&(a.clone(), b.clone())).unwrap();
        prop_assert_eq!(&(&d * &b) + &m, a.clone(), "a = (a/b)*b + a%b");
        if b.is_zero() {
            prop_assert!(d.is_zero(), "a / 0 = 0");
            prop_assert_eq!(&m, &a, "a mod 0 = a");
        } else {
            prop_assert!(m.abs() < b.abs(), "|a%b| < |b|");
            prop_assert!(
                m.is_zero() || (m.is_negative() == a.is_negative()),
                "remainder takes the dividend's sign"
            );
            // truncation toward zero: (−a)/b = −(a/b)
            let neg_a = IntNeg.eval(&a).unwrap();
            prop_assert_eq!(
                IntDiv.eval(&(neg_a, b.clone())).unwrap(),
                IntNeg.eval(&d).unwrap()
            );
        }
    }

    /// `sgn(a) · |a| = a`, with `|·|` landing in `nat` and re-embedded
    /// via `nat.toInt`.
    #[test]
    fn int_abs_sgn_decomposition(a in int_any()) {
        let s = IntSgn.eval(&a).unwrap();
        let mag = IntAbs.eval(&a).unwrap();
        let mag_int = NatToInt.eval(&mag).unwrap();
        prop_assert_eq!(IntMul.eval(&(s.clone(), mag_int)).unwrap(), a.clone());
        prop_assert_eq!(s.is_zero(), a.is_zero());
        prop_assert_eq!(s.is_negative(), a.is_negative());
    }

    /// `int.le` / `int.lt` agree with the value order and each other.
    #[test]
    fn int_comparisons_are_the_order(a in int_any(), b in int_any()) {
        let le = IntLe.eval(&(a.clone(), b.clone())).unwrap();
        let lt = IntLt.eval(&(a.clone(), b.clone())).unwrap();
        prop_assert_eq!(le, a <= b);
        prop_assert_eq!(lt, a < b);
        prop_assert_eq!(lt, le && a != b);
    }
}

// ===========================================================================
// bytes — totality over Nat indices/lengths, reference agreement
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: cases(96),
        ..ProptestConfig::default()
    })]

    /// `bytes.cat` / `bytes.len` / `bytes.consNat`: monoid laws, length
    /// arithmetic, and the mod-256 cons against independent references.
    #[test]
    fn bytes_cat_len_cons(a in bytes_any(), b in bytes_any(), c in bytes_any(), n0 in nat_any()) {
        let cat = |x: &Bytes, y: &Bytes| BytesCat.eval(&(x.clone(), y.clone())).unwrap();
        let len = |x: &Bytes| BytesLen.eval(&x.clone()).unwrap();
        // reference: Vec concatenation
        let mut r = a.as_ref().to_vec();
        r.extend_from_slice(b.as_ref());
        let ab = cat(&a, &b);
        prop_assert_eq!(ab.as_ref(), &r[..]);
        // monoid
        let empty = Bytes::from(Vec::new());
        prop_assert_eq!(cat(&cat(&a, &b), &c), cat(&a, &cat(&b, &c)));
        prop_assert_eq!(cat(&a, &empty), a.clone());
        prop_assert_eq!(cat(&empty, &a), a.clone());
        prop_assert_eq!(len(&cat(&a, &b)), &len(&a) + &len(&b));
        prop_assert_eq!(len(&a), Nat::from(a.len()));
        // consNat = cat of the single mod-256 byte; independent reference:
        // the LOW LE byte of the nat operand.
        let low = *n0.to_bytes_le().first().unwrap_or(&0);
        let consed = BytesConsNat.eval(&(n0.clone(), b.clone())).unwrap();
        prop_assert_eq!(&consed, &cat(&Bytes::from(vec![low]), &b));
        prop_assert_eq!(
            NatMod.eval(&(n0, Nat::from(256u64))).unwrap(),
            Nat::from(u64::from(low)),
            "cross-check: the consed byte IS n mod 256"
        );
    }

    /// TOTALITY + reference: `bytes.at` never refuses; in-range indices
    /// read the buffer, everything else (including multi-digit `Nat`
    /// indices) reads 0. Exercises the guarded `expect` in
    /// `src/bytes.rs::nat_to_usize` over the adversarial domain.
    #[test]
    fn bytes_at_total_reference(bs in bytes_any(), i in nat_index()) {
        let r = BytesAt
            .eval(&(bs.clone(), i.clone()))
            .expect("bytes.at is TOTAL: it must never refuse");
        let expected = match nat_to_u128(&i) {
            Some(v) if (v as usize) < bs.len() && v <= usize::MAX as u128 => {
                Nat::from(u64::from(bs.as_ref()[v as usize]))
            }
            _ => Nat::zero(), // out of range (incl. beyond u128): reads 0
        };
        prop_assert_eq!(r, expected);
    }

    /// TOTALITY + reference: `bytes.slice` never refuses; start/len clamp
    /// against the REAL buffer length; identities and `at`-composition.
    #[test]
    fn bytes_slice_total_reference(bs in bytes_any(), start in nat_index(), len in nat_index()) {
        let r = BytesSlice
            .eval(&(bs.clone(), start.clone(), len.clone()))
            .expect("bytes.slice is TOTAL: it must never refuse");
        // independent reference in usize space (buffer lengths ≤ 64 KiB, so
        // an index that overflows u128 is certainly ≥ the length: clamp).
        let n = bs.len();
        let s = nat_to_u128(&start).map_or(n, |v| (v.min(n as u128)) as usize);
        let l = nat_to_u128(&len).map_or(n - s, |v| (v.min((n - s) as u128)) as usize);
        prop_assert_eq!(r.as_ref(), &bs.as_ref()[s..s + l]);
        // length law: |slice(bs, s, l)| = min(l, |bs| ∸ s)
        prop_assert_eq!(
            BytesLen.eval(&r.clone()).unwrap(),
            NatSub.eval(&(Nat::from(n), start.clone())).unwrap().min(
                match nat_to_u128(&len) { Some(v) if v <= n as u128 => Nat::from(v), _ => Nat::from(n) }
            )
        );
        // whole-buffer identity
        prop_assert_eq!(
            BytesSlice.eval(&(bs.clone(), Nat::zero(), Nat::from(n))).unwrap(),
            bs.clone()
        );
        // at ∘ slice: reading inside the slice reads the source
        if !r.is_empty() {
            let mid = Nat::from(r.len() / 2);
            prop_assert_eq!(
                BytesAt.eval(&(r.clone(), mid.clone())).unwrap(),
                BytesAt.eval(&(bs, &Nat::from(s) + &mid)).unwrap()
            );
        }
    }
}

/// Megabyte-shaped buffer with boundary and beyond-`u64` indices — the
/// deterministic heavyweight case (kept out of the generators for CI cost).
#[test]
fn megabyte_buffer_edges() {
    let len: usize = 1 << 20;
    let v: Vec<u8> = (0..len)
        .map(|i| (i.wrapping_mul(31).wrapping_add(7)) as u8)
        .collect();
    let bs = Bytes::from(v.clone());
    let huge = &Nat::from(u64::MAX) + &Nat::one(); // 2^64
    // len
    assert_eq!(BytesLen.eval(&bs.clone()), Some(Nat::from(len)));
    // at: first, last, one-past, huge
    assert_eq!(
        BytesAt.eval(&(bs.clone(), Nat::zero())),
        Some(Nat::from(u64::from(v[0])))
    );
    assert_eq!(
        BytesAt.eval(&(bs.clone(), Nat::from(len - 1))),
        Some(Nat::from(u64::from(v[len - 1])))
    );
    assert_eq!(
        BytesAt.eval(&(bs.clone(), Nat::from(len))),
        Some(Nat::zero())
    );
    assert_eq!(BytesAt.eval(&(bs.clone(), huge.clone())), Some(Nat::zero()));
    // slice: interior window, over-long len (clamps to end), huge start (empty),
    // huge len (whole tail)
    assert_eq!(
        BytesSlice
            .eval(&(bs.clone(), Nat::from(len - 3), Nat::from(100u64)))
            .unwrap()
            .as_ref(),
        &v[len - 3..]
    );
    assert_eq!(
        BytesSlice
            .eval(&(bs.clone(), huge.clone(), Nat::from(3u64)))
            .unwrap(),
        Bytes::from(Vec::new())
    );
    assert_eq!(
        BytesSlice.eval(&(bs.clone(), Nat::zero(), huge)).unwrap(),
        bs.clone()
    );
    // cat with itself: 2 MiB, length adds
    let doubled = BytesCat.eval(&(bs.clone(), bs)).unwrap();
    assert_eq!(doubled.len(), 2 * len);
}

// ===========================================================================
// fixed-width — every family member vs native Rust integer semantics
// ===========================================================================

/// One suite per representation: all 20 family ops cross-checked against
/// native Rust integers (an independent implementation of the same
/// WebAssembly-style semantics), plus the nat/int conversion boundaries
/// with adversarial arbitrary-precision inputs.
macro_rules! fw_suite {
    ($modname:ident, $t:ty, $ut:ty) => {
        mod $modname {
            use super::*;

            /// Full-range values with the classical edge cases mixed in.
            fn val() -> impl Strategy<Value = $t> {
                prop_oneof![
                    3 => any::<$t>(),
                    1 => select(vec![
                        <$t>::MIN,
                        <$t>::MAX,
                        0 as $t,
                        1 as $t,
                        (0 as $t).wrapping_sub(1),
                    ]),
                ]
            }

            proptest! {
                #[test]
                fn binops_match_native(a in val(), b in val()) {
                    prop_assert_eq!(FwAdd::<$t>::new().eval(&(a, b)), Some(a.wrapping_add(b)));
                    prop_assert_eq!(FwSub::<$t>::new().eval(&(a, b)), Some(a.wrapping_sub(b)));
                    prop_assert_eq!(FwMul::<$t>::new().eval(&(a, b)), Some(a.wrapping_mul(b)));
                    // div/rem: x/0 = 0, x rem 0 = x (FORCED); else native
                    // wrapping semantics (MIN/−1 wraps, rem = 0).
                    let d = FwDiv::<$t>::new().eval(&(a, b)).unwrap();
                    let r = FwRem::<$t>::new().eval(&(a, b)).unwrap();
                    if b == 0 {
                        prop_assert_eq!(d, 0);
                        prop_assert_eq!(r, a);
                    } else {
                        prop_assert_eq!(d, a.wrapping_div(b));
                        prop_assert_eq!(r, a.wrapping_rem(b));
                    }
                    // the invariant closes wrapping-ly on the WHOLE domain
                    prop_assert_eq!(d.wrapping_mul(b).wrapping_add(r), a);
                    // bitwise
                    prop_assert_eq!(FwAnd::<$t>::new().eval(&(a, b)), Some(a & b));
                    prop_assert_eq!(FwOr::<$t>::new().eval(&(a, b)), Some(a | b));
                    prop_assert_eq!(FwXor::<$t>::new().eval(&(a, b)), Some(a ^ b));
                    // shifts: amount = UNSIGNED bit value of b, mod width
                    let s = ((b as $ut) % (<$t>::BITS as $ut)) as u32;
                    prop_assert_eq!(FwShl::<$t>::new().eval(&(a, b)), Some(a.wrapping_shl(s)));
                    prop_assert_eq!(FwShr::<$t>::new().eval(&(a, b)), Some(a.wrapping_shr(s)));
                    // comparisons read the type's signedness = native Ord
                    prop_assert_eq!(FwLt::<$t>::new().eval(&(a, b)), Some(a < b));
                    prop_assert_eq!(FwLe::<$t>::new().eval(&(a, b)), Some(a <= b));
                    prop_assert_eq!(FwGt::<$t>::new().eval(&(a, b)), Some(a > b));
                    prop_assert_eq!(FwGe::<$t>::new().eval(&(a, b)), Some(a >= b));
                }

                #[test]
                fn unary_and_conversions(a in val(), n0 in nat_any(), z0 in int_any()) {
                    prop_assert_eq!(FwNeg::<$t>::new().eval(&a), Some(a.wrapping_neg()));
                    prop_assert_eq!(FwNot::<$t>::new().eval(&a), Some(!a));
                    // value reads: toNat = unsigned bits, toInt = typed value
                    // (`as i128` is value-preserving for all eight types)
                    let n = FwToNat::<$t>::new().eval(&a).unwrap();
                    prop_assert_eq!(&n, &Nat::from((a as $ut) as u128));
                    let z = FwToInt::<$t>::new().eval(&a).unwrap();
                    prop_assert_eq!(&z, &Int::from(a as i128));
                    // round trips: store(value(a)) = a on both routes
                    prop_assert_eq!(FwFromNat::<$t>::new().eval(&n), Some(a));
                    prop_assert_eq!(FwFromInt::<$t>::new().eval(&z), Some(a));
                    // fromNat = n mod 2^w, adversarial arbitrary-precision n
                    let modulus = Nat::from(1u128 << <$t>::BITS);
                    let low = nat_to_u128(&(&n0 % &modulus)).expect("residue < 2^64");
                    prop_assert_eq!(FwFromNat::<$t>::new().eval(&n0), Some(low as $t));
                    // fromInt = two's-complement residue, adversarial z
                    let mi = Int::from(1u128 << <$t>::BITS);
                    let euclid = &(&(&z0 % &mi) + &mi) % &mi; // ∈ [0, 2^w)
                    let elow = nat_to_u128(&euclid.abs()).expect("residue < 2^64");
                    prop_assert_eq!(FwFromInt::<$t>::new().eval(&z0), Some(elow as $t));
                }
            }
        }
    };
}

fw_suite!(fw_u8, u8, u8);
fw_suite!(fw_u16, u16, u16);
fw_suite!(fw_u32, u32, u32);
fw_suite!(fw_u64, u64, u64);
fw_suite!(fw_i8, i8, u8);
fw_suite!(fw_i16, i16, u16);
fw_suite!(fw_i32, i32, u32);
fw_suite!(fw_i64, i64, u64);

// ===========================================================================
// the 8×8 zext/sext cast grid vs native `as` casts
// ===========================================================================

/// `zext` must equal casting through the source-width UNSIGNED type and
/// `sext` through the source-width SIGNED type — native Rust `as` chains,
/// independent of the 128-bit `value_u`/`value_s` route the ops take.
macro_rules! cast_suite {
    ($modname:ident, $src:ty, $ut:ty, $st:ty) => {
        mod $modname {
            use super::*;

            proptest! {
                #[test]
                fn zext_sext_match_native_casts(a in any::<$src>()) {
                    macro_rules! chk {
                        ($dst:ty) => {
                            prop_assert_eq!(
                                Zext::<$src, $dst>::new().eval(&a),
                                Some((a as $ut) as $dst),
                                "zext {} -> {}", stringify!($src), stringify!($dst)
                            );
                            prop_assert_eq!(
                                Sext::<$src, $dst>::new().eval(&a),
                                Some((a as $st) as $dst),
                                "sext {} -> {}", stringify!($src), stringify!($dst)
                            );
                        };
                    }
                    chk!(u8);
                    chk!(u16);
                    chk!(u32);
                    chk!(u64);
                    chk!(i8);
                    chk!(i16);
                    chk!(i32);
                    chk!(i64);
                }
            }
        }
    };
}

cast_suite!(cast_from_u8, u8, u8, i8);
cast_suite!(cast_from_u16, u16, u16, i16);
cast_suite!(cast_from_u32, u32, u32, i32);
cast_suite!(cast_from_u64, u64, u64, i64);
cast_suite!(cast_from_i8, i8, u8, i8);
cast_suite!(cast_from_i16, i16, u16, i16);
cast_suite!(cast_from_i32, i32, u32, i32);
cast_suite!(cast_from_i64, i64, u64, i64);
