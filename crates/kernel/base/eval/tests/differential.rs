//! DIFFERENTIAL suite: every `Builtins` CanonRule is checked value-for-value
//! against `covalence-core`'s the legacy accelerated
//! kernel reduction path this crate replaces (`Thm::reduce_*` in
//! `covalence-core`), over edge cases (0, 1, max-width, div/mod/rem
//! by zero, sign boundaries) and a fixed pseudo-random-looking corpus.
//!
//! ANY divergence is a HARD WALL for the toHOL purge: it means the retained
//! unfolding equations could mint `⊢ False`. If an assertion here fails, do
//! NOT "fix" either side unilaterally — stop and report (see
//! notes/vibes/pure-hol-and-build-plan.md and the stage brief).
//!
//! This file is the only consumer of the `covalence-core` dev-dependency
//! and dies with the legacy kernel reducer.

use covalence_core::defs::{self, IntOp};
use covalence_core::{IntTag, Term, TermKind, Thm};
use covalence_pure::CanonRule;
use covalence_pure_eval::*;
use covalence_types::{Bytes, Int, Nat};

// ============================================================================
// kernel-reducer plumbing (the deprecated surface — counted by the purge
// ratchet; keep each pattern to ONE occurrence)
// ============================================================================

/// Run the kernel's accelerated reduction on `t`; return the RHS of the
/// minted equation `⊢ t = rhs`, or `None` if the kernel refuses.
fn kernel_reduce(t: &Term) -> Option<Term> {
    let thm = Thm::reduce_prim(t.clone()).ok()?;
    // Conclusion shape: App(App(Eq, lhs), rhs) — a HOL equation at bool.
    let TermKind::App(eq_lhs, rhs) = thm.concl().kind() else {
        panic!("kernel-reducer conclusion is not an App: {:?}", thm.concl());
    };
    let TermKind::App(eq_op, lhs) = eq_lhs.kind() else {
        panic!(
            "kernel-reducer conclusion LHS is not an App: {:?}",
            thm.concl()
        );
    };
    assert!(
        matches!(eq_op.kind(), TermKind::Eq(_)),
        "kernel-reducer conclusion head is not `=`: {:?}",
        thm.concl()
    );
    assert_eq!(lhs, t, "kernel reducer equated a different LHS");
    Some(rhs.clone())
}

/// Map a native value to the literal `Term` the kernel mints for it.
trait ToTerm {
    fn to_term(&self) -> Term;
}

impl ToTerm for Nat {
    fn to_term(&self) -> Term {
        Term::nat_lit(self.clone())
    }
}
impl ToTerm for Int {
    fn to_term(&self) -> Term {
        Term::int_lit(self.clone())
    }
}
impl ToTerm for Bytes {
    fn to_term(&self) -> Term {
        Term::blob(self.clone())
    }
}
impl ToTerm for bool {
    fn to_term(&self) -> Term {
        Term::bool_lit(*self)
    }
}

macro_rules! to_term_fixed {
    ($($t:ty => $ctor:ident),* $(,)?) => {
        $(impl ToTerm for $t {
            fn to_term(&self) -> Term {
                Term::$ctor(*self)
            }
        })*
    };
}
to_term_fixed! {
    u8 => u8_lit, u16 => u16_lit, u32 => u32_lit, u64 => u64_lit,
    i8 => s8_lit, i16 => s16_lit, i32 => s32_lit, i64 => s64_lit,
}

// ============================================================================
// The differential checks
// ============================================================================

/// Assert CanonRule == kernel reducer on a unary op.
fn check1<F>(op_term: &Term, rule: F, a: &F::In)
where
    F: CanonRule,
    F::In: ToTerm + Clone + std::fmt::Debug,
    F::Out: ToTerm,
{
    let t = Term::app(op_term.clone(), a.to_term());
    let Some(kernel) = kernel_reduce(&t) else {
        panic!("kernel reducer refused in-range argument {a:?} for {op_term:?}");
    };
    let ours = rule.eval(a).to_term();
    assert_eq!(
        kernel, ours,
        "HARD WALL — DIVERGENCE between covalence-pure-eval and the kernel reducer \
         on {op_term:?} applied to {a:?}"
    );
}

/// Assert CanonRule == kernel reducer on a binary op.
fn check2<F, A, B>(op_term: &Term, rule: F, a: &A, b: &B)
where
    F: CanonRule<In = (A, B)>,
    A: ToTerm + Clone + std::fmt::Debug,
    B: ToTerm + Clone + std::fmt::Debug,
    F::Out: ToTerm,
{
    let t = Term::app(Term::app(op_term.clone(), a.to_term()), b.to_term());
    let Some(kernel) = kernel_reduce(&t) else {
        panic!("kernel reducer refused in-range arguments ({a:?}, {b:?}) for {op_term:?}");
    };
    let ours = rule.eval(&(a.clone(), b.clone())).to_term();
    assert_eq!(
        kernel, ours,
        "HARD WALL — DIVERGENCE between covalence-pure-eval and the kernel reducer \
         on {op_term:?} applied to ({a:?}, {b:?})"
    );
}

/// Assert CanonRule == kernel reducer on a ternary op.
fn check3<F, A, B, C>(op_term: &Term, rule: F, a: &A, b: &B, c: &C)
where
    F: CanonRule<In = (A, B, C)>,
    A: ToTerm + Clone + std::fmt::Debug,
    B: ToTerm + Clone + std::fmt::Debug,
    C: ToTerm + Clone + std::fmt::Debug,
    F::Out: ToTerm,
{
    let t = Term::app(
        Term::app(Term::app(op_term.clone(), a.to_term()), b.to_term()),
        c.to_term(),
    );
    let Some(kernel) = kernel_reduce(&t) else {
        panic!("kernel reducer refused in-range arguments for {op_term:?}");
    };
    let ours = rule.eval(&(a.clone(), b.clone(), c.clone())).to_term();
    assert_eq!(
        kernel, ours,
        "HARD WALL — DIVERGENCE between covalence-pure-eval and the kernel reducer \
         on {op_term:?} applied to ({a:?}, {b:?}, {c:?})"
    );
}

// ============================================================================
// Corpora: edge cases + fixed "random-looking" values (deterministic)
// ============================================================================

fn nats() -> Vec<Nat> {
    let mut v: Vec<Nat> = [
        0u128,
        1,
        2,
        3,
        5,
        7,
        10,
        16,
        17,
        100,
        255,
        256,
        257,
        4095,
        65535,
        65536,
        0xDEAD_BEEF,
        (1 << 32) - 1,
        1 << 32,
        u64::MAX as u128 - 1,
        u64::MAX as u128,
        (u64::MAX as u128) + 1,
        u128::MAX,
    ]
    .into_iter()
    .map(Nat::from)
    .collect();
    // Multi-limb values beyond u128.
    v.push(Nat::from(u128::MAX) * Nat::from(u128::MAX));
    v.push(Nat::from_str_radix("123456789012345678901234567890123456789012345678901", 10).unwrap());
    v
}

/// Exponents / shift amounts small enough that the kernel reducer accepts them
/// and the results stay reasonably sized.
fn small_nats() -> Vec<Nat> {
    [0u128, 1, 2, 3, 7, 8, 31, 32, 63, 64, 100, 1000]
        .into_iter()
        .map(Nat::from)
        .collect()
}

fn ints() -> Vec<Int> {
    let mut v: Vec<Int> = [
        0i128,
        1,
        -1,
        2,
        -2,
        3,
        -3,
        7,
        -7,
        17,
        -17,
        255,
        -255,
        256,
        -256,
        65536,
        -65536,
        0xDEAD_BEEF,
        -0xDEAD_BEEF,
        i64::MAX as i128,
        i64::MIN as i128,
        i128::MAX,
        i128::MIN,
    ]
    .into_iter()
    .map(Int::from)
    .collect();
    v.push(
        "-987654321098765432109876543210987654321"
            .parse::<Int>()
            .unwrap(),
    );
    v
}

fn byte_strings() -> Vec<Bytes> {
    vec![
        Bytes::new(),
        Bytes::from(vec![0u8]),
        Bytes::from(vec![1u8]),
        Bytes::from(vec![0u8, 0]),
        Bytes::from(vec![255u8]),
        Bytes::from(vec![1u8, 2, 3]),
        Bytes::from(vec![255u8; 4]),
        Bytes::from((0u8..=255).step_by(7).collect::<Vec<u8>>()),
        Bytes::from((0..300).map(|i| (i * 31 % 256) as u8).collect::<Vec<u8>>()),
    ]
}

// ============================================================================
// nat / int / bytes
// ============================================================================

#[test]
fn diff_nat_binops() {
    let ns = nats();
    for a in &ns {
        for b in &ns {
            check2(&defs::nat_add(), NatAdd, a, b);
            check2(&defs::nat_mul(), NatMul, a, b);
            check2(&defs::nat_sub(), NatSub, a, b);
            check2(&defs::nat_div(), NatDiv, a, b);
            check2(&defs::nat_mod(), NatMod, a, b);
            check2(&defs::nat_bit_and(), NatBitAnd, a, b);
            check2(&defs::nat_bit_or(), NatBitOr, a, b);
            check2(&defs::nat_bit_xor(), NatBitXor, a, b);
            check2(&defs::nat_le(), NatLe, a, b);
            check2(&defs::nat_lt(), NatLt, a, b);
        }
        // pow / shl / shr with bounded right operands (the kernel reducer refuses
        // oversize ones — that parity is covered in tests/semantics.rs and
        // diff_oversize_refusals below).
        for s in &small_nats() {
            check2(&defs::nat_pow(), NatPow, a, s);
            check2(&defs::nat_shl(), NatShl, a, s);
            check2(&defs::nat_shr(), NatShr, a, s);
        }
    }
}

#[test]
fn diff_nat_unary_and_conversions() {
    for a in &nats() {
        check1(&defs::nat_pred(), NatPred, a);
        check1(&defs::nat_to_int(), NatToInt, a);
        check1(&defs::nat_to_bytes_le(), NatToBytesLe, a);
        check1(&defs::nat_to_bytes_be(), NatToBytesBe, a);
    }
    for b in &byte_strings() {
        check1(&defs::nat_from_bytes_le(), NatFromBytesLe, b);
        check1(&defs::nat_from_bytes_be(), NatFromBytesBe, b);
    }
}

#[test]
fn diff_int_ops() {
    let zs = ints();
    for a in &zs {
        check1(&defs::int_succ(), IntSucc, a);
        check1(&defs::int_pred(), IntPred, a);
        check1(&defs::int_neg(), IntNeg, a);
        check1(&defs::int_abs(), IntAbs, a);
        check1(&defs::int_sgn(), IntSgn, a);
        for b in &zs {
            check2(&defs::int_add(), IntAdd, a, b);
            check2(&defs::int_mul(), IntMul, a, b);
            check2(&defs::int_sub(), IntSub, a, b);
            check2(&defs::int_div(), IntDiv, a, b);
            check2(&defs::int_mod(), IntMod, a, b);
            check2(&defs::int_le(), IntLe, a, b);
            check2(&defs::int_lt(), IntLt, a, b);
        }
    }
}

#[test]
fn diff_bytes_ops() {
    let bss = byte_strings();
    let ns = nats();
    for a in &bss {
        check1(&defs::bytes_len(), BytesLen, a);
        for b in &bss {
            check2(&defs::bytes_cat(), BytesCat, a, b);
        }
        // Index by every corpus nat — includes out-of-bounds and
        // beyond-usize values (both read as 0 / clamp).
        for i in &ns {
            check2(&defs::bytes_at(), BytesAt, a, i);
        }
        for start in &small_nats() {
            for len in &small_nats() {
                check3(&defs::bytes_slice(), BytesSlice, a, start, len);
            }
            // Oversize start/len saturate.
            for huge in [Nat::from(u128::MAX), Nat::from(1u128 << 64)] {
                check3(&defs::bytes_slice(), BytesSlice, a, start, &huge);
                check3(&defs::bytes_slice(), BytesSlice, a, &huge, start);
            }
        }
    }
    for n in &ns {
        for bs in &bss {
            // consNat reduces the nat operand mod 256.
            check2(&defs::bytes_cons_nat(), BytesConsNat, n, bs);
        }
    }
}

#[test]
fn diff_oversize_refusals() {
    // Where builtins.rs refuses (returns None → the kernel reducer errs), eval
    // panics: neither side produces a value.
    let two = Nat::from(2u8);
    let one = Nat::from(1u8);
    let huge_exp = Nat::from(1u128 << 32); // > u32
    let huge_shift = Nat::from(1u128 << 64); // > u64
    let pow = Term::app(
        Term::app(defs::nat_pow(), two.to_term()),
        huge_exp.to_term(),
    );
    assert!(
        kernel_reduce(&pow).is_none(),
        "kernel must refuse oversize exponent"
    );
    let shl = Term::app(
        Term::app(defs::nat_shl(), one.to_term()),
        huge_shift.to_term(),
    );
    assert!(
        kernel_reduce(&shl).is_none(),
        "kernel must refuse oversize shift"
    );
    let shr = Term::app(
        Term::app(defs::nat_shr(), one.to_term()),
        huge_shift.to_term(),
    );
    assert!(
        kernel_reduce(&shr).is_none(),
        "kernel must refuse oversize shift"
    );
    // The matching eval panics are pinned in tests/semantics.rs.
}

// ============================================================================
// Fixed-width families
// ============================================================================

macro_rules! fw_vals {
    ($t:ty) => {{
        let v: Vec<$t> = vec![
            0,
            1,
            2,
            3,
            5,
            7,
            <$t>::MIN,
            <$t>::MIN / 2,
            <$t>::MAX,
            <$t>::MAX - 1,
            <$t>::MAX / 2,
            <$t>::MAX / 3,
            (<$t>::MAX / 3) ^ <$t>::MAX, // bit-pattern-ish
            (0 as $t).wrapping_sub(1),   // all-ones bits (-1 / uN::MAX)
        ];
        v
    }};
}

macro_rules! fw_diff {
    ($t:ty, $tag:expr) => {{
        let tag = $tag;
        let vals = fw_vals!($t);
        for &a in &vals {
            for &b in &vals {
                check2(&defs::int_op(tag, IntOp::Add), FwAdd::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Sub), FwSub::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Mul), FwMul::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Div), FwDiv::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Rem), FwRem::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::And), FwAnd::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Or), FwOr::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Xor), FwXor::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Shl), FwShl::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Shr), FwShr::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Lt), FwLt::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Le), FwLe::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Gt), FwGt::<$t>::new(), &a, &b);
                check2(&defs::int_op(tag, IntOp::Ge), FwGe::<$t>::new(), &a, &b);
            }
            check1(&defs::int_op(tag, IntOp::Neg), FwNeg::<$t>::new(), &a);
            check1(&defs::int_op(tag, IntOp::Not), FwNot::<$t>::new(), &a);
            check1(&defs::int_to_nat(tag), FwToNat::<$t>::new(), &a);
            check1(&defs::int_to_int(tag), FwToInt::<$t>::new(), &a);
        }
        for n in &nats() {
            check1(&defs::int_from_nat(tag), FwFromNat::<$t>::new(), n);
        }
        for z in &ints() {
            check1(&defs::int_from_int(tag), FwFromInt::<$t>::new(), z);
        }
    }};
}

#[test]
fn diff_fw_u8() {
    fw_diff!(u8, IntTag::U8);
}
#[test]
fn diff_fw_u16() {
    fw_diff!(u16, IntTag::U16);
}
#[test]
fn diff_fw_u32() {
    fw_diff!(u32, IntTag::U32);
}
#[test]
fn diff_fw_u64() {
    fw_diff!(u64, IntTag::U64);
}
#[test]
fn diff_fw_s8() {
    fw_diff!(i8, IntTag::S8);
}
#[test]
fn diff_fw_s16() {
    fw_diff!(i16, IntTag::S16);
}
#[test]
fn diff_fw_s32() {
    fw_diff!(i32, IntTag::S32);
}
#[test]
fn diff_fw_s64() {
    fw_diff!(i64, IntTag::S64);
}

// ============================================================================
// The 8×8 cast grid
// ============================================================================

macro_rules! cast_diff {
    ($s:ty, $stag:expr) => {{
        let stag = $stag;
        for &a in &fw_vals!($s) {
            cast_diff!(@to $s, stag, a; u8, IntTag::U8);
            cast_diff!(@to $s, stag, a; u16, IntTag::U16);
            cast_diff!(@to $s, stag, a; u32, IntTag::U32);
            cast_diff!(@to $s, stag, a; u64, IntTag::U64);
            cast_diff!(@to $s, stag, a; i8, IntTag::S8);
            cast_diff!(@to $s, stag, a; i16, IntTag::S16);
            cast_diff!(@to $s, stag, a; i32, IntTag::S32);
            cast_diff!(@to $s, stag, a; i64, IntTag::S64);
        }
    }};
    (@to $s:ty, $stag:expr, $a:expr; $d:ty, $dtag:expr) => {{
        check1(&defs::int_zext($stag, $dtag), Zext::<$s, $d>::new(), &$a);
        check1(&defs::int_sext($stag, $dtag), Sext::<$s, $d>::new(), &$a);
    }};
}

#[test]
fn diff_casts_from_u8() {
    cast_diff!(u8, IntTag::U8);
}
#[test]
fn diff_casts_from_u16() {
    cast_diff!(u16, IntTag::U16);
}
#[test]
fn diff_casts_from_u32() {
    cast_diff!(u32, IntTag::U32);
}
#[test]
fn diff_casts_from_u64() {
    cast_diff!(u64, IntTag::U64);
}
#[test]
fn diff_casts_from_s8() {
    cast_diff!(i8, IntTag::S8);
}
#[test]
fn diff_casts_from_s16() {
    cast_diff!(i16, IntTag::S16);
}
#[test]
fn diff_casts_from_s32() {
    cast_diff!(i32, IntTag::S32);
}
#[test]
fn diff_casts_from_s64() {
    cast_diff!(i64, IntTag::S64);
}
