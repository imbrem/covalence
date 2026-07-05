//! Builtin primitive reductions on closed-form literal arguments.
//!
//! The kernel's `Thm::reduce_prim` rule defers to the pattern
//! matcher here. Each match arm corresponds to one entry in the
//! catalogue documented on `Thm::reduce_prim`.
//!
//! This module is in the Core TCB. Audit by checking that:
//!
//! - Each reduction matches the documented arithmetic semantics
//!   (Euclidean div/mod with `n/0 = 0` and `n%0 = n` — see the
//!   soundness note on `nat.mod` below; saturating nat sub and pred;
//!   byte-cons mod-256 on the nat operand).
//! - No unsound shortcut: the function returns `None` for any
//!   shape that isn't an exact-arity application of a `Prim` to
//!   the right number of literal arguments.
//! - The fixed-width integer ops (`u8`…`u64` / `s8`…`s64`, dispatched
//!   via [`crate::defs::int_ops::lookup_op`]) compute in 128-bit space
//!   and re-encode through `store`: arithmetic wraps mod `2^width`,
//!   signed/unsigned `div`/`rem`/`shr`/comparisons read the operand's
//!   tag, and `div`/`rem` by zero yield `0` (mirroring `nat`/`int`).

use std::collections::HashMap;
use std::sync::LazyLock;

use covalence_types::{Int, Nat, Sign};

use crate::defs;
use crate::defs::int_ops::{IntOp, OpKey};
use crate::term::{IntTag, SmallIntLiteral, Term, TermKind};

/// One-step reduction. Returns the reduced term when `t` is an
/// exactly-shaped `TermKind::Spec` application with all-literal
/// arguments (or a HOL `=` over two closed literals at a supported
/// type), `None` otherwise.
pub(crate) fn reduce_prim_term(t: &Term) -> Option<Term> {
    let (head, args) = unwind_app(t);

    // HOL `=` decided on closed literals: `Bool`, `Nat`, `Int`,
    // `SmallInt`, or `Blob`. The kernel commits to literal
    // distinctness — two literals of the same kind are equal iff they
    // are structurally equal.
    if let TermKind::Eq(_) = head.kind() {
        if args.len() == 2 {
            return literal_eq(&args[0], &args[1]).map(Term::bool_lit);
        }
        return None;
    }

    // The primitive successor on a closed literal: `succ n → n + 1`.
    if let TermKind::Succ = head.kind() {
        return unary(&args, as_nat_lit)
            .map(|n| Term::nat_lit(Nat::from_inner(n.as_inner() + 1u32)));
    }

    // Term-spec catalogue dispatch: closed-form reduction by pointer
    // identity on the spec handle. The canonical handles live in
    // `crate::defs`; both code paths reach the same `Arc` so
    // `ptr_eq` is unambiguous.
    if let TermKind::Spec(handle, type_args) = head.kind() {
        if !type_args.is_empty() {
            return None;
        }
        return reduce_spec(handle, &args);
    }

    None
}

// ============================================================================
// Pattern matchers
// ============================================================================

fn unwind_app(t: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut cursor = t.clone();
    while let TermKind::App(f, x) = cursor.kind() {
        args.push(x.clone());
        let next = f.clone();
        cursor = next;
    }
    args.reverse();
    (cursor, args)
}

fn as_nat_lit(t: &Term) -> Option<&Nat> {
    match t.kind() {
        TermKind::Nat(n) => Some(n),
        _ => None,
    }
}

fn as_int_lit(t: &Term) -> Option<&Int> {
    match t.kind() {
        TermKind::Int(n) => Some(n),
        _ => None,
    }
}

fn as_blob(t: &Term) -> Option<&[u8]> {
    match t.kind() {
        TermKind::Blob(b) => Some(b),
        _ => None,
    }
}

/// Decide structural equality of two kernel literals (`Bool`, `Nat`,
/// `Int`, `SmallInt`, `Blob`). Returns `None` if either argument is
/// not a recognised literal at one of those types — the rule is
/// undefined (and `reduce_prim` errors) for non-literal arguments.
fn literal_eq(a: &Term, b: &Term) -> Option<bool> {
    match (a.kind(), b.kind()) {
        (TermKind::Bool(x), TermKind::Bool(y)) => Some(x == y),
        (TermKind::Nat(x), TermKind::Nat(y)) => Some(x == y),
        (TermKind::Int(x), TermKind::Int(y)) => Some(x == y),
        (TermKind::SmallInt(x), TermKind::SmallInt(y)) => Some(x == y),
        (TermKind::Blob(x), TermKind::Blob(y)) => Some(x == y),
        _ => None,
    }
}

/// A reducible nat / int / bytes catalogue operation — one of the
/// term-spec constants the kernel commits to a Rust-side computation for.
/// Each variant maps one-to-one to a canonical `defs::*_spec()` handle in
/// [`PRIM_TABLE`], and its arithmetic lives in the matching arm of
/// [`eval_prim`]. (The fixed-width `uN`/`sN` ops have their own registry,
/// [`crate::defs::int_ops`].)
#[derive(Clone, Copy)]
enum Prim {
    // nat → nat (unary)
    NatPred,
    // nat → nat → nat
    NatAdd,
    NatMul,
    NatSub,
    NatDiv,
    NatMod,
    NatPow,
    NatShl,
    NatShr,
    NatBitAnd,
    NatBitOr,
    NatBitXor,
    // nat → nat → bool
    NatLe,
    NatLt,
    // nat ↔ int / bytes
    NatToInt,
    NatToBytesLe,
    NatToBytesBe,
    NatFromBytesLe,
    NatFromBytesBe,
    // int (unary)
    IntSucc,
    IntPred,
    IntNeg,
    IntAbs,
    IntSgn,
    // int → int → int / bool
    IntAdd,
    IntMul,
    IntSub,
    IntDiv,
    IntMod,
    IntLe,
    IntLt,
    // bytes
    BytesCat,
    BytesConsNat,
    BytesLen,
    BytesAt,
    BytesSlice,
}

/// `spec.ptr_id() → Prim` — the dispatch table, built once from the
/// canonical `defs` handles. A user-built spec that merely *shares a
/// label* is a different `Arc` allocation, so it is absent here and never
/// reduces — the safety a per-arm `ptr_eq` chain gives.
///
/// This list is the single audit point for *what reduces*; the semantics
/// of each entry live in [`eval_prim`].
static PRIM_TABLE: LazyLock<HashMap<usize, Prim>> = LazyLock::new(|| {
    // (canonical-handle accessor, op) pairs.
    type Entry = (fn() -> defs::TermSpec, Prim);
    let entries: &[Entry] = &[
        (defs::nat_pred_spec, Prim::NatPred),
        (defs::nat_add_spec, Prim::NatAdd),
        (defs::nat_mul_spec, Prim::NatMul),
        (defs::nat_sub_spec, Prim::NatSub),
        (defs::nat_div_spec, Prim::NatDiv),
        (defs::nat_mod_spec, Prim::NatMod),
        (defs::nat_pow_spec, Prim::NatPow),
        (defs::nat_shl_spec, Prim::NatShl),
        (defs::nat_shr_spec, Prim::NatShr),
        (defs::nat_bit_and_spec, Prim::NatBitAnd),
        (defs::nat_bit_or_spec, Prim::NatBitOr),
        (defs::nat_bit_xor_spec, Prim::NatBitXor),
        (defs::nat_le_spec, Prim::NatLe),
        (defs::nat_lt_spec, Prim::NatLt),
        (defs::nat_to_int_spec, Prim::NatToInt),
        (defs::nat_to_bytes_le_spec, Prim::NatToBytesLe),
        (defs::nat_to_bytes_be_spec, Prim::NatToBytesBe),
        (defs::nat_from_bytes_le_spec, Prim::NatFromBytesLe),
        (defs::nat_from_bytes_be_spec, Prim::NatFromBytesBe),
        (defs::int_succ_spec, Prim::IntSucc),
        (defs::int_pred_spec, Prim::IntPred),
        (defs::int_neg_spec, Prim::IntNeg),
        (defs::int_abs_spec, Prim::IntAbs),
        (defs::int_sgn_spec, Prim::IntSgn),
        (defs::int_add_spec, Prim::IntAdd),
        (defs::int_mul_spec, Prim::IntMul),
        (defs::int_sub_spec, Prim::IntSub),
        (defs::int_div_spec, Prim::IntDiv),
        (defs::int_mod_spec, Prim::IntMod),
        (defs::int_le_spec, Prim::IntLe),
        (defs::int_lt_spec, Prim::IntLt),
        (defs::bytes_cat_spec, Prim::BytesCat),
        (defs::bytes_cons_nat_spec, Prim::BytesConsNat),
        (defs::bytes_len_spec, Prim::BytesLen),
        (defs::bytes_at_spec, Prim::BytesAt),
        (defs::bytes_slice_spec, Prim::BytesSlice),
    ];
    entries.iter().map(|(f, p)| (f().ptr_id(), *p)).collect()
});

/// Dispatch closed-form reduction for a term-spec leaf applied to `args`.
/// The handle is matched by pointer identity: the nat/int/bytes catalogue
/// via [`PRIM_TABLE`], then the fixed-width integer ops via
/// [`crate::defs::int_ops::lookup_op`]. Returns `None` for any handle in
/// neither table — the user can still reason about it abstractly via its
/// definitional axioms in `covalence-hol`.
fn reduce_spec(handle: &defs::TermSpec, args: &[Term]) -> Option<Term> {
    if let Some(&prim) = PRIM_TABLE.get(&handle.ptr_id()) {
        return eval_prim(prim, args);
    }
    let key = defs::int_ops::lookup_op(handle)?;
    reduce_int_op(key, args)
}

/// Extract a single literal argument: `None` unless `args` is exactly one
/// element that `extract` recognises.
fn unary<'a, T>(args: &'a [Term], extract: impl Fn(&'a Term) -> Option<T>) -> Option<T> {
    match args {
        [a] => extract(a),
        _ => None,
    }
}

/// Compute the result of one [`Prim`] on `args`. Arity and literal-kind
/// checks live in the `unary` / `reduce_*` helpers, so each arm is just
/// the operation; edge-case conventions (saturation, div/mod by zero,
/// oversize refusal) are commented where they bear on soundness.
fn eval_prim(prim: Prim, args: &[Term]) -> Option<Term> {
    use Prim::*;
    match prim {
        // ---- nat: unary ----
        // Saturating predecessor: `pred 0 = 0`.
        NatPred => Some(Term::nat_lit(
            unary(args, as_nat_lit)?
                .checked_sub(&Nat::one())
                .unwrap_or_else(Nat::zero),
        )),

        // ---- nat: binary arithmetic / bitwise ----
        NatAdd => reduce_nat_binop(args, |a, b| a + b),
        NatMul => reduce_nat_binop(args, |a, b| a * b),
        // Saturating subtraction: `a - b = 0` when `b > a`.
        NatSub => reduce_nat_binop(args, |a, b| a.checked_sub(b).unwrap_or_else(Nat::zero)),
        // `a / 0 = 0` (paired with `a mod 0 = a` below).
        NatDiv => reduce_nat_binop(args, |a, b| if b.is_zero() { Nat::zero() } else { a / b }),
        NatMod => reduce_nat_binop(args, |a, b| {
            // `n mod 0 = n` (NOT 0) — FORCED for soundness. `nat.mod` has a
            // let-style body `λn m. n - (n/m)*m`, which at `m = 0` (with
            // `n/0 = 0`) evaluates to `n - 0 = n`. Returning 0 here would
            // let `unfold_term_spec` (→ n) and `reduce_prim` (→ 0) derive
            // `n = 0` for any `n` — a contradiction. `n mod 0 = n` also
            // satisfies `n = (n/m)*m + (n mod m)` and matches Lean/Coq.
            if b.is_zero() { a.clone() } else { a % b }
        }),
        NatPow => match args {
            [base, exp] => {
                let base = as_nat_lit(base)?;
                let exp = as_nat_lit(exp)?;
                // `BigUint::pow` takes a `u32` exponent. Refuse an oversize
                // exponent rather than truncate it.
                let exp_digits = exp.as_inner().to_u32_digits();
                if exp_digits.len() > 1 {
                    return None;
                }
                Some(Term::nat_lit(
                    base.pow(exp_digits.first().copied().unwrap_or(0)),
                ))
            }
            _ => None,
        },
        NatShl => reduce_nat_shift(args, true),
        NatShr => reduce_nat_shift(args, false),
        NatBitAnd => reduce_nat_binop(args, |a, b| Nat::from_inner(a.as_inner() & b.as_inner())),
        NatBitOr => reduce_nat_binop(args, |a, b| Nat::from_inner(a.as_inner() | b.as_inner())),
        NatBitXor => reduce_nat_binop(args, |a, b| Nat::from_inner(a.as_inner() ^ b.as_inner())),

        // ---- nat: comparison ----
        NatLe => reduce_nat_cmp(args, |a, b| a <= b),
        NatLt => reduce_nat_cmp(args, |a, b| a < b),

        // ---- nat ↔ int / bytes ----
        NatToInt => {
            let n = unary(args, as_nat_lit)?;
            let sign = if n.is_zero() {
                Sign::Zero
            } else {
                Sign::Positive
            };
            Some(Term::int_lit(Int::from_sign_nat(sign, n.clone())))
        }
        NatToBytesLe => Some(Term::blob(unary(args, as_nat_lit)?.to_bytes_le())),
        NatToBytesBe => Some(Term::blob(unary(args, as_nat_lit)?.to_bytes_be())),
        NatFromBytesLe => Some(Term::nat_lit(Nat::from_bytes_le(unary(args, as_blob)?))),
        NatFromBytesBe => Some(Term::nat_lit(Nat::from_bytes_be(unary(args, as_blob)?))),

        // ---- int: unary ----
        IntSucc => Some(Term::int_lit(unary(args, as_int_lit)? + &Int::one())),
        IntPred => Some(Term::int_lit(unary(args, as_int_lit)? - &Int::one())),
        IntNeg => Some(Term::int_lit(-unary(args, as_int_lit)?)),
        IntAbs => Some(Term::nat_lit(unary(args, as_int_lit)?.abs())),
        IntSgn => {
            let sgn = match unary(args, as_int_lit)?.sign() {
                Sign::Negative => Int::from_sign_nat(Sign::Negative, Nat::one()),
                Sign::Zero => Int::zero(),
                Sign::Positive => Int::from_sign_nat(Sign::Positive, Nat::one()),
            };
            Some(Term::int_lit(sgn))
        }

        // ---- int: binary arithmetic / comparison ----
        IntAdd => reduce_int_binop(args, |a, b| a + b),
        IntMul => reduce_int_binop(args, |a, b| a * b),
        IntSub => reduce_int_binop(args, |a, b| a - b),
        // Truncating division; remainder takes the dividend's sign.
        // `a / 0 = 0` and `a mod 0 = a`. `int.div`/`int.mod` now have
        // let-style bodies (`defs::int_div`/`int_mod`) built from
        // reduce_prim-reducible sub-ops, so — exactly as for `nat.mod` —
        // `a mod 0` MUST be `a` (the body's value at `b = 0`), not 0.
        IntDiv => reduce_int_binop(args, |a, b| if b.is_zero() { Int::zero() } else { a / b }),
        IntMod => reduce_int_binop(args, |a, b| if b.is_zero() { a.clone() } else { a % b }),
        IntLe => reduce_int_cmp(args, |a, b| a <= b),
        IntLt => reduce_int_cmp(args, |a, b| a < b),

        // ---- bytes ----
        BytesCat => match args {
            [a, b] => Some(Term::blob(covalence_types::blob::cat(
                as_blob(a)?,
                as_blob(b)?,
            ))),
            _ => None,
        },
        // The nat operand is reduced mod 256 to a single byte.
        BytesConsNat => match args {
            [n, bs] => Some(Term::blob(covalence_types::blob::cons(
                nat_mod_256(as_nat_lit(n)?),
                as_blob(bs)?,
            ))),
            _ => None,
        },
        BytesLen => Some(Term::nat_lit(Nat::from_inner(
            unary(args, as_blob)?.len().into(),
        ))),
        // Out-of-bounds index reads as 0.
        BytesAt => match args {
            [bs, i] => {
                let bs = as_blob(bs)?;
                let idx = nat_to_usize(as_nat_lit(i)?).unwrap_or(usize::MAX);
                Some(Term::nat_lit(Nat::from_inner(
                    (covalence_types::blob::at(bs, idx) as u32).into(),
                )))
            }
            _ => None,
        },
        // Saturating slice with `(start, len)` convention.
        BytesSlice => match args {
            [bs, start, len] => {
                let bs = as_blob(bs)?;
                let start = nat_to_usize(as_nat_lit(start)?).unwrap_or(usize::MAX);
                let len = nat_to_usize(as_nat_lit(len)?).unwrap_or(usize::MAX);
                Some(Term::blob(covalence_types::blob::slice(bs, start, len)))
            }
            _ => None,
        },
    }
}

// ============================================================================
// Fixed-width integer reduction
//
// All values are computed in 128-bit space and re-encoded into the
// operand's tag via `store` (masking to the tag's width and
// sign-extending signed results into the literal's `u64` payload, so
// the result round-trips with `SmallIntLiteral`).
// ============================================================================

fn as_small_int(t: &Term) -> Option<SmallIntLiteral> {
    match t.kind() {
        TermKind::SmallInt(lit) => Some(*lit),
        _ => None,
    }
}

/// Low-`width`-bits mask.
fn width_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// The unsigned value of `bits` interpreted at `tag` (low `width`
/// bits, zero-extended).
fn value_u(tag: IntTag, bits: u64) -> u128 {
    (bits as u128) & width_mask(tag.width())
}

/// The signed (two's-complement) value of `bits` interpreted at `tag`.
fn value_s(tag: IntTag, bits: u64) -> i128 {
    let w = tag.width();
    let m = width_mask(w);
    let u = (bits as u128) & m;
    if u & (1u128 << (w - 1)) != 0 {
        (u as i128) - ((m + 1) as i128)
    } else {
        u as i128
    }
}

/// Encode a low-bits result into the canonical `u64` payload for
/// `tag`: mask to `width`, then sign-extend (signed) / zero-extend
/// (unsigned) into the full 64 bits.
fn store(tag: IntTag, low: u128) -> u64 {
    let w = tag.width();
    let m = width_mask(w);
    let low = low & m;
    if tag.is_signed() && (low & (1u128 << (w - 1))) != 0 {
        (low | !m) as u64
    } else {
        low as u64
    }
}

/// Low `width` bits of a `Nat`, via its little-endian byte encoding.
fn nat_low_bits(n: &Nat, width: u32) -> u128 {
    let bytes = n.to_bytes_le();
    let nbytes = width.div_ceil(8) as usize;
    let mut acc: u128 = 0;
    for i in 0..nbytes {
        if let Some(&b) = bytes.get(i) {
            acc |= (b as u128) << (8 * i);
        }
    }
    acc & width_mask(width)
}

fn int_binop(tag: IntTag, op: IntOp, ab: u64, bb: u64) -> u64 {
    let w = tag.width();
    let m = width_mask(w);
    let au = value_u(tag, ab);
    let bu = value_u(tag, bb);
    let low = match op {
        IntOp::Add => au.wrapping_add(bu) & m,
        IntOp::Sub => au.wrapping_sub(bu) & m,
        IntOp::Mul => au.wrapping_mul(bu) & m,
        IntOp::And => au & bu,
        IntOp::Or => au | bu,
        IntOp::Xor => au ^ bu,
        IntOp::Shl => {
            let s = (bu % w as u128) as u32;
            (au << s) & m
        }
        IntOp::Shr => {
            let s = (bu % w as u128) as u32;
            if tag.is_signed() {
                ((value_s(tag, ab) >> s) as u128) & m
            } else {
                au >> s
            }
        }
        // Truncating division; `x / 0 = 0` and `x rem 0 = x` (Euclidean,
        // mirroring nat/int). Both `int.Div`/`int.Rem` now have let-style
        // bodies (`defs::int_ops::op_body`), so these values are FORCED to
        // match the bodies: `Div`'s body is `fromInt(intDiv …)` (→ 0 at
        // y=0, since `int.div n 0 = 0`), and `Rem`'s is `fromInt(intMod …)`
        // / `fromNat(natMod …)` (→ the dividend at y=0). `au` is the
        // dividend's low-`w` bits, i.e. its own value.
        // TCB: keep the explicit `y = 0` branch mirroring the signed/`Rem`
        // arms rather than restructuring into `checked_div`.
        #[allow(clippy::manual_checked_ops)]
        IntOp::Div => {
            if tag.is_signed() {
                let bv = value_s(tag, bb);
                if bv == 0 {
                    0
                } else {
                    (value_s(tag, ab).wrapping_div(bv) as u128) & m
                }
            } else if bu == 0 {
                0
            } else {
                au / bu
            }
        }
        IntOp::Rem => {
            if tag.is_signed() {
                let bv = value_s(tag, bb);
                if bv == 0 {
                    au
                } else {
                    (value_s(tag, ab).wrapping_rem(bv) as u128) & m
                }
            } else if bu == 0 {
                au
            } else {
                au % bu
            }
        }
        IntOp::Lt | IntOp::Le | IntOp::Gt | IntOp::Ge | IntOp::Neg | IntOp::Not => {
            unreachable!("non-binary-arith op routed to int_binop")
        }
    };
    store(tag, low)
}

fn int_cmp(tag: IntTag, op: IntOp, ab: u64, bb: u64) -> bool {
    if tag.is_signed() {
        let a = value_s(tag, ab);
        let b = value_s(tag, bb);
        match op {
            IntOp::Lt => a < b,
            IntOp::Le => a <= b,
            IntOp::Gt => a > b,
            IntOp::Ge => a >= b,
            _ => unreachable!("non-comparison op routed to int_cmp"),
        }
    } else {
        let a = value_u(tag, ab);
        let b = value_u(tag, bb);
        match op {
            IntOp::Lt => a < b,
            IntOp::Le => a <= b,
            IntOp::Gt => a > b,
            IntOp::Ge => a >= b,
            _ => unreachable!("non-comparison op routed to int_cmp"),
        }
    }
}

fn int_unary(tag: IntTag, op: IntOp, ab: u64) -> u64 {
    let au = value_u(tag, ab);
    match op {
        IntOp::Neg => store(tag, 0u128.wrapping_sub(au)),
        IntOp::Not => store(tag, !au),
        _ => unreachable!("non-unary op routed to int_unary"),
    }
}

fn reduce_int_op(key: OpKey, args: &[Term]) -> Option<Term> {
    match key {
        OpKey::Op(tag, op) if op.is_unary() => {
            if args.len() != 1 {
                return None;
            }
            let a = as_small_int(&args[0])?;
            if a.tag != tag {
                return None;
            }
            Some(Term::small_int(SmallIntLiteral::new(
                tag,
                int_unary(tag, op, a.bits),
            )))
        }
        OpKey::Op(tag, op) if op.is_cmp() => {
            if args.len() != 2 {
                return None;
            }
            let a = as_small_int(&args[0])?;
            let b = as_small_int(&args[1])?;
            if a.tag != tag || b.tag != tag {
                return None;
            }
            Some(Term::bool_lit(int_cmp(tag, op, a.bits, b.bits)))
        }
        OpKey::Op(tag, op) => {
            if args.len() != 2 {
                return None;
            }
            let a = as_small_int(&args[0])?;
            let b = as_small_int(&args[1])?;
            if a.tag != tag || b.tag != tag {
                return None;
            }
            Some(Term::small_int(SmallIntLiteral::new(
                tag,
                int_binop(tag, op, a.bits, b.bits),
            )))
        }
        OpKey::Zext(src, dst) => {
            if args.len() != 1 {
                return None;
            }
            let a = as_small_int(&args[0])?;
            if a.tag != src {
                return None;
            }
            Some(Term::small_int(SmallIntLiteral::new(
                dst,
                store(dst, value_u(src, a.bits)),
            )))
        }
        OpKey::Sext(src, dst) => {
            if args.len() != 1 {
                return None;
            }
            let a = as_small_int(&args[0])?;
            if a.tag != src {
                return None;
            }
            Some(Term::small_int(SmallIntLiteral::new(
                dst,
                store(dst, value_s(src, a.bits) as u128),
            )))
        }
        OpKey::ToNat(tag) => {
            if args.len() != 1 {
                return None;
            }
            let a = as_small_int(&args[0])?;
            if a.tag != tag {
                return None;
            }
            Some(Term::nat_lit(Nat::from(value_u(tag, a.bits))))
        }
        OpKey::ToInt(tag) => {
            if args.len() != 1 {
                return None;
            }
            let a = as_small_int(&args[0])?;
            if a.tag != tag {
                return None;
            }
            let z = if tag.is_signed() {
                Int::from(value_s(tag, a.bits))
            } else {
                Int::from(value_u(tag, a.bits))
            };
            Some(Term::int_lit(z))
        }
        OpKey::FromNat(tag) => {
            if args.len() != 1 {
                return None;
            }
            let n = as_nat_lit(&args[0])?;
            Some(Term::small_int(SmallIntLiteral::new(
                tag,
                store(tag, nat_low_bits(n, tag.width())),
            )))
        }
        OpKey::FromInt(tag) => {
            if args.len() != 1 {
                return None;
            }
            let z = as_int_lit(&args[0])?;
            let w = tag.width();
            let mag_low = nat_low_bits(&z.abs(), w);
            let low = if z.is_negative() {
                (width_mask(w) + 1).wrapping_sub(mag_low) & width_mask(w)
            } else {
                mag_low
            };
            Some(Term::small_int(SmallIntLiteral::new(tag, store(tag, low))))
        }
    }
}

fn reduce_nat_binop(args: &[Term], op: impl Fn(&Nat, &Nat) -> Nat) -> Option<Term> {
    if args.len() != 2 {
        return None;
    }
    let a = as_nat_lit(&args[0])?;
    let b = as_nat_lit(&args[1])?;
    Some(Term::nat_lit(op(a, b)))
}

fn reduce_nat_cmp(args: &[Term], op: impl Fn(&Nat, &Nat) -> bool) -> Option<Term> {
    if args.len() != 2 {
        return None;
    }
    let a = as_nat_lit(&args[0])?;
    let b = as_nat_lit(&args[1])?;
    Some(Term::bool_lit(op(a, b)))
}

fn reduce_int_binop(args: &[Term], op: impl Fn(&Int, &Int) -> Int) -> Option<Term> {
    if args.len() != 2 {
        return None;
    }
    let a = as_int_lit(&args[0])?;
    let b = as_int_lit(&args[1])?;
    Some(Term::int_lit(op(a, b)))
}

fn reduce_nat_shift(args: &[Term], is_left: bool) -> Option<Term> {
    if args.len() != 2 {
        return None;
    }
    let a = as_nat_lit(&args[0])?;
    let shift = as_nat_lit(&args[1])?;
    // Shifts above `usize::MAX` bits are refused; the kernel falls
    // back to abstract reasoning rather than truncating an unbounded
    // exponent.
    let shift_digits = shift.as_inner().to_u64_digits();
    if shift_digits.len() > 1 {
        return None;
    }
    let shift_u64 = shift_digits.first().copied().unwrap_or(0);
    let shift_usize = usize::try_from(shift_u64).ok()?;
    Some(Term::nat_lit(Nat::from_inner(if is_left {
        a.as_inner() << shift_usize
    } else {
        a.as_inner() >> shift_usize
    })))
}

fn reduce_int_cmp(args: &[Term], op: impl Fn(&Int, &Int) -> bool) -> Option<Term> {
    if args.len() != 2 {
        return None;
    }
    let a = as_int_lit(&args[0])?;
    let b = as_int_lit(&args[1])?;
    Some(Term::bool_lit(op(a, b)))
}

// ============================================================================
// Nat helpers
// ============================================================================

fn nat_mod_256(n: &Nat) -> u8 {
    let modded = n.as_inner() % 256u32;
    // `BigUint % 256u32` fits in a single u32; pull the LSB.
    let digits = modded.to_u32_digits();
    digits.first().copied().unwrap_or(0) as u8
}

fn nat_to_usize(n: &Nat) -> Option<usize> {
    let digits = n.as_inner().to_u64_digits();
    if digits.len() > 1 {
        return None;
    }
    let v = digits.first().copied().unwrap_or(0);
    usize::try_from(v).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Thm, Type};

    fn nat(n: u32) -> Term {
        Term::nat_lit(Nat::from_inner(n.into()))
    }
    fn int(n: i32) -> Term {
        let nat = Nat::from_inner(n.unsigned_abs().into());
        let sign = if n == 0 {
            Sign::Zero
        } else if n > 0 {
            Sign::Positive
        } else {
            Sign::Negative
        };
        Term::int_lit(Int::from_sign_nat(sign, nat))
    }

    fn assert_reduces(t: Term, want: Term) {
        let thm = Thm::reduce_prim(t.clone())
            .unwrap_or_else(|e| panic!("reduce failed for {t:?}: {e:?}"));
        // Conclusion shape: App(App(Eq, lhs), rhs) — a HOL
        // equation at bool. Walk it structurally.
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
        assert_eq!(lhs, &t, "LHS mismatch");
        assert_eq!(rhs, &want, "RHS mismatch");
    }

    #[test]
    fn nat_succ_reduces() {
        assert_reduces(Term::app(defs::nat_succ(), nat(5)), nat(6));
    }

    #[test]
    fn nat_pred_saturates_at_zero() {
        assert_reduces(Term::app(defs::nat_pred(), nat(0)), nat(0));
        assert_reduces(Term::app(defs::nat_pred(), nat(7)), nat(6));
    }

    fn binary(f: Term, a: Term, b: Term) -> Term {
        Term::app(Term::app(f, a), b)
    }

    #[test]
    fn nat_add_mul() {
        assert_reduces(binary(defs::nat_add(), nat(3), nat(4)), nat(7));
        assert_reduces(binary(defs::nat_mul(), nat(6), nat(7)), nat(42));
    }

    #[test]
    fn nat_sub_saturates() {
        assert_reduces(binary(defs::nat_sub(), nat(2), nat(5)), nat(0));
        assert_reduces(binary(defs::nat_sub(), nat(10), nat(3)), nat(7));
    }

    #[test]
    fn nat_div_mod_zero() {
        // `n / 0 = 0` and `n mod 0 = n` (the Euclidean convention; the
        // `mod` value is forced by `nat.mod`'s let-style body — see the
        // comment in `reduce_spec`).
        assert_reduces(binary(defs::nat_div(), nat(10), nat(0)), nat(0));
        assert_reduces(binary(defs::nat_mod(), nat(10), nat(0)), nat(10));
        assert_reduces(binary(defs::nat_div(), nat(17), nat(5)), nat(3));
        assert_reduces(binary(defs::nat_mod(), nat(17), nat(5)), nat(2));
    }

    #[test]
    fn int_arith() {
        assert_reduces(binary(defs::int_add(), int(-3), int(4)), int(1));
        assert_reduces(binary(defs::int_sub(), int(3), int(7)), int(-4));
        assert_reduces(binary(defs::int_mul(), int(-2), int(-3)), int(6));
    }

    #[test]
    fn int_neg() {
        assert_reduces(Term::app(defs::int_neg(), int(7)), int(-7));
        assert_reduces(Term::app(defs::int_neg(), int(-7)), int(7));
    }

    #[test]
    fn fixed_width_arith_wraps() {
        use defs::IntOp::*;
        let u8 = IntTag::U8;
        let op = |o| defs::int_op(u8, o);
        // 200 + 100 = 300 ≡ 44 (mod 256)
        assert_reduces(
            binary(op(Add), Term::u8_lit(200), Term::u8_lit(100)),
            Term::u8_lit(44),
        );
        // 5 - 8 ≡ 253 (mod 256)
        assert_reduces(
            binary(op(Sub), Term::u8_lit(5), Term::u8_lit(8)),
            Term::u8_lit(253),
        );
        // 20 * 20 = 400 ≡ 144 (mod 256)
        assert_reduces(
            binary(op(Mul), Term::u8_lit(20), Term::u8_lit(20)),
            Term::u8_lit(144),
        );
        assert_reduces(
            binary(op(Div), Term::u8_lit(200), Term::u8_lit(7)),
            Term::u8_lit(28),
        );
        assert_reduces(
            binary(op(Rem), Term::u8_lit(200), Term::u8_lit(7)),
            Term::u8_lit(4),
        );
        // div by zero → 0
        assert_reduces(
            binary(op(Div), Term::u8_lit(5), Term::u8_lit(0)),
            Term::u8_lit(0),
        );
    }

    #[test]
    fn fixed_width_signed_div_and_shr() {
        use defs::IntOp::*;
        let s8 = IntTag::S8;
        // -7 / 2 = -3 (truncating toward zero)
        assert_reduces(
            binary(defs::int_op(s8, Div), Term::s8_lit(-7), Term::s8_lit(2)),
            Term::s8_lit(-3),
        );
        // -8 >> 1 = -4 (arithmetic shift)
        assert_reduces(
            binary(defs::int_op(s8, Shr), Term::s8_lit(-8), Term::s8_lit(1)),
            Term::s8_lit(-4),
        );
        // unsigned 0x80 >> 1 = 0x40 (logical shift)
        assert_reduces(
            binary(
                defs::int_op(IntTag::U8, Shr),
                Term::u8_lit(0x80),
                Term::u8_lit(1),
            ),
            Term::u8_lit(0x40),
        );
    }

    #[test]
    fn fixed_width_bitwise_and_compare() {
        use defs::IntOp::*;
        let u8 = IntTag::U8;
        assert_reduces(
            binary(
                defs::int_op(u8, And),
                Term::u8_lit(0b1100),
                Term::u8_lit(0b1010),
            ),
            Term::u8_lit(0b1000),
        );
        assert_reduces(
            binary(
                defs::int_op(u8, Xor),
                Term::u8_lit(0b1100),
                Term::u8_lit(0b1010),
            ),
            Term::u8_lit(0b0110),
        );
        // unsigned: 200 < 100 is false
        assert_reduces(
            binary(defs::int_op(u8, Lt), Term::u8_lit(200), Term::u8_lit(100)),
            Term::bool_lit(false),
        );
        // signed: -1 < 1 is true (but the same bits, 0xFF < 0x01, would
        // be false unsigned)
        assert_reduces(
            binary(
                defs::int_op(IntTag::S8, Lt),
                Term::s8_lit(-1),
                Term::s8_lit(1),
            ),
            Term::bool_lit(true),
        );
        assert_reduces(
            Term::app(defs::int_op(u8, Not), Term::u8_lit(0)),
            Term::u8_lit(255),
        );
        assert_reduces(
            Term::app(defs::int_op(u8, Neg), Term::u8_lit(1)),
            Term::u8_lit(255),
        );
    }

    #[test]
    fn fixed_width_conversions() {
        // zext u8 → u32 (zero-extend)
        assert_reduces(
            Term::app(defs::int_zext(IntTag::U8, IntTag::U32), Term::u8_lit(200)),
            Term::u32_lit(200),
        );
        // sext s8 → s32 (sign-extend a negative)
        assert_reduces(
            Term::app(defs::int_sext(IntTag::S8, IntTag::S32), Term::s8_lit(-1)),
            Term::s32_lit(-1),
        );
        // zext as wrap: u32 0x1FF → u8 0xFF
        assert_reduces(
            Term::app(
                defs::int_zext(IntTag::U32, IntTag::U8),
                Term::u32_lit(0x1FF),
            ),
            Term::u8_lit(0xFF),
        );
    }

    #[test]
    fn fixed_width_nat_int_casts() {
        // toNat / toInt
        assert_reduces(
            Term::app(defs::int_to_nat(IntTag::U8), Term::u8_lit(200)),
            nat(200),
        );
        assert_reduces(
            Term::app(defs::int_to_int(IntTag::S8), Term::s8_lit(-5)),
            int(-5),
        );
        // fromNat wraps mod 256
        assert_reduces(
            Term::app(defs::int_from_nat(IntTag::U8), nat(300)),
            Term::u8_lit(44),
        );
        // fromInt wraps a negative into two's complement
        assert_reduces(
            Term::app(defs::int_from_int(IntTag::S8), int(-1)),
            Term::s8_lit(-1),
        );
        assert_reduces(
            Term::app(defs::int_from_int(IntTag::U8), int(-1)),
            Term::u8_lit(255),
        );
    }

    #[test]
    fn bytes_cat_concatenates() {
        let cat = binary(
            defs::bytes_cat(),
            Term::blob(vec![1u8, 2]),
            Term::blob(vec![3u8, 4, 5]),
        );
        assert_reduces(cat, Term::blob(vec![1u8, 2, 3, 4, 5]));
    }

    #[test]
    fn bytes_cons_mod_256() {
        assert_reduces(
            binary(defs::bytes_cons_nat(), nat(257), Term::blob(vec![9u8])),
            Term::blob(vec![1u8, 9]),
        );
    }

    #[test]
    fn bytes_len_index() {
        assert_reduces(
            Term::app(defs::bytes_len(), Term::blob(vec![1u8, 2, 3])),
            nat(3),
        );
        assert_reduces(
            binary(defs::bytes_at(), Term::blob(vec![7u8, 8, 9]), nat(1)),
            nat(8),
        );
        // Out-of-bounds → 0.
        assert_reduces(
            binary(defs::bytes_at(), Term::blob(vec![7u8, 8, 9]), nat(99)),
            nat(0),
        );
    }

    #[test]
    fn bytes_slice_saturates() {
        let bs = Term::blob(vec![10u8, 20, 30, 40, 50]);
        let slice = Term::app(
            Term::app(Term::app(defs::bytes_slice(), bs.clone()), nat(1)),
            nat(3),
        );
        assert_reduces(slice, Term::blob(vec![20u8, 30, 40]));
        let past = Term::app(
            Term::app(Term::app(defs::bytes_slice(), bs), nat(3)),
            nat(100),
        );
        assert_reduces(past, Term::blob(vec![40u8, 50]));
    }

    #[test]
    fn nat_to_int_round_trips_positive() {
        assert_reduces(Term::app(defs::nat_to_int(), nat(42)), int(42));
        assert_reduces(Term::app(defs::nat_to_int(), nat(0)), int(0));
    }

    fn hol_eq_at(alpha: Type) -> Term {
        Term::eq_op(alpha)
    }

    fn hol_eq(lhs: Term, rhs: Term) -> Term {
        let alpha = lhs.type_of().unwrap();
        Term::app(Term::app(hol_eq_at(alpha), lhs), rhs)
    }

    #[test]
    fn hol_eq_decides_bool_literals() {
        assert_reduces(
            hol_eq(Term::bool_lit(true), Term::bool_lit(true)),
            Term::bool_lit(true),
        );
        assert_reduces(
            hol_eq(Term::bool_lit(true), Term::bool_lit(false)),
            Term::bool_lit(false),
        );
    }

    #[test]
    fn hol_eq_decides_nat_literals() {
        assert_reduces(hol_eq(nat(5), nat(5)), Term::bool_lit(true));
        assert_reduces(hol_eq(nat(0), nat(5)), Term::bool_lit(false));
    }

    #[test]
    fn hol_eq_decides_int_literals() {
        assert_reduces(hol_eq(int(-3), int(-3)), Term::bool_lit(true));
        assert_reduces(hol_eq(int(-3), int(3)), Term::bool_lit(false));
    }

    #[test]
    fn hol_eq_decides_small_int_literals() {
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
    fn hol_eq_decides_blob_literals() {
        assert_reduces(
            hol_eq(Term::blob(vec![1u8, 2]), Term::blob(vec![1u8, 2])),
            Term::bool_lit(true),
        );
        assert_reduces(
            hol_eq(Term::blob(vec![1u8, 2]), Term::blob(vec![3u8])),
            Term::bool_lit(false),
        );
    }

    #[test]
    fn hol_eq_refuses_open_forms() {
        let n = Term::free("n", Type::nat());
        assert!(Thm::reduce_prim(hol_eq(nat(5), n)).is_err());
    }

    #[test]
    fn term_spec_nat_add_reduces() {
        // defs::nat_add() applied to literals: same shape as
        // Prim::NatArith(Add) but dispatched by handle ptr_eq.
        let t = Term::app(Term::app(defs::nat_add(), nat(3)), nat(4));
        assert_reduces(t, nat(7));
    }

    #[test]
    fn term_spec_nat_sub_saturates() {
        let t = Term::app(Term::app(defs::nat_sub(), nat(2)), nat(5));
        assert_reduces(t, nat(0));
    }

    #[test]
    fn term_spec_nat_le_returns_bool() {
        let t = Term::app(Term::app(defs::nat_le(), nat(3)), nat(5));
        assert_reduces(t, Term::bool_lit(true));
        let t = Term::app(Term::app(defs::nat_le(), nat(7)), nat(5));
        assert_reduces(t, Term::bool_lit(false));
    }

    #[test]
    fn term_spec_int_arith() {
        let t = Term::app(Term::app(defs::int_add(), int(-3)), int(8));
        assert_reduces(t, int(5));
        let t = Term::app(Term::app(defs::int_sub(), int(3)), int(8));
        assert_reduces(t, int(-5));
    }

    #[test]
    fn term_spec_int_lt() {
        let t = Term::app(Term::app(defs::int_lt(), int(-3)), int(2));
        assert_reduces(t, Term::bool_lit(true));
    }

    #[test]
    fn term_spec_nat_div_mod() {
        assert_reduces(
            Term::app(Term::app(defs::nat_div(), nat(17)), nat(5)),
            nat(3),
        );
        assert_reduces(
            Term::app(Term::app(defs::nat_mod(), nat(17)), nat(5)),
            nat(2),
        );
        // Division by zero saturates at zero (kernel convention).
        assert_reduces(
            Term::app(Term::app(defs::nat_div(), nat(17)), nat(0)),
            nat(0),
        );
    }

    #[test]
    fn term_spec_nat_pow() {
        assert_reduces(
            Term::app(Term::app(defs::nat_pow(), nat(2)), nat(10)),
            nat(1024),
        );
        assert_reduces(
            Term::app(Term::app(defs::nat_pow(), nat(7)), nat(0)),
            nat(1),
        );
    }

    #[test]
    fn term_spec_nat_to_int() {
        let t = Term::app(defs::nat_to_int(), nat(42));
        assert_reduces(t, int(42));
        let t = Term::app(defs::nat_to_int(), nat(0));
        assert_reduces(t, int(0));
    }

    #[test]
    fn term_spec_int_div_mod() {
        assert_reduces(
            Term::app(Term::app(defs::int_div(), int(17)), int(5)),
            int(3),
        );
        assert_reduces(
            Term::app(Term::app(defs::int_mod(), int(17)), int(5)),
            int(2),
        );
        // BigInt division truncates toward zero.
        assert_reduces(
            Term::app(Term::app(defs::int_div(), int(-17)), int(5)),
            int(-3),
        );
    }

    #[test]
    fn term_spec_nat_bitwise() {
        // shl: 1 << 4 = 16
        assert_reduces(
            Term::app(Term::app(defs::nat_shl(), nat(1)), nat(4)),
            nat(16),
        );
        // shr: 16 >> 2 = 4
        assert_reduces(
            Term::app(Term::app(defs::nat_shr(), nat(16)), nat(2)),
            nat(4),
        );
        // and / or / xor
        assert_reduces(
            Term::app(Term::app(defs::nat_bit_and(), nat(0b1100)), nat(0b1010)),
            nat(0b1000),
        );
        assert_reduces(
            Term::app(Term::app(defs::nat_bit_or(), nat(0b1100)), nat(0b1010)),
            nat(0b1110),
        );
        assert_reduces(
            Term::app(Term::app(defs::nat_bit_xor(), nat(0b1100)), nat(0b1010)),
            nat(0b0110),
        );
    }

    #[test]
    fn term_spec_nat_bytes_round_trip() {
        // LE: 256 = [0, 1]
        assert_reduces(
            Term::app(defs::nat_to_bytes_le(), nat(256)),
            Term::blob(vec![0, 1]),
        );
        // BE: 256 = [1, 0]
        assert_reduces(
            Term::app(defs::nat_to_bytes_be(), nat(256)),
            Term::blob(vec![1, 0]),
        );
        // Round trip
        assert_reduces(
            Term::app(defs::nat_from_bytes_le(), Term::blob(vec![0, 1])),
            nat(256),
        );
        assert_reduces(
            Term::app(defs::nat_from_bytes_be(), Term::blob(vec![1, 0])),
            nat(256),
        );
    }

    #[test]
    fn term_spec_int_neg_abs_sgn() {
        assert_reduces(Term::app(defs::int_neg(), int(7)), int(-7));
        assert_reduces(Term::app(defs::int_neg(), int(-7)), int(7));
        assert_reduces(Term::app(defs::int_abs(), int(-12)), nat(12));
        assert_reduces(Term::app(defs::int_abs(), int(12)), nat(12));
        assert_reduces(Term::app(defs::int_sgn(), int(-9)), int(-1));
        assert_reduces(Term::app(defs::int_sgn(), int(0)), int(0));
        assert_reduces(Term::app(defs::int_sgn(), int(9)), int(1));
    }

    #[test]
    fn non_reducible_terms_return_err() {
        // A TermSpec not yet applied to enough args.
        let partial = defs::nat_add();
        assert!(Thm::reduce_prim(partial).is_err());
        // An `App` whose head is not a TermSpec/HolOp.
        let not_spec = Term::app(
            Term::const_("f", Type::fun(Type::nat(), Type::nat())),
            nat(5),
        );
        assert!(Thm::reduce_prim(not_spec).is_err());
        // Args that aren't literals (one is a `Free`).
        let not_lit = Term::app(
            Term::app(defs::nat_add(), nat(1)),
            Term::free("x", Type::nat()),
        );
        assert!(Thm::reduce_prim(not_lit).is_err());
    }
}
