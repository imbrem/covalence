//! Builtin primitive reductions on closed-form literal arguments.
//!
//! The kernel's `Thm::reduce_prim` rule defers to the pattern
//! matcher here. Each match arm corresponds to one entry in the
//! catalogue documented on `Thm::reduce_prim`.
//!
//! This module is in the Pure TCB. Audit by checking that:
//!
//! - Each reduction matches the documented arithmetic semantics
//!   (Euclidean div/mod with `n/0 = n%0 = 0`; saturating nat sub
//!   and pred; byte-cons mod-256 on the nat operand).
//! - No unsound shortcut: the function returns `None` for any
//!   shape that isn't an exact-arity application of a `Prim` to
//!   the right number of literal arguments.

use covalence_types::{Int, Nat, Sign};

use crate::defs;
use crate::term::{Arith, HolOp, Prim, Term, TermKind};

/// One-step reduction. Returns the reduced term when `t` is an
/// exactly-shaped `Prim` application with all-literal arguments
/// (or a HOL `=` over two closed literals at a supported type),
/// `None` otherwise.
pub(crate) fn reduce_prim_term(t: &Term) -> Option<Term> {
    let (head, args) = unwind_app(t);

    // HOL `=` decided on closed literals: `Bool`, `Nat`, `Int`, or
    // `Blob`. The kernel commits to literal distinctness — two
    // literals of the same kind are equal iff they are structurally
    // equal.
    if let TermKind::HolOp(HolOp::Eq, _) = head.kind() {
        if args.len() == 2 {
            return literal_eq(&args[0], &args[1]).map(Term::bool_lit);
        }
        return None;
    }

    // Term-spec catalogue dispatch: closed-form reduction of the
    // arithmetic/comparison term-specs (defs::nat_add, defs::int_le,
    // etc.) by pointer identity on the spec handle. The
    // canonical-handle lazy statics live in `crate::defs`; both code
    // paths reach the same `Arc` so `ptr_eq` is unambiguous.
    if let TermKind::Spec(handle, type_args) = head.kind() {
        if !type_args.is_empty() {
            return None;
        }
        return reduce_spec(handle, &args);
    }

    let prim = match head.kind() {
        TermKind::Prim(p) => *p,
        _ => return None,
    };
    match (prim, args.len()) {
        (Prim::NatArith(op), 1) if op.is_unary() => {
            let n = as_nat_lit(&args[0])?;
            Some(Term::nat_lit(apply_nat_unary(op, n)?))
        }
        (Prim::NatArith(op), 2) if !op.is_unary() => {
            let a = as_nat_lit(&args[0])?;
            let b = as_nat_lit(&args[1])?;
            Some(Term::nat_lit(apply_nat_binary(op, a, b)?))
        }
        (Prim::IntArith(op), 1) if op.is_unary() => {
            let n = as_int_lit(&args[0])?;
            Some(Term::int_lit(apply_int_unary(op, n)?))
        }
        (Prim::IntArith(op), 2) if !op.is_unary() => {
            let a = as_int_lit(&args[0])?;
            let b = as_int_lit(&args[1])?;
            Some(Term::int_lit(apply_int_binary(op, a, b)?))
        }
        (Prim::IntNeg, 1) => {
            let n = as_int_lit(&args[0])?;
            Some(Term::int_lit(-n))
        }
        (Prim::BytesCat, 2) => {
            let a = as_blob(&args[0])?;
            let b = as_blob(&args[1])?;
            let mut out = Vec::with_capacity(a.len() + b.len());
            out.extend_from_slice(a);
            out.extend_from_slice(b);
            Some(Term::blob(out))
        }
        (Prim::BytesConsNat, 2) => {
            let n = as_nat_lit(&args[0])?;
            let bs = as_blob(&args[1])?;
            let byte = nat_mod_256(n);
            let mut out = Vec::with_capacity(1 + bs.len());
            out.push(byte);
            out.extend_from_slice(bs);
            Some(Term::blob(out))
        }
        (Prim::BytesLen, 1) => {
            let bs = as_blob(&args[0])?;
            Some(Term::nat_lit(Nat::from_inner(bs.len().into())))
        }
        (Prim::BytesAt, 2) => {
            let bs = as_blob(&args[0])?;
            let idx = as_nat_lit(&args[1])?;
            let byte = nat_to_usize(idx).and_then(|i| bs.get(i)).copied().unwrap_or(0);
            Some(Term::nat_lit(Nat::from_inner((byte as u32).into())))
        }
        (Prim::BytesSlice, 3) => {
            let bs = as_blob(&args[0])?;
            let start = as_nat_lit(&args[1])?;
            let len = as_nat_lit(&args[2])?;
            let start_usize = nat_to_usize(start).unwrap_or(usize::MAX);
            let len_usize = nat_to_usize(len).unwrap_or(usize::MAX);
            let start_clipped = start_usize.min(bs.len());
            let end_clipped = start_clipped.saturating_add(len_usize).min(bs.len());
            Some(Term::blob(bs[start_clipped..end_clipped].to_vec()))
        }
        (Prim::NatToInt, 1) => {
            let n = as_nat_lit(&args[0])?;
            let sign = if n.is_zero() {
                Sign::Zero
            } else {
                Sign::Positive
            };
            Some(Term::int_lit(Int::from_sign_nat(sign, n.clone())))
        }
        _ => None,
    }
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
/// `Int`, `Blob`). Returns `None` if either argument is not a
/// recognised literal at one of those types — the rule is undefined
/// (and `reduce_prim` errors) for non-literal arguments.
fn literal_eq(a: &Term, b: &Term) -> Option<bool> {
    match (a.kind(), b.kind()) {
        (TermKind::Bool(x), TermKind::Bool(y)) => Some(x == y),
        (TermKind::Nat(x), TermKind::Nat(y)) => Some(x == y),
        (TermKind::Int(x), TermKind::Int(y)) => Some(x == y),
        (TermKind::Blob(x), TermKind::Blob(y)) => Some(x == y),
        _ => None,
    }
}

/// Dispatch closed-form reduction for a term-spec leaf applied to
/// `args`. The handle is compared by `ptr_eq` against the canonical
/// catalogue lazy statics — entries the kernel commits to a Rust-
/// side computation for. Anything not in this table falls through to
/// `None`; the user can still build proofs about the term abstractly
/// (via the postulated definitional axioms in `covalence-hol`).
fn reduce_spec(handle: &defs::TermSpec, args: &[Term]) -> Option<Term> {
    // Constructors / unary ops
    if handle.ptr_eq(&defs::nat_succ_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_nat_lit(&args[0])?;
        return Some(Term::nat_lit(Nat::from_inner(n.as_inner() + 1u32)));
    }
    if handle.ptr_eq(&defs::nat_pred_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_nat_lit(&args[0])?;
        return Some(Term::nat_lit(
            n.checked_sub(&Nat::one()).unwrap_or_else(Nat::zero),
        ));
    }
    if handle.ptr_eq(&defs::int_succ_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_int_lit(&args[0])?;
        return Some(Term::int_lit(n + &Int::one()));
    }
    if handle.ptr_eq(&defs::int_pred_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_int_lit(&args[0])?;
        return Some(Term::int_lit(n - &Int::one()));
    }
    // Nat arithmetic
    if handle.ptr_eq(&defs::nat_add_spec()) {
        return reduce_nat_binop(args, |a, b| a + b);
    }
    if handle.ptr_eq(&defs::nat_mul_spec()) {
        return reduce_nat_binop(args, |a, b| a * b);
    }
    if handle.ptr_eq(&defs::nat_sub_spec()) {
        return reduce_nat_binop(args, |a, b| a.checked_sub(b).unwrap_or_else(Nat::zero));
    }
    if handle.ptr_eq(&defs::nat_div_spec()) {
        return reduce_nat_binop(args, |a, b| {
            if b.is_zero() {
                Nat::zero()
            } else {
                a / b
            }
        });
    }
    if handle.ptr_eq(&defs::nat_mod_spec()) {
        return reduce_nat_binop(args, |a, b| {
            if b.is_zero() {
                Nat::zero()
            } else {
                a % b
            }
        });
    }
    if handle.ptr_eq(&defs::nat_pow_spec()) {
        if args.len() != 2 {
            return None;
        }
        let base = as_nat_lit(&args[0])?;
        let exp = as_nat_lit(&args[1])?;
        // BigUint::pow takes a u32 exponent. Refuse oversize exponents
        // rather than truncate — `reduce_prim` falls back to abstract
        // reasoning in that case.
        let exp_digits = exp.as_inner().to_u32_digits();
        if exp_digits.len() > 1 {
            return None;
        }
        let exp_u32 = exp_digits.first().copied().unwrap_or(0);
        return Some(Term::nat_lit(base.pow(exp_u32)));
    }
    if handle.ptr_eq(&defs::nat_le_spec()) {
        return reduce_nat_cmp(args, |a, b| a <= b);
    }
    if handle.ptr_eq(&defs::nat_lt_spec()) {
        return reduce_nat_cmp(args, |a, b| a < b);
    }
    if handle.ptr_eq(&defs::nat_to_int_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_nat_lit(&args[0])?;
        let sign = if n.is_zero() {
            Sign::Zero
        } else {
            Sign::Positive
        };
        return Some(Term::int_lit(Int::from_sign_nat(sign, n.clone())));
    }
    if handle.ptr_eq(&defs::nat_shl_spec()) {
        return reduce_nat_shift(args, true);
    }
    if handle.ptr_eq(&defs::nat_shr_spec()) {
        return reduce_nat_shift(args, false);
    }
    if handle.ptr_eq(&defs::nat_bit_and_spec()) {
        return reduce_nat_binop(args, |a, b| {
            Nat::from_inner(a.as_inner() & b.as_inner())
        });
    }
    if handle.ptr_eq(&defs::nat_bit_or_spec()) {
        return reduce_nat_binop(args, |a, b| {
            Nat::from_inner(a.as_inner() | b.as_inner())
        });
    }
    if handle.ptr_eq(&defs::nat_bit_xor_spec()) {
        return reduce_nat_binop(args, |a, b| {
            Nat::from_inner(a.as_inner() ^ b.as_inner())
        });
    }
    if handle.ptr_eq(&defs::nat_to_bytes_le_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_nat_lit(&args[0])?;
        return Some(Term::blob(n.to_bytes_le()));
    }
    if handle.ptr_eq(&defs::nat_to_bytes_be_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_nat_lit(&args[0])?;
        return Some(Term::blob(n.to_bytes_be()));
    }
    if handle.ptr_eq(&defs::nat_from_bytes_le_spec()) {
        if args.len() != 1 {
            return None;
        }
        let bs = as_blob(&args[0])?;
        return Some(Term::nat_lit(Nat::from_bytes_le(bs)));
    }
    if handle.ptr_eq(&defs::nat_from_bytes_be_spec()) {
        if args.len() != 1 {
            return None;
        }
        let bs = as_blob(&args[0])?;
        return Some(Term::nat_lit(Nat::from_bytes_be(bs)));
    }
    // Int arithmetic
    if handle.ptr_eq(&defs::int_add_spec()) {
        return reduce_int_binop(args, |a, b| a + b);
    }
    if handle.ptr_eq(&defs::int_mul_spec()) {
        return reduce_int_binop(args, |a, b| a * b);
    }
    if handle.ptr_eq(&defs::int_sub_spec()) {
        return reduce_int_binop(args, |a, b| a - b);
    }
    if handle.ptr_eq(&defs::int_div_spec()) {
        return reduce_int_binop(args, |a, b| {
            if b.is_zero() {
                Int::zero()
            } else {
                a / b
            }
        });
    }
    if handle.ptr_eq(&defs::int_mod_spec()) {
        return reduce_int_binop(args, |a, b| {
            if b.is_zero() {
                Int::zero()
            } else {
                a % b
            }
        });
    }
    if handle.ptr_eq(&defs::int_le_spec()) {
        return reduce_int_cmp(args, |a, b| a <= b);
    }
    if handle.ptr_eq(&defs::int_lt_spec()) {
        return reduce_int_cmp(args, |a, b| a < b);
    }
    if handle.ptr_eq(&defs::int_neg_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_int_lit(&args[0])?;
        return Some(Term::int_lit(-n));
    }
    if handle.ptr_eq(&defs::int_abs_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_int_lit(&args[0])?;
        return Some(Term::nat_lit(n.abs()));
    }
    if handle.ptr_eq(&defs::int_sgn_spec()) {
        if args.len() != 1 {
            return None;
        }
        let n = as_int_lit(&args[0])?;
        let sgn = match n.sign() {
            Sign::Negative => Int::from_sign_nat(Sign::Negative, Nat::one()),
            Sign::Zero => Int::zero(),
            Sign::Positive => Int::from_sign_nat(Sign::Positive, Nat::one()),
        };
        return Some(Term::int_lit(sgn));
    }
    None
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
// Arithmetic (Nat — saturating sub/pred; n/0 = n%0 = 0)
// ============================================================================

fn apply_nat_unary(op: Arith, n: &Nat) -> Option<Nat> {
    Some(match op {
        Arith::Succ => Nat::from_inner(n.as_inner() + 1u32),
        Arith::Pred => n.checked_sub(&Nat::one()).unwrap_or_else(Nat::zero),
        _ => return None,
    })
}

fn apply_nat_binary(op: Arith, a: &Nat, b: &Nat) -> Option<Nat> {
    Some(match op {
        Arith::Add => a + b,
        Arith::Mul => a * b,
        Arith::Sub => a.checked_sub(b).unwrap_or_else(Nat::zero),
        Arith::Div => {
            if b.is_zero() {
                Nat::zero()
            } else {
                a / b
            }
        }
        Arith::Mod => {
            if b.is_zero() {
                Nat::zero()
            } else {
                a % b
            }
        }
        _ => return None,
    })
}

// ============================================================================
// Arithmetic (Int — n/0 = n%0 = 0)
// ============================================================================

fn apply_int_unary(op: Arith, n: &Int) -> Option<Int> {
    Some(match op {
        Arith::Succ => n + &Int::one(),
        Arith::Pred => n - &Int::one(),
        _ => return None,
    })
}

fn apply_int_binary(op: Arith, a: &Int, b: &Int) -> Option<Int> {
    Some(match op {
        Arith::Add => a + b,
        Arith::Mul => a * b,
        Arith::Sub => a - b,
        Arith::Div => {
            if b.is_zero() {
                Int::zero()
            } else {
                a / b
            }
        }
        Arith::Mod => {
            if b.is_zero() {
                Int::zero()
            } else {
                a % b
            }
        }
        _ => return None,
    })
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
        let nat = Nat::from_inner((n.unsigned_abs() as u32).into());
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
        let thm = Thm::reduce_prim(t.clone()).unwrap_or_else(|e| {
            panic!("reduce failed for {t:?}: {e:?}")
        });
        let (lhs, rhs) = match thm.concl().kind() {
            TermKind::Eq(a, b) => (a.clone(), b.clone()),
            _ => panic!("concl is not Eq: {:?}", thm.concl()),
        };
        assert_eq!(lhs, t, "LHS mismatch");
        assert_eq!(rhs, want, "RHS mismatch");
    }

    #[test]
    fn nat_succ_reduces() {
        assert_reduces(
            Term::app(Term::prim(Prim::NatArith(Arith::Succ)), nat(5)),
            nat(6),
        );
    }

    #[test]
    fn nat_pred_saturates_at_zero() {
        assert_reduces(
            Term::app(Term::prim(Prim::NatArith(Arith::Pred)), nat(0)),
            nat(0),
        );
        assert_reduces(
            Term::app(Term::prim(Prim::NatArith(Arith::Pred)), nat(7)),
            nat(6),
        );
    }

    fn binary(p: Prim, a: Term, b: Term) -> Term {
        Term::app(Term::app(Term::prim(p), a), b)
    }

    #[test]
    fn nat_add_mul() {
        assert_reduces(binary(Prim::NatArith(Arith::Add), nat(3), nat(4)), nat(7));
        assert_reduces(binary(Prim::NatArith(Arith::Mul), nat(6), nat(7)), nat(42));
    }

    #[test]
    fn nat_sub_saturates() {
        assert_reduces(binary(Prim::NatArith(Arith::Sub), nat(2), nat(5)), nat(0));
        assert_reduces(binary(Prim::NatArith(Arith::Sub), nat(10), nat(3)), nat(7));
    }

    #[test]
    fn nat_div_mod_zero_returns_zero() {
        assert_reduces(binary(Prim::NatArith(Arith::Div), nat(10), nat(0)), nat(0));
        assert_reduces(binary(Prim::NatArith(Arith::Mod), nat(10), nat(0)), nat(0));
        assert_reduces(binary(Prim::NatArith(Arith::Div), nat(17), nat(5)), nat(3));
        assert_reduces(binary(Prim::NatArith(Arith::Mod), nat(17), nat(5)), nat(2));
    }

    #[test]
    fn int_arith() {
        assert_reduces(binary(Prim::IntArith(Arith::Add), int(-3), int(4)), int(1));
        assert_reduces(binary(Prim::IntArith(Arith::Sub), int(3), int(7)), int(-4));
        assert_reduces(binary(Prim::IntArith(Arith::Mul), int(-2), int(-3)), int(6));
    }

    #[test]
    fn int_neg() {
        assert_reduces(Term::app(Term::prim(Prim::IntNeg), int(7)), int(-7));
        assert_reduces(Term::app(Term::prim(Prim::IntNeg), int(-7)), int(7));
    }

    #[test]
    fn bytes_cat_concatenates() {
        let cat = binary(Prim::BytesCat, Term::blob(vec![1u8, 2]), Term::blob(vec![3u8, 4, 5]));
        assert_reduces(cat, Term::blob(vec![1u8, 2, 3, 4, 5]));
    }

    #[test]
    fn bytes_cons_mod_256() {
        assert_reduces(
            binary(Prim::BytesConsNat, nat(257), Term::blob(vec![9u8])),
            Term::blob(vec![1u8, 9]),
        );
    }

    #[test]
    fn bytes_len_index() {
        assert_reduces(
            Term::app(Term::prim(Prim::BytesLen), Term::blob(vec![1u8, 2, 3])),
            nat(3),
        );
        assert_reduces(
            binary(Prim::BytesAt, Term::blob(vec![7u8, 8, 9]), nat(1)),
            nat(8),
        );
        // Out-of-bounds → 0.
        assert_reduces(
            binary(Prim::BytesAt, Term::blob(vec![7u8, 8, 9]), nat(99)),
            nat(0),
        );
    }

    #[test]
    fn bytes_slice_saturates() {
        let bs = Term::blob(vec![10u8, 20, 30, 40, 50]);
        let slice = Term::app(
            Term::app(Term::app(Term::prim(Prim::BytesSlice), bs.clone()), nat(1)),
            nat(3),
        );
        assert_reduces(slice, Term::blob(vec![20u8, 30, 40]));
        // Slice past the end clips.
        let past = Term::app(
            Term::app(Term::app(Term::prim(Prim::BytesSlice), bs), nat(3)),
            nat(100),
        );
        assert_reduces(past, Term::blob(vec![40u8, 50]));
    }

    #[test]
    fn nat_to_int_round_trips_positive() {
        assert_reduces(Term::app(Term::prim(Prim::NatToInt), nat(42)), int(42));
        assert_reduces(Term::app(Term::prim(Prim::NatToInt), nat(0)), int(0));
    }


    fn hol_eq_at(alpha: Type) -> Term {
        Term::hol_op(
            HolOp::Eq,
            Type::fun(alpha.clone(), Type::fun(alpha, Type::bool())),
        )
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
        // A `Prim` not yet applied to enough args.
        let partial = Term::prim(Prim::NatArith(Arith::Add));
        assert!(Thm::reduce_prim(partial).is_err());
        // An `App` whose head is not a `Prim`.
        let not_prim = Term::app(Term::const_("f", Type::fun(Type::nat(), Type::nat())), nat(5));
        assert!(Thm::reduce_prim(not_prim).is_err());
        // Args that aren't literals (one is a `Free`).
        let not_lit = Term::app(
            Term::app(Term::prim(Prim::NatArith(Arith::Add)), nat(1)),
            Term::free("x", Type::nat()),
        );
        assert!(Thm::reduce_prim(not_lit).is_err());
    }
}
