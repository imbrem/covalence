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

use crate::term::{Arith, Prim, Term, TermKind};

/// One-step reduction. Returns the reduced term when `t` is an
/// exactly-shaped `Prim` application with all-literal arguments,
/// `None` otherwise.
pub(crate) fn reduce_prim_term(t: &Term) -> Option<Term> {
    let (head, args) = unwind_app(t);
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
        TermKind::NatLit(n) => Some(n),
        _ => None,
    }
}

fn as_int_lit(t: &Term) -> Option<&Int> {
    match t.kind() {
        TermKind::IntLit(n) => Some(n),
        _ => None,
    }
}

fn as_blob(t: &Term) -> Option<&[u8]> {
    match t.kind() {
        TermKind::Blob(b) => Some(b),
        _ => None,
    }
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
