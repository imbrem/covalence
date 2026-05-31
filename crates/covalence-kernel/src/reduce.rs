//! Top-level reduction rules (`docs/prover-primops.md` §10).
//!
//! These are the rule definitions that fire when an outside caller
//! asks "is this term reducible at the top?" The arena itself is
//! definition-blind — it only exposes `rewrite`, `union`, `subst`,
//! and the congruence/equality predicates. The judgement that a
//! particular reduction produces a *true* equality lives in the
//! [`Thm`](crate::Thm) layer; this module provides the pure
//! computation that builds the reduced term so [`Thm::reduce`] can
//! wrap it in a kernel-checked `Eq`.
//!
//! Current coverage:
//!
//! - **Literal-arg evaluation (§10.1)** for the boolean logic ops,
//!   basic nat/int arithmetic, comparison primitives, and a few
//!   fixed-width ops.
//! - **Numeral normalisation (§10.2)** for `NatSucc(NatInline)`,
//!   `NatPred(NatInline)`, and `IntNeg(IntInline)`.
//! - **Ite-on-literal-cond (§10.5)** for `Comb(Ite(cond, then), else)`
//!   when `cond` is a literal.
//! - **Identity combinator (§10.6)**: `Comb(Id(_), x) → x`.

use crate::arena::Arena;
use crate::primop::{PrimOp1, PrimOp2};
use crate::term::{TermDef, TermRef};

/// Try one top-level reduction step on `t`. Returns the reduced
/// `TermRef` if a rule fires, otherwise `None`. The arena's UF is
/// **not** modified — equality recording is the caller's
/// responsibility (typically via [`Thm::reduce`](crate::Thm::reduce)).
pub fn step(arena: &mut Arena, t: TermRef) -> Option<TermRef> {
    let local_id = t.as_local()?;
    let def = *arena.term_def(local_id);
    match def {
        TermDef::Op1(op, x) => reduce_op1(arena, op, x),
        TermDef::Op2(op, a, b) => reduce_op2(arena, op, a, b),
        TermDef::Comb(f, x) => reduce_comb(arena, f, x),
        _ => None,
    }
}

fn reduce_op1(arena: &mut Arena, op: PrimOp1, x: TermRef) -> Option<TermRef> {
    use PrimOp1::*;
    let x_id = x.as_local()?;
    let x_def = *arena.term_def(x_id);
    let new_def = match (op, x_def) {
        // Boolean negation.
        (LogicalNot, TermDef::True) => TermDef::False,
        (LogicalNot, TermDef::False) => TermDef::True,
        // Naturals: numeral normalisation.
        (NatSucc, TermDef::NatInline(p)) => {
            let v = p.to_u64();
            if let Some(next) = v.checked_add(1) {
                TermDef::nat_inline(next)
            } else {
                use covalence_types::Nat;
                let big = Nat::from(v) + Nat::from(1u64);
                let id = arena.intern_nat(big);
                TermDef::NatStored(id)
            }
        }
        (NatPred, TermDef::NatInline(p)) => {
            let v = p.to_u64();
            TermDef::nat_inline(v.saturating_sub(1))
        }
        (NatPopcount, TermDef::NatInline(p)) => {
            TermDef::nat_inline(p.to_u64().count_ones() as u64)
        }
        // Integer negation.
        (IntNeg, TermDef::IntInline(p)) => {
            let v = p.to_i64();
            if let Some(neg) = v.checked_neg() {
                TermDef::int_inline(neg)
            } else {
                // i64::MIN — fall through; caller can handle via a wider int.
                return None;
            }
        }
        // Fixed-width: bitwise NOT.
        (U8Not, TermDef::U8(v)) => TermDef::U8(!v),
        (U16Not, TermDef::U16(v)) => TermDef::U16(!v),
        (U32Not, TermDef::U32(v)) => TermDef::U32(!v),
        (U64Not, TermDef::U64(p)) => TermDef::u64_literal(!p.to_u64()),
        (I8Not, TermDef::I8(v)) => TermDef::I8(!v),
        (I16Not, TermDef::I16(v)) => TermDef::I16(!v),
        (I32Not, TermDef::I32(v)) => TermDef::I32(!v),
        (I64Not, TermDef::I64(p)) => TermDef::i64_literal(!p.to_i64()),
        // Fixed-width: popcount.
        (U8Popcount, TermDef::U8(v)) => TermDef::U8(v.count_ones() as u8),
        (U16Popcount, TermDef::U16(v)) => TermDef::U16(v.count_ones() as u16),
        (U32Popcount, TermDef::U32(v)) => TermDef::U32(v.count_ones()),
        (U64Popcount, TermDef::U64(p)) => TermDef::u64_literal(p.to_u64().count_ones() as u64),
        // Fixed-width: eqz.
        (U8Eqz, TermDef::U8(v)) => if v == 0 { TermDef::True } else { TermDef::False },
        (U16Eqz, TermDef::U16(v)) => if v == 0 { TermDef::True } else { TermDef::False },
        (U32Eqz, TermDef::U32(v)) => if v == 0 { TermDef::True } else { TermDef::False },
        (U64Eqz, TermDef::U64(p)) => {
            if p.to_u64() == 0 { TermDef::True } else { TermDef::False }
        }
        _ => return None,
    };
    Some(TermRef::local(arena.alloc_term(new_def)))
}

fn reduce_op2(arena: &mut Arena, op: PrimOp2, a: TermRef, b: TermRef) -> Option<TermRef> {
    use PrimOp2::*;
    let a_id = a.as_local()?;
    let b_id = b.as_local()?;
    let a_def = *arena.term_def(a_id);
    let b_def = *arena.term_def(b_id);
    let new_def = match (op, a_def, b_def) {
        // Boolean: full truth tables on literal args.
        (LogicalAnd, TermDef::True, TermDef::True) => TermDef::True,
        (LogicalAnd, TermDef::False, _) | (LogicalAnd, _, TermDef::False) => TermDef::False,
        (LogicalOr, TermDef::True, _) | (LogicalOr, _, TermDef::True) => TermDef::True,
        (LogicalOr, TermDef::False, TermDef::False) => TermDef::False,
        (LogicalXor, TermDef::True, TermDef::True) => TermDef::False,
        (LogicalXor, TermDef::True, TermDef::False) => TermDef::True,
        (LogicalXor, TermDef::False, TermDef::True) => TermDef::True,
        (LogicalXor, TermDef::False, TermDef::False) => TermDef::False,
        (LogicalImp, TermDef::True, TermDef::True) => TermDef::True,
        (LogicalImp, TermDef::True, TermDef::False) => TermDef::False,
        (LogicalImp, TermDef::False, _) => TermDef::True,
        (LogicalNand, x, y) => reduce_via_other_2(arena, LogicalAnd, x, y, true)?,
        (LogicalNor, x, y) => reduce_via_other_2(arena, LogicalOr, x, y, true)?,

        // Naturals: arithmetic on inline literals.
        (NatAdd, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            let (av, bv) = (p.to_u64(), q.to_u64());
            if let Some(sum) = av.checked_add(bv) {
                TermDef::nat_inline(sum)
            } else {
                use covalence_types::Nat;
                let big = Nat::from(av) + Nat::from(bv);
                let id = arena.intern_nat(big);
                TermDef::NatStored(id)
            }
        }
        (NatSub, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            TermDef::nat_inline(p.to_u64().saturating_sub(q.to_u64()))
        }
        (NatMul, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            let (av, bv) = (p.to_u64(), q.to_u64());
            if let Some(prod) = av.checked_mul(bv) {
                TermDef::nat_inline(prod)
            } else {
                use covalence_types::Nat;
                let big = Nat::from(av) * Nat::from(bv);
                let id = arena.intern_nat(big);
                TermDef::NatStored(id)
            }
        }
        (NatDiv, TermDef::NatInline(_), TermDef::NatInline(q)) if q.to_u64() == 0 => {
            TermDef::nat_inline(0) // axiom: div by 0 = 0
        }
        (NatMod, TermDef::NatInline(_), TermDef::NatInline(q)) if q.to_u64() == 0 => {
            TermDef::nat_inline(0)
        }
        (NatDiv, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            TermDef::nat_inline(p.to_u64() / q.to_u64())
        }
        (NatMod, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            TermDef::nat_inline(p.to_u64() % q.to_u64())
        }
        (NatEq, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            if p.to_u64() == q.to_u64() { TermDef::True } else { TermDef::False }
        }
        (NatLt, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            if p.to_u64() < q.to_u64() { TermDef::True } else { TermDef::False }
        }
        (NatLe, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            if p.to_u64() <= q.to_u64() { TermDef::True } else { TermDef::False }
        }

        // Integers: arithmetic on inline literals.
        (IntAdd, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            let (av, bv) = (p.to_i64(), q.to_i64());
            if let Some(sum) = av.checked_add(bv) {
                TermDef::int_inline(sum)
            } else {
                use covalence_types::Int;
                let big = Int::from(av) + Int::from(bv);
                let id = arena.intern_int(big);
                TermDef::IntStored(id)
            }
        }
        (IntSub, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            let (av, bv) = (p.to_i64(), q.to_i64());
            if let Some(diff) = av.checked_sub(bv) {
                TermDef::int_inline(diff)
            } else {
                use covalence_types::Int;
                let big = Int::from(av) - Int::from(bv);
                let id = arena.intern_int(big);
                TermDef::IntStored(id)
            }
        }
        (IntMul, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            let (av, bv) = (p.to_i64(), q.to_i64());
            if let Some(prod) = av.checked_mul(bv) {
                TermDef::int_inline(prod)
            } else {
                use covalence_types::Int;
                let big = Int::from(av) * Int::from(bv);
                let id = arena.intern_int(big);
                TermDef::IntStored(id)
            }
        }
        (IntEq, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            if p.to_i64() == q.to_i64() { TermDef::True } else { TermDef::False }
        }
        (IntLt, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            if p.to_i64() < q.to_i64() { TermDef::True } else { TermDef::False }
        }
        (IntLe, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            if p.to_i64() <= q.to_i64() { TermDef::True } else { TermDef::False }
        }

        // Fixed-width: wrapping arithmetic. (Representative family.)
        (U32Add, TermDef::U32(av), TermDef::U32(bv)) => TermDef::U32(av.wrapping_add(bv)),
        (U32Sub, TermDef::U32(av), TermDef::U32(bv)) => TermDef::U32(av.wrapping_sub(bv)),
        (U32Mul, TermDef::U32(av), TermDef::U32(bv)) => TermDef::U32(av.wrapping_mul(bv)),
        (U32And, TermDef::U32(av), TermDef::U32(bv)) => TermDef::U32(av & bv),
        (U32Or, TermDef::U32(av), TermDef::U32(bv)) => TermDef::U32(av | bv),
        (U32Xor, TermDef::U32(av), TermDef::U32(bv)) => TermDef::U32(av ^ bv),
        (U32Eq, TermDef::U32(av), TermDef::U32(bv)) => {
            if av == bv { TermDef::True } else { TermDef::False }
        }

        _ => return None,
    };
    Some(TermRef::local(arena.alloc_term(new_def)))
}

/// Reduce `op(a, b)` indirectly via another op, optionally negating
/// the result (used for `Nand` = `Not (And ...)`, `Nor` = `Not (Or
/// ...)`).
fn reduce_via_other_2(
    arena: &mut Arena,
    op: PrimOp2,
    a: TermDef,
    b: TermDef,
    negate: bool,
) -> Option<TermDef> {
    let a_id = arena.alloc_term(a);
    let b_id = arena.alloc_term(b);
    let result = reduce_op2(arena, op, TermRef::local(a_id), TermRef::local(b_id))?;
    let result_def = *arena.term_def(result.as_local()?);
    Some(if negate {
        match result_def {
            TermDef::True => TermDef::False,
            TermDef::False => TermDef::True,
            _ => return None,
        }
    } else {
        result_def
    })
}

fn reduce_comb(arena: &mut Arena, f: TermRef, x: TermRef) -> Option<TermRef> {
    // Comb(Id(_), x) → x.
    let f_id = f.as_local()?;
    let f_def = *arena.term_def(f_id);
    if let TermDef::Id(_) = f_def {
        return Some(x);
    }
    // Comb(Ite(cond, then), else) on a literal cond → branch.
    if let TermDef::Ite(cond, then_branch) = f_def {
        let cond_id = cond.as_local()?;
        match arena.term_def(cond_id) {
            TermDef::True => return Some(then_branch),
            TermDef::False => return Some(x),
            _ => {}
        }
    }
    None
}
