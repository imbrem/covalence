//! Top-level reduction rules.
//!
//! The kernel only reduces **fully-constant** expressions: a primop
//! applied to literals returns its computed literal result.
//! Algebraic identities like `a + 0 = a`, short-circuit shortcuts
//! like `LogicalAnd False x = False`, and definitional unfoldings
//! like `Comb(Id, x) = x` are not kernel reductions — they're
//! ordinary theorems proved against the kernel's axioms.
//!
//! Current coverage:
//!
//! - **Boolean primops** — full truth tables on `(True, False)` args.
//! - **`Nat`** — `Succ`, `Pred`, `Popcount` on inline literals;
//!   `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Eq`, `Lt`, `Le` on pairs of
//!   inline literals. (`NatDiv` and `NatMod` saturate to zero on a
//!   zero divisor — both args must still be literals.)
//! - **`Int`** — `Neg` on an inline literal; `Add`, `Sub`, `Mul`,
//!   `Eq`, `Lt`, `Le` on pairs of inline literals.

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
        _ => None,
    }
}

fn reduce_op1(arena: &mut Arena, op: PrimOp1, x: TermRef) -> Option<TermRef> {
    use PrimOp1::*;
    let x_id = x.as_local()?;
    let x_def = *arena.term_def(x_id);
    let new_def = match (op, x_def) {
        // Boolean negation.
        (LogicalNot, TermDef::Bool(true)) => TermDef::Bool(false),
        (LogicalNot, TermDef::Bool(false)) => TermDef::Bool(true),
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
            TermDef::nat_inline(p.to_u64().saturating_sub(1))
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
        // Boolean: full truth tables. Both args must be literals.
        (LogicalAnd, TermDef::Bool(true), TermDef::Bool(true)) => TermDef::Bool(true),
        (LogicalAnd, TermDef::Bool(true), TermDef::Bool(false)) => TermDef::Bool(false),
        (LogicalAnd, TermDef::Bool(false), TermDef::Bool(true)) => TermDef::Bool(false),
        (LogicalAnd, TermDef::Bool(false), TermDef::Bool(false)) => TermDef::Bool(false),
        (LogicalOr, TermDef::Bool(true), TermDef::Bool(true)) => TermDef::Bool(true),
        (LogicalOr, TermDef::Bool(true), TermDef::Bool(false)) => TermDef::Bool(true),
        (LogicalOr, TermDef::Bool(false), TermDef::Bool(true)) => TermDef::Bool(true),
        (LogicalOr, TermDef::Bool(false), TermDef::Bool(false)) => TermDef::Bool(false),
        (LogicalXor, TermDef::Bool(true), TermDef::Bool(true)) => TermDef::Bool(false),
        (LogicalXor, TermDef::Bool(true), TermDef::Bool(false)) => TermDef::Bool(true),
        (LogicalXor, TermDef::Bool(false), TermDef::Bool(true)) => TermDef::Bool(true),
        (LogicalXor, TermDef::Bool(false), TermDef::Bool(false)) => TermDef::Bool(false),
        (LogicalImp, TermDef::Bool(true), TermDef::Bool(true)) => TermDef::Bool(true),
        (LogicalImp, TermDef::Bool(true), TermDef::Bool(false)) => TermDef::Bool(false),
        (LogicalImp, TermDef::Bool(false), TermDef::Bool(true)) => TermDef::Bool(true),
        (LogicalImp, TermDef::Bool(false), TermDef::Bool(false)) => TermDef::Bool(true),
        (LogicalNand, TermDef::Bool(true), TermDef::Bool(true)) => TermDef::Bool(false),
        (LogicalNand, TermDef::Bool(true), TermDef::Bool(false)) => TermDef::Bool(true),
        (LogicalNand, TermDef::Bool(false), TermDef::Bool(true)) => TermDef::Bool(true),
        (LogicalNand, TermDef::Bool(false), TermDef::Bool(false)) => TermDef::Bool(true),
        (LogicalNor, TermDef::Bool(true), TermDef::Bool(true)) => TermDef::Bool(false),
        (LogicalNor, TermDef::Bool(true), TermDef::Bool(false)) => TermDef::Bool(false),
        (LogicalNor, TermDef::Bool(false), TermDef::Bool(true)) => TermDef::Bool(false),
        (LogicalNor, TermDef::Bool(false), TermDef::Bool(false)) => TermDef::Bool(true),

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
        (NatDiv, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            let qv = q.to_u64();
            // Axiom: divide-by-zero saturates to zero.
            let result = if qv == 0 { 0 } else { p.to_u64() / qv };
            TermDef::nat_inline(result)
        }
        (NatMod, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            let qv = q.to_u64();
            let result = if qv == 0 { 0 } else { p.to_u64() % qv };
            TermDef::nat_inline(result)
        }
        (NatEq, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            if p.to_u64() == q.to_u64() { TermDef::Bool(true) } else { TermDef::Bool(false) }
        }
        (NatLt, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            if p.to_u64() < q.to_u64() { TermDef::Bool(true) } else { TermDef::Bool(false) }
        }
        (NatLe, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            if p.to_u64() <= q.to_u64() { TermDef::Bool(true) } else { TermDef::Bool(false) }
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
            if p.to_i64() == q.to_i64() { TermDef::Bool(true) } else { TermDef::Bool(false) }
        }
        (IntLt, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            if p.to_i64() < q.to_i64() { TermDef::Bool(true) } else { TermDef::Bool(false) }
        }
        (IntLe, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            if p.to_i64() <= q.to_i64() { TermDef::Bool(true) } else { TermDef::Bool(false) }
        }

        _ => return None,
    };
    Some(TermRef::local(arena.alloc_term(new_def)))
}
