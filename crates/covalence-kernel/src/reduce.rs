//! Computation table for the kernel's single `reduce_primop`.
//!
//! Public entry point is [`Arena::reduce_primop`](crate::Arena::reduce_primop).
//! This module only owns the per-op pure-computation tables, kept separate
//! from `arena.rs` so the audit surface for "what does the kernel reduce?"
//! lives in one ~150-line file.
//!
//! Discipline: a primop reduces **iff every input is a literal**. No
//! algebraic identities, no short-circuits, no definitional unfoldings.
//! Those are theorems over the kernel's axioms, not kernel reductions.

use crate::arena::Arena;
use crate::primop::{PrimOp1, PrimOp2};
use crate::term::TermDef;

/// What `compute` produces — either a plain `TermDef` (no interning
/// needed) or a payload that has to land in `arena`'s interning tables.
pub(crate) enum PrimResult {
    Def(TermDef),
    NatBig(covalence_types::Nat),
    IntBig(covalence_types::Int),
}

/// Try to reduce `def` (the top-level term being reduced) interpreted in
/// `arena`. `def` is expected to be an applied primop; child literals are
/// dereferenced through `arena` (transparently following foreign
/// imports). Returns `None` if no rule fires or any child can't be
/// dereferenced.
pub(crate) fn compute(arena: &Arena, def: TermDef) -> Option<PrimResult> {
    match def {
        TermDef::Op1(op, x) => {
            let (_, x_def) = arena.deref_term(x)?;
            apply_op1(op, x_def)
        }
        TermDef::Op2(op, a, b) => {
            let (_, a_def) = arena.deref_term(a)?;
            let (_, b_def) = arena.deref_term(b)?;
            apply_op2(op, a_def, b_def)
        }
        _ => None,
    }
}

fn apply_op1(op: PrimOp1, x: TermDef) -> Option<PrimResult> {
    use PrimOp1::*;
    let def = match (op, x) {
        (LogicalNot, TermDef::Bool(a)) => TermDef::Bool(!a),
        (NatSucc, TermDef::NatInline(p)) => {
            let v = p.to_u64();
            return Some(match v.checked_add(1) {
                Some(n) => PrimResult::Def(TermDef::nat_inline(n)),
                None => {
                    use covalence_types::Nat;
                    PrimResult::NatBig(Nat::from(v) + Nat::from(1u64))
                }
            });
        }
        (NatPred, TermDef::NatInline(p)) => TermDef::nat_inline(p.to_u64().saturating_sub(1)),
        (NatPopcount, TermDef::NatInline(p)) => TermDef::nat_inline(p.to_u64().count_ones() as u64),
        (IntNeg, TermDef::IntInline(p)) => {
            let v = p.to_i64();
            // i64::MIN can't be negated to i64; defer to a wider int caller.
            TermDef::int_inline(v.checked_neg()?)
        }
        _ => return None,
    };
    Some(PrimResult::Def(def))
}

fn apply_op2(op: PrimOp2, a: TermDef, b: TermDef) -> Option<PrimResult> {
    use PrimOp2::*;
    let def = match (op, a, b) {
        // -- booleans: full truth tables --
        (LogicalAnd, TermDef::Bool(x), TermDef::Bool(y)) => TermDef::Bool(x && y),
        (LogicalOr, TermDef::Bool(x), TermDef::Bool(y)) => TermDef::Bool(x || y),
        (LogicalXor, TermDef::Bool(x), TermDef::Bool(y)) => TermDef::Bool(x ^ y),
        (LogicalImp, TermDef::Bool(x), TermDef::Bool(y)) => TermDef::Bool(!x || y),
        (LogicalNand, TermDef::Bool(x), TermDef::Bool(y)) => TermDef::Bool(!(x && y)),
        (LogicalNor, TermDef::Bool(x), TermDef::Bool(y)) => TermDef::Bool(!(x || y)),

        // -- naturals: arithmetic + comparisons --
        (NatAdd, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            let (av, bv) = (p.to_u64(), q.to_u64());
            return Some(match av.checked_add(bv) {
                Some(n) => PrimResult::Def(TermDef::nat_inline(n)),
                None => {
                    use covalence_types::Nat;
                    PrimResult::NatBig(Nat::from(av) + Nat::from(bv))
                }
            });
        }
        (NatSub, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            TermDef::nat_inline(p.to_u64().saturating_sub(q.to_u64()))
        }
        (NatMul, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            let (av, bv) = (p.to_u64(), q.to_u64());
            return Some(match av.checked_mul(bv) {
                Some(n) => PrimResult::Def(TermDef::nat_inline(n)),
                None => {
                    use covalence_types::Nat;
                    PrimResult::NatBig(Nat::from(av) * Nat::from(bv))
                }
            });
        }
        (NatDiv, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            let (pv, qv) = (p.to_u64(), q.to_u64());
            TermDef::nat_inline(if qv == 0 { 0 } else { pv / qv })
        }
        (NatMod, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            let (pv, qv) = (p.to_u64(), q.to_u64());
            TermDef::nat_inline(if qv == 0 { 0 } else { pv % qv })
        }
        (NatEq, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            TermDef::Bool(p.to_u64() == q.to_u64())
        }
        (NatLt, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            TermDef::Bool(p.to_u64() < q.to_u64())
        }
        (NatLe, TermDef::NatInline(p), TermDef::NatInline(q)) => {
            TermDef::Bool(p.to_u64() <= q.to_u64())
        }

        // -- integers: arithmetic + comparisons --
        (IntAdd, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            let (av, bv) = (p.to_i64(), q.to_i64());
            return Some(match av.checked_add(bv) {
                Some(n) => PrimResult::Def(TermDef::int_inline(n)),
                None => {
                    use covalence_types::Int;
                    PrimResult::IntBig(Int::from(av) + Int::from(bv))
                }
            });
        }
        (IntSub, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            let (av, bv) = (p.to_i64(), q.to_i64());
            return Some(match av.checked_sub(bv) {
                Some(n) => PrimResult::Def(TermDef::int_inline(n)),
                None => {
                    use covalence_types::Int;
                    PrimResult::IntBig(Int::from(av) - Int::from(bv))
                }
            });
        }
        (IntMul, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            let (av, bv) = (p.to_i64(), q.to_i64());
            return Some(match av.checked_mul(bv) {
                Some(n) => PrimResult::Def(TermDef::int_inline(n)),
                None => {
                    use covalence_types::Int;
                    PrimResult::IntBig(Int::from(av) * Int::from(bv))
                }
            });
        }
        (IntEq, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            TermDef::Bool(p.to_i64() == q.to_i64())
        }
        (IntLt, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            TermDef::Bool(p.to_i64() < q.to_i64())
        }
        (IntLe, TermDef::IntInline(p), TermDef::IntInline(q)) => {
            TermDef::Bool(p.to_i64() <= q.to_i64())
        }

        _ => return None,
    };
    Some(PrimResult::Def(def))
}
