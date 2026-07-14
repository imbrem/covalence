//! The [`Builtin`] backend: same trait as [`Symbolic`], but relationships are
//! decided by the kernel's existing `reduce` / `prove_true` CanonRule
//! procedures — the fast path.
//!
//! Where [`Symbolic`] reduces both sides and chains equations by hand,
//! `Builtin` forms the *decision* term (`(=) a b`, `nat.lt a b`) and hands it to
//! `prove_true`, which runs one CanonRule certificate (`LitEqCert`,
//! `NatArithCert`, …) and lands `⊢ a = b` / `⊢ nat.lt a b` directly. It agrees
//! with [`Symbolic`] by construction — both bottom out in the same kernel
//! certificates.

use covalence_hol_eval::defs::nat_lt;
use covalence_hol_eval::{EvalThm, prove_true};
use covalence_init::Term;
use covalence_types::{Decimal, Int, Nat, Rat};

use super::symbolic::{NumeralTerm, Rung, Symbolic};
use crate::lit::{FloatCert32, NumeralBackend};

/// The fast CanonRule-backed kernel backend. See the module docs.
#[derive(Clone, Copy, Debug, Default)]
pub struct Builtin;

impl NumeralBackend for Builtin {
    type Repr = NumeralTerm;
    type Thm = EvalThm;

    // Term construction is identical to `Symbolic` — reuse it.
    fn nat(&self, value: &Nat) -> NumeralTerm {
        Symbolic.nat(value)
    }
    fn int(&self, value: &Int) -> NumeralTerm {
        Symbolic.int(value)
    }
    fn decimal(&self, value: &Decimal) -> NumeralTerm {
        Symbolic.decimal(value)
    }
    fn rat(&self, value: &Rat) -> NumeralTerm {
        Symbolic.rat(value)
    }
    fn f32_bits(&self, bits: u32) -> NumeralTerm {
        Symbolic.f32_bits(bits)
    }

    fn prove_eq(&self, a: &NumeralTerm, b: &NumeralTerm) -> Option<EvalThm> {
        // Decide `(=) a b` by one reduction to `T`. `prove_true` runs the
        // `LitEqCert` on the two literal leaves and concludes `⊢ a = b`.
        let ty = a.term.type_of().ok()?;
        let eq = Term::app(Term::app(Term::eq_op(ty), a.term.clone()), b.term.clone());
        prove_true(&eq).ok()
    }

    fn prove_lt(&self, a: &NumeralTerm, b: &NumeralTerm) -> Option<EvalThm> {
        if a.rung == Rung::Nat && b.rung == Rung::Nat {
            let lt = Term::app(Term::app(nat_lt(), a.term.clone()), b.term.clone());
            return prove_true(&lt).ok();
        }
        None
    }

    fn prove_to_rat(&self, a: &NumeralTerm, r: &NumeralTerm) -> Option<EvalThm> {
        // Same proved decimal-injection lemma as `Symbolic`.
        Symbolic.prove_to_rat(a, r)
    }

    fn ground_f32(&self, value: &Decimal) -> FloatCert32<EvalThm> {
        Symbolic.ground_f32(value)
    }
}
