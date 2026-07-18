//! The [`Wasm`] backend — **SKELETON**.
//!
//! The intended design certifies a *verified WASM evaluation trace*: a numeral
//! relationship (`a = b`, `a < b`, `toRat a = r`) is proved by running a
//! trusted WASM arithmetic component over the literal payloads and admitting its
//! output trace through the same trace-certification path the kernel uses for
//! other executors. It builds the kernel terms (delegating to [`Symbolic`]) so
//! the *representation* is ready; the trace-certified proofs are not wired yet.
//!
//! Deferred: `source-local TODO markers`.

use covalence_hol_eval::EvalThm;
use covalence_types::{Decimal, Int, Nat, Rat};

use super::symbolic::{NumeralTerm, Symbolic};
use crate::lit::{FloatCert32, NumeralBackend};

/// Verified-trace numeral backend (**skeleton** — builds terms, proves nothing
/// yet).
#[derive(Clone, Copy, Debug, Default)]
pub struct Wasm;

impl NumeralBackend for Wasm {
    type Repr = NumeralTerm;
    type Thm = EvalThm;

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

    // SKELETON: trace-certified proofs are not implemented. Never fabricate a
    // theorem — return `None` until the WASM trace path lands.
    fn prove_eq(&self, _a: &NumeralTerm, _b: &NumeralTerm) -> Option<EvalThm> {
        None
    }
    fn prove_lt(&self, _a: &NumeralTerm, _b: &NumeralTerm) -> Option<EvalThm> {
        None
    }
    fn prove_to_rat(&self, _a: &NumeralTerm, _r: &NumeralTerm) -> Option<EvalThm> {
        None
    }
    fn ground_f32(&self, _value: &Decimal) -> FloatCert32<EvalThm> {
        FloatCert32::Unproven
    }
}
