//! Double/successor construction backend for the logic-agnostic Nat API.
//!
//! [`DoubleSuccNat`] deliberately remains a distinct backend from
//! [`NativeHol`](super::hol::NativeHol): natural literals are assembled from
//! `zero`, [`crate::init::nat_binary::double`], and successor instead of the
//! kernel's nonzero `Nat` leaf.
//!
//! This is a representation stress test, not yet full leaf elimination. Both
//! backends currently share the native HOL `Type`, `Term`, theorem, and error
//! carriers; `zero`, arithmetic, order, and the proved Peano laws still lower
//! to today's native theory. A later leaf-elimination backend can replace
//! those carriers and interpretations while consumers generic over the
//! `covalence-logic-api` capabilities remain unchanged.
//!
//! `nat_bits_iso` was also audited for this adapter. Its proved
//! `nat_of_bits ∘ nat_to_bits = id` supplies a useful representation morphism,
//! but it does not yet make `list bool` a standalone Nat backend: arithmetic,
//! order, constructor freeness, and the complete Nat law surface have not been
//! transported to that carrier. This backend therefore uses the proved
//! double/successor term representation and makes no stronger claim.
//!
//! @covalence-api-impl {"api":"A0002","name":"DoubleSuccNat","representation":"logarithmic-depth double/successor terms over native HOL carriers"}

use covalence_core::{Result, Term, Type};
use covalence_kernel_data::numeric::nat::NatSyntax;

use super::nat_backend_common::impl_native_nat_theory;
use crate::init::{nat, nat_binary};

/// Nat terms whose nonzero literals use the binary double/successor encoding.
#[derive(Clone, Copy, Debug, Default)]
pub struct DoubleSuccNat;

impl_native_nat_theory!(DoubleSuccNat);

impl NatSyntax for DoubleSuccNat {
    fn nat_type(&self) -> Type {
        Type::nat()
    }

    fn nat_zero(&self) -> Term {
        nat::zero()
    }

    fn nat_succ(&self, n: Term) -> Result<Term> {
        Ok(Term::app(nat::nat_succ(), n))
    }

    fn nat_literal(&self, n: u64) -> Term {
        fn encode(n: u64) -> Term {
            if n == 0 {
                return nat::zero();
            }
            let prefix = encode(n / 2);
            if n % 2 == 0 {
                nat_binary::bit0(prefix)
            } else {
                nat_binary::bit1(prefix)
            }
        }

        encode(n)
    }
}
