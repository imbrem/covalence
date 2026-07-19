//! Capability traits for natural numbers over any HOL backend.
//!
//! Consumers should ask only for the capabilities they use:
//!
//! - [`NatSyntax`] owns the carrier, zero, successor, and literals;
//! - [`NatArithmetic`] builds addition and multiplication, while [`NatOrder`]
//!   builds comparisons;
//! - [`NatFreeness`], [`NatRecursionLaws`], [`NatAdditiveLaws`], and
//!   [`NatMultiplicativeLaws`] expose independently implementable laws;
//! - [`NatEqDecision`] and [`NatNormalization`] are optional accelerators.
//!
//! [`Nat`] remains as a compatibility umbrella over the complete constructive
//! and law surface. New generic code should prefer the narrow traits. Optional
//! capabilities are deliberately not part of [`Nat`]: a backend advertises
//! them by implementing the corresponding trait, with no runtime
//! “not implemented” result.

use covalence_core::Result;
use covalence_logic_api::nat as logic_nat;

use crate::Hol;

/// The natural-number carrier and its primitive constructors.
///
/// Compatibility adapter for the dependency-free
/// [`logic_nat::NatSyntax`] capability. New logic-generic consumers should use
/// that trait directly.
pub trait NatSyntax: Hol {
    /// The type of natural numbers.
    fn nat_ty(&self) -> Self::Type;
    /// `0 : nat`.
    fn zero(&self) -> Self::Term;
    /// `S n` — the successor of `n`.
    fn succ(&self, n: Self::Term) -> Result<Self::Term>;
    /// The numeral `n : nat` (via the kernel's `nat` literal).
    fn lit(&self, n: u64) -> Self::Term;
}

/// Natural-number arithmetic term constructors.
pub trait NatArithmetic: NatSyntax {
    /// `a + b`.
    fn add(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a * b`.
    fn mul(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
}

/// Natural-number order term constructors.
pub trait NatOrder: NatSyntax {
    /// `a < b`.
    fn lt(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a ≤ b`.
    fn le(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
}

/// Freeness of zero and successor.
pub trait NatFreeness: NatSyntax {
    /// `⊢ ∀m n. (S m = S n) ⟹ (m = n)` — successor injectivity.
    fn succ_inj(&self) -> Result<Self::Thm>;
    /// `⊢ ∀n. ¬(0 = S n)` — zero is not a successor.
    fn zero_ne_succ(&self) -> Result<Self::Thm>;
}

/// Defining recursion equations for arithmetic.
pub trait NatRecursionLaws: NatArithmetic {
    /// `⊢ ∀b. 0 + b = b`.
    fn add_base(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. (S a) + b = S (a + b)`.
    fn add_step(&self) -> Result<Self::Thm>;
    /// `⊢ ∀b. 0 * b = 0`.
    fn mul_base(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. (S a) * b = b + a * b`.
    fn mul_step(&self) -> Result<Self::Thm>;
}

/// Derived additive laws.
pub trait NatAdditiveLaws: NatArithmetic {
    /// `⊢ ∀a. a + 0 = a`.
    fn add_zero(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. a + S b = S (a + b)`.
    fn add_succ_r(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. a + b = b + a` — commutativity of `+`.
    fn add_comm(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. (a + b) + c = a + (b + c)` — associativity of `+`.
    fn add_assoc(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. (a + c = b + c) ⟹ (a = b)` — right cancellation.
    fn add_cancel(&self) -> Result<Self::Thm>;
}

/// Derived multiplicative laws.
pub trait NatMultiplicativeLaws: NatArithmetic {
    /// `⊢ ∀a. a * 0 = 0`.
    fn mul_zero(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. a * S b = a + a * b`.
    fn mul_succ_r(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. a * b = b * a` — commutativity of `*`.
    fn mul_comm(&self) -> Result<Self::Thm>;
}

/// The complete law package currently supplied by the native backend.
pub trait NatLaws:
    NatFreeness + NatRecursionLaws + NatAdditiveLaws + NatMultiplicativeLaws
{
}

impl<T> NatLaws for T where
    T: NatFreeness + NatRecursionLaws + NatAdditiveLaws + NatMultiplicativeLaws
{
}

/// Compatibility facade for consumers that use the entire natural-number API.
///
/// Its methods preserve the original `Nat::lit(backend, n)` UFCS surface.
/// Implementors should implement the narrow capabilities instead; this trait
/// is supplied automatically.
pub trait Nat: Hol {
    fn nat_ty(&self) -> Self::Type;
    fn zero(&self) -> Self::Term;
    fn succ(&self, n: Self::Term) -> Result<Self::Term>;
    fn lit(&self, n: u64) -> Self::Term;
    fn add(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    fn mul(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    fn succ_inj(&self) -> Result<Self::Thm>;
    fn zero_ne_succ(&self) -> Result<Self::Thm>;
    fn add_base(&self) -> Result<Self::Thm>;
    fn add_step(&self) -> Result<Self::Thm>;
    fn mul_base(&self) -> Result<Self::Thm>;
    fn mul_step(&self) -> Result<Self::Thm>;
    fn add_zero(&self) -> Result<Self::Thm>;
    fn add_succ_r(&self) -> Result<Self::Thm>;
    fn add_comm(&self) -> Result<Self::Thm>;
    fn add_assoc(&self) -> Result<Self::Thm>;
    fn add_cancel(&self) -> Result<Self::Thm>;
    fn mul_zero(&self) -> Result<Self::Thm>;
    fn mul_succ_r(&self) -> Result<Self::Thm>;
    fn mul_comm(&self) -> Result<Self::Thm>;
}

impl<T> Nat for T
where
    T: NatArithmetic + NatLaws,
{
    fn nat_ty(&self) -> Self::Type {
        NatSyntax::nat_ty(self)
    }
    fn zero(&self) -> Self::Term {
        NatSyntax::zero(self)
    }
    fn succ(&self, n: Self::Term) -> Result<Self::Term> {
        NatSyntax::succ(self, n)
    }
    fn lit(&self, n: u64) -> Self::Term {
        NatSyntax::lit(self, n)
    }
    fn add(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term> {
        NatArithmetic::add(self, a, b)
    }
    fn mul(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term> {
        NatArithmetic::mul(self, a, b)
    }
    fn succ_inj(&self) -> Result<Self::Thm> {
        NatFreeness::succ_inj(self)
    }
    fn zero_ne_succ(&self) -> Result<Self::Thm> {
        NatFreeness::zero_ne_succ(self)
    }
    fn add_base(&self) -> Result<Self::Thm> {
        NatRecursionLaws::add_base(self)
    }
    fn add_step(&self) -> Result<Self::Thm> {
        NatRecursionLaws::add_step(self)
    }
    fn mul_base(&self) -> Result<Self::Thm> {
        NatRecursionLaws::mul_base(self)
    }
    fn mul_step(&self) -> Result<Self::Thm> {
        NatRecursionLaws::mul_step(self)
    }
    fn add_zero(&self) -> Result<Self::Thm> {
        NatAdditiveLaws::add_zero(self)
    }
    fn add_succ_r(&self) -> Result<Self::Thm> {
        NatAdditiveLaws::add_succ_r(self)
    }
    fn add_comm(&self) -> Result<Self::Thm> {
        NatAdditiveLaws::add_comm(self)
    }
    fn add_assoc(&self) -> Result<Self::Thm> {
        NatAdditiveLaws::add_assoc(self)
    }
    fn add_cancel(&self) -> Result<Self::Thm> {
        NatAdditiveLaws::add_cancel(self)
    }
    fn mul_zero(&self) -> Result<Self::Thm> {
        NatMultiplicativeLaws::mul_zero(self)
    }
    fn mul_succ_r(&self) -> Result<Self::Thm> {
        NatMultiplicativeLaws::mul_succ_r(self)
    }
    fn mul_comm(&self) -> Result<Self::Thm> {
        NatMultiplicativeLaws::mul_comm(self)
    }
}

/// Optional capability for deciding equality of closed natural-number terms.
///
/// The returned theorem concludes either `a = b` or `¬(a = b)`. Backends that
/// cannot decide their representation simply do not implement this trait.
pub trait NatEqDecision: NatSyntax {
    fn decide_nat_eq(&self, a: Self::Term, b: Self::Term) -> Result<Self::Thm>;
}

/// Optional capability for accelerating normalization of a closed natural
/// term. The result proves `term = n` for a numeral `n`.
pub trait NatNormalization: NatSyntax {
    fn normalize_nat(&self, term: Self::Term) -> Result<Self::Thm>;
}

// The concrete-HOL API remains source-compatible while forwarding every
// operation to the dependency-free capability surface implemented by
// `covalence-init`, which owns `NativeHol`.
impl NatSyntax for crate::NativeHol {
    fn nat_ty(&self) -> Self::Type {
        logic_nat::NatSyntax::nat_type(self)
    }
    fn zero(&self) -> Self::Term {
        logic_nat::NatSyntax::nat_zero(self)
    }
    fn succ(&self, n: Self::Term) -> Result<Self::Term> {
        logic_nat::NatSyntax::nat_succ(self, n)
    }
    fn lit(&self, n: u64) -> Self::Term {
        logic_nat::NatSyntax::nat_literal(self, n)
    }
}

impl NatArithmetic for crate::NativeHol {
    fn add(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term> {
        logic_nat::NatArithmetic::nat_add(self, a, b)
    }
    fn mul(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term> {
        logic_nat::NatArithmetic::nat_multiply(self, a, b)
    }
}

impl NatOrder for crate::NativeHol {
    fn lt(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term> {
        logic_nat::NatOrder::nat_less_than(self, a, b)
    }
    fn le(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term> {
        logic_nat::NatOrder::nat_less_equal(self, a, b)
    }
}

impl NatFreeness for crate::NativeHol {
    fn succ_inj(&self) -> Result<Self::Thm> {
        logic_nat::NatFreeness::nat_successor_injective(self)
    }
    fn zero_ne_succ(&self) -> Result<Self::Thm> {
        logic_nat::NatFreeness::nat_zero_not_successor(self)
    }
}

impl NatRecursionLaws for crate::NativeHol {
    fn add_base(&self) -> Result<Self::Thm> {
        logic_nat::NatRecursionLaws::nat_add_base(self)
    }
    fn add_step(&self) -> Result<Self::Thm> {
        logic_nat::NatRecursionLaws::nat_add_step(self)
    }
    fn mul_base(&self) -> Result<Self::Thm> {
        logic_nat::NatRecursionLaws::nat_multiply_base(self)
    }
    fn mul_step(&self) -> Result<Self::Thm> {
        logic_nat::NatRecursionLaws::nat_multiply_step(self)
    }
}

impl NatAdditiveLaws for crate::NativeHol {
    fn add_zero(&self) -> Result<Self::Thm> {
        logic_nat::NatAdditiveLaws::nat_add_zero(self)
    }
    fn add_succ_r(&self) -> Result<Self::Thm> {
        logic_nat::NatAdditiveLaws::nat_add_successor_right(self)
    }
    fn add_comm(&self) -> Result<Self::Thm> {
        logic_nat::NatAdditiveLaws::nat_add_commutative(self)
    }
    fn add_assoc(&self) -> Result<Self::Thm> {
        logic_nat::NatAdditiveLaws::nat_add_associative(self)
    }
    fn add_cancel(&self) -> Result<Self::Thm> {
        logic_nat::NatAdditiveLaws::nat_add_cancel_right(self)
    }
}

impl NatMultiplicativeLaws for crate::NativeHol {
    fn mul_zero(&self) -> Result<Self::Thm> {
        logic_nat::NatMultiplicativeLaws::nat_multiply_zero(self)
    }
    fn mul_succ_r(&self) -> Result<Self::Thm> {
        logic_nat::NatMultiplicativeLaws::nat_multiply_successor_right(self)
    }
    fn mul_comm(&self) -> Result<Self::Thm> {
        logic_nat::NatMultiplicativeLaws::nat_multiply_commutative(self)
    }
}
