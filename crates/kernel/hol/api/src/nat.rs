//! The **`Nat` trait** — a high-level natural-number surface over any HOL
//! backend.
//!
//! A consumer building arithmetic terms and invoking Peano lemmas should do so
//! through this trait rather than applying `nat_add()` to raw `Term`s and
//! naming `covalence_init::init::nat` accessors directly. The trait carries:
//!
//! - the **carrier**: the type of naturals ([`Nat::nat_ty`]);
//! - **term builders**: [`Nat::zero`] / [`Nat::succ`] / [`Nat::lit`] and the
//!   binary ops [`Nat::add`] / [`Nat::mul`];
//! - **theorem accessors**: the workhorse lemmas by name — freeness
//!   ([`Nat::succ_inj`] / [`Nat::zero_ne_succ`]), the recursion equations
//!   ([`Nat::add_base`] / [`Nat::add_step`] / [`Nat::mul_base`] /
//!   [`Nat::mul_step`]), and the algebraic theory ([`Nat::add_zero`] /
//!   [`Nat::add_comm`] / [`Nat::add_assoc`] / [`Nat::add_cancel`] /
//!   [`Nat::mul_zero`] / [`Nat::mul_comm`], …).
//!
//! Only the [`NativeHol`](crate::NativeHol) impl mentions the concrete backend
//! (it delegates to `covalence_init` / `covalence_hol_eval`); a different
//! backend supplies its own `Nat` impl and every consumer written against the
//! trait carries over unchanged.
//!
//! The trait shares [`Hol`]'s error convention (`covalence_core::Result`) — a
//! `Nat` backend is a `Hol` backend that additionally knows the naturals, so it
//! reports failures the same way.

use covalence_core::Result;

use crate::Hol;

/// Natural-number term builders and Peano theorem accessors, over a [`Hol`]
/// backend.
///
/// Term builders return `Result` because typed application can fail on an
/// ill-typed argument (e.g. a non-`nat` term); the theorem accessors return
/// `Result` because the underlying derivations are fallible. Every method is a
/// thin delegation in the concrete impl, so a `Nat`-generic consumer is exactly
/// as trusted as the backend.
pub trait Nat: Hol {
    // -- Carrier --

    /// The type of natural numbers.
    fn nat_ty(&self) -> Self::Type;

    // -- Term builders --

    /// `0 : nat`.
    fn zero(&self) -> Self::Term;
    /// `S n` — the successor of `n`.
    fn succ(&self, n: Self::Term) -> Result<Self::Term>;
    /// The numeral `n : nat` (via the kernel's `nat` literal).
    fn lit(&self, n: u64) -> Self::Term;
    /// `a + b`.
    fn add(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a * b`.
    fn mul(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;

    // -- Freeness --

    /// `⊢ ∀m n. (S m = S n) ⟹ (m = n)` — successor injectivity.
    fn succ_inj(&self) -> Result<Self::Thm>;
    /// `⊢ ∀n. ¬(0 = S n)` — zero is not a successor.
    fn zero_ne_succ(&self) -> Result<Self::Thm>;

    // -- Recursion equations --

    /// `⊢ ∀b. 0 + b = b`.
    fn add_base(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. (S a) + b = S (a + b)`.
    fn add_step(&self) -> Result<Self::Thm>;
    /// `⊢ ∀b. 0 * b = 0`.
    fn mul_base(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. (S a) * b = b + a * b`.
    fn mul_step(&self) -> Result<Self::Thm>;

    // -- Additive theory --

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

    // -- Multiplicative theory --

    /// `⊢ ∀a. a * 0 = 0`.
    fn mul_zero(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. a * S b = a + a * b`.
    fn mul_succ_r(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. a * b = b * a` — commutativity of `*`.
    fn mul_comm(&self) -> Result<Self::Thm>;
}

// ============================================================================
// The native backend
// ============================================================================

use covalence_core::Term;
use covalence_init::init::nat;

/// `Nat` over the native `covalence-core` kernel — each method delegates to a
/// `covalence_init::init::nat` accessor or a fast `covalence-core`/`-eval`
/// constructor. The *only* place in this crate that names the concrete
/// natural-number ops.
impl Nat for crate::NativeHol {
    fn nat_ty(&self) -> Self::Type {
        crate::Type::nat()
    }

    fn zero(&self) -> Term {
        covalence_hol_eval::mk_nat(covalence_types::Nat::zero())
    }
    fn succ(&self, n: Term) -> Result<Term> {
        Hol::app(self, nat::nat_succ(), n)
    }
    fn lit(&self, n: u64) -> Term {
        covalence_hol_eval::mk_nat(covalence_types::Nat::from(n))
    }
    fn add(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, nat::nat_add(), a)?, b)
    }
    fn mul(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, nat::nat_mul(), a)?, b)
    }

    fn succ_inj(&self) -> Result<Self::Thm> {
        Ok(nat::succ_inj())
    }
    fn zero_ne_succ(&self) -> Result<Self::Thm> {
        Ok(nat::zero_ne_succ())
    }

    fn add_base(&self) -> Result<Self::Thm> {
        Ok(nat::add_base())
    }
    fn add_step(&self) -> Result<Self::Thm> {
        Ok(nat::add_step())
    }
    fn mul_base(&self) -> Result<Self::Thm> {
        Ok(nat::mul_base())
    }
    fn mul_step(&self) -> Result<Self::Thm> {
        Ok(nat::mul_step())
    }

    fn add_zero(&self) -> Result<Self::Thm> {
        Ok(nat::add_zero())
    }
    fn add_succ_r(&self) -> Result<Self::Thm> {
        Ok(nat::add_succ_r())
    }
    fn add_comm(&self) -> Result<Self::Thm> {
        Ok(nat::add_comm())
    }
    fn add_assoc(&self) -> Result<Self::Thm> {
        Ok(nat::add_assoc())
    }
    fn add_cancel(&self) -> Result<Self::Thm> {
        Ok(nat::add_cancel())
    }

    fn mul_zero(&self) -> Result<Self::Thm> {
        Ok(nat::mul_zero())
    }
    fn mul_succ_r(&self) -> Result<Self::Thm> {
        Ok(nat::mul_succ_r())
    }
    fn mul_comm(&self) -> Result<Self::Thm> {
        Ok(nat::mul_comm())
    }
}
