//! Representation-neutral **linear order** + a **parametric discharger** for
//! closed atoms — the surface an arithmetic proof-replay chains over without
//! committing to a number representation *or* to how closed comparisons get
//! proved.
//!
//! Two independent axes:
//!
//! - [`LinOrder`] — a type carrying `<` / `≤` with the transitivity lemmas and
//!   `lt_irrefl`-style refutation. Any ordered carrier implements it: the native
//!   eval-backed `int`, a `succ`-tower `nat`, an object-level order inside
//!   internal PA/SOA. It is deliberately weaker than [`Int`](crate::Int) (no
//!   ring ops) so non-ring carriers like `nat` qualify.
//! - [`Discharger`] — how a *closed* literal comparison (`5 ≤ 2`, `3 < 3`) is
//!   discharged. The eval backend ([`EvalDischarger`]) computes it through the
//!   `covalence-hol-eval` computation-cert TCB; a `succ`-representation
//!   discharger proves it by pure induction with **no eval-TCB dependency**.
//!   Making this a parameter is the whole point: the same chain replay runs in
//!   the trusted eval kernel and in a from-scratch core representation.

use covalence_core::Result;

use crate::Hol;

/// The strictness of an ordering relation / edge.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Strict {
    /// `<`
    Lt,
    /// `≤`
    Le,
}

impl Strict {
    /// The strictness of a transitive composition: strict if either side is.
    pub fn join(self, other: Strict) -> Strict {
        if self == Strict::Lt || other == Strict::Lt {
            Strict::Lt
        } else {
            Strict::Le
        }
    }

    /// Is `a ⋈ b` arithmetically false for these integer values? (`a ≥ b` for
    /// `<`, `a > b` for `≤`.) The chain-close test.
    pub fn is_false_on(self, a: i128, b: i128) -> bool {
        match self {
            Strict::Lt => a >= b,
            Strict::Le => a > b,
        }
    }
}

/// A carrier with a linear order `<` / `≤` and the chaining lemmas a
/// transitivity-based arithmetic replay needs. Weaker than [`Int`](crate::Int):
/// it asks only for the order, so a non-ring carrier (`nat` as `succ`-towers)
/// qualifies.
pub trait LinOrder: Hol {
    /// `a < b` (a `bool`-valued atom).
    fn lt(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a ≤ b`.
    fn le(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;

    /// `⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c`.
    fn lt_trans(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a ≤ b ⟹ b ≤ c ⟹ a ≤ c`.
    fn le_trans(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a ≤ b ⟹ b < c ⟹ a < c`.
    fn lt_of_le_of_lt(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a < b ⟹ b ≤ c ⟹ a < c`.
    fn lt_of_lt_of_le(&self) -> Result<Self::Thm>;

    /// From `⊢ a < a`, derive falsity `⊢ ⊥` (via `lt_irrefl`).
    fn absurd_lt(&self, a: Self::Term, lt_aa: Self::Thm) -> Result<Self::Thm>;
}

/// The closed-atom oracle: how a *literal* comparison is proved. Swapping this
/// is how a replay moves between the trusted eval kernel and an eval-TCB-free
/// representation. `L` is the order carrier the discharged theorems live in.
pub trait Discharger<L: LinOrder> {
    /// The literal `n` in this discharger's representation of `L`'s carrier.
    fn lit(&self, l: &L, n: i128) -> L::Term;

    /// Given `acc : ⊢ a ⋈ b` where `a`, `b` are literal terms and the relation
    /// is arithmetically **false**, derive `⊢ ⊥`.
    ///
    /// The discharger proves `⊢ ¬(a ⋈ b)` however it can — by computation (eval
    /// TCB) or by pure induction (no eval TCB) — and eliminates it against
    /// `acc`. It must *fail* if `a ⋈ b` is actually true (so a bogus chain can't
    /// mint `⊢ ⊥`).
    fn close(&self, l: &L, a: L::Term, b: L::Term, strict: Strict, acc: L::Thm) -> Result<L::Thm>;
}

// ============================================================================
// Native eval backend: the mathematical `int`, closed comparisons by computation
// ============================================================================

use covalence_core::Term;
use covalence_init::init::int;

/// [`LinOrder`] for the native `int` — the order lemmas are the proved
/// `covalence_init::init::int` theorems (delegated through [`Int`](crate::Int)).
impl LinOrder for crate::NativeHol {
    fn lt(&self, a: Term, b: Term) -> Result<Term> {
        crate::Int::lt(self, a, b)
    }
    fn le(&self, a: Term, b: Term) -> Result<Term> {
        crate::Int::le(self, a, b)
    }
    fn lt_trans(&self) -> Result<Self::Thm> {
        Ok(int::lt_trans())
    }
    fn le_trans(&self) -> Result<Self::Thm> {
        Ok(int::le_trans())
    }
    fn lt_of_le_of_lt(&self) -> Result<Self::Thm> {
        Ok(int::lt_of_le_of_lt())
    }
    fn lt_of_lt_of_le(&self) -> Result<Self::Thm> {
        Ok(int::lt_of_lt_of_le())
    }
    fn absurd_lt(&self, a: Term, lt_aa: Self::Thm) -> Result<Self::Thm> {
        crate::Int::absurd_lt(self, a, lt_aa)
    }
}

/// The **eval-TCB discharger**: closed `int` comparisons are decided by the
/// computation-cert path (`covalence_init::init::logic::decide`, which folds the
/// literal comparison to a boolean through `covalence-hol-eval`'s `IntArithCert`).
/// Fast, but leans on the eval TCB. Contrast a `succ`-representation discharger,
/// which proves the same facts by pure induction.
#[derive(Clone, Copy, Debug, Default)]
pub struct EvalDischarger;

impl Discharger<crate::NativeHol> for EvalDischarger {
    fn lit(&self, l: &crate::NativeHol, n: i128) -> Term {
        crate::Int::int_lit(l, n)
    }

    fn close(
        &self,
        l: &crate::NativeHol,
        a: Term,
        b: Term,
        strict: Strict,
        acc: <crate::NativeHol as Hol>::Thm,
    ) -> Result<<crate::NativeHol as Hol>::Thm> {
        use covalence_hol_eval::derived::DerivedRules;
        let atom = match strict {
            Strict::Lt => crate::Int::lt(l, a, b)?,
            Strict::Le => crate::Int::le(l, a, b)?,
        };
        // `decide` proves `⊢ ¬atom` for a false closed comparison (and `⊢ atom`
        // for a true one — then `not_elim` fails, rejecting a bogus chain).
        let neg = covalence_init::init::logic::decide(&atom)?;
        neg.not_elim(acc)
    }
}
