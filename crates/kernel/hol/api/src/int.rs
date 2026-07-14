//! The **`Int` trait** — a high-level integer surface over any HOL backend.
//!
//! The peer of [`Nat`](crate::Nat) for the mathematical integers (`int`, the
//! Grothendieck completion `(nat × nat)/~` built in `covalence_init::init::int`).
//! A consumer that builds linear-arithmetic terms and invokes the ordered-ring
//! lemmas should do so through this trait rather than applying `int_add()` to
//! raw `Term`s and naming `covalence_init::init::int` accessors directly. The
//! trait carries:
//!
//! - the **carrier**: the type of integers ([`Int::int_ty`]);
//! - **term builders**: the literal [`Int::int_lit`] and the operations
//!   [`Int::add`] / [`Int::mul`] / [`Int::neg`] / [`Int::sub`] and the
//!   comparisons [`Int::lt`] / [`Int::le`];
//! - **term destructors**: [`Int::dest_add`] / [`Int::dest_lt`] / … and the
//!   literal recogniser [`Int::as_int_lit`], so a backend-generic reader can
//!   walk an arithmetic atom without knowing the concrete representation;
//! - **theorem accessors**: the ordered-ring workhorse lemmas by name — the ring
//!   axioms, the linear-order lemmas, and the discreteness lemma
//!   [`Int::lt_succ`] (the integer-strengthening fact `a < b ⟺ a + 1 ≤ b`).
//!
//! ## Why abstract the *representation*
//!
//! There is more than one way to model the integers in a proof backend: the
//! native `covalence-core` `int` (a real quotient type, evaluated by the
//! computation-cert TCB) is one; a `succ`/`pred`-tower or a double-and-add
//! numeral encoding is another; a reflected object-level `int` inside internal
//! Peano arithmetic or second-order arithmetic is a third. All of them satisfy
//! the *same* ordered-ring interface. Code written against `Int` — most
//! importantly the linear-arithmetic proof replay in `covalence-kernel-smt` —
//! carries across every one of them; only the trait **impl** changes. That is
//! the whole point of routing SMT (Alethe/cvc5) arithmetic through here.
//!
//! Only the [`NativeHol`](crate::NativeHol) impl mentions the concrete backend
//! (it delegates to `covalence_init::init::int` / `covalence_hol_eval`); it
//! shares [`Hol`]'s error convention (`covalence_core::Result`).

use covalence_core::Result;

use crate::Hol;

/// Integer term builders, destructors, and ordered-ring theorem accessors, over
/// a [`Hol`] backend.
///
/// Term builders that apply an operation return `Result` (typed application can
/// fail on an ill-typed argument); the literal builder and the carrier are
/// infallible. Destructors return `Option` (a shape match). Theorem accessors
/// return `Result` because the underlying derivations are fallible. Every method
/// is a thin delegation in the concrete impl, so an `Int`-generic consumer is
/// exactly as trusted as the backend.
pub trait Int: Hol {
    // -- Carrier --

    /// The type of integers.
    fn int_ty(&self) -> Self::Type;

    // -- Term builders --

    /// The numeral `n : int` (via the kernel's `int` literal; accepts
    /// negatives).
    fn int_lit(&self, n: i128) -> Self::Term;
    /// `a + b`.
    fn add(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a * b`.
    fn mul(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `-a`.
    fn neg(&self, a: Self::Term) -> Result<Self::Term>;
    /// `a - b`.
    fn sub(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a < b` (a `bool`-valued atom).
    fn lt(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a ≤ b` (a `bool`-valued atom).
    fn le(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;

    // -- Term destructors (shape matches; representation-hiding) --

    /// `a + b` → `(a, b)`.
    fn dest_add(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// `a * b` → `(a, b)`.
    fn dest_mul(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// `-a` → `a`.
    fn dest_neg(&self, t: &Self::Term) -> Option<Self::Term>;
    /// `a - b` → `(a, b)`.
    fn dest_sub(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// `a < b` → `(a, b)`.
    fn dest_lt(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// `a ≤ b` → `(a, b)`.
    fn dest_le(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// The integer value of a literal term, if it is one.
    fn as_int_lit(&self, t: &Self::Term) -> Option<i128>;

    // -- Ring axioms --

    /// `⊢ ∀a b. a + b = b + a`.
    fn add_comm(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. (a + b) + c = a + (b + c)`.
    fn add_assoc(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a. a + 0 = a`.
    fn add_zero(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a. a + (-a) = 0`.
    fn add_neg(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. a * b = b * a`.
    fn mul_comm(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. (a * b) * c = a * (b * c)`.
    fn mul_assoc(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a. a * 1 = a`.
    fn mul_one(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a. a * 0 = 0`.
    fn mul_zero(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a * (b + c) = a * b + a * c` — left distributivity.
    fn distrib(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. a - b = a + (-b)`.
    fn sub_def(&self) -> Result<Self::Thm>;

    // -- Linear-order lemmas --

    /// `⊢ ∀a. ¬(a < a)`.
    fn lt_irrefl(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c`.
    fn lt_trans(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. (a < b) ∨ ((a = b) ∨ (b < a))` — trichotomy.
    fn lt_trichotomy(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. (a ≤ b) = (a < b ∨ a = b)`.
    fn le_def(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a < b ⟹ a + c < b + c` — strict additive monotonicity.
    fn lt_add_mono(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. 0 < c ⟹ a < b ⟹ a * c < b * c` — strict positive scaling.
    fn lt_mul_pos(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b. (a < b) = (a + 1 ≤ b)` — discreteness / integer strengthening.
    fn lt_succ(&self) -> Result<Self::Thm>;

    // -- Derived mixed-order chaining (the Farkas replay's kit) --

    /// `⊢ ∀a b. a < b ⟹ a ≤ b`.
    fn lt_imp_le(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a. a ≤ a`.
    fn le_refl(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a ≤ b ⟹ b < c ⟹ a < c`.
    fn lt_of_le_of_lt(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a < b ⟹ b ≤ c ⟹ a < c`.
    fn lt_of_lt_of_le(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c. a ≤ b ⟹ b ≤ c ⟹ a ≤ c`.
    fn le_trans(&self) -> Result<Self::Thm>;
    /// `⊢ ∀a b c d. a < b ⟹ c < d ⟹ a + c < b + d`.
    fn lt_add_lt(&self) -> Result<Self::Thm>;

    /// From `⊢ a < a`, derive falsity `⊢ ⊥` (via `lt_irrefl`). The refutation
    /// closer — kept on the backend so the generic `Hol` surface needn't expose
    /// negation elimination.
    fn absurd_lt(&self, a: Self::Term, lt_aa: Self::Thm) -> Result<Self::Thm>;

    // -- Derived cancellation / positivity --

    /// `⊢ ∀a b. 0 < a ⟹ 0 < b ⟹ 0 < a + b`.
    fn add_pos(&self) -> Result<Self::Thm>;
    /// `⊢ ∀x y k. (x + k < y + k) = (x < y)`.
    fn lt_add_cancel_iff(&self) -> Result<Self::Thm>;
    /// `⊢ ∀x y c. 0 < c ⟹ (x * c < y * c) = (x < y)`.
    fn lt_mul_pos_iff(&self) -> Result<Self::Thm>;
    /// `⊢ ∀x y d. ¬(d = 0) ⟹ x * d = y * d ⟹ x = y` — integral domain.
    fn int_mul_rcancel(&self) -> Result<Self::Thm>;
}

// ============================================================================
// The native backend
// ============================================================================

use covalence_core::Term;
use covalence_hol_eval::defs;
use covalence_init::init::int;

/// `Int` over the native `covalence-core` kernel — each method delegates to a
/// `covalence_init::init::int` accessor or a `covalence-hol-eval` `defs`
/// constructor. The *only* place in this crate that names the concrete integer
/// ops. Destructors match on the canonical `defs` op-spec by pointer identity
/// (`ptr_eq`), the same discipline the linear-arithmetic replay uses.
impl Int for crate::NativeHol {
    fn int_ty(&self) -> Self::Type {
        crate::Type::int()
    }

    fn int_lit(&self, n: i128) -> Term {
        covalence_hol_eval::mk_int(n)
    }
    fn add(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, defs::int_add(), a)?, b)
    }
    fn mul(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, defs::int_mul(), a)?, b)
    }
    fn neg(&self, a: Term) -> Result<Term> {
        Hol::app(self, defs::int_neg(), a)
    }
    fn sub(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, defs::int_sub(), a)?, b)
    }
    fn lt(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, defs::int_lt(), a)?, b)
    }
    fn le(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, defs::int_le(), a)?, b)
    }

    fn dest_add(&self, t: &Term) -> Option<(Term, Term)> {
        dest_binop(t, &defs::int_add())
    }
    fn dest_mul(&self, t: &Term) -> Option<(Term, Term)> {
        dest_binop(t, &defs::int_mul())
    }
    fn dest_sub(&self, t: &Term) -> Option<(Term, Term)> {
        dest_binop(t, &defs::int_sub())
    }
    fn dest_lt(&self, t: &Term) -> Option<(Term, Term)> {
        dest_binop(t, &defs::int_lt())
    }
    fn dest_le(&self, t: &Term) -> Option<(Term, Term)> {
        dest_binop(t, &defs::int_le())
    }
    fn dest_neg(&self, t: &Term) -> Option<Term> {
        dest_unop(t, &defs::int_neg())
    }
    fn as_int_lit(&self, t: &Term) -> Option<i128> {
        let v = covalence_hol_eval::as_int(t)?;
        i128::try_from(&v).ok()
    }

    fn add_comm(&self) -> Result<Self::Thm> {
        Ok(int::add_comm())
    }
    fn add_assoc(&self) -> Result<Self::Thm> {
        Ok(int::add_assoc())
    }
    fn add_zero(&self) -> Result<Self::Thm> {
        Ok(int::add_zero())
    }
    fn add_neg(&self) -> Result<Self::Thm> {
        Ok(int::add_neg())
    }
    fn mul_comm(&self) -> Result<Self::Thm> {
        Ok(int::mul_comm())
    }
    fn mul_assoc(&self) -> Result<Self::Thm> {
        Ok(int::mul_assoc())
    }
    fn mul_one(&self) -> Result<Self::Thm> {
        Ok(int::mul_one())
    }
    fn mul_zero(&self) -> Result<Self::Thm> {
        Ok(int::mul_zero())
    }
    fn distrib(&self) -> Result<Self::Thm> {
        Ok(int::distrib())
    }
    fn sub_def(&self) -> Result<Self::Thm> {
        Ok(int::sub_def())
    }

    fn lt_irrefl(&self) -> Result<Self::Thm> {
        Ok(int::lt_irrefl())
    }
    fn lt_trans(&self) -> Result<Self::Thm> {
        Ok(int::lt_trans())
    }
    fn lt_trichotomy(&self) -> Result<Self::Thm> {
        Ok(int::lt_trichotomy())
    }
    fn le_def(&self) -> Result<Self::Thm> {
        Ok(int::le_def())
    }
    fn lt_add_mono(&self) -> Result<Self::Thm> {
        Ok(int::lt_add_mono())
    }
    fn lt_mul_pos(&self) -> Result<Self::Thm> {
        Ok(int::lt_mul_pos())
    }
    fn lt_succ(&self) -> Result<Self::Thm> {
        Ok(int::lt_succ())
    }

    fn lt_imp_le(&self) -> Result<Self::Thm> {
        Ok(int::lt_imp_le())
    }
    fn le_refl(&self) -> Result<Self::Thm> {
        Ok(int::le_refl())
    }
    fn lt_of_le_of_lt(&self) -> Result<Self::Thm> {
        Ok(int::lt_of_le_of_lt())
    }
    fn lt_of_lt_of_le(&self) -> Result<Self::Thm> {
        Ok(int::lt_of_lt_of_le())
    }
    fn le_trans(&self) -> Result<Self::Thm> {
        Ok(int::le_trans())
    }
    fn lt_add_lt(&self) -> Result<Self::Thm> {
        Ok(int::lt_add_lt())
    }

    fn absurd_lt(&self, a: Term, lt_aa: Self::Thm) -> Result<Self::Thm> {
        use covalence_hol_eval::derived::DerivedRules;
        int::lt_irrefl().all_elim(a)?.not_elim(lt_aa)
    }

    fn add_pos(&self) -> Result<Self::Thm> {
        Ok(int::add_pos())
    }
    fn lt_add_cancel_iff(&self) -> Result<Self::Thm> {
        Ok(int::lt_add_cancel_iff())
    }
    fn lt_mul_pos_iff(&self) -> Result<Self::Thm> {
        Ok(int::lt_mul_pos_iff())
    }
    fn int_mul_rcancel(&self) -> Result<Self::Thm> {
        Ok(int::int_mul_rcancel())
    }
}

/// `App(App(op, a), b)` → `(a, b)` when `t`'s spine head is `op`'s canonical
/// spec (compared by pointer identity).
fn dest_binop(t: &Term, op: &Term) -> Option<(Term, Term)> {
    let (f, b) = t.as_app()?;
    let (head, a) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    let (op_spec, _) = op.as_spec()?;
    spec.ptr_eq(op_spec).then(|| (a.clone(), b.clone()))
}

/// `App(op, a)` → `a` when `t`'s head is `op`'s canonical spec.
fn dest_unop(t: &Term, op: &Term) -> Option<Term> {
    let (head, a) = t.as_app()?;
    let (spec, _) = head.as_spec()?;
    let (op_spec, _) = op.as_spec()?;
    spec.ptr_eq(op_spec).then(|| a.clone())
}
