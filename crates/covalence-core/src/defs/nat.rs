//! Term-level nat arithmetic / comparison / coercion.
//!
//! Each binary spec aims to carry a *selector predicate* in its `tm`
//! field — a `(nat → nat → nat) → bool` characterising the operation
//! by the standard recursion equations. Hilbert ε on the predicate
//! picks out the unique solution. See `nat_add_spec` for the
//! prototype shape:
//!
//! ```text
//! natAdd ≔ ε(λf:nat→nat→nat.
//!   (∀m. f 0 m = m) ∧ (∀n m. f (succ n) m = succ (f n m)))
//! ```
//!
//! `natAdd` and `natMul` carry their selector predicates. The rest
//! of the ops still default to `tm = None`; landing the remaining
//! predicates (sub via saturating-pred, the comparison ops, etc.)
//! follows the same recipe and is a follow-up.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::sigs;
use super::spec::TermSpec;

fn nat_bin_op(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::nat_nat_to_nat()), None)
}

fn nat_cmp_op(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::nat_nat_to_bool()), None)
}

/// `f 0 m = m`, `∀m. f 0 m = m`, etc — built around a candidate
/// binary `f`. Returns the predicate
/// `λf. (∀m. f 0 m = m) ∧ (∀n m. f (succ n) m = step (f n m))`.
fn nat_recursion_predicate(step: impl Fn(Term) -> Term) -> Term {
    let f_ty = sigs::nat_nat_to_nat();
    let f = Term::free("f", f_ty.clone());

    let m = Term::free("m", Type::nat());
    let zero = hol::zero();
    let f_zero_m = Term::app(Term::app(f.clone(), zero), m.clone());
    let base_body = hol::hol_eq(f_zero_m, m.clone());
    let base = hol::hol_forall("m", Type::nat(), base_body);

    let n = Term::free("n", Type::nat());
    let m2 = Term::free("m", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let f_succ_n_m = Term::app(Term::app(f.clone(), succ_n), m2.clone());
    let f_n_m = Term::app(Term::app(f.clone(), n.clone()), m2.clone());
    let step_body = hol::hol_eq(f_succ_n_m, step(f_n_m));
    let step_m = hol::hol_forall("m", Type::nat(), step_body);
    let step_n = hol::hol_forall("n", Type::nat(), step_m);

    let body = hol::hol_and(base, step_n);
    hol::pub_abs("f", f_ty, body)
}

/// `λf. (∀m. f 0 m = m) ∧ (∀n m. f (succ n) m = succ (f n m))`.
fn nat_add_predicate() -> Term {
    nat_recursion_predicate(|rec| Term::app(hol::succ_fn(), rec))
}

/// `natAdd : nat → nat → nat`. Selector predicate witnesses the
/// standard primitive-recursion equations for addition.
pub fn nat_add_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatAdd,
            Some(sigs::nat_nat_to_nat()),
            Some(nat_add_predicate()),
        )
    });
    LAZY.clone()
}
pub fn nat_add() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_add_spec(), vec![]));
    LAZY.clone()
}

/// `λf. (∀m. f 0 m = 0) ∧ (∀n m. f (succ n) m = natAdd m (f n m))`.
fn nat_mul_predicate() -> Term {
    let f_ty = sigs::nat_nat_to_nat();
    let f = Term::free("f", f_ty.clone());

    let m = Term::free("m", Type::nat());
    let zero = hol::zero();
    let f_zero_m = Term::app(Term::app(f.clone(), zero.clone()), m.clone());
    let base_body = hol::hol_eq(f_zero_m, zero);
    let base = hol::hol_forall("m", Type::nat(), base_body);

    let n = Term::free("n", Type::nat());
    let m2 = Term::free("m", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let f_succ_n_m = Term::app(Term::app(f.clone(), succ_n), m2.clone());
    let f_n_m = Term::app(Term::app(f.clone(), n), m2.clone());
    // step: add m (f n m). Use nat_add() applied curried.
    let add = nat_add();
    let step_rhs = Term::app(Term::app(add, m2.clone()), f_n_m);
    let step_body = hol::hol_eq(f_succ_n_m, step_rhs);
    let step_m = hol::hol_forall("m", Type::nat(), step_body);
    let step_n = hol::hol_forall("n", Type::nat(), step_m);

    let body = hol::hol_and(base, step_n);
    hol::pub_abs("f", f_ty, body)
}

/// `natMul : nat → nat → nat`. Selector predicate witnesses the
/// usual primitive-recursion equations for multiplication.
pub fn nat_mul_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatMul,
            Some(sigs::nat_nat_to_nat()),
            Some(nat_mul_predicate()),
        )
    });
    LAZY.clone()
}
pub fn nat_mul() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_mul_spec(), vec![]));
    LAZY.clone()
}

/// `natSub : nat → nat → nat` (saturating).
pub fn nat_sub_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatSub));
    LAZY.clone()
}
pub fn nat_sub() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_sub_spec(), vec![]));
    LAZY.clone()
}

/// `natDiv : nat → nat → nat` (Euclidean).
pub fn nat_div_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatDiv));
    LAZY.clone()
}
pub fn nat_div() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_div_spec(), vec![]));
    LAZY.clone()
}

/// `natMod : nat → nat → nat` (Euclidean).
pub fn nat_mod_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatMod));
    LAZY.clone()
}
pub fn nat_mod() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_mod_spec(), vec![]));
    LAZY.clone()
}

/// `natPow : nat → nat → nat`.
pub fn nat_pow_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatPow));
    LAZY.clone()
}
pub fn nat_pow() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_pow_spec(), vec![]));
    LAZY.clone()
}

/// `natLe : nat → nat → bool`.
pub fn nat_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_cmp_op(Canonical::NatLe));
    LAZY.clone()
}
pub fn nat_le() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_le_spec(), vec![]));
    LAZY.clone()
}

/// `natLt : nat → nat → bool`.
pub fn nat_lt_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_cmp_op(Canonical::NatLt));
    LAZY.clone()
}
pub fn nat_lt() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_lt_spec(), vec![]));
    LAZY.clone()
}

/// `natShl : nat → nat → nat` — left shift.
pub fn nat_shl_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatShl));
    LAZY.clone()
}
pub fn nat_shl() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_shl_spec(), vec![]));
    LAZY.clone()
}

/// `natShr : nat → nat → nat` — right shift.
pub fn nat_shr_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatShr));
    LAZY.clone()
}
pub fn nat_shr() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_shr_spec(), vec![]));
    LAZY.clone()
}

/// `natBitAnd : nat → nat → nat`.
pub fn nat_bit_and_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatBitAnd));
    LAZY.clone()
}
pub fn nat_bit_and() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_and_spec(), vec![]));
    LAZY.clone()
}

/// `natBitOr : nat → nat → nat`.
pub fn nat_bit_or_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatBitOr));
    LAZY.clone()
}
pub fn nat_bit_or() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_or_spec(), vec![]));
    LAZY.clone()
}

/// `natBitXor : nat → nat → nat`.
pub fn nat_bit_xor_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op(Canonical::NatBitXor));
    LAZY.clone()
}
pub fn nat_bit_xor() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_xor_spec(), vec![]));
    LAZY.clone()
}

/// `natToBytesLe : nat → blob`.
pub fn nat_to_bytes_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatToBytesLe,
            Some(sigs::nat_to_bytes()),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_to_bytes_le() -> Term {
    static LAZY: LazyLock<Term> =
        LazyLock::new(|| Term::term_spec(nat_to_bytes_le_spec(), vec![]));
    LAZY.clone()
}

/// `natToBytesBe : nat → blob`.
pub fn nat_to_bytes_be_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatToBytesBe,
            Some(sigs::nat_to_bytes()),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_to_bytes_be() -> Term {
    static LAZY: LazyLock<Term> =
        LazyLock::new(|| Term::term_spec(nat_to_bytes_be_spec(), vec![]));
    LAZY.clone()
}

/// `natFromBytesLe : blob → nat`.
pub fn nat_from_bytes_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatFromBytesLe,
            Some(sigs::bytes_to_nat()),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_from_bytes_le() -> Term {
    static LAZY: LazyLock<Term> =
        LazyLock::new(|| Term::term_spec(nat_from_bytes_le_spec(), vec![]));
    LAZY.clone()
}

/// `natFromBytesBe : blob → nat`.
pub fn nat_from_bytes_be_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatFromBytesBe,
            Some(sigs::bytes_to_nat()),
            None,
        )
    });
    LAZY.clone()
}
pub fn nat_from_bytes_be() -> Term {
    static LAZY: LazyLock<Term> =
        LazyLock::new(|| Term::term_spec(nat_from_bytes_be_spec(), vec![]));
    LAZY.clone()
}

/// `natToInt : nat → int`.
pub fn nat_to_int_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(Canonical::NatToInt, Some(sigs::nat_to_int()), None)
    });
    LAZY.clone()
}
pub fn nat_to_int() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_to_int_spec(), vec![]));
    LAZY.clone()
}
