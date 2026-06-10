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
//! `natAdd`, `natMul`, `natSub` (saturating), `natLe`, and `natLt`
//! carry their selector predicates. The remaining ops (div, mod,
//! pow, the byte/bit ops, the coercions) still default to
//! `tm = None`; landing those predicates follows the same recipe
//! and is a follow-up.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::sigs;
use super::spec::TermSpec;

fn nat_bin_op(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::nat_nat_to_nat()), None)
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

/// `λf. (∀n. f n 0 = n) ∧ (∀n m. f n (succ m) = pred (f n m))`.
/// Saturating subtraction via the kernel's saturating `pred`.
fn nat_sub_predicate() -> Term {
    let f_ty = sigs::nat_nat_to_nat();
    let f = Term::free("f", f_ty.clone());

    let n = Term::free("n", Type::nat());
    let zero = hol::zero();
    let f_n_zero = Term::app(Term::app(f.clone(), n.clone()), zero);
    let base_body = hol::hol_eq(f_n_zero, n.clone());
    let base = hol::hol_forall("n", Type::nat(), base_body);

    let n2 = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());
    let succ_m = Term::app(hol::succ_fn(), m.clone());
    let f_n_succ_m = Term::app(Term::app(f.clone(), n2.clone()), succ_m);
    let f_n_m = Term::app(Term::app(f.clone(), n2.clone()), m.clone());
    let step_rhs = Term::app(hol::pred_fn(), f_n_m);
    let step_body = hol::hol_eq(f_n_succ_m, step_rhs);
    let step_m = hol::hol_forall("m", Type::nat(), step_body);
    let step_n = hol::hol_forall("n", Type::nat(), step_m);

    let body = hol::hol_and(base, step_n);
    hol::pub_abs("f", f_ty, body)
}

/// `natSub : nat → nat → nat` (saturating).
pub fn nat_sub_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatSub,
            Some(sigs::nat_nat_to_nat()),
            Some(nat_sub_predicate()),
        )
    });
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

/// Predicate for a `nat → nat → bool` comparison: three clauses on
/// `cmp(0, m)`, `cmp(succ n, 0)`, `cmp(succ n, succ m) = cmp(n, m)`.
fn nat_cmp_predicate(zero_zero: bool, zero_succ: bool, succ_zero: bool) -> Term {
    let cmp_ty = sigs::nat_nat_to_bool();
    let cmp = Term::free("cmp", cmp_ty.clone());

    // ∀m. cmp 0 m = (case m { 0 => zero_zero; succ _ => zero_succ })
    // Easier: encode two clauses.
    //   cmp 0 0 = zero_zero
    //   ∀m. cmp 0 (succ m) = zero_succ
    //   ∀n. cmp (succ n) 0 = succ_zero
    //   ∀n m. cmp (succ n) (succ m) = cmp n m
    let zero = hol::zero();
    let lit = |b: bool| Term::bool_lit(b);

    let cmp_00 = hol::hol_eq(
        Term::app(Term::app(cmp.clone(), zero.clone()), zero.clone()),
        lit(zero_zero),
    );

    let m = Term::free("m", Type::nat());
    let succ_m = Term::app(hol::succ_fn(), m.clone());
    let cmp_0_succm = hol::hol_eq(
        Term::app(Term::app(cmp.clone(), zero.clone()), succ_m.clone()),
        lit(zero_succ),
    );
    let cmp_0_succ = hol::hol_forall("m", Type::nat(), cmp_0_succm);

    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let cmp_succn_0 = hol::hol_eq(
        Term::app(Term::app(cmp.clone(), succ_n.clone()), zero),
        lit(succ_zero),
    );
    let cmp_succ_0 = hol::hol_forall("n", Type::nat(), cmp_succn_0);

    let n2 = Term::free("n", Type::nat());
    let m2 = Term::free("m", Type::nat());
    let succ_n2 = Term::app(hol::succ_fn(), n2.clone());
    let succ_m2 = Term::app(hol::succ_fn(), m2.clone());
    let cmp_succ_succ = hol::hol_eq(
        Term::app(Term::app(cmp.clone(), succ_n2), succ_m2),
        Term::app(Term::app(cmp.clone(), n2), m2),
    );
    let cmp_ss_m = hol::hol_forall("m", Type::nat(), cmp_succ_succ);
    let cmp_ss = hol::hol_forall("n", Type::nat(), cmp_ss_m);

    let body = hol::hol_and(
        cmp_00,
        hol::hol_and(cmp_0_succ, hol::hol_and(cmp_succ_0, cmp_ss)),
    );
    hol::pub_abs("cmp", cmp_ty, body)
}

/// `natLe : nat → nat → bool`. Selector predicate:
/// `le 0 0 = T`, `∀m. le 0 (S m) = T`, `∀n. le (S n) 0 = F`,
/// `∀n m. le (S n) (S m) = le n m`.
pub fn nat_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatLe,
            Some(sigs::nat_nat_to_bool()),
            Some(nat_cmp_predicate(true, true, false)),
        )
    });
    LAZY.clone()
}
pub fn nat_le() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_le_spec(), vec![]));
    LAZY.clone()
}

/// `natLt : nat → nat → bool`. Selector predicate:
/// `lt 0 0 = F`, `∀m. lt 0 (S m) = T`, `∀n. lt (S n) 0 = F`,
/// `∀n m. lt (S n) (S m) = lt n m`.
pub fn nat_lt_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(
            Canonical::NatLt,
            Some(sigs::nat_nat_to_bool()),
            Some(nat_cmp_predicate(false, true, false)),
        )
    });
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
