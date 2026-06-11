//! Term-level nat arithmetic / comparison / coercion.
//!
//! `natRec` is defined first as a `def` (ε-style) with the standard
//! primitive-recursor uniqueness predicate as its `tm`. Every other
//! op (`natAdd`, `natMul`, `natSub`, …) is a `let` definition whose
//! body is a direct lambda built from `natRec`. Specifications like
//!
//! ```text
//! ∀n m. natAdd 0 m = m ∧ natAdd (succ n) m = succ (natAdd n m)
//! ```
//!
//! are therefore **theorems** about these definitions, not the
//! definitions themselves — they're provable by `eq_reflection` on
//! the body plus the natRec equations.
//!
//! Ops still defaulting to `tm = None` (`natDiv`, `natMod`, `natPow`,
//! the byte/bit ops, `natToInt`) are awaiting their definitions in
//! follow-up commits.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::sigs;
use super::spec::TermSpec;

// ============================================================================
// Type signatures used here
// ============================================================================

/// `nat → α → α` — the step function expected by `natRec`.
fn nat_alpha_to_alpha(alpha: &Type) -> Type {
    Type::fun(Type::nat(), Type::fun(alpha.clone(), alpha.clone()))
}

/// `α → (nat → α → α) → nat → α` — natRec's full type with `α` free.
fn nat_rec_ty() -> Type {
    let alpha = Type::tfree("a");
    Type::fun(
        alpha.clone(),
        Type::fun(
            nat_alpha_to_alpha(&alpha),
            Type::fun(Type::nat(), alpha),
        ),
    )
}

// ============================================================================
// natRec — primitive recursor
// ============================================================================

/// `λr. ∀z f. r z f 0 = z ∧ ∀n. r z f (succ n) = f n (r z f n)`.
fn nat_rec_predicate() -> Term {
    let alpha = Type::tfree("a");
    let f_ty = nat_alpha_to_alpha(&alpha);
    let r_ty = Type::fun(
        alpha.clone(),
        Type::fun(f_ty.clone(), Type::fun(Type::nat(), alpha.clone())),
    );

    let r = Term::free("r", r_ty.clone());
    let z = Term::free("z", alpha.clone());
    let f = Term::free("f", f_ty.clone());

    // r z f 0 = z
    let r_z_f = Term::app(Term::app(r.clone(), z.clone()), f.clone());
    let r_z_f_0 = Term::app(r_z_f.clone(), hol::zero());
    let base_eq = hol::hol_eq(r_z_f_0, z.clone());

    // ∀n. r z f (succ n) = f n (r z f n)
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(hol::succ_fn(), n.clone());
    let r_z_f_succ_n = Term::app(r_z_f.clone(), succ_n);
    let r_z_f_n = Term::app(r_z_f, n.clone());
    let f_n_rec = Term::app(Term::app(f.clone(), n.clone()), r_z_f_n);
    let step_eq = hol::hol_eq(r_z_f_succ_n, f_n_rec);
    let step = hol::hol_forall("n", Type::nat(), step_eq);

    let body = hol::hol_and(base_eq, step);
    let body_zf = hol::hol_forall("z", alpha, hol::hol_forall("f", f_ty, body));
    hol::pub_abs("r", r_ty, body_zf)
}

poly_def_term! {
    /// `natRec : 'a → (nat → 'a → 'a) → nat → 'a`. The standard
    /// primitive recursor; every nat-typed operation derives from
    /// applying `natRec` at the appropriate `α`.
    nat_rec_spec, nat_rec(alpha), Canonical::NatRec, nat_rec_ty(), nat_rec_predicate()
}

// ============================================================================
// natAdd — let natAdd := λn m. natRec m (λ_ acc. succ acc) n
// ============================================================================

fn nat_add_body() -> Term {
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());

    // step: λ_:nat. λacc:nat. succ acc
    let acc = Term::free("acc", Type::nat());
    let succ_acc = Term::app(hol::succ_fn(), acc);
    let step_inner = hol::pub_abs("acc", Type::nat(), succ_acc);
    let step = hol::pub_abs("_", Type::nat(), step_inner);

    // natRec[nat] m step n
    let rec_at_nat = nat_rec(Type::nat());
    let app1 = Term::app(rec_at_nat, m.clone());
    let app2 = Term::app(app1, step);
    let body = Term::app(app2, n.clone());

    let lam_m = hol::pub_abs("m", Type::nat(), body);
    hol::pub_abs("n", Type::nat(), lam_m)
}

let_term! {
    /// `natAdd : nat → nat → nat`. Defined as
    /// `λn m. natRec m (λ_ acc. succ acc) n` — recurses on the
    /// first argument, threading the second through unchanged.
    nat_add_spec, nat_add, Canonical::NatAdd, nat_add_body()
}

// ============================================================================
// natMul — let natMul := λn m. natRec 0 (λ_ acc. natAdd m acc) n
// ============================================================================

fn nat_mul_body() -> Term {
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());

    // step: λ_:nat. λacc:nat. natAdd m acc
    let acc = Term::free("acc", Type::nat());
    let add_m_acc = Term::app(Term::app(nat_add(), m.clone()), acc);
    let step_inner = hol::pub_abs("acc", Type::nat(), add_m_acc);
    let step = hol::pub_abs("_", Type::nat(), step_inner);

    // natRec[nat] 0 step n
    let rec_at_nat = nat_rec(Type::nat());
    let app1 = Term::app(rec_at_nat, hol::zero());
    let app2 = Term::app(app1, step);
    let body = Term::app(app2, n.clone());

    let lam_m = hol::pub_abs("m", Type::nat(), body);
    hol::pub_abs("n", Type::nat(), lam_m)
}

let_term! {
    /// `natMul : nat → nat → nat`. Defined as
    /// `λn m. natRec 0 (λ_ acc. natAdd m acc) n`.
    nat_mul_spec, nat_mul, Canonical::NatMul, nat_mul_body()
}

// ============================================================================
// natSub — let natSub := λn m. natRec n (λ_ acc. pred acc) m
//
// Recurses on the *second* argument so that saturating-pred kicks in
// the right number of times.
// ============================================================================

fn nat_sub_body() -> Term {
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());

    // step: λ_:nat. λacc:nat. pred acc
    let acc = Term::free("acc", Type::nat());
    let pred_acc = Term::app(hol::pred_fn(), acc);
    let step_inner = hol::pub_abs("acc", Type::nat(), pred_acc);
    let step = hol::pub_abs("_", Type::nat(), step_inner);

    // natRec[nat] n step m
    let rec_at_nat = nat_rec(Type::nat());
    let app1 = Term::app(rec_at_nat, n.clone());
    let app2 = Term::app(app1, step);
    let body = Term::app(app2, m.clone());

    let lam_m = hol::pub_abs("m", Type::nat(), body);
    hol::pub_abs("n", Type::nat(), lam_m)
}

let_term! {
    /// `natSub : nat → nat → nat` (saturating). Defined as
    /// `λn m. natRec n (λ_ acc. pred acc) m`.
    nat_sub_spec, nat_sub, Canonical::NatSub, nat_sub_body()
}

// ============================================================================
// natLe / natLt — selector-predicate definitions (booleans, no clean
// natRec route without if-then-else infrastructure).
// ============================================================================

/// Predicate for a `nat → nat → bool` comparison: four clauses on
/// `cmp(0, 0)`, `cmp(0, S m)`, `cmp(S n, 0)`, `cmp(S n, S m) = cmp(n, m)`.
fn nat_cmp_predicate(zero_zero: bool, zero_succ: bool, succ_zero: bool) -> Term {
    let cmp_ty = sigs::nat_nat_to_bool();
    let cmp = Term::free("cmp", cmp_ty.clone());

    let zero = hol::zero();
    let lit = Term::bool_lit;

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

def_term! {
    /// `natLe : nat → nat → bool`. Selector predicate:
    /// `le 0 0 = T`, `∀m. le 0 (S m) = T`, `∀n. le (S n) 0 = F`,
    /// `∀n m. le (S n) (S m) = le n m`.
    nat_le_spec, nat_le, Canonical::NatLe,
    sigs::nat_nat_to_bool(), nat_cmp_predicate(true, true, false)
}

def_term! {
    /// `natLt : nat → nat → bool`. Selector predicate:
    /// `lt 0 0 = F`, `∀m. lt 0 (S m) = T`, `∀n. lt (S n) 0 = F`,
    /// `∀n m. lt (S n) (S m) = lt n m`.
    nat_lt_spec, nat_lt, Canonical::NatLt,
    sigs::nat_nat_to_bool(), nat_cmp_predicate(false, true, false)
}

// ============================================================================
// Ops still without a definitional body (TODO: land via natRec / Euclidean
// recursion / Hilbert ε on uniqueness):
//
//   natDiv, natMod, natPow, natShl, natShr, natBitAnd, natBitOr, natBitXor,
//   natToBytesLe/Be, natFromBytesLe/Be, natToInt
//
// For now these expose only their type and rely on the
// `builtins::reduce_spec` Rust-side reduction for closed inputs.
// ============================================================================

fn nat_bin_op_spec(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::nat_nat_to_nat()), None)
}

/// `natDiv : nat → nat → nat`.
pub fn nat_div_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op_spec(Canonical::NatDiv));
    LAZY.clone()
}
pub fn nat_div() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_div_spec(), vec![]));
    LAZY.clone()
}

/// `natMod : nat → nat → nat`.
pub fn nat_mod_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op_spec(Canonical::NatMod));
    LAZY.clone()
}
pub fn nat_mod() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_mod_spec(), vec![]));
    LAZY.clone()
}

/// `natPow : nat → nat → nat`.
pub fn nat_pow_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op_spec(Canonical::NatPow));
    LAZY.clone()
}
pub fn nat_pow() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_pow_spec(), vec![]));
    LAZY.clone()
}

/// `natShl : nat → nat → nat`.
pub fn nat_shl_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op_spec(Canonical::NatShl));
    LAZY.clone()
}
pub fn nat_shl() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_shl_spec(), vec![]));
    LAZY.clone()
}

/// `natShr : nat → nat → nat`.
pub fn nat_shr_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op_spec(Canonical::NatShr));
    LAZY.clone()
}
pub fn nat_shr() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_shr_spec(), vec![]));
    LAZY.clone()
}

/// `natBitAnd : nat → nat → nat`.
pub fn nat_bit_and_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op_spec(Canonical::NatBitAnd));
    LAZY.clone()
}
pub fn nat_bit_and() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_and_spec(), vec![]));
    LAZY.clone()
}

/// `natBitOr : nat → nat → nat`.
pub fn nat_bit_or_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op_spec(Canonical::NatBitOr));
    LAZY.clone()
}
pub fn nat_bit_or() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_or_spec(), vec![]));
    LAZY.clone()
}

/// `natBitXor : nat → nat → nat`.
pub fn nat_bit_xor_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| nat_bin_op_spec(Canonical::NatBitXor));
    LAZY.clone()
}
pub fn nat_bit_xor() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(nat_bit_xor_spec(), vec![]));
    LAZY.clone()
}

/// `natToBytesLe : nat → blob`.
pub fn nat_to_bytes_le_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        TermSpec::new(Canonical::NatToBytesLe, Some(sigs::nat_to_bytes()), None)
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
        TermSpec::new(Canonical::NatToBytesBe, Some(sigs::nat_to_bytes()), None)
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
        TermSpec::new(Canonical::NatFromBytesLe, Some(sigs::bytes_to_nat()), None)
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
        TermSpec::new(Canonical::NatFromBytesBe, Some(sigs::bytes_to_nat()), None)
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
