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

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::sigs;

// ============================================================================
// natSucc / natPred — TermSpec constants. No body; `builtins::reduce_spec`
// matches on them to evaluate closed-form applications.
// ============================================================================

term_decl! {
    /// `natSucc : nat → nat` — the constructor. Reduces on literals via
    /// `builtins::reduce_spec`.
    nat_succ_spec, nat_succ, Canonical::NatSucc, sigs::nat_to_nat()
}

term_decl! {
    /// `natPred : nat → nat` — saturating predecessor (`pred 0 = 0`).
    nat_pred_spec, nat_pred, Canonical::NatPred, sigs::nat_to_nat()
}

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

poly_spec_term! {
    /// `natRec : 'a → (nat → 'a → 'a) → nat → 'a`. The standard
    /// primitive recursor; every nat-typed operation derives from
    /// applying `natRec` at the appropriate `α`.
    nat_rec_spec, nat_rec(alpha), Canonical::NatRec, nat_rec_ty(), nat_rec_predicate()
}

// ============================================================================
// iter — n-fold function iteration.
//
// iter n f a ≔ natRec a (λ_:nat. f) n
//
// Equations (provable from the definition + natRec equations):
//   iter 0     f a = a
//   iter (S n) f a = f (iter n f a)
//
// Useful corollary (provable by induction on n):
//   iter (S n) f a = iter n f (f a)
//
// Every binary nat op below (add/mul/sub/pow/shl/shr) factors through
// iter: each step ignores `n`, so iter is the more idiomatic choice
// than the full natRec.
// ============================================================================

fn iter_body() -> Term {
    let alpha = Type::tfree("a");
    let alpha_to_alpha = Type::fun(alpha.clone(), alpha.clone());

    let n = Term::free("n", Type::nat());
    let f = Term::free("f", alpha_to_alpha.clone());
    let a = Term::free("a", alpha.clone());

    // step: λ_:nat. f
    let step = hol::pub_abs("_", Type::nat(), f.clone());

    let rec_at_alpha = nat_rec(alpha.clone());
    let app1 = Term::app(rec_at_alpha, a.clone());
    let app2 = Term::app(app1, step);
    let body = Term::app(app2, n.clone());

    let lam_a = hol::pub_abs("a", alpha.clone(), body);
    let lam_f = hol::pub_abs("f", alpha_to_alpha, lam_a);
    hol::pub_abs("n", Type::nat(), lam_f)
}

poly_let_term! {
    /// `iter : nat → ('a → 'a) → 'a → 'a`. Defined as
    /// `λn f a. natRec a (λ_. f) n`. Equations: `iter 0 f a = a`,
    /// `iter (S n) f a = f (iter n f a)`. Corollary:
    /// `iter (S n) f a = iter n f (f a)`.
    iter_spec, iter(alpha), Canonical::Iter, iter_body()
}

/// Build a body of the shape `λn m. iter[nat] $n_arg $step_fn $a_arg`
/// where `n_arg` / `a_arg` pick between `n` and `m`, and `step_fn` is
/// the unary function being iterated. Used to keep the
/// `natAdd`/`natMul`/`natSub`/etc. definitions one-liners.
fn iter_binary(
    iter_count: Either,
    step_fn: Term,
    seed: Term,
) -> Term {
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());

    let count = match iter_count {
        Either::N => n.clone(),
        Either::M => m.clone(),
    };

    let app1 = Term::app(iter(Type::nat()), count);
    let app2 = Term::app(app1, step_fn);
    let body = Term::app(app2, seed);

    let lam_m = hol::pub_abs("m", Type::nat(), body);
    hol::pub_abs("n", Type::nat(), lam_m)
}

/// Which of the two outer parameters threads through as the iter
/// count (n) vs the seed (a).
#[derive(Clone, Copy)]
enum Either {
    N,
    M,
}

fn nat_add_body() -> Term {
    // natAdd n m ≔ iter n succ m
    iter_binary(Either::N, hol::succ_fn(), Term::free("m", Type::nat()))
}

let_term! {
    /// `natAdd : nat → nat → nat` ≡ `λn m. iter n succ m`.
    /// Equations: `natAdd 0 m = m`, `natAdd (S n) m = S (natAdd n m)`.
    nat_add_spec, nat_add, Canonical::NatAdd, nat_add_body()
}

fn nat_mul_body() -> Term {
    // natMul n m ≔ iter n (λx. natAdd m x) 0
    let x = Term::free("x", Type::nat());
    let m = Term::free("m", Type::nat());
    let add_m_x = Term::app(Term::app(nat_add(), m), x);
    let step = hol::pub_abs("x", Type::nat(), add_m_x);
    iter_binary(Either::N, step, hol::zero())
}

let_term! {
    /// `natMul : nat → nat → nat` ≡ `λn m. iter n (λx. natAdd m x) 0`.
    /// Equations: `natMul 0 m = 0`, `natMul (S n) m = natAdd m (natMul n m)`.
    nat_mul_spec, nat_mul, Canonical::NatMul, nat_mul_body()
}

fn nat_sub_body() -> Term {
    // natSub n m ≔ iter m pred n
    iter_binary(Either::M, hol::pred_fn(), Term::free("n", Type::nat()))
}

let_term! {
    /// `natSub : nat → nat → nat` (saturating) ≡ `λn m. iter m pred n`.
    /// Equations: `natSub n 0 = n`, `natSub n (S m) = pred (natSub n m)`.
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

spec_term! {
    /// `natLe : nat → nat → bool`. Selector predicate:
    /// `le 0 0 = T`, `∀m. le 0 (S m) = T`, `∀n. le (S n) 0 = F`,
    /// `∀n m. le (S n) (S m) = le n m`.
    nat_le_spec, nat_le, Canonical::NatLe,
    sigs::nat_nat_to_bool(), nat_cmp_predicate(true, true, false)
}

spec_term! {
    /// `natLt : nat → nat → bool`. Selector predicate:
    /// `lt 0 0 = F`, `∀m. lt 0 (S m) = T`, `∀n. lt (S n) 0 = F`,
    /// `∀n m. lt (S n) (S m) = lt n m`.
    nat_lt_spec, nat_lt, Canonical::NatLt,
    sigs::nat_nat_to_bool(), nat_cmp_predicate(false, true, false)
}

// ============================================================================
// natPow / natShl / natShr — all factor through iter on the second arg.
// ============================================================================

fn one() -> Term {
    Term::app(hol::succ_fn(), hol::zero())
}

fn two() -> Term {
    Term::app(hol::succ_fn(), one())
}

fn nat_pow_body() -> Term {
    // natPow n m ≔ iter m (λx. natMul n x) 1
    let x = Term::free("x", Type::nat());
    let n = Term::free("n", Type::nat());
    let mul_n_x = Term::app(Term::app(nat_mul(), n), x);
    let step = hol::pub_abs("x", Type::nat(), mul_n_x);
    iter_binary(Either::M, step, one())
}

let_term! {
    /// `natPow : nat → nat → nat` ≡ `λn m. iter m (λx. natMul n x) 1`.
    /// Equations: `natPow n 0 = 1`, `natPow n (S m) = natMul n (natPow n m)`.
    nat_pow_spec, nat_pow, Canonical::NatPow, nat_pow_body()
}

fn nat_shl_body() -> Term {
    // natShl n m ≔ iter m (λx. natMul 2 x) n
    let x = Term::free("x", Type::nat());
    let mul_2_x = Term::app(Term::app(nat_mul(), two()), x);
    let step = hol::pub_abs("x", Type::nat(), mul_2_x);
    iter_binary(Either::M, step, Term::free("n", Type::nat()))
}

let_term! {
    /// `natShl : nat → nat → nat` ≡ `λn m. iter m (λx. natMul 2 x) n`.
    nat_shl_spec, nat_shl, Canonical::NatShl, nat_shl_body()
}

fn nat_shr_body() -> Term {
    // natShr n m ≔ iter m (λx. natDiv x 2) n
    let x = Term::free("x", Type::nat());
    let div_x_2 = Term::app(Term::app(nat_div(), x), two());
    let step = hol::pub_abs("x", Type::nat(), div_x_2);
    iter_binary(Either::M, step, Term::free("n", Type::nat()))
}

let_term! {
    /// `natShr : nat → nat → nat` ≡ `λn m. iter m (λx. natDiv x 2) n`.
    /// (Well-typed even though `natDiv` is still a declaration; the
    /// kernel will use it once natDiv has a body.)
    nat_shr_spec, nat_shr, Canonical::NatShr, nat_shr_body()
}

// ============================================================================
// Ops still without a definitional body (TODO: land via natRec / Euclidean
// recursion / Hilbert ε on uniqueness):
//
//   natDiv, natMod (Euclidean — predicate-style ε needed),
//   natBitAnd, natBitOr, natBitXor (bit-level recursion),
//   natToBytesLe/Be, natFromBytesLe/Be, natToInt
// ============================================================================

term_decl! {
    /// `natDiv : nat → nat → nat`.
    nat_div_spec, nat_div, Canonical::NatDiv, sigs::nat_nat_to_nat()
}

fn nat_mod_body() -> Term {
    // natMod n m ≔ n - (n / m) * m
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());
    let div_nm = Term::app(Term::app(nat_div(), n.clone()), m.clone());
    let mul = Term::app(Term::app(nat_mul(), div_nm), m.clone());
    let sub = Term::app(Term::app(nat_sub(), n.clone()), mul);
    let lam_m = hol::pub_abs("m", Type::nat(), sub);
    hol::pub_abs("n", Type::nat(), lam_m)
}

let_term! {
    /// `natMod : nat → nat → nat`, defined as
    /// `λn m. nat_sub n (nat_mul (nat_div n m) m)`. Standard
    /// Euclidean remainder by composition.
    nat_mod_spec, nat_mod, Canonical::NatMod, nat_mod_body()
}

term_decl! {
    /// `natBitAnd : nat → nat → nat`.
    nat_bit_and_spec, nat_bit_and, Canonical::NatBitAnd, sigs::nat_nat_to_nat()
}

term_decl! {
    /// `natBitOr : nat → nat → nat`.
    nat_bit_or_spec, nat_bit_or, Canonical::NatBitOr, sigs::nat_nat_to_nat()
}

term_decl! {
    /// `natBitXor : nat → nat → nat`.
    nat_bit_xor_spec, nat_bit_xor, Canonical::NatBitXor, sigs::nat_nat_to_nat()
}

term_decl! {
    /// `natToBytesLe : nat → blob`.
    nat_to_bytes_le_spec, nat_to_bytes_le, Canonical::NatToBytesLe, sigs::nat_to_bytes()
}

term_decl! {
    /// `natToBytesBe : nat → blob`.
    nat_to_bytes_be_spec, nat_to_bytes_be, Canonical::NatToBytesBe, sigs::nat_to_bytes()
}

term_decl! {
    /// `natFromBytesLe : blob → nat`.
    nat_from_bytes_le_spec, nat_from_bytes_le, Canonical::NatFromBytesLe, sigs::bytes_to_nat()
}

term_decl! {
    /// `natFromBytesBe : blob → nat`.
    nat_from_bytes_be_spec, nat_from_bytes_be, Canonical::NatFromBytesBe, sigs::bytes_to_nat()
}

fn nat_to_int_body() -> Term {
    // λn:nat. iter[int] n int_succ 0_int
    let n = Term::free("n", Type::nat());
    let int_succ = super::int::int_succ();
    let zero_int = super::int::int_zero();
    let iter_at_int = iter(Type::int());
    let body = Term::app(Term::app(Term::app(iter_at_int, n.clone()), int_succ), zero_int);
    hol::pub_abs("n", Type::nat(), body)
}

let_term! {
    /// `natToInt : nat → int` ≔ `λn. iter[int] n intSucc 0`.
    /// Closed-form reduction continues to work via
    /// `builtins::reduce_spec` (ptr_eq dispatch on the spec).
    nat_to_int_spec, nat_to_int, Canonical::NatToInt, nat_to_int_body()
}
