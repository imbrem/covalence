//! The derived `nat` arithmetic ops (moved from the core `defs/`
//! catalogue): `natMul`, `natSub`, `natPow`, `natShl`, `natShr`,
//! `natDiv`, `natMod`, the bit ops, the nat<->bytes conversions, and
//! `natToInt`.
//!
//! The `nat` ops the residual TYPE chain needs (`iter`, `natRec`,
//! `natSucc`, `natPred`, `natAdd`, `natLe`, `natLt`) are D3 residue in
//! `covalence_core::defs::nat`.

use covalence_core::hol;
use covalence_core::term::{Term, Type};

use crate::defs::sigs;
use crate::defs::{
    Canonical, cond, int_succ, int_zero, iter, nat_add, nat_lt, nat_rec, nat_succ, or,
};

/// Build a body of the shape `λn m. iter[nat] $n_arg $step_fn $a_arg`
/// where `n_arg` / `a_arg` pick between `n` and `m`, and `step_fn` is
/// the unary function being iterated. (Private twin of the residue
/// helper in `covalence_core::defs::nat`.)
fn iter_binary(iter_count: Either, step_fn: Term, seed: Term) -> Term {
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

/// The explicit **course-of-values** division function — choice-free.
///
/// `natDiv := λn. (B (S n)) n`, where the bounded approximation
/// `B := natRec (λx. λm. 0) (λk g x. F x g)` iterates the division step
/// functional `F n g := λm. cond (m=0 ∨ n<m) 0 (S (g (n−m) m))`. Since `F` reads
/// its history `g` only *below* `n` (when the guard is false, at `n−m < n`), the
/// approximation stabilises and `λx. B (S x) x` is its fixpoint — exactly the cv
/// recursion construction in `covalence_init::init::cv_recursion`. Defining
/// `natDiv` as this term, rather than ε-selecting a function satisfying the
/// Euclidean bounds, keeps the kernel definition foundation-neutral (no Hilbert
/// `ε` beyond the shared `natRec`). The bounds `d·m ≤ n < (d+1)·m` and the
/// recurrence are then **theorems** (`covalence_init::init::nat_div`), and the
/// closed-literal certificate reduction (`n/0 = 0`, else truncating = flooring
/// division) computes the same floor.
fn nat_div_body() -> Term {
    let nat = Type::nat();
    let nn = Type::fun(nat.clone(), nat.clone()); // 'a = nat → nat
    let g_ty = Type::fun(nat.clone(), nn.clone()); // history: nat → (nat → nat)
    let app2 = |f: Term, a: Term, b: Term| Term::app(Term::app(f, a), b);

    // F := λn g m. cond (or (m=0) (n<m)) 0 (succ (g (n−m) m))
    let f_div = {
        let n = Term::free("n", nat.clone());
        let g = Term::free("g", g_ty.clone());
        let m = Term::free("m", nat.clone());
        let guard = app2(
            or(),
            hol::hol_eq(m.clone(), hol::zero()),
            app2(nat_lt(), n.clone(), m.clone()),
        );
        let g_rec = app2(g, app2(nat_sub(), n.clone(), m.clone()), m.clone()); // g (n−m) m
        let s = Term::app(nat_succ(), g_rec); // S (g (n−m) m)
        let body = Term::app(app2(cond(nat.clone()), guard, hol::zero()), s);
        let lm = hol::pub_abs("m", nat.clone(), body);
        let lg = hol::pub_abs("g", g_ty.clone(), lm);
        hol::pub_abs("n", nat.clone(), lg)
    };

    // base := λx. (λm. 0)   (a constant history; the seed is irrelevant)
    let base = hol::pub_abs(
        "x",
        nat.clone(),
        hol::pub_abs("m", nat.clone(), hol::zero()),
    );
    // step := λk g x. F x g   (drops the fuel `k`)
    let step = {
        let f_x_g = app2(
            f_div,
            Term::free("x", nat.clone()),
            Term::free("g", g_ty.clone()),
        );
        let lx = hol::pub_abs("x", nat.clone(), f_x_g);
        let lg = hol::pub_abs("g", g_ty.clone(), lx);
        hol::pub_abs("k", nat.clone(), lg)
    };
    // B := natRec base step
    let b = app2(nat_rec(g_ty.clone()), base, step);

    // λx. (B (S x)) x
    let x = Term::free("x", nat.clone());
    let bsx = app2(b, Term::app(nat_succ(), x.clone()), x.clone());
    hol::pub_abs("x", nat, bsx)
}

let_term! {
    /// `natDiv : nat → nat → nat` — Euclidean (flooring) division, defined by
    /// course-of-values recursion (the explicit, choice-free fixpoint
    /// `nat_div_body`). `n mod m` is `n - (n / m) * m` (see [`nat_mod`]).
    nat_div_spec, nat_div, Canonical::NatDiv, nat_div_body()
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
    let int_succ = int_succ();
    let zero_int = int_zero();
    let iter_at_int = iter(Type::int());
    let body = Term::app(
        Term::app(Term::app(iter_at_int, n.clone()), int_succ),
        zero_int,
    );
    hol::pub_abs("n", Type::nat(), body)
}

let_term! {
    /// `natToInt : nat → int` ≔ `λn. iter[int] n intSucc 0`.
    /// Closed-form reduction continues to work via the
    /// certificate path (ptr_eq dispatch on the spec).
    nat_to_int_spec, nat_to_int, Canonical::NatToInt, nat_to_int_body()
}
