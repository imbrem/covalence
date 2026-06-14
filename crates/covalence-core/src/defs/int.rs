//! `int := (nat × nat) / ~` (Grothendieck construction), plus
//! term-level int arithmetic / comparison / coercion.
//!
//! A pair `(a, b) : nat × nat` represents the integer `a − b`, and
//! `(a, b) ~ (c, d) ⟺ a + d = c + b`. The type is the quotient of
//! `prod nat nat` by that relation; the carrier of the quotient is
//! `(prod nat nat) → bool` (an equivalence class is the *set* of pairs
//! it contains). We bridge class ↔ representative with the spec
//! abstraction/representation coercions:
//!
//! ```text
//!     repPair x ≔ ε(λp. rep x p)            -- some pair in x's class
//!     mkInt p   ≔ abs (λq. p ~ q)           -- the int whose class is [p]
//! ```
//!
//! Each arithmetic op picks representatives, computes on the nat
//! components, and re-quotients — the standard Grothendieck formulas:
//!
//! ```text
//!     succ (a−b) = (a+1) − b          neg (a−b) = b − a
//!     (a−b)+(c−d) = (a+c) − (b+d)     (a−b)−(c−d) = (a+d) − (b+c)
//!     (a−b)·(c−d) = (a·c+b·d) − (a·d+b·c)
//!     (a−b) ≤ (c−d) ⟺ a+d ≤ c+b
//! ```
//!
//! Integer *literals* stay the builtin `TermKind::Int`; closed-form
//! reduction continues to go through `builtins::reduce_spec` (handle
//! `ptr_eq`), independent of these bodies. The bodies make the open
//! ops *provable* (`covalence-hol` derives the defining equations);
//! they do not change reduction.
//!
//! `intDiv`/`intMod` remain declaration-only: Euclidean division on
//! the quotient needs well-founded recursion the kernel does not yet
//! expose. They still reduce on literals (truncating toward zero,
//! `n/0 = n%0 = 0`) via `builtins::reduce_spec`. (TODO — see
//! `docs/roadmap.md`.)

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::cond::cond;
use super::nat::{nat_add, nat_le, nat_mul, nat_succ};
use super::prod::{fst, pair, prod, snd};
use super::sigs;
use super::spec::{TermSpec, TypeSpec};

// ============================================================================
// `int` as a derived TypeSpec — the Grothendieck construction
// ============================================================================

/// `nat × nat` — the representative-pair carrier.
fn nn_pair() -> Type {
    prod(Type::nat(), Type::nat())
}

/// `fst p` at `(nat, nat)`.
fn fst_nn(p: Term) -> Term {
    Term::app(fst(Type::nat(), Type::nat()), p)
}
/// `snd p` at `(nat, nat)`.
fn snd_nn(p: Term) -> Term {
    Term::app(snd(Type::nat(), Type::nat()), p)
}
/// `pair a b : nat × nat`.
fn nn(a: Term, b: Term) -> Term {
    Term::app(Term::app(pair(Type::nat(), Type::nat()), a), b)
}
/// `a + b` on nat.
fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add(), a), b)
}
/// `a * b` on nat.
fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_mul(), a), b)
}

/// `λp q. fst p + snd q = fst q + snd p` — the Grothendieck relation
/// `(a, b) ~ (c, d) ⟺ a + d = c + b`.
fn int_rel() -> Term {
    let pair_ty = nn_pair();
    let p = Term::free("p", pair_ty.clone());
    let q = Term::free("q", pair_ty.clone());
    let lhs = add(fst_nn(p.clone()), snd_nn(q.clone()));
    let rhs = add(fst_nn(q), snd_nn(p));
    let eq = hol::hol_eq(lhs, rhs);
    hol::pub_abs("p", pair_ty.clone(), hol::pub_abs("q", pair_ty, eq))
}

/// `int := (nat × nat) / ~`, where `(a, b)` represents `a − b` and
/// `(a, b) ~ (c, d) ⟺ a + d = c + b`. The type of integer literals
/// (`TermKind::Int`).
pub fn int_ty_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| TypeSpec::quot(Canonical::Int, nn_pair(), int_rel()));
    LAZY.clone()
}

// ----------------------------------------------------------------------------
// class ↔ representative bridge
// ----------------------------------------------------------------------------

/// `λq:nat×nat. fst p + snd q = fst q + snd p` — the equivalence class
/// of the pair term `p` (a subset of `nat × nat`). `p` must be a
/// closed/free pair term; the result is the carrier value `mkInt`
/// abstracts.
fn class_of(p: Term) -> Term {
    let pair_ty = nn_pair();
    let q = Term::free("q", pair_ty.clone());
    let lhs = add(fst_nn(p.clone()), snd_nn(q.clone()));
    let rhs = add(fst_nn(q), snd_nn(p));
    hol::pub_abs("q", pair_ty, hol::hol_eq(lhs, rhs))
}

/// `mkInt p ≔ abs (class_of p)` — the integer whose class is `[p]`.
fn mk_int(p: Term) -> Term {
    let abs = Term::spec_abs(int_ty_spec(), Vec::new());
    Term::app(abs, class_of(p))
}

/// `repPair x ≔ ε(λp:nat×nat. rep x p)` — a representative pair drawn
/// from the class of the int term `x`.
fn rep_pair(x: Term) -> Term {
    let pair_ty = nn_pair();
    let rep = Term::spec_rep(int_ty_spec(), Vec::new());
    let rep_x = Term::app(rep, x); // (nat×nat) → bool
    let p = Term::free("p", pair_ty.clone());
    let pred = hol::pub_abs("p", pair_ty.clone(), Term::app(rep_x, p));
    Term::app(Term::select_op(pair_ty), pred)
}

/// `0 : int` — the canonical integer-zero literal. Reused by
/// `nat_to_int`'s definitional body and downstream proofs.
pub fn int_zero() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::int_lit(covalence_types::Int::zero()));
    LAZY.clone()
}

// ============================================================================
// Unary ops: succ / pred / neg
// ============================================================================

fn unary_int_body(build: impl Fn(Term, Term) -> Term) -> Term {
    // λx:int. mkInt (build a b), where (a, b) = repPair x.
    let x = Term::free("x", Type::int());
    let rp = rep_pair(x.clone());
    let a = fst_nn(rp.clone());
    let b = snd_nn(rp);
    let body = mk_int(build(a, b));
    hol::pub_abs("x", Type::int(), body)
}

fn int_succ_body() -> Term {
    // succ (a − b) = (a + 1) − b
    unary_int_body(|a, b| nn(Term::app(nat_succ(), a), b))
}

let_term! {
    /// `intSucc : int → int` ≡ `λx. mkInt (succ a, b)` where
    /// `(a, b) = repPair x`. Reduces on literals via
    /// `builtins::reduce_spec`.
    int_succ_spec, int_succ, Canonical::IntSucc, int_succ_body()
}

fn int_pred_body() -> Term {
    // pred (a − b) = a − (b + 1)
    unary_int_body(|a, b| nn(a, Term::app(nat_succ(), b)))
}

let_term! {
    /// `intPred : int → int` ≡ `λx. mkInt (a, succ b)`.
    int_pred_spec, int_pred, Canonical::IntPred, int_pred_body()
}

fn int_neg_body() -> Term {
    // neg (a − b) = b − a  (swap the components)
    unary_int_body(|a, b| nn(b, a))
}

let_term! {
    /// `intNeg : int → int` ≡ `λx. mkInt (b, a)`.
    int_neg_spec, int_neg, Canonical::IntNeg, int_neg_body()
}

// ============================================================================
// Binary ops: add / sub / mul
// ============================================================================

/// `λx y:int. mkInt (build ax bx ay by)`, where `(ax, bx) = repPair x`
/// and `(ay, by) = repPair y`.
fn binary_int_body(build: impl Fn(Term, Term, Term, Term) -> Term) -> Term {
    let x = Term::free("x", Type::int());
    let y = Term::free("y", Type::int());
    let px = rep_pair(x.clone());
    let py = rep_pair(y.clone());
    let ax = fst_nn(px.clone());
    let bx = snd_nn(px);
    let ay = fst_nn(py.clone());
    let by = snd_nn(py);
    let body = mk_int(build(ax, bx, ay, by));
    hol::pub_abs("x", Type::int(), hol::pub_abs("y", Type::int(), body))
}

fn int_add_body() -> Term {
    // (a − b) + (c − d) = (a + c) − (b + d)
    binary_int_body(|a, b, c, d| nn(add(a, c), add(b, d)))
}

let_term! {
    /// `intAdd : int → int → int` ≡ Grothendieck addition
    /// `(a+c) − (b+d)`.
    int_add_spec, int_add, Canonical::IntAdd, int_add_body()
}

fn int_sub_body() -> Term {
    // (a − b) − (c − d) = (a + d) − (b + c)
    binary_int_body(|a, b, c, d| nn(add(a, d), add(b, c)))
}

let_term! {
    /// `intSub : int → int → int` ≡ `(a+d) − (b+c)`.
    int_sub_spec, int_sub, Canonical::IntSub, int_sub_body()
}

fn int_mul_body() -> Term {
    // (a − b)·(c − d) = (a·c + b·d) − (a·d + b·c)
    binary_int_body(|a, b, c, d| {
        let pos = add(mul(a.clone(), c.clone()), mul(b.clone(), d.clone()));
        let neg = add(mul(a, d), mul(b, c));
        nn(pos, neg)
    })
}

let_term! {
    /// `intMul : int → int → int` ≡ `(ac+bd) − (ad+bc)`.
    int_mul_spec, int_mul, Canonical::IntMul, int_mul_body()
}

// ============================================================================
// Comparison: le / lt
// ============================================================================

/// `λx y:int. cmp (fst px + snd py) (fst py + snd px)` — lifts a nat
/// comparison through the Grothendieck encoding
/// (`a − b ⋚ c − d ⟺ a + d ⋚ c + b`).
fn int_cmp_body(cmp: Term) -> Term {
    let x = Term::free("x", Type::int());
    let y = Term::free("y", Type::int());
    let px = rep_pair(x.clone());
    let py = rep_pair(y.clone());
    let lhs = add(fst_nn(px.clone()), snd_nn(py.clone())); // a + d
    let rhs = add(fst_nn(py), snd_nn(px)); // c + b
    let body = Term::app(Term::app(cmp, lhs), rhs);
    hol::pub_abs("x", Type::int(), hol::pub_abs("y", Type::int(), body))
}

fn int_le_body() -> Term {
    int_cmp_body(nat_le())
}

let_term! {
    /// `intLe : int → int → bool` ≡ `a + d ≤ c + b`.
    int_le_spec, int_le, Canonical::IntLe, int_le_body()
}

fn int_lt_body() -> Term {
    int_cmp_body(super::nat::nat_lt())
}

let_term! {
    /// `intLt : int → int → bool` ≡ `a + d < c + b`.
    int_lt_spec, int_lt, Canonical::IntLt, int_lt_body()
}

// ============================================================================
// abs / sgn
// ============================================================================

fn int_abs_body() -> Term {
    // |a − b| : nat = if b ≤ a then a − b else b − a
    let x = Term::free("x", Type::int());
    let rp = rep_pair(x.clone());
    let a = fst_nn(rp.clone());
    let b = snd_nn(rp);
    let b_le_a = Term::app(Term::app(nat_le(), b.clone()), a.clone());
    let a_minus_b = Term::app(Term::app(super::nat::nat_sub(), a.clone()), b.clone());
    let b_minus_a = Term::app(Term::app(super::nat::nat_sub(), b), a);
    let body = Term::app(
        Term::app(Term::app(cond(Type::nat()), b_le_a), a_minus_b),
        b_minus_a,
    );
    hol::pub_abs("x", Type::int(), body)
}

let_term! {
    /// `intAbs : int → nat` ≡ `if b ≤ a then a − b else b − a`
    /// where `(a, b) = repPair x`.
    int_abs_spec, int_abs, Canonical::IntAbs, int_abs_body()
}

fn int_sgn_body() -> Term {
    // sgn (a − b) = if a ≤ b then (if b ≤ a then 0 else −1) else 1
    //   a < b → −1 ; a = b → 0 ; a > b → 1
    let x = Term::free("x", Type::int());
    let rp = rep_pair(x.clone());
    let a = fst_nn(rp.clone());
    let b = snd_nn(rp);
    let neg_one = int_neg_lit();
    let zero = int_zero();
    let one = int_one();
    let a_le_b = Term::app(Term::app(nat_le(), a.clone()), b.clone());
    let b_le_a = Term::app(Term::app(nat_le(), b), a);
    // if b ≤ a then 0 else −1   (i.e. a ≤ b branch: a=b ↦ 0, a<b ↦ −1)
    let le_branch = Term::app(
        Term::app(Term::app(cond(Type::int()), b_le_a), zero),
        neg_one,
    );
    let body = Term::app(
        Term::app(Term::app(cond(Type::int()), a_le_b), le_branch),
        one,
    );
    hol::pub_abs("x", Type::int(), body)
}

let_term! {
    /// `intSgn : int → int` ≡ `−1`/`0`/`1` by comparing the
    /// representative components.
    int_sgn_spec, int_sgn, Canonical::IntSgn, int_sgn_body()
}

/// `1 : int` literal helper.
fn int_one() -> Term {
    Term::int_lit(covalence_types::Int::one())
}
/// `−1 : int` literal helper.
fn int_neg_lit() -> Term {
    Term::int_lit(-&covalence_types::Int::one())
}

// ============================================================================
// Euclidean div / mod — declaration-only (reduce on literals only).
// ============================================================================

fn int_bin_op(symbol: Canonical) -> TermSpec {
    TermSpec::new(symbol, Some(sigs::int_int_to_int()), None)
}

/// `intDiv : int → int → int` (Euclidean toward zero, `n/0 = 0`).
/// Declaration-only — reduces on literals via `builtins::reduce_spec`.
pub fn int_div_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_bin_op(Canonical::IntDiv));
    LAZY.clone()
}
pub fn int_div() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_div_spec(), vec![]));
    LAZY.clone()
}

/// `intMod : int → int → int` (Euclidean, `n%0 = 0`).
/// Declaration-only — reduces on literals via `builtins::reduce_spec`.
pub fn int_mod_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| int_bin_op(Canonical::IntMod));
    LAZY.clone()
}
pub fn int_mod() -> Term {
    static LAZY: LazyLock<Term> = LazyLock::new(|| Term::term_spec(int_mod_spec(), vec![]));
    LAZY.clone()
}
