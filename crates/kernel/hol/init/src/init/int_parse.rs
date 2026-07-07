//! `int_parse` — **signed integer parsing** (stage NP3): an optional sign
//! (`'-'` / `'+'`) followed by a decimal `nat`, lifted to `int`.
//!
//! [`parse_int`] `: string → option (int × string)` reads an optional leading
//! sign character and then a maximal decimal-digit prefix (via NP2's
//! [`crate::init::nat_parse::parse_nat_dec`]), lifting the parsed `nat` to an
//! `int`:
//!
//! - `'-'` ↦ `int_neg (nat_to_int n)` (negative),
//! - `'+'` or no sign ↦ `nat_to_int n` (positive).
//!
//! It returns `some (value, remaining-suffix)` when the digit run after the
//! (optional) sign is non-empty, else `none`. `nat_to_int : nat → int` is the
//! `iter[int] n intSucc 0` embedding and `int_neg` the ring negation, so the
//! whole thing reduces to an `int` literal on concrete input.
//!
//! ## What is proved
//!
//! The **sign-lift** lemmas ([`lift_pos_some`] / [`lift_neg_some`] /
//! [`lift_none`]) discharge exactly how a `nat`-parse result maps to the
//! signed `int` result — the sign-correctness contract: a `some (n, suf)`
//! result becomes `nat_to_int n` (positive) or `int_neg (nat_to_int n)`
//! (negative), and a `none` stays `none`.
//!
//! The **end-to-end sign selection** (which leading character fires which
//! branch, chained with these lift lemmas) is deferred — it resolves two
//! nested `cond`s whose branches contain redexes, and `cond_true`'s internal
//! `reduce` ε-ifies an inner `cond`; the fix (reduce-the-whole-application-
//! first, as in NP2's test-only eval) is recorded in `SKELETONS.md`.

use crate::init::char::char_ty;
use crate::init::ext::{TermExt, ThmExt};
use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{
    char_code, cond, fst, head, int_neg, nat_le, nat_to_int, none, option_case, pair, snd, some,
    tail,
};

// ============================================================================
// Types.
// ============================================================================

fn char_t() -> Type {
    char_ty()
}

fn int_t() -> Type {
    Type::int()
}

fn bool_t() -> Type {
    Type::bool()
}

/// `string := list char`.
fn str_t() -> Type {
    defs::list(char_t())
}

/// `nat × string` — the NP2 nat-parse payload.
fn ns_t() -> Type {
    defs::prod(Type::nat(), str_t())
}

/// `int × string` — the signed-parse payload.
fn is_t() -> Type {
    defs::prod(int_t(), str_t())
}

/// `option (int × string)`.
fn opt_is_t() -> Type {
    defs::option(is_t())
}

// ============================================================================
// Small builders.
// ============================================================================

fn lit(k: u64) -> Term {
    covalence_hol_eval::mk_nat(k)
}

fn lam(name: &str, ty: Type, body: Term) -> Term {
    Term::abs(ty, subst::close(&body, name))
}

/// `char_code c : nat`.
fn code(c: &Term) -> Term {
    Term::app(char_code(), c.clone())
}

/// `nat_le a b : bool`.
fn le(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_le(), a), b)
}

fn band(a: Term, b: Term) -> Term {
    crate::HolLightCtx::new().mk_and(a, b)
}

/// `nat_to_int n : int`.
fn to_int(n: Term) -> Term {
    Term::app(nat_to_int(), n)
}

/// `int_neg z : int`.
fn neg(z: Term) -> Term {
    Term::app(int_neg(), z)
}

/// `fst p : nat` for `p : nat × string`.
fn fst_ns(p: Term) -> Term {
    Term::app(fst(Type::nat(), str_t()), p)
}

/// `snd p : string` for `p : nat × string`.
fn snd_ns(p: Term) -> Term {
    Term::app(snd(Type::nat(), str_t()), p)
}

/// `pair v s : int × string`.
fn pair_is(v: Term, s: Term) -> Term {
    Term::app(Term::app(pair(int_t(), str_t()), v), s)
}

/// `some p : option (int × string)`.
fn some_is(p: Term) -> Term {
    Term::app(some(is_t()), p)
}

/// `none : option (int × string)`.
fn none_is() -> Term {
    none(is_t())
}

// ============================================================================
// The signed value and the result-lifting map.
// ============================================================================

/// `signed_val neg n : int` = `nat_to_int n` if `¬neg`, else
/// `int_neg (nat_to_int n)`.
fn signed_val(neg: &Term, n: Term) -> Term {
    Term::app(
        Term::app(Term::app(cond(int_t()), neg.clone()), neg_wrap(n.clone())),
        to_int(n),
    )
}

/// `int_neg (nat_to_int n)`.
fn neg_wrap(n: Term) -> Term {
    neg(to_int(n))
}

/// `λp:(nat×string). some (pair (signed_val neg (fst p)) (snd p))` — the
/// `some`-branch of the result lift for a given sign.
fn map_step(neg: &Term) -> Term {
    let p = Term::free("p", ns_t());
    let v = signed_val(neg, fst_ns(p.clone()));
    let body = some_is(pair_is(v, snd_ns(p.clone())));
    lam("p", ns_t(), body)
}

/// `lift_signed neg : option (nat × string) → option (int × string)` ≡
/// `option_case none (map_step neg)` — turn a `nat`-parse result into the
/// signed `int` result.
fn lift_signed(neg: &Term) -> Term {
    Term::app(
        Term::app(option_case(ns_t(), opt_is_t()), none_is()),
        map_step(neg),
    )
}

/// `lift_signed neg r` applied.
fn lift_app(neg: &Term, r: &Term) -> Term {
    Term::app(lift_signed(neg), r.clone())
}

// ============================================================================
// The parser.
// ============================================================================

/// `λc. nat_le k (code c) ∧ nat_le (code c) k` — "the char is codepoint `k`".
fn char_is(k: u64) -> Term {
    let c = Term::free("c", char_t());
    let body = band(le(lit(k), code(&c)), le(code(&c), lit(k)));
    lam("c", char_t(), body)
}

/// `option_case false (char_is k) (head s) : bool` — "the first char of `s`
/// exists and is codepoint `k`".
fn head_is(k: u64, s: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(option_case(char_t(), bool_t()), Term::bool_lit(false)),
            char_is(k),
        ),
        Term::app(head(char_t()), s.clone()),
    )
}

/// `list.tail s : string`.
fn tail_s(s: &Term) -> Term {
    Term::app(tail(char_t()), s.clone())
}

/// `parseNatDec s : option (nat × string)` — NP2's decimal `nat` parser.
fn parse_nat_dec(s: &Term) -> Term {
    Term::app(crate::init::nat_parse::parse_nat_dec(), s.clone())
}

/// `parse_int : string → option (int × string)` — optional sign then a
/// decimal `nat`, lifted to `int`. `'-'` negates, `'+'`/absent stays positive.
pub fn parse_int() -> Term {
    let s = Term::free("s", str_t());
    let neg_true = Term::bool_lit(true);
    let neg_false = Term::bool_lit(false);
    // '-' = 45, '+' = 43.
    let minus_branch = lift_app(&neg_true, &parse_nat_dec(&tail_s(&s)));
    let plus_branch = lift_app(&neg_false, &parse_nat_dec(&tail_s(&s)));
    let bare_branch = lift_app(&neg_false, &parse_nat_dec(&s));
    let inner = Term::app(
        Term::app(Term::app(cond(opt_is_t()), head_is(43, &s)), plus_branch),
        bare_branch,
    );
    let body = Term::app(
        Term::app(Term::app(cond(opt_is_t()), head_is(45, &s)), minus_branch),
        inner,
    );
    lam("s", str_t(), body)
}

// ============================================================================
// The sign-lift lemmas — how a `nat`-parse result maps to the signed result.
// ============================================================================

/// `⊢ lift_signed neg none = none` — a failed `nat` parse stays a failure.
/// Genuine (hypothesis- and oracle-free).
pub fn lift_none(neg: &Term) -> Result<Thm> {
    crate::init::option::case_none(&ns_t(), &opt_is_t(), &none_is(), &map_step(neg))
}

/// `⊢ lift_signed false (some (pair n suf)) = some (pair (nat_to_int n) suf)`
/// — a **positive** parse lifts the `nat` value by `nat_to_int`. Genuine.
pub fn lift_pos_some(n: &Term, suf: &Term) -> Result<Thm> {
    let neg = Term::bool_lit(false);
    let collapse = cond_signed_false(n)?; // signed_val false n = nat_to_int n
    lift_some_general(&neg, n, suf)?.rhs_conv(|t| t.rw_all(&collapse))
}

/// `⊢ lift_signed true (some (pair n suf)) =
///     some (pair (int_neg (nat_to_int n)) suf)` — a **negative** parse
/// negates the lifted value. Genuine.
pub fn lift_neg_some(n: &Term, suf: &Term) -> Result<Thm> {
    let neg = Term::bool_lit(true);
    let collapse = cond_signed_true(n)?; // signed_val true n = int_neg (nat_to_int n)
    lift_some_general(&neg, n, suf)?.rhs_conv(|t| t.rw_all(&collapse))
}

/// `⊢ lift_signed neg (some (pair n suf)) =
///     some (pair (signed_val neg n) suf)` — the general (unresolved-`cond`)
/// some-case, via `option_case`'s `some` clause + β + the pair projections.
fn lift_some_general(neg: &Term, n: &Term, suf: &Term) -> Result<Thm> {
    let p = Term::app(
        Term::app(pair(Type::nat(), str_t()), n.clone()),
        suf.clone(),
    );
    // lift_signed neg (some p) = map_step neg p.
    let cs = crate::init::option::case_some(&ns_t(), &opt_is_t(), &none_is(), &map_step(neg), &p)?;
    // β-reduce `map_step neg p`, then collapse `fst (pair n suf)`/`snd …`.
    let red = rhs_of(&cs).reduce()?; // some (pair (signed_val neg (fst p)) (snd p))
    let f = crate::init::prod::fst_pair(&Type::nat(), &str_t(), n, suf)?; // fst p = n
    let s = crate::init::prod::snd_pair(&Type::nat(), &str_t(), n, suf)?; // snd p = suf
    cs.trans(red)?
        .rhs_conv(|t| t.rw_all(&f))?
        .rhs_conv(|t| t.rw_all(&s))
}

/// `⊢ signed_val false n = nat_to_int n` — the positive branch of `cond`.
fn cond_signed_false(n: &Term) -> Result<Thm> {
    // rewrite the whole `some (pair (signed_val false n) suf)` isn't needed;
    // we only collapse the `cond` sitting at the value position. Build the
    // cond-collapse equation and lift it through `some (pair · suf)` at the
    // call site via `rhs_conv`. Here we just provide `signed_val false n = …`.
    crate::init::cond::cond_false(&int_t(), &neg_wrap(n.clone()), &to_int(n.clone()))
}

/// `⊢ signed_val true n = int_neg (nat_to_int n)` — the negative branch.
fn cond_signed_true(n: &Term) -> Result<Thm> {
    crate::init::cond::cond_true(&int_t(), &neg_wrap(n.clone()), &to_int(n.clone()))
}

/// The RHS of an equational theorem.
fn rhs_of(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::int_parse: expected an equation")
        .1
        .clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `⊢ lift_signed neg (some (pair n suf)) = some (pair v suf)` where the
    /// value branch has been resolved — used to check the shapes.
    #[test]
    fn lift_lemmas_are_genuine() {
        let n = Term::free("n", Type::nat());
        let suf = Term::free("suf", str_t());
        for t in [
            lift_pos_some(&n, &suf).unwrap(),
            lift_neg_some(&n, &suf).unwrap(),
            lift_none(&Term::bool_lit(true)).unwrap(),
            lift_none(&Term::bool_lit(false)).unwrap(),
        ] {
            assert!(t.hyps().is_empty(), "lift lemma must be axiom-free");
        }
        // positive lift = nat_to_int n ; negative = int_neg (nat_to_int n).
        assert_eq!(
            rhs_of(&lift_pos_some(&n, &suf).unwrap()),
            some_is(pair_is(to_int(n.clone()), suf.clone()))
        );
        assert_eq!(
            rhs_of(&lift_neg_some(&n, &suf).unwrap()),
            some_is(pair_is(neg_wrap(n.clone()), suf.clone()))
        );
    }

    #[test]
    fn parse_int_builds_and_types() {
        // `parse_int : string → option (int × string)` — well-typed.
        assert_eq!(
            parse_int().type_of().unwrap(),
            Type::fun(str_t(), opt_is_t())
        );
    }
}
