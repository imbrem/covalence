//! `nat_parse` — **string parsers** for `nat` in radices 2, 8, 10, 16, in
//! the HOL-only dialect (no reliance on `nat` *literals* for the machinery;
//! literals appear only as concrete inputs in tests).
//!
//! A parser is `parseNatR : string → option (nat × string)`: it consumes a
//! **maximal prefix** of `R`-digit characters and returns `some (value,
//! remaining-suffix)` — or `none` when the string does not *start* with an
//! `R`-digit. `string := list char`, `char` the Unicode scalar subtype of
//! `nat` (see [`crate::init::char`]), so a digit test is a comparison on
//! `char_code c : nat`.
//!
//! ## The uniform build
//!
//! Everything is generic over a **radix configuration** — a digit predicate
//! `is_digit : char → bool` and a digit value `digit_val : char → nat`
//! (plus the radix `R : nat`). The four public radices instantiate it.
//!
//! - **[`span_digits`]** `is_digit : string → (string × string)` — the
//!   maximal digit-prefix split, `(consumed, rest)`, as a **`foldr`**: the
//!   `cons` step keeps a digit char on the prefix, and on the first
//!   non-digit resets the prefix to `nil` and folds the whole tail into
//!   `rest` (reconstructed as `cat prefix rest`, so no paramorphism is
//!   needed). Its recursion clauses are [`span_nil`] / [`span_cons`].
//! - **[`nat_of_digits`]** `digit_val R : string → nat` — the radix-`R`
//!   positional value of an all-digits string, the **left fold**
//!   `foldl (λacc d. acc·R + digit_val d) 0`, realised as a `foldr` into a
//!   `nat → nat` accumulator function. Its defining clauses [`go_nil`] /
//!   [`go_cons`] *are* the fold equations of the spec. For **binary**,
//!   [`nat_of_bin_digits`] builds the value directly in the NP1 binary
//!   normal form (`bit0`/`bit1`, [`crate::init::nat_binary`]), so binary
//!   parse is log-depth and canonical.
//! - **[`parse_nat`]** `is_digit digit_val : string → option (nat ×
//!   string)` — `some (value consumed, rest)` when the first char is a
//!   digit, else `none` (the head test is `option_case false is_digit (head
//!   l)`, so `parse` returns `some` exactly when the maximal prefix is
//!   non-empty).
//!
//! ## Correctness
//!
//! [`span_cat`] (`∀l. cat (fst (span l)) (snd (span l)) = l` — the split is
//! a genuine partition) is proved for *all* radices at once by `list`
//! induction. The value clauses [`go_nil`]/[`go_cons`] discharge the
//! "`v` = the radix-`R` fold" obligation directly. The remaining
//! obligations (prefix all-digits, suffix maximality) are recorded in
//! the generated open-work index.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{
    cond, cons, fst, head, list_cat, list_foldr, nat_add, nat_le, nat_mul, nat_sub, nil, none,
    option_case, pair, snd, some,
};
use covalence_hol_eval::derived::DerivedRules;

use crate::init::char::char_ty;
use crate::init::cond::{cond_false, cond_true};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::list_recursion::{cat_cons, cat_nil, foldr_cons, foldr_nil};
use crate::init::nat_binary::{bit0, bit1};

// ============================================================================
// Types.
// ============================================================================

fn char_t() -> Type {
    char_ty()
}

fn nat_t() -> Type {
    Type::nat()
}

fn bool_t() -> Type {
    Type::bool()
}

/// `string := list char`.
fn str_t() -> Type {
    defs::list(char_t())
}

/// `string × string` — the `span` result (consumed prefix, remaining rest).
fn ss_t() -> Type {
    defs::prod(str_t(), str_t())
}

/// `nat × string` — the `parse` payload (value, remaining rest).
fn ns_t() -> Type {
    defs::prod(nat_t(), str_t())
}

/// `option (nat × string)` — the `parse` result.
fn opt_ns_t() -> Type {
    defs::option(ns_t())
}

// ============================================================================
// Small term builders.
// ============================================================================

fn lit(k: u64) -> Term {
    // Route through the eval `mk_nat` facade rather than the deprecated
    // literal ctor (keeps the toHOL literal-ctor purge ratchet flat).
    covalence_hol_eval::mk_nat(k)
}

/// `char_code c : nat`.
fn code(c: &Term) -> Term {
    Term::app(defs::char_code(), c.clone())
}

/// `nat_le a b : bool`.
fn le(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_le(), a), b)
}

/// `nat_add a b`.
fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add(), a), b)
}

/// `nat_mul a b`.
fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_mul(), a), b)
}

/// `nat_sub a b`.
fn sub(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_sub(), a), b)
}

fn band(a: Term, b: Term) -> Term {
    crate::HolLightCtx::new().mk_and(a, b)
}

fn bor(a: Term, b: Term) -> Term {
    crate::HolLightCtx::new().mk_or(a, b)
}

/// `cons c l : list char`.
fn cons_c(c: Term, l: Term) -> Term {
    Term::app(Term::app(cons(char_t()), c), l)
}

/// `nil : list char`.
fn nil_c() -> Term {
    nil(char_t())
}

/// `list_cat a b : list char`.
fn cat(a: Term, b: Term) -> Term {
    Term::app(Term::app(list_cat(char_t()), a), b)
}

/// `pair a b : string × string`.
fn pair_ss(a: Term, b: Term) -> Term {
    Term::app(Term::app(pair(str_t(), str_t()), a), b)
}

/// `fst p : string` for `p : string × string`.
fn fst_ss(p: Term) -> Term {
    Term::app(fst(str_t(), str_t()), p)
}

/// `snd p : string` for `p : string × string`.
fn snd_ss(p: Term) -> Term {
    Term::app(snd(str_t(), str_t()), p)
}

/// `⊢ cat a1 b1 = cat a2 b2` from `a_eq : ⊢ a1 = a2` and `b_eq : ⊢ b1 = b2`
/// — congruence of `list_cat` on both arguments.
fn cat_cong(a_eq: &Thm, b_eq: &Thm) -> Result<Thm> {
    let a2 = rhs(a_eq);
    let l = a_eq
        .clone()
        .cong_arg(list_cat(char_t()))?
        .cong_fn(rhs(&b_eq.clone().sym()?))?; // cat a1 b1 = cat a2 b1
    let r = b_eq.clone().cong_arg(Term::app(list_cat(char_t()), a2))?; // cat a2 b1 = cat a2 b2
    l.trans(r)
}

/// `cond[α] b x y`.
fn cond_app(ty: Type, b: Term, x: Term, y: Term) -> Term {
    Term::app(Term::app(Term::app(cond(ty), b), x), y)
}

/// `λname:ty. body`.
fn lam(name: &str, ty: Type, body: Term) -> Term {
    Term::abs(ty, subst::close(&body, name))
}

/// The RHS of an equational theorem (panics if not `⊢ _ = _`).
fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::nat_parse: expected an equation")
        .1
        .clone()
}

// ============================================================================
// `span_digits` — the maximal digit-prefix split, as a `foldr`.
// ============================================================================

/// `λc acc. cond (is_digit c) (pair (cons c (fst acc)) (snd acc))
///                            (pair nil (cons c (cat (fst acc) (snd acc))))`
/// — the `span` fold step.
fn span_step(is_digit: &Term) -> Term {
    let c = Term::free("c", char_t());
    let acc = Term::free("acc", ss_t());
    let p = fst_ss(acc.clone());
    let r = snd_ss(acc.clone());
    let digit_branch = pair_ss(cons_c(c.clone(), p.clone()), r.clone());
    let rest = cons_c(c.clone(), cat(p, r));
    let nondigit_branch = pair_ss(nil_c(), rest);
    let cnd = cond_app(
        ss_t(),
        Term::app(is_digit.clone(), c.clone()),
        digit_branch,
        nondigit_branch,
    );
    lam("c", char_t(), lam("acc", ss_t(), cnd))
}

/// `span_digits is_digit : string → (string × string)` ≡
/// `foldr (span_step is_digit) (pair nil nil)`.
pub fn span_digits(is_digit: &Term) -> Term {
    Term::app(
        Term::app(list_foldr(char_t(), ss_t()), span_step(is_digit)),
        pair_ss(nil_c(), nil_c()),
    )
}

/// `span_digits is_digit l` applied.
fn span_app(is_digit: &Term, l: &Term) -> Term {
    Term::app(span_digits(is_digit), l.clone())
}

/// `⊢ span_digits is_digit nil = pair nil nil` — the empty split.
pub fn span_nil(is_digit: &Term) -> Result<Thm> {
    foldr_nil(
        &char_t(),
        &ss_t(),
        &span_step(is_digit),
        &pair_ss(nil_c(), nil_c()),
    )
}

/// `⊢ span_digits is_digit (cons c cs) =
///     cond (is_digit c) (pair (cons c (fst (span cs))) (snd (span cs)))
///                       (pair nil (cons c (cat (fst (span cs)) (snd (span cs)))))`
/// — the general (unresolved-`cond`) `cons` clause.
pub fn span_cons(is_digit: &Term, c: &Term, cs: &Term) -> Result<Thm> {
    let base = pair_ss(nil_c(), nil_c());
    let fc = foldr_cons(&char_t(), &ss_t(), &span_step(is_digit), &base, c, cs)?;
    let red = rhs(&fc).reduce()?; // β: fire the span_step application
    fc.trans(red)
}

// ============================================================================
// `nat_of_digits` — the radix-R positional value (left fold into an
// accumulator function).
// ============================================================================

/// `λc rec. λacc. rec (acc·R + digit_val c)` — the left-fold step, threaded
/// through the `nat → nat` accumulator.
fn go_step(digit_val: &Term, radix: &Term) -> Term {
    let c = Term::free("c", char_t());
    let rec = Term::free("rec", Type::fun(nat_t(), nat_t()));
    let acc = Term::free("acc", nat_t());
    let next = add(
        mul(acc.clone(), radix.clone()),
        Term::app(digit_val.clone(), c.clone()),
    );
    let inner = lam("acc", nat_t(), Term::app(rec.clone(), next));
    lam(
        "c",
        char_t(),
        lam("rec", Type::fun(nat_t(), nat_t()), inner),
    )
}

/// `go digit_val R : string → (nat → nat)` ≡ `foldr (go_step …) (λa. a)`.
fn go(digit_val: &Term, radix: &Term) -> Term {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    Term::app(
        Term::app(
            list_foldr(char_t(), Type::fun(nat_t(), nat_t())),
            go_step(digit_val, radix),
        ),
        id,
    )
}

/// `nat_of_digits digit_val R : string → nat` ≡ `λl. go l 0`.
pub fn nat_of_digits(digit_val: &Term, radix: &Term) -> Term {
    let l = Term::free("l", str_t());
    let applied = Term::app(Term::app(go(digit_val, radix), l.clone()), lit(0));
    lam("l", str_t(), applied)
}

/// `⊢ go l acc = acc` at `l = nil` — the fold base clause (`foldl … 0 nil =
/// 0` form). Genuine.
pub fn go_nil(digit_val: &Term, radix: &Term, acc: &Term) -> Result<Thm> {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    // go nil = id, then apply acc and β-reduce `id acc = acc`.
    let fold = foldr_nil(
        &char_t(),
        &Type::fun(nat_t(), nat_t()),
        &go_step(digit_val, radix),
        &id,
    )?; // go nil = id
    let cong = fold.cong_fn(acc.clone())?; // go nil acc = id acc
    let red = rhs(&cong).reduce()?; // id acc = acc
    cong.trans(red)
}

/// `⊢ go (cons c cs) acc = go cs (acc·R + digit_val c)` — the fold step
/// clause (`foldl (λa d. a·R + d) acc (c :: cs) = foldl … (acc·R + d c) cs`).
/// These two clauses *are* the radix-`R` fold the spec asks for. Genuine.
pub fn go_cons(digit_val: &Term, radix: &Term, c: &Term, cs: &Term) -> Result<Thm> {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    let acc = Term::free("acc", nat_t());
    let fc = foldr_cons(
        &char_t(),
        &Type::fun(nat_t(), nat_t()),
        &go_step(digit_val, radix),
        &id,
        c,
        cs,
    )?; // go (cons c cs) = go_step c (go cs)
    let cong = fc.cong_fn(acc.clone())?; // go (cons c cs) acc = go_step c (go cs) acc
    let red = rhs(&cong).reduce()?; // β: = go cs (acc·R + digit_val c)
    cong.trans(red)?.all_intro("acc", nat_t())
}

// ============================================================================
// `nat_of_bin_digits` — binary value directly in the NP1 binary normal form.
// ============================================================================

/// `λc rec. λacc. rec (cond (is_one c) (bit1 acc) (bit0 acc))` — the binary
/// step, building the value with `bit0`/`bit1` (log-depth normal form).
/// `is_one c` = `nat_le 49 (char_code c)` (the char is `'1'`, code 49).
fn bin_step() -> Term {
    let c = Term::free("c", char_t());
    let rec = Term::free("rec", Type::fun(nat_t(), nat_t()));
    let acc = Term::free("acc", nat_t());
    let is_one = le(lit(49), code(&c));
    let next = cond_app(nat_t(), is_one, bit1(acc.clone()), bit0(acc.clone()));
    let inner = lam("acc", nat_t(), Term::app(rec.clone(), next));
    lam(
        "c",
        char_t(),
        lam("rec", Type::fun(nat_t(), nat_t()), inner),
    )
}

fn bin_go() -> Term {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    Term::app(
        Term::app(
            list_foldr(char_t(), Type::fun(nat_t(), nat_t())),
            bin_step(),
        ),
        id,
    )
}

/// `nat_of_bin_digits : string → nat` — the binary value in NP1 `bit0`/`bit1`
/// normal form (`λl. bin_go l 0`). Log-depth and canonical.
pub fn nat_of_bin_digits() -> Term {
    let l = Term::free("l", str_t());
    let applied = Term::app(Term::app(bin_go(), l.clone()), lit(0));
    lam("l", str_t(), applied)
}

/// `⊢ bin_go nil acc = acc`. Genuine.
pub fn bin_go_nil(acc: &Term) -> Result<Thm> {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    let fold = foldr_nil(&char_t(), &Type::fun(nat_t(), nat_t()), &bin_step(), &id)?;
    let cong = fold.cong_fn(acc.clone())?;
    let red = rhs(&cong).reduce()?;
    cong.trans(red)
}

/// `⊢ bin_go (cons c cs) acc = bin_go cs (cond (is_one c) (bit1 acc) (bit0
/// acc))` — the binary step clause. Genuine.
pub fn bin_go_cons(c: &Term, cs: &Term, acc: &Term) -> Result<Thm> {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    let fc = foldr_cons(
        &char_t(),
        &Type::fun(nat_t(), nat_t()),
        &bin_step(),
        &id,
        c,
        cs,
    )?;
    let cong = fc.cong_fn(acc.clone())?;
    let red = rhs(&cong).reduce()?;
    cong.trans(red)
}

// ============================================================================
// `parse_nat` — the assembled parser.
// ============================================================================

/// `option_case false is_digit (head l) : bool` — "the first char of `l`
/// exists and is an `R`-digit".
fn head_is_digit(is_digit: &Term, l: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(
                option_case(char_t(), bool_t()),
                covalence_hol_eval::mk_bool(false),
            ),
            is_digit.clone(),
        ),
        Term::app(head(char_t()), l.clone()),
    )
}

/// `parse_nat is_digit value : string → option (nat × string)` ≡
/// `λl. cond (head_is_digit is_digit l)
///           (some (pair (value (fst (span l))) (snd (span l))))
///           none`.
///
/// `value : string → nat` is the radix's value function
/// ([`nat_of_digits`] / [`nat_of_bin_digits`]).
pub fn parse_nat(is_digit: &Term, value: &Term) -> Term {
    let l = Term::free("l", str_t());
    let sp = span_app(is_digit, &l);
    let v = Term::app(value.clone(), fst_ss(sp.clone()));
    let payload = Term::app(Term::app(pair(nat_t(), str_t()), v), snd_ss(sp));
    let body = cond_app(
        opt_ns_t(),
        head_is_digit(is_digit, &l),
        Term::app(some(ns_t()), payload),
        none(ns_t()),
    );
    lam("l", str_t(), body)
}

/// `parse_nat is_digit value l` applied.
#[cfg(test)]
fn parse_app(is_digit: &Term, value: &Term, l: &Term) -> Term {
    Term::app(parse_nat(is_digit, value), l.clone())
}

// ============================================================================
// The four radix configurations.
// ============================================================================

/// `λc. nat_le lo (code c) ∧ nat_le (code c) hi` — the digit predicate for a
/// single contiguous codepoint range `[lo, hi]`.
fn range_pred(lo: u64, hi: u64) -> Term {
    let c = Term::free("c", char_t());
    let body = band(le(lit(lo), code(&c)), le(code(&c), lit(hi)));
    lam("c", char_t(), body)
}

/// `is_digit` for **binary** — `'0'..='1'` (codes 48..=49).
pub fn is_digit_bin() -> Term {
    range_pred(48, 49)
}

/// `is_digit` for **octal** — `'0'..='7'` (48..=55).
pub fn is_digit_oct() -> Term {
    range_pred(48, 55)
}

/// `is_digit` for **decimal** — `'0'..='9'` (48..=57).
pub fn is_digit_dec() -> Term {
    range_pred(48, 57)
}

/// `is_digit` for **hex** — `'0'..='9' ∨ 'A'..='F' ∨ 'a'..='f'`.
pub fn is_digit_hex() -> Term {
    let c = Term::free("c", char_t());
    let dec = band(le(lit(48), code(&c)), le(code(&c), lit(57)));
    let upper = band(le(lit(65), code(&c)), le(code(&c), lit(70)));
    let lower = band(le(lit(97), code(&c)), le(code(&c), lit(102)));
    lam("c", char_t(), bor(bor(dec, upper), lower))
}

/// `λc. code c − 48` — the digit value for a `'0'`-based decimal-style digit
/// (correct for binary / octal / decimal).
pub fn digit_val_dec() -> Term {
    let c = Term::free("c", char_t());
    lam("c", char_t(), sub(code(&c), lit(48)))
}

/// `λc. cond (code c ≤ 57) (code c − 48)
///           (cond (code c ≤ 70) (code c − 55) (code c − 87))` — the hex
/// digit value (`'0'-'9'` ↦ 0-9, `'A'-'F'` ↦ 10-15, `'a'-'f'` ↦ 10-15).
pub fn digit_val_hex() -> Term {
    let c = Term::free("c", char_t());
    let lower = sub(code(&c), lit(87));
    let mid = cond_app(
        nat_t(),
        le(code(&c), lit(70)),
        sub(code(&c), lit(55)),
        lower,
    );
    let body = cond_app(nat_t(), le(code(&c), lit(57)), sub(code(&c), lit(48)), mid);
    lam("c", char_t(), body)
}

/// `parseNatBin : string → option (nat × string)` — value in NP1 binary
/// normal form.
pub fn parse_nat_bin() -> Term {
    parse_nat(&is_digit_bin(), &nat_of_bin_digits())
}

/// `parseNatOct : string → option (nat × string)`.
pub fn parse_nat_oct() -> Term {
    parse_nat(&is_digit_oct(), &nat_of_digits(&digit_val_dec(), &lit(8)))
}

/// `parseNatDec : string → option (nat × string)`.
pub fn parse_nat_dec() -> Term {
    parse_nat(&is_digit_dec(), &nat_of_digits(&digit_val_dec(), &lit(10)))
}

/// `parseNatHex : string → option (nat × string)`.
pub fn parse_nat_hex() -> Term {
    parse_nat(&is_digit_hex(), &nat_of_digits(&digit_val_hex(), &lit(16)))
}

// ============================================================================
// General correctness: the split is a genuine partition (`cat prefix rest =
// l`), for *every* radix at once. By `list`-induction, splitting the `cons`
// head with `bool.cases` on `is_digit c`.
// ============================================================================

use crate::init::eq::{beta_expand, beta_nf, beta_nf_concl, beta_reduce};
use crate::init::list::{head_cons, head_nil};
use crate::init::nat_div::bool_cases;
use crate::init::option::{case_none, case_some, some_inj, some_ne_none};
use crate::init::prod::{fst_pair, pair_inj, snd_pair};

/// `⊢ ∀l. cat (fst (span_digits is_digit l)) (snd (span_digits is_digit l)) =
/// l` — **the split is a partition**: the consumed prefix concatenated with
/// the remaining suffix is the original string, for any digit predicate. By
/// `list`-induction on `l`. Genuine (hypothesis- and oracle-free).
pub fn span_cat(is_digit: &Term) -> Result<Thm> {
    // motive P ≔ λl. cat (fst (span l)) (snd (span l)) = l.
    let l = Term::free("l", str_t());
    let cat_of = |t: &Term| -> Term {
        let sp = span_app(is_digit, t);
        cat(fst_ss(sp.clone()), snd_ss(sp))
    };
    let motive = {
        let body = cat_of(&l).equals(l.clone())?;
        Term::abs(str_t(), subst::close(&body, "l"))
    };

    // ---- base: P nil. span nil = pair nil nil; cat nil nil = nil. ----
    let base = {
        let sn = span_nil(is_digit)?; // span nil = pair nil nil
        let f = fst_pair(&str_t(), &str_t(), &nil_c(), &nil_c())?; // fst (pair nil nil) = nil
        let s = snd_pair(&str_t(), &str_t(), &nil_c(), &nil_c())?; // snd (pair nil nil) = nil
        // cat (fst (span nil)) (snd (span nil)) = cat nil nil = nil.
        let lhs = Thm::refl(cat_of(&nil_c()))?
            .rhs_conv(|t| t.rw_all(&sn))? // rewrite span nil → pair nil nil
            .rhs_conv(|t| t.rw_all(&f))? // fst → nil
            .rhs_conv(|t| t.rw_all(&s))?; // snd → nil
        let base_eq = lhs.trans(cat_nil(&char_t(), &nil_c())?)?; // = nil
        beta_expand(&motive, nil_c(), base_eq)? // ⊢ P nil
    };

    // ---- cons_case: ∀c cs. P cs ⟹ P (cons c cs). ----
    let c = Term::free("c", char_t());
    let cs = Term::free("cs", str_t());
    let cons_case = {
        let consed = cons_c(c.clone(), cs.clone());
        let ante = Term::app(motive.clone(), cs.clone());
        let ih = beta_reduce(Thm::assume(ante.clone())?)?; // {P cs} ⊢ cat (fst (span cs)) (snd (span cs)) = cs
        let goal = cat_of(&consed).equals(consed.clone())?;

        let sp_cs = span_app(is_digit, &cs);
        let p = fst_ss(sp_cs.clone()); // fst (span cs)
        let r = snd_ss(sp_cs); // snd (span cs)
        let general = span_cons(is_digit, &c, &cs)?; // span (cons c cs) = cond …
        // `span_cons` β-reduces the `is_digit c` redex, so the `cond`
        // condition in `general` is the *reduced* predicate application.
        // Split on that exact term so `cond_true`/`cond_false` bridge.
        let cond_c = rhs(&Term::app(is_digit.clone(), c.clone()).reduce()?);

        // b = true (digit): span (cons c cs) = pair (cons c p) r.
        let branch_t = {
            let hbt = Thm::assume(cond_c.clone().equals(covalence_hol_eval::mk_bool(true))?)?;
            let digit_branch = pair_ss(cons_c(c.clone(), p.clone()), r.clone());
            let ct = cond_true(
                &ss_t(),
                &digit_branch,
                &pair_ss(nil_c(), cons_c(c.clone(), cat(p.clone(), r.clone()))),
            )?; // cond T x y = x
            // span (cons c cs) = pair (cons c p) r.
            let span_eq = general.clone().rewrite(&hbt)?.trans(ct)?;
            let fp = fst_pair(&str_t(), &str_t(), &cons_c(c.clone(), p.clone()), &r)?; // fst branch = cons c p
            let sp = snd_pair(&str_t(), &str_t(), &cons_c(c.clone(), p.clone()), &r)?; // snd branch = r
            // fst (span(cons c cs)) = cons c p ; snd (span(cons c cs)) = r.
            let fst_eq = span_eq.clone().cong_arg(fst(str_t(), str_t()))?.trans(fp)?;
            let snd_eq = span_eq.cong_arg(snd(str_t(), str_t()))?.trans(sp)?;
            // cat (fst..) (snd..) = cat (cons c p) r = cons c (cat p r) = cons c cs.
            let cat_eq = cat_cong(&fst_eq, &snd_eq)?;
            let cc = cat_cons(&char_t(), &c, &p, &r)?; // cat (cons c p) r = cons c (cat p r)
            let use_ih = ih.clone().cong_arg(Term::app(cons(char_t()), c.clone()))?; // cons c (cat p r) = cons c cs
            let t1 = cat_eq.trans(cc)?;
            t1.trans(use_ih)?
                .imp_intro(&cond_c.clone().equals(covalence_hol_eval::mk_bool(true))?)?
        };

        // b = false (non-digit): span (cons c cs) = pair nil (cons c (cat p r)).
        let branch_f = {
            let hbf = Thm::assume(cond_c.clone().equals(covalence_hol_eval::mk_bool(false))?)?;
            let x = cons_c(c.clone(), cat(p.clone(), r.clone()));
            let cf = cond_false(
                &ss_t(),
                &pair_ss(cons_c(c.clone(), p.clone()), r.clone()),
                &pair_ss(nil_c(), x.clone()),
            )?; // cond F x y = y
            let span_eq = general.clone().rewrite(&hbf)?.trans(cf)?; // span(cons c cs) = pair nil x
            let fp = fst_pair(&str_t(), &str_t(), &nil_c(), &x)?; // fst (pair nil x) = nil
            let sp = snd_pair(&str_t(), &str_t(), &nil_c(), &x)?; // snd (pair nil x) = x
            let fst_eq = span_eq.clone().cong_arg(fst(str_t(), str_t()))?.trans(fp)?; // fst(span..) = nil
            let snd_eq = span_eq.cong_arg(snd(str_t(), str_t()))?.trans(sp)?; // snd(span..) = cons c (cat p r)
            // cat (fst..) (snd..) = cat nil (snd..). Use `cat_nil` on the
            // *unreduced* `snd (span (cons c cs))` — its only `list_cat` is
            // under the `span_step` λ, so `cat_nil`'s spine `delta_all` leaves
            // it folded (unlike the reduced `cons c (cat p r)`, whose top-level
            // `list_cat` `delta_all` would over-unfold).
            let snd_span = snd_ss(span_app(is_digit, &consed));
            let cat_l = fst_eq
                .cong_arg(list_cat(char_t()))?
                .cong_fn(snd_span.clone())?; // cat(fst..)(snd..) = cat nil (snd..)
            let cn = cat_nil(&char_t(), &snd_span)?; // cat nil (snd..) = snd..
            let use_ih = ih.clone().cong_arg(Term::app(cons(char_t()), c.clone()))?; // cons c (cat p r) = cons c cs
            let snd_to_cons = snd_eq.trans(use_ih)?; // snd(span..) = cons c cs
            cat_l
                .trans(cn)?
                .trans(snd_to_cons)?
                .imp_intro(&cond_c.clone().equals(covalence_hol_eval::mk_bool(false))?)?
        };

        let combined = bool_cases()
            .all_elim(cond_c.clone())?
            .or_elim(branch_t, branch_f)?; // {P cs} ⊢ goal
        let _ = goal;
        let p_cons = beta_expand(&motive, consed, combined)?; // {P cs} ⊢ P (cons c cs)
        p_cons
            .imp_intro(&ante)?
            .all_intro("cs", str_t())?
            .all_intro("c", char_t())?
    };

    let li = crate::init::list::list_induct(&char_t(), &motive, base, cons_case)?;
    beta_nf_concl(li)
}

// ============================================================================
// `list_all` — "every element satisfies `p`", as a `foldr` into `bool`. This
// is the predicate the parser-correctness spec uses to characterise the
// consumed prefix ("all its chars are `R`-digits").
// ============================================================================

/// `λx:α. λacc:bool. p x ∧ acc` — the `list_all` fold step.
fn all_step(alpha: &Type, p: &Term) -> Term {
    let x = Term::free("x", alpha.clone());
    let acc = Term::free("acc", bool_t());
    let body = band(Term::app(p.clone(), x.clone()), acc.clone());
    lam("x", alpha.clone(), lam("acc", bool_t(), body))
}

/// `list_all p : list α → bool` ≡ `foldr (λx acc. p x ∧ acc) T` — every
/// element of the list satisfies `p`.
pub fn list_all(alpha: &Type, p: &Term) -> Term {
    Term::app(
        Term::app(list_foldr(alpha.clone(), bool_t()), all_step(alpha, p)),
        covalence_hol_eval::mk_bool(true),
    )
}

/// `list_all p l` applied.
fn all_app(alpha: &Type, p: &Term, l: &Term) -> Term {
    Term::app(list_all(alpha, p), l.clone())
}

/// `⊢ list_all p nil = T` — the empty list vacuously satisfies any `p`.
/// Genuine (hypothesis- and oracle-free).
pub fn all_nil(alpha: &Type, p: &Term) -> Result<Thm> {
    foldr_nil(
        alpha,
        &bool_t(),
        &all_step(alpha, p),
        &covalence_hol_eval::mk_bool(true),
    )
}

/// `⊢ list_all p (cons x xs) = (p x ∧ list_all p xs)` — the `cons` clause.
/// Genuine.
///
/// Proved with a *fresh* predicate variable `q`, then `INST q := p`. Because
/// `q` is a free variable, the `foldr` β-step leaves `q x` opaque (it is not a
/// redex); the instantiation then keeps `p x` un-β-reduced even when `p` is a
/// λ (a radix digit predicate), so the clause reads uniformly `p x ∧ …`.
pub fn all_cons(alpha: &Type, p: &Term, x: &Term, xs: &Term) -> Result<Thm> {
    let q = Term::free("q__la", Type::fun(alpha.clone(), bool_t()));
    let fc = foldr_cons(
        alpha,
        &bool_t(),
        &all_step(alpha, &q),
        &covalence_hol_eval::mk_bool(true),
        x,
        xs,
    )?; // list_all q (cons x xs) = all_step q x (list_all q xs)
    let red = rhs(&fc).reduce()?; // β: = (q x ∧ list_all q xs)
    fc.trans(red)?.inst("q__la", p.clone())
}

// ============================================================================
// Prefix all-digits — the consumed prefix `fst (span l)` is entirely
// `R`-digits, for every radix at once. By `list`-induction, splitting the
// `cons` head with `bool.cases` on `is_digit c`.
// ============================================================================

/// `⊢ ∀l. list_all is_digit (fst (span_digits is_digit l)) = T` — **the
/// consumed prefix is all digits**: every char of `fst (span l)` satisfies
/// `is_digit`, for any digit predicate. By `list`-induction on `l`. Genuine
/// (hypothesis- and oracle-free).
pub fn prefix_all_digits(is_digit: &Term) -> Result<Thm> {
    // motive P ≔ λl. list_all is_digit (fst (span l)) = T.
    let l = Term::free("l", str_t());
    let all_of =
        |t: &Term| -> Term { all_app(&char_t(), is_digit, &fst_ss(span_app(is_digit, t))) };
    let motive = {
        let body = all_of(&l).equals(covalence_hol_eval::mk_bool(true))?;
        Term::abs(str_t(), subst::close(&body, "l"))
    };

    // ---- base: P nil. fst (span nil) = nil; list_all is_digit nil = T. ----
    let base = {
        let sn = span_nil(is_digit)?; // span nil = pair nil nil
        let fp = fst_pair(&str_t(), &str_t(), &nil_c(), &nil_c())?; // fst (pair nil nil) = nil
        let an = all_nil(&char_t(), is_digit)?; // list_all is_digit nil = T
        let base_eq = Thm::refl(all_of(&nil_c()))?
            .rhs_conv(|t| t.rw_all(&sn))? // span nil → pair nil nil
            .rhs_conv(|t| t.rw_all(&fp))? // fst → nil
            .rhs_conv(|t| t.rw_all(&an))?; // list_all is_digit nil → T
        beta_expand(&motive, nil_c(), base_eq)?
    };

    // ---- cons_case: ∀c cs. P cs ⟹ P (cons c cs). ----
    let c = Term::free("c", char_t());
    let cs = Term::free("cs", str_t());
    let cons_case = {
        let consed = cons_c(c.clone(), cs.clone());
        let ante = Term::app(motive.clone(), cs.clone());
        let ih = beta_reduce(Thm::assume(ante.clone())?)?; // {P cs} ⊢ list_all is_digit (fst (span cs)) = T

        let sp_cs = span_app(is_digit, &cs);
        let pfx = fst_ss(sp_cs.clone()); // fst (span cs)
        let rst = snd_ss(sp_cs); // snd (span cs)
        let general = span_cons(is_digit, &c, &cs)?; // span (cons c cs) = cond …
        // `span_cons` β-reduces the `is_digit c` redex; split on that reduced
        // predicate application (as `span_cat` does).
        let cond_c = rhs(&Term::app(is_digit.clone(), c.clone()).reduce()?);
        let red_eq = Term::app(is_digit.clone(), c.clone()).reduce()?; // ⊢ is_digit c = cond_c

        // b = true (digit): fst (span (cons c cs)) = cons c pfx.
        let branch_t = {
            let hbt = Thm::assume(cond_c.clone().equals(covalence_hol_eval::mk_bool(true))?)?;
            let digit_branch = pair_ss(cons_c(c.clone(), pfx.clone()), rst.clone());
            let ct = cond_true(
                &ss_t(),
                &digit_branch,
                &pair_ss(nil_c(), cons_c(c.clone(), cat(pfx.clone(), rst.clone()))),
            )?;
            let span_eq = general.clone().rewrite(&hbt)?.trans(ct)?; // span (cons c cs) = pair (cons c pfx) rst
            let fp = fst_pair(&str_t(), &str_t(), &cons_c(c.clone(), pfx.clone()), &rst)?;
            let fst_eq = span_eq.cong_arg(fst(str_t(), str_t()))?.trans(fp)?; // fst (span (cons c cs)) = cons c pfx
            // list_all is_digit (fst (span (cons c cs))) = list_all is_digit (cons c pfx).
            let e1 = fst_eq.cong_arg(list_all(&char_t(), is_digit))?;
            // = (is_digit c ∧ list_all is_digit pfx).
            let e2 = all_cons(&char_t(), is_digit, &c, &pfx)?;
            // Both conjuncts are true, so the ∧ = T.
            let isdig = red_eq.clone().trans(hbt.clone())?.eqt_elim()?; // {cond_c=T} ⊢ is_digit c
            let ih_bool = ih.clone().eqt_elim()?; // {P cs} ⊢ list_all is_digit pfx
            let conj_t = isdig.and_intro(ih_bool)?.eqt_intro()?; // (is_digit c ∧ list_all is_digit pfx) = T
            e1.trans(e2)?
                .trans(conj_t)?
                .imp_intro(&cond_c.clone().equals(covalence_hol_eval::mk_bool(true))?)?
        };

        // b = false (non-digit): fst (span (cons c cs)) = nil.
        let branch_f = {
            let hbf = Thm::assume(cond_c.clone().equals(covalence_hol_eval::mk_bool(false))?)?;
            let x = cons_c(c.clone(), cat(pfx.clone(), rst.clone()));
            let cf = cond_false(
                &ss_t(),
                &pair_ss(cons_c(c.clone(), pfx.clone()), rst.clone()),
                &pair_ss(nil_c(), x.clone()),
            )?;
            let span_eq = general.clone().rewrite(&hbf)?.trans(cf)?; // span (cons c cs) = pair nil x
            let fp = fst_pair(&str_t(), &str_t(), &nil_c(), &x)?;
            let fst_eq = span_eq.cong_arg(fst(str_t(), str_t()))?.trans(fp)?; // fst (span (cons c cs)) = nil
            let e1 = fst_eq.cong_arg(list_all(&char_t(), is_digit))?; // list_all is_digit (fst..) = list_all is_digit nil
            let an = all_nil(&char_t(), is_digit)?; // list_all is_digit nil = T
            e1.trans(an)?
                .imp_intro(&cond_c.clone().equals(covalence_hol_eval::mk_bool(false))?)?
        };

        let combined = bool_cases()
            .all_elim(cond_c.clone())?
            .or_elim(branch_t, branch_f)?; // {P cs} ⊢ P (cons c cs) body
        let p_cons = beta_expand(&motive, consed, combined)?;
        p_cons
            .imp_intro(&ante)?
            .all_intro("cs", str_t())?
            .all_intro("c", char_t())?
    };

    let li = crate::init::list::list_induct(&char_t(), &motive, base, cons_case)?;
    beta_nf_concl(li)
}

// ============================================================================
// Suffix maximality — the remaining suffix `snd (span l)` does not start with
// a digit: either it is `nil` or its head is a non-digit. Both cases are
// captured by `head_is_digit is_digit (snd (span l)) = F` (the very predicate
// `parse` tests): `head nil = none` and a non-digit head both make it `F`.
// ============================================================================

/// `⊢ ∀l. head_is_digit is_digit (snd (span_digits is_digit l)) = F` — **the
/// suffix is maximal**: the first un-consumed char (if any) is not a digit, so
/// the parser stopped at the longest digit run. Equivalently `snd (span l) =
/// nil ∨ ¬is_digit (head …)`. By `list`-induction on `l`. Genuine.
pub fn suffix_maximal(is_digit: &Term) -> Result<Thm> {
    // `option_case false is_digit : option char → bool`, the "head is a digit"
    // decider applied under `head`.
    let oc_fun = Term::app(
        Term::app(
            option_case(char_t(), bool_t()),
            covalence_hol_eval::mk_bool(false),
        ),
        is_digit.clone(),
    );
    let head_c = head(char_t());

    // motive Q ≔ λl. head_is_digit is_digit (snd (span l)) = F.
    let l = Term::free("l", str_t());
    let hd_of = |t: &Term| -> Term { head_is_digit(is_digit, &snd_ss(span_app(is_digit, t))) };
    let motive = {
        let body = hd_of(&l).equals(covalence_hol_eval::mk_bool(false))?;
        Term::abs(str_t(), subst::close(&body, "l"))
    };

    // ---- base: Q nil. snd (span nil) = nil; head nil = none; option_case … = F.
    let base = {
        let sn = span_nil(is_digit)?; // span nil = pair nil nil
        let sp = snd_pair(&str_t(), &str_t(), &nil_c(), &nil_c())?; // snd (pair nil nil) = nil
        let hn = head_nil(&char_t())?; // head nil = none
        let cn = case_none(
            &char_t(),
            &bool_t(),
            &covalence_hol_eval::mk_bool(false),
            is_digit,
        )?; // option_case false is_digit none = false
        let base_eq = Thm::refl(hd_of(&nil_c()))?
            .rhs_conv(|t| t.rw_all(&sn))? // span nil → pair nil nil
            .rhs_conv(|t| t.rw_all(&sp))? // snd → nil
            .rhs_conv(|t| t.rw_all(&hn))? // head nil → none
            .rhs_conv(|t| t.rw_all(&cn))?; // option_case false is_digit none → F
        beta_expand(&motive, nil_c(), base_eq)?
    };

    // ---- cons_case: ∀c cs. Q cs ⟹ Q (cons c cs). ----
    let c = Term::free("c", char_t());
    let cs = Term::free("cs", str_t());
    let cons_case = {
        let consed = cons_c(c.clone(), cs.clone());
        let ante = Term::app(motive.clone(), cs.clone());
        let ih = beta_reduce(Thm::assume(ante.clone())?)?; // {Q cs} ⊢ head_is_digit is_digit (snd (span cs)) = F

        let sp_cs = span_app(is_digit, &cs);
        let pfx = fst_ss(sp_cs.clone()); // fst (span cs)
        let rst = snd_ss(sp_cs); // snd (span cs)
        let general = span_cons(is_digit, &c, &cs)?;
        let cond_c = rhs(&Term::app(is_digit.clone(), c.clone()).reduce()?);
        let red_eq = Term::app(is_digit.clone(), c.clone()).reduce()?; // ⊢ is_digit c = cond_c

        // b = true (digit): snd (span (cons c cs)) = rst = snd (span cs); Q reduces to IH.
        let branch_t = {
            let hbt = Thm::assume(cond_c.clone().equals(covalence_hol_eval::mk_bool(true))?)?;
            let digit_branch = pair_ss(cons_c(c.clone(), pfx.clone()), rst.clone());
            let ct = cond_true(
                &ss_t(),
                &digit_branch,
                &pair_ss(nil_c(), cons_c(c.clone(), cat(pfx.clone(), rst.clone()))),
            )?;
            let span_eq = general.clone().rewrite(&hbt)?.trans(ct)?; // span (cons c cs) = pair (cons c pfx) rst
            let sp = snd_pair(&str_t(), &str_t(), &cons_c(c.clone(), pfx.clone()), &rst)?;
            let snd_eq = span_eq.cong_arg(snd(str_t(), str_t()))?.trans(sp)?; // snd (span (cons c cs)) = rst
            // head_is_digit is_digit (snd (span (cons c cs))) = head_is_digit is_digit rst.
            let head_eq = snd_eq.cong_arg(head_c.clone())?.cong_arg(oc_fun.clone())?;
            head_eq
                .trans(ih.clone())?
                .imp_intro(&cond_c.clone().equals(covalence_hol_eval::mk_bool(true))?)?
        };

        // b = false (non-digit): snd (span (cons c cs)) = cons c (cat pfx rst); head = some c; = is_digit c = F.
        let branch_f = {
            let hbf = Thm::assume(cond_c.clone().equals(covalence_hol_eval::mk_bool(false))?)?;
            let tail = cat(pfx.clone(), rst.clone());
            let x = cons_c(c.clone(), tail.clone());
            let cf = cond_false(
                &ss_t(),
                &pair_ss(cons_c(c.clone(), pfx.clone()), rst.clone()),
                &pair_ss(nil_c(), x.clone()),
            )?;
            let span_eq = general.clone().rewrite(&hbf)?.trans(cf)?; // span (cons c cs) = pair nil x
            let sp = snd_pair(&str_t(), &str_t(), &nil_c(), &x)?;
            let snd_eq = span_eq.cong_arg(snd(str_t(), str_t()))?.trans(sp)?; // snd (span (cons c cs)) = cons c (cat pfx rst)
            let hc = head_cons(&char_t(), &c, &tail)?; // head (cons c (cat pfx rst)) = some c
            let head_eq = snd_eq.cong_arg(head_c.clone())?.trans(hc)?; // head (snd (span (cons c cs))) = some c
            // head_is_digit is_digit (snd (span (cons c cs))) = option_case false is_digit (some c) = is_digit c.
            let e1 = head_eq.cong_arg(oc_fun.clone())?;
            let cs_some = case_some(
                &char_t(),
                &bool_t(),
                &covalence_hol_eval::mk_bool(false),
                is_digit,
                &c,
            )?; // = is_digit c
            let isdig_f = red_eq.clone().trans(hbf.clone())?; // is_digit c = F
            e1.trans(cs_some)?
                .trans(isdig_f)?
                .imp_intro(&cond_c.clone().equals(covalence_hol_eval::mk_bool(false))?)?
        };

        let combined = bool_cases()
            .all_elim(cond_c.clone())?
            .or_elim(branch_t, branch_f)?; // {Q cs} ⊢ Q (cons c cs) body
        let q_cons = beta_expand(&motive, consed, combined)?;
        q_cons
            .imp_intro(&ante)?
            .all_intro("cs", str_t())?
            .all_intro("c", char_t())?
    };

    let li = crate::init::list::list_induct(&char_t(), &motive, base, cons_case)?;
    beta_nf_concl(li)
}

// ============================================================================
// The full parser-correctness theorem — a genuine, hypothesis-free implication
// assembling the partition (`span_cat`), prefix all-digits, suffix maximality,
// and the value characterisation. Radix-generic over `(is_digit, value)`.
// ============================================================================

/// `⊢ some x = some y ⟹ x = y` **with `x`,`y` verbatim** — the catalogue
/// [`some_inj`](crate::init::option::some_inj) β-normalises its payload (via
/// the internal `option_case` reduction), which would unfold `is_digit` inside
/// the span and diverge from the span lemmas. Proving injectivity over *fresh
/// variables* and then `INST`-ing the payloads sidesteps that: the reduction
/// runs over variables (a no-op), and the kernel `Inst` substitutes the folded
/// payloads without touching them.
fn some_inj_raw(alpha: &Type, x: &Term, y: &Term) -> Result<Thm> {
    let fx = Term::free("__six", alpha.clone());
    let fy = Term::free("__siy", alpha.clone());
    some_inj(alpha, &fx, &fy)? // some fx = some fy ⟹ fx = fy
        .inst("__six", x.clone())?
        .inst("__siy", y.clone())
}

/// `⊢ pair a b = pair c d ⟹ (a = c ∧ b = d)` **with `a`..`d` verbatim** — the
/// same fresh-variable + `INST` trick as [`some_inj_raw`], since the catalogue
/// [`pair_inj`](crate::init::prod::pair_inj) β-normalises the pair components.
fn pair_inj_raw(alpha: &Type, beta: &Type, a: &Term, b: &Term, c: &Term, d: &Term) -> Result<Thm> {
    let fa = Term::free("__pia", alpha.clone());
    let fb = Term::free("__pib", beta.clone());
    let fc = Term::free("__pic", alpha.clone());
    let fd = Term::free("__pid", beta.clone());
    pair_inj(alpha, beta, &fa, &fb, &fc, &fd)? // pair fa fb = pair fc fd ⟹ (fa=fc ∧ fb=fd)
        .inst("__pia", a.clone())?
        .inst("__pib", b.clone())?
        .inst("__pic", c.clone())?
        .inst("__pid", d.clone())
}

/// `⊢ ∀s v rest. parse_nat is_digit value s = some (pair v rest) ⟹`
/// `  (s = cat consumed rest)`
/// `∧ list_all is_digit consumed`
/// `∧ (head_is_digit is_digit rest = F)`
/// `∧ (v = value consumed)`
///
/// where `consumed = fst (span s)` — the **complete parser spec**: a successful
/// parse splits `s` into a consumed prefix and the returned `rest`, the prefix
/// is all digits, `rest` does not start with a digit (maximality), and the
/// value is the radix fold of the prefix. Hypothesis- and oracle-free, for any
/// radix configuration `(is_digit, value)`.
///
/// (The `span`/`list_all`/`consumed` subterms appear in β-normal form — the
/// span lemmas evaluate `is_digit` inside the fold — but this is definitionally
/// the maximal digit-prefix split; the third conjunct's `head_is_digit is_digit
/// rest = F` is exactly "`rest` is `nil` or its head is a non-digit".)
pub fn parse_nat_correct(is_digit: &Term, value: &Term) -> Result<Thm> {
    let s = Term::free("s", str_t());
    let v = Term::free("v", nat_t());
    let rest = Term::free("rest", str_t());

    let sp_s = span_app(is_digit, &s);
    let consumed = fst_ss(sp_s.clone()); // fst (span s)
    let sp_rest = snd_ss(sp_s); // snd (span s)
    let val = Term::app(value.clone(), consumed.clone()); // value (fst (span s))

    // parse s = cond OC (some (pair val sp_rest)) none (one outer β; the inner
    // `value (fst (span s))` and `head_is_digit …` stay folded — crucially,
    // `is_digit` inside the span stays a λ, unreduced, matching the span
    // lemmas). `some_inj_raw`/`pair_inj` below are chosen to *not* β-reduce
    // their payloads, so this folded representation is preserved throughout.
    let parse_s = Term::app(parse_nat(is_digit, value), s.clone());
    let parse_red = Thm::beta_conv(parse_s.clone())?;
    let oc = head_is_digit(is_digit, &s); // OC
    let a_payload = Term::app(
        Term::app(pair(nat_t(), str_t()), val.clone()),
        sp_rest.clone(),
    ); // pair val sp_rest
    let a_br = Term::app(some(ns_t()), a_payload.clone()); // some (pair val sp_rest)
    let none_br = none(ns_t());

    // The theorem hypothesis and its target conjunction.
    let vr_pair = Term::app(Term::app(pair(nat_t(), str_t()), v.clone()), rest.clone()); // pair v rest
    let some_vr = Term::app(some(ns_t()), vr_pair.clone()); // some (pair v rest)
    let hyp_term = parse_s.clone().equals(some_vr.clone())?;
    let h = Thm::assume(hyp_term.clone())?;

    // The span lemmas β-normalise their conclusions (so `is_digit` inside the
    // span is *evaluated*); the assembled goal is therefore taken directly from
    // their (β-normal) outputs — and shared verbatim by both `bool_cases`
    // branches, so the `or_elim` consequents agree. `consumed`/`sp_rest` are
    // bridged to that β-normal form (`CF`/`CS`) via `beta_nf`.
    let cf_eq = beta_nf(consumed.clone()); // ⊢ consumed = CF
    let cs_eq = beta_nf(sp_rest.clone()); // ⊢ sp_rest = CS

    let oc_t = oc.clone().equals(covalence_hol_eval::mk_bool(true))?;
    let oc_f = oc.clone().equals(covalence_hol_eval::mk_bool(false))?;

    // OC = T: parse s = A, so some (pair v rest) = some (pair val sp_rest);
    // build the goal conjunction here (its conclusion becomes `goal`).
    let hbt = Thm::assume(oc_t.clone())?;
    let ct = cond_true(&opt_ns_t(), &a_br, &none_br)?; // cond T A none = A
    let parse_eq_a = parse_red.clone().rewrite(&hbt)?.trans(ct)?; // parse s = A
    let some_eq = h.clone().sym()?.trans(parse_eq_a)?; // some (pair v rest) = some (pair val sp_rest)
    let pair_eq = some_inj_raw(&ns_t(), &vr_pair, &a_payload)?.imp_elim(some_eq)?; // pair v rest = pair val sp_rest
    let vr_eq = pair_inj_raw(&nat_t(), &str_t(), &v, &rest, &val, &sp_rest)?.imp_elim(pair_eq)?;
    let v_eq = vr_eq.clone().and_elim_l()?; // v = val = value consumed
    let rest_eq = vr_eq.and_elim_r()?.trans(cs_eq)?; // rest = sp_rest = CS

    // a1: s = cat CF rest (from span_cat, then CS ← rest).
    let p1 = span_cat(is_digit)?
        .all_elim(s.clone())? // cat CF CS = s
        .sym()? // s = cat CF CS
        .rewrite(&rest_eq.clone().sym()?)?; // CS → rest
    // a2: list_all is_digit CF (from prefix_all_digits).
    let p2 = prefix_all_digits(is_digit)?
        .all_elim(s.clone())?
        .eqt_elim()?;
    // a3: head_is_digit is_digit rest = F (from suffix_maximal, then CS ← rest).
    let p3 = suffix_maximal(is_digit)?
        .all_elim(s.clone())? // head_is_digit is_digit CS = F
        .rewrite(&rest_eq.clone().sym()?)?; // CS → rest
    // a4: v = value CF (bridge the folded `value consumed` to `value CF`).
    let p4 = v_eq.trans(cf_eq.clone().cong_arg(value.clone())?)?; // v = value consumed = value CF
    let conj = p1.and_intro(p2.and_intro(p3.and_intro(p4)?)?)?; // {hyp, OC=T} ⊢ goal
    let goal = conj.concl().clone();
    let branch_t = conj.imp_intro(&oc_t)?;

    // OC = F: parse s = none, contradicting some (pair v rest) = none.
    let branch_f = {
        let hbf = Thm::assume(oc_f.clone())?;
        let cf = cond_false(&opt_ns_t(), &a_br, &none_br)?; // cond F A none = none
        let parse_eq_none = parse_red.clone().rewrite(&hbf)?.trans(cf)?; // parse s = none
        let some_eq_none = h.clone().sym()?.trans(parse_eq_none)?; // some (pair v rest) = none
        let f = some_ne_none(&ns_t(), &vr_pair)?.not_elim(some_eq_none)?; // ⊢ F
        f.false_elim(goal.clone())?.imp_intro(&oc_f)?
    };

    let combined = bool_cases()
        .all_elim(oc.clone())?
        .or_elim(branch_t, branch_f)?; // {hyp} ⊢ goal
    combined
        .imp_intro(&hyp_term)?
        .all_intro("rest", str_t())?
        .all_intro("v", nat_t())?
        .all_intro("s", str_t())
}

/// Concrete parser evaluators (test-only), shared with the `init::int_parse`
/// test battery. Compute `⊢ parse … <literal> = <result>` for a concrete
/// input by chaining the (genuine) clause lemmas — no oracle.
#[cfg(test)]
pub(crate) mod ceval {
    use super::*;
    use crate::init::char::{char_lit, code_mk};
    use crate::init::cond::collapse_conds;
    use crate::init::list::{head_cons, head_nil};
    use crate::init::logic::prop_eq;
    use crate::init::option::{case_none, case_some};
    use crate::init::prod::{fst_pair, snd_pair};

    /// `char.mk k : char`.
    pub(crate) fn ch(k: u64) -> Term {
        char_lit(k)
    }

    /// A `string` literal from ASCII bytes (each a `char.mk`).
    pub(crate) fn s(bytes: &[u8]) -> Term {
        let mut t = nil_c();
        for &b in bytes.iter().rev() {
            t = cons_c(ch(b as u64), t);
        }
        t
    }

    /// `⊢ char_code (char.mk k) = k`, as a rewrite rule.
    pub(crate) fn code_rw(k: u64) -> Thm {
        code_mk(&lit(k)).unwrap()
    }

    /// The `(a, b)` of a concrete `pair a b` term.
    pub(crate) fn pair_parts(t: &Term) -> (Term, Term) {
        let (fa, b) = t.as_app().unwrap();
        let (_pair, a) = fa.as_app().unwrap();
        (a.clone(), b.clone())
    }

    /// `⊢ t = <T|F>` and the bool — decide a closed bool term whose only
    /// opacity is `char.code (char.mk k)` for the given `ks`. Reduces (β +
    /// `nat.le` folding), rewrites the codepoints, then decides the residual
    /// `∧`/`∨` combination with `prop_eq`.
    pub(crate) fn decide(t: &Term, ks: &[u64]) -> (Thm, bool) {
        let mut red = Thm::refl(t.clone())
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        for &k in ks {
            red = red.rhs_conv(|x| x.rw_all(&code_rw(k))).unwrap();
        }
        let red = red.rhs_conv(|x| x.reduce()).unwrap();
        let combo = rhs(&red);
        match prop_eq(&combo, &covalence_hol_eval::mk_bool(true)) {
            Ok(tt) => (red.trans(tt).unwrap(), true),
            Err(_) => {
                let ff = prop_eq(&combo, &covalence_hol_eval::mk_bool(false)).unwrap();
                (red.trans(ff).unwrap(), false)
            }
        }
    }

    /// `⊢ t = <nat literal>` — fold a closed `nat` term whose only opacity is
    /// `char.code (char.mk k)`, and whose head may be a literal-conditioned
    /// `cond` (the hex `digit_val`): rewrite the codepoint, fold arithmetic,
    /// collapse the head `cond`, fold again.
    pub(crate) fn eval_digit(t: &Term, k: u64) -> Thm {
        let r0 = Thm::refl(t.clone())
            .unwrap()
            .rhs_conv(|x| x.rw_all(&code_rw(k)))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let coll = collapse_conds(&rhs(&r0)).unwrap();
        r0.trans(coll).unwrap().rhs_conv(|x| x.reduce()).unwrap()
    }

    /// `⊢ go digit_val R (s bytes) acc = <nat literal>` (the left-fold value),
    /// for a concrete all-digit `bytes` and literal `acc`.
    pub(crate) fn eval_go(dv: &Term, r: &Term, bytes: &[u8], acc: &Term) -> Thm {
        if bytes.is_empty() {
            return go_nil(dv, r, acc).unwrap();
        }
        let k = bytes[0] as u64;
        let cs = s(&bytes[1..]);
        let step = go_cons(dv, r, &ch(k), &cs)
            .unwrap()
            .all_elim(acc.clone())
            .unwrap();
        let arg = rhs(&step).as_app().unwrap().1.clone(); // acc·R + dv c
        // Fold `dv c` (a `nat.sub`, or a head-`cond` for hex) to a literal in
        // isolation, then rewrite it into `arg` and fold the arithmetic
        // (`collapse_conds` fires only on a head `cond`, not one nested under
        // `+`, so the digit value must be collapsed on its own first).
        let dvc = arg.as_app().unwrap().1.clone();
        let dvc_eq = eval_digit(&dvc, k);
        let arg_lit = Thm::refl(arg)
            .unwrap()
            .rhs_conv(|x| x.rw_all(&dvc_eq))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let new_acc = rhs(&arg_lit);
        let cong = arg_lit.cong_arg(Term::app(go(dv, r), cs.clone())).unwrap();
        step.trans(cong)
            .unwrap()
            .trans(eval_go(dv, r, &bytes[1..], &new_acc))
            .unwrap()
    }

    /// `⊢ bin_go (s bytes) acc = <bit tree>` — the binary value in NP1
    /// `bit0`/`bit1` normal form, for concrete `bytes` and a bit-tree `acc`.
    pub(crate) fn eval_bin_go(bytes: &[u8], acc: &Term) -> Thm {
        if bytes.is_empty() {
            return bin_go_nil(acc).unwrap();
        }
        let k = bytes[0] as u64;
        let cs = s(&bytes[1..]);
        let step = bin_go_cons(&ch(k), &cs, acc).unwrap();
        let arg = rhs(&step).as_app().unwrap().1.clone(); // cond (is_one c) (bit1 acc) (bit0 acc)
        let arg_red = Thm::refl(arg)
            .unwrap()
            .rhs_conv(|x| x.rw_all(&code_rw(k)))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let coll = collapse_conds(&rhs(&arg_red)).unwrap();
        let arg_eq = arg_red.trans(coll).unwrap(); // arg = bit0/bit1 acc
        let new_acc = rhs(&arg_eq);
        let cong = arg_eq.cong_arg(Term::app(bin_go(), cs.clone())).unwrap();
        step.trans(cong)
            .unwrap()
            .trans(eval_bin_go(&bytes[1..], &new_acc))
            .unwrap()
    }

    /// `⊢ span_digits is_digit (s bytes) = pair <prefix> <rest>` — the maximal
    /// digit split, computed for a concrete `bytes`.
    pub(crate) fn eval_span(is_digit: &Term, bytes: &[u8]) -> Thm {
        if bytes.is_empty() {
            return span_nil(is_digit).unwrap();
        }
        let k = bytes[0] as u64;
        let c = ch(k);
        let cs = s(&bytes[1..]);
        let general = span_cons(is_digit, &c, &cs).unwrap();
        let cond_c = rhs(&Term::app(is_digit.clone(), c.clone()).reduce().unwrap());
        let (cc_eq, is_dig) = decide(&cond_c, &[k]);
        let resolved = general.rewrite(&cc_eq).unwrap();
        let p = fst_ss(span_app(is_digit, &cs));
        let r = snd_ss(span_app(is_digit, &cs));
        let dig = pair_ss(cons_c(c.clone(), p.clone()), r.clone());
        let nondig = pair_ss(nil_c(), cons_c(c.clone(), cat(p.clone(), r.clone())));
        if is_dig {
            let ct = cond_true(&ss_t(), &dig, &nondig).unwrap();
            let span_eq = resolved.trans(ct).unwrap(); // = pair (cons c (fst(span cs))) (snd(span cs))
            let rec = eval_span(is_digit, &bytes[1..]); // span cs = pair pre rest
            let (pre_t, rest_t) = pair_parts(&rhs(&rec));
            let fpre = rec
                .clone()
                .cong_arg(fst(str_t(), str_t()))
                .unwrap()
                .trans(fst_pair(&str_t(), &str_t(), &pre_t, &rest_t).unwrap())
                .unwrap(); // fst(span cs) = pre
            let rrest = rec
                .cong_arg(snd(str_t(), str_t()))
                .unwrap()
                .trans(snd_pair(&str_t(), &str_t(), &pre_t, &rest_t).unwrap())
                .unwrap(); // snd(span cs) = rest
            span_eq
                .rhs_conv(|x| x.rw_all(&fpre))
                .unwrap()
                .rhs_conv(|x| x.rw_all(&rrest))
                .unwrap()
        } else {
            let cf = cond_false(&ss_t(), &dig, &nondig).unwrap();
            let span_eq = resolved.trans(cf).unwrap(); // = pair nil (cons c (cat (fst(span cs)) (snd(span cs))))
            // Reconstruct `cat (fst(span cs)) (snd(span cs)) = cs` for the
            // concrete tail (span_cat holds generically, but its `beta_nf`d
            // `span_step` no longer matches this term's; rebuild by recursion).
            let rec = eval_span(is_digit, &bytes[1..]); // span cs = pair pre' rest'
            let (pre_t, rest_t) = pair_parts(&rhs(&rec));
            let fpre = rec
                .clone()
                .cong_arg(fst(str_t(), str_t()))
                .unwrap()
                .trans(fst_pair(&str_t(), &str_t(), &pre_t, &rest_t).unwrap())
                .unwrap();
            let rrest = rec
                .cong_arg(snd(str_t(), str_t()))
                .unwrap()
                .trans(snd_pair(&str_t(), &str_t(), &pre_t, &rest_t).unwrap())
                .unwrap();
            let cat_eq = cat_cong(&fpre, &rrest).unwrap(); // cat(fst(span cs))(snd(span cs)) = cat pre' rest'
            let recon = cat_eq.trans(eval_cat(&pre_t, &rest_t)).unwrap(); // = cs
            span_eq.rhs_conv(|x| x.rw_all(&recon)).unwrap() // = pair nil (cons c cs)
        }
    }

    /// `⊢ list_cat a b = <concrete list>` for a concrete char-list `a`, by the
    /// `cat_nil`/`cat_cons` clauses (both `a`, `b` free of nested `list_cat`).
    pub(crate) fn eval_cat(a: &Term, b: &Term) -> Thm {
        match a
            .as_app()
            .and_then(|(f, tl)| f.as_app().map(|(_, h)| (h.clone(), tl.clone())))
        {
            Some((x, xs)) => {
                let cc = cat_cons(&char_t(), &x, &xs, b).unwrap(); // cat (cons x xs) b = cons x (cat xs b)
                let cong = eval_cat(&xs, b)
                    .cong_arg(Term::app(cons(char_t()), x))
                    .unwrap();
                cc.trans(cong).unwrap()
            }
            None => cat_nil(&char_t(), b).unwrap(), // cat nil b = b
        }
    }

    /// `⊢ parse_nat is_digit value (s input) = <result>` — the full parser,
    /// computed for concrete `input`. `pre` is the (Rust-known) maximal digit
    /// prefix. `value_eq(prefix_term)` supplies `⊢ value <prefix_term> =
    /// <val>` (radix-specific).
    pub(crate) fn eval_parse(
        is_digit: &Term,
        value: &Term,
        input: &[u8],
        pre: &[u8],
        value_of: &dyn Fn(&[u8]) -> Thm,
    ) -> Thm {
        let l = s(input);
        let red = parse_app(is_digit, value, &l).reduce().unwrap();
        let oc_term = head_is_digit(is_digit, &l);

        if input.is_empty() {
            // head nil = none ; option_case false is_digit none = false ; cond F → none.
            let hn = head_nil(&char_t()).unwrap();
            let cn = case_none(
                &char_t(),
                &bool_t(),
                &covalence_hol_eval::mk_bool(false),
                is_digit,
            )
            .unwrap();
            let oc_eq = Thm::refl(oc_term)
                .unwrap()
                .rhs_conv(|x| x.rw_all(&hn))
                .unwrap()
                .trans(cn)
                .unwrap();
            return finish_parse(red, oc_eq, false, is_digit, input, pre, value_of);
        }

        let k0 = input[0] as u64;
        let c0 = ch(k0);
        let cs0 = s(&input[1..]);
        let hc = head_cons(&char_t(), &c0, &cs0).unwrap(); // head l = some c0
        let cse = case_some(
            &char_t(),
            &bool_t(),
            &covalence_hol_eval::mk_bool(false),
            is_digit,
            &c0,
        )
        .unwrap(); // option_case false is_digit (some c0) = is_digit c0
        let (id_eq, is_dig) = decide(&Term::app(is_digit.clone(), c0.clone()), &[k0]);
        let oc_eq = Thm::refl(oc_term)
            .unwrap()
            .rhs_conv(|x| x.rw_all(&hc))
            .unwrap()
            .trans(cse)
            .unwrap()
            .trans(id_eq)
            .unwrap(); // OC = <bool>
        finish_parse(red, oc_eq, is_dig, is_digit, input, pre, value_of)
    }

    /// Resolve `parse l = cond OC TRUE none` given `oc_eq : ⊢ OC = <bool>`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn finish_parse(
        red: Thm,
        oc_eq: Thm,
        is_dig: bool,
        is_digit: &Term,
        input: &[u8],
        pre: &[u8],
        value_of: &dyn Fn(&[u8]) -> Thm,
    ) -> Thm {
        let resolved = red.rhs_conv(|x| x.rw_all(&oc_eq)).unwrap(); // parse l = cond bool TRUE none
        let true_br = rhs(&resolved)
            .as_app()
            .unwrap()
            .0
            .as_app()
            .unwrap()
            .1
            .clone();
        let none_br = rhs(&resolved).as_app().unwrap().1.clone();
        if !is_dig {
            let cf = cond_false(&opt_ns_t(), &true_br, &none_br).unwrap();
            return resolved.trans(cf).unwrap(); // = none
        }
        let ct = cond_true(&opt_ns_t(), &true_br, &none_br).unwrap();
        let step = resolved.trans(ct).unwrap(); // parse l = some (pair (value (fst (span l))) (snd (span l)))

        let span_eq = eval_span(is_digit, input); // span l = pair pre rest
        let (pre_t, rest_t) = pair_parts(&rhs(&span_eq));
        let fpre = span_eq
            .clone()
            .cong_arg(fst(str_t(), str_t()))
            .unwrap()
            .trans(fst_pair(&str_t(), &str_t(), &pre_t, &rest_t).unwrap())
            .unwrap(); // fst(span l) = pre
        let rrest = span_eq
            .cong_arg(snd(str_t(), str_t()))
            .unwrap()
            .trans(snd_pair(&str_t(), &str_t(), &pre_t, &rest_t).unwrap())
            .unwrap(); // snd(span l) = rest
        let val_eq = value_of(pre); // value (s pre) = <val>  (after fst rewrite this matches)
        step.rhs_conv(|x| x.rw_all(&fpre))
            .unwrap()
            .rhs_conv(|x| x.rw_all(&val_eq))
            .unwrap()
            .rhs_conv(|x| x.rw_all(&rrest))
            .unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::ceval::*;
    use super::*;

    // ---- genuineness of the general theorems ----

    #[test]
    fn span_cat_is_genuine() {
        for p in [
            is_digit_bin(),
            is_digit_oct(),
            is_digit_dec(),
            is_digit_hex(),
        ] {
            let thm = span_cat(&p).unwrap();
            assert!(thm.hyps().is_empty(), "span_cat must be axiom-free");
            assert!(thm.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn go_clauses_are_genuine() {
        let dv = digit_val_dec();
        let r = lit(10);
        let acc = Term::free("a", nat_t());
        let cs = Term::free("cs", str_t());
        let c = ch(b'5' as u64);
        assert!(go_nil(&dv, &r, &acc).unwrap().hyps().is_empty());
        assert!(go_cons(&dv, &r, &c, &cs).unwrap().hyps().is_empty());
    }

    // ---- concrete value computations ----

    #[test]
    fn decimal_value_computes() {
        // "42" decimal = 42, via the left-fold clauses.
        let dv = digit_val_dec();
        let v = eval_go(&dv, &lit(10), b"42", &lit(0));
        assert!(v.hyps().is_empty());
        assert_eq!(rhs(&v), lit(42));
    }

    #[test]
    fn binary_value_in_normal_form() {
        // "101" binary = 0b101 = bit1 (bit0 (bit1 0)) — the NP1 log-depth
        // normal form (= 5).
        let v = eval_bin_go(b"101", &lit(0));
        assert!(v.hyps().is_empty());
        assert_eq!(rhs(&v), bit1(bit0(bit1(lit(0)))));
    }

    // ---- the required end-to-end parse examples ----

    #[test]
    fn parse_decimal_42x() {
        // parse "42x" decimal = (42, "x").
        let dv = digit_val_dec();
        let value = nat_of_digits(&dv, &lit(10));
        let dvc = dv.clone();
        let thm = eval_parse(&is_digit_dec(), &value, b"42x", b"42", &move |pre| {
            eval_go(&dvc, &lit(10), pre, &lit(0)) // ⊢ go (s pre) 0 = <val>
        });
        assert!(thm.hyps().is_empty(), "parse must be oracle-free");
        let payload = rhs(&thm).as_app().unwrap().1.clone(); // pair 42 "x"
        let (v, rest) = pair_parts(&payload);
        assert_eq!(v, lit(42));
        assert_eq!(rest, s(b"x"));
    }

    #[test]
    fn parse_octal_777() {
        // parse "777" octal = (511, "").
        let dv = digit_val_dec();
        let value = nat_of_digits(&dv, &lit(8));
        let dvc = dv.clone();
        let thm = eval_parse(&is_digit_oct(), &value, b"777", b"777", &move |pre| {
            eval_go(&dvc, &lit(8), pre, &lit(0))
        });
        assert!(thm.hyps().is_empty());
        let (v, rest) = pair_parts(&rhs(&thm).as_app().unwrap().1.clone());
        assert_eq!(v, lit(0o777)); // 511
        assert_eq!(rest, s(b""));
    }

    #[test]
    fn parse_hex_ff_space() {
        // parse "ff " hex = (255, " ").
        let dv = digit_val_hex();
        let value = nat_of_digits(&dv, &lit(16));
        let dvc = dv.clone();
        let thm = eval_parse(&is_digit_hex(), &value, b"ff ", b"ff", &move |pre| {
            eval_go(&dvc, &lit(16), pre, &lit(0))
        });
        assert!(thm.hyps().is_empty());
        let (v, rest) = pair_parts(&rhs(&thm).as_app().unwrap().1.clone());
        assert_eq!(v, lit(255));
        assert_eq!(rest, s(b" "));
    }

    #[test]
    fn parse_binary_101_normal_form() {
        // parse "101" binary = (0b101, "") — value in NP1 normal form.
        let value = nat_of_bin_digits();
        let thm = eval_parse(&is_digit_bin(), &value, b"101", b"101", &move |pre| {
            eval_bin_go(pre, &lit(0))
        });
        assert!(thm.hyps().is_empty());
        let (v, rest) = pair_parts(&rhs(&thm).as_app().unwrap().1.clone());
        assert_eq!(v, bit1(bit0(bit1(lit(0)))));
        assert_eq!(rest, s(b""));
    }

    #[test]
    fn parse_none_on_empty_and_nondigit() {
        // Empty and no-leading-digit both parse to `none`.
        let dv = digit_val_dec();
        let value = nat_of_digits(&dv, &lit(10));
        let nope = |input: &[u8]| {
            eval_parse(&is_digit_dec(), &value, input, b"", &|_pre| {
                unreachable!("value not evaluated on the `none` path")
            })
        };
        for input in [b"".as_slice(), b"x".as_slice(), b" 12".as_slice()] {
            let thm = nope(input);
            assert!(thm.hyps().is_empty());
            assert_eq!(rhs(&thm), none(ns_t()), "parse {input:?} = none");
        }
    }

    // ---- `list_all` + the universal parser-correctness theorem ----

    /// The four radix configurations as `(is_digit, value)` pairs.
    fn configs() -> Vec<(Term, Term)> {
        vec![
            (is_digit_bin(), nat_of_bin_digits()),
            (is_digit_oct(), nat_of_digits(&digit_val_dec(), &lit(8))),
            (is_digit_dec(), nat_of_digits(&digit_val_dec(), &lit(10))),
            (is_digit_hex(), nat_of_digits(&digit_val_hex(), &lit(16))),
        ]
    }

    #[test]
    fn list_all_clauses_are_genuine() {
        let p = is_digit_dec();
        let x = ch(b'5' as u64);
        let xs = Term::free("xs", str_t());
        let an = all_nil(&char_t(), &p).unwrap();
        assert!(an.hyps().is_empty());
        let (l, r) = an.concl().as_eq().unwrap();
        assert_eq!(l, &all_app(&char_t(), &p, &nil_c()));
        assert_eq!(r, &covalence_hol_eval::mk_bool(true));

        let ac = all_cons(&char_t(), &p, &x, &xs).unwrap();
        assert!(ac.hyps().is_empty());
        let (l, r) = ac.concl().as_eq().unwrap();
        assert_eq!(l, &all_app(&char_t(), &p, &cons_c(x.clone(), xs.clone())));
        // rhs = (p x ∧ list_all p xs) with `p x` un-reduced.
        let expect_r = band(Term::app(p.clone(), x.clone()), all_app(&char_t(), &p, &xs));
        assert_eq!(r, &expect_r);
    }

    #[test]
    fn prefix_all_digits_is_genuine() {
        for (is_digit, _) in configs() {
            let thm = prefix_all_digits(&is_digit).unwrap();
            assert!(
                thm.hyps().is_empty(),
                "prefix_all_digits must be axiom-free"
            );
            assert!(thm.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn suffix_maximal_is_genuine() {
        for (is_digit, _) in configs() {
            let thm = suffix_maximal(&is_digit).unwrap();
            assert!(thm.hyps().is_empty(), "suffix_maximal must be axiom-free");
            assert!(thm.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn parse_nat_correct_is_genuine() {
        for (is_digit, value) in configs() {
            let thm = parse_nat_correct(&is_digit, &value).unwrap();
            assert!(
                thm.hyps().is_empty(),
                "parse_nat_correct must be hypothesis-free"
            );
            assert!(thm.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn parse_nat_correct_applied_to_a_concrete_input() {
        // Instantiate the universal decimal theorem at parse "42x" = (42, "x").
        // `imp_elim` succeeds only if the concrete parser output matches the
        // theorem's hypothesis exactly, so this ties the spec to computation.
        let value = nat_of_digits(&digit_val_dec(), &lit(10));
        let corr = parse_nat_correct(&is_digit_dec(), &value).unwrap();
        let inst = corr
            .all_elim(s(b"42x"))
            .unwrap()
            .all_elim(lit(42))
            .unwrap()
            .all_elim(s(b"x"))
            .unwrap();
        let dvc = digit_val_dec();
        let concrete = eval_parse(&is_digit_dec(), &value, b"42x", b"42", &move |pre| {
            eval_go(&dvc, &lit(10), pre, &lit(0))
        });
        let facts = inst.imp_elim(concrete).unwrap();
        assert!(facts.hyps().is_empty(), "derived facts must be oracle-free");
        // The spec is a 4-way conjunction (partition ∧ all-digits ∧ maximal ∧ value).
        assert_eq!(facts.into_conjuncts().len(), 4);
    }
}
