//! `int_parse` — **signed integer parsing** (stage NP3/IP2): an optional sign
//! (`'-'` / `'+'`) followed by a `nat` in any radix, lifted to `int`.
//!
//! [`parse_int_gen`] `(is_digit, value) : string → option (int × string)` reads
//! an optional leading sign character and then a maximal digit prefix (via NP2's
//! [`crate::init::nat_parse::parse_nat`]), lifting the parsed `nat` to an `int`:
//!
//! - `'-'` (code 45) ↦ `int_neg (nat_to_int n)` (negative),
//! - `'+'` (code 43) or no sign ↦ `nat_to_int n` (positive).
//!
//! It returns `some (value, remaining-suffix)` when the digit run after the
//! (optional) sign is non-empty, else `none`. `nat_to_int : nat → int` is the
//! `iter[int] n intSucc 0` embedding and `int_neg` the ring negation, so the
//! whole thing reduces to an `int` literal on concrete input. The four public
//! radices ([`parse_int_bin`] / [`parse_int_oct`] / [`parse_int`] (decimal) /
//! [`parse_int_hex`]) instantiate the generic parser with NP2's radix configs.
//!
//! ## Edge conventions (decided + tested)
//!
//! - **Sign with no following digit ⟹ `none`.** `"-"`, `"+"`, `"-x"` all parse
//!   to `none`: the inner `parseNat` on the (post-sign) run is `none`, and
//!   [`lift_none`] maps `none ↦ none` (there is no bare-sign integer).
//! - **Leading `'+'` is allowed** and denotes a positive integer (`"+7" ↦ 7`).
//! - **`"-0"` ⟹ `int 0`.** The value is `int_neg (nat_to_int 0)`, which is the
//!   integer `0` (negation fixes zero); no separate "negative zero".
//! - The parser is **greedy / maximal**: it consumes the longest digit run and
//!   stops at the first non-digit (`head_is_digit is_digit rest = F`).
//!
//! ## What is proved
//!
//! - **Sign-lift lemmas** ([`lift_pos_some`] / [`lift_neg_some`] /
//!   [`lift_none`]) — how a `nat`-parse result maps to the signed `int` result.
//! - **Sign selection** ([`select_minus`] / [`select_plus`] / [`select_bare`])
//!   — which leading character fires which branch. The nested `cond`s are
//!   resolved head-first via [`crate::init::cond::cond_true`] /
//!   [`crate::init::cond::cond_false`] (which δ-unfold only the head `cond` and
//!   leave the redex-containing branches verbatim), so the old "`cond_true`'s
//!   inner `reduce` ε-ifies a nested `cond`" blocker does not arise.
//! - **Forward composition** ([`parse_int_neg`] / [`parse_int_pos`] /
//!   [`parse_int_bare`]) — a `nat`-parse `some` result lifts to the signed
//!   `int` result on the corresponding leading character.
//! - **[`parse_int_correct`]** — the full, hypothesis-free, radix-generic
//!   correctness theorem: a successful `parse_int_gen` result determines, per
//!   leading-character class, the partition of the string into a consumed digit
//!   run and the returned rest, that the run is all digits, that the rest does
//!   not start with a digit (maximality), and that the value is the signed
//!   magnitude (`± nat_to_int (value consumed)`).
//! - **[`sign_reconstruct`]** — the string-level bridge `head_is k s = T ⟹
//!   ∃c. cons c (tail s) = s`, giving the full `s = sign_str ++ consumed ++
//!   rest` identity from a sign case's `tail s = consumed ++ rest`.

use crate::init::char::char_ty;
use crate::init::cond::{cond_false, cond_true};
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::exists_elim;
use crate::init::logic::truth;
use crate::init::nat_parse::{
    digit_val_dec, digit_val_hex, is_digit_bin, is_digit_dec, is_digit_hex, is_digit_oct,
    nat_of_bin_digits, nat_of_digits, parse_nat, parse_nat_correct,
};
use crate::init::option::{case_none, case_some, option_cases, some_inj, some_ne_none};
use crate::init::prod::{fst_pair, pair_inj, snd_pair, surjective_pairing};
use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{
    char_code, cond, fst, head, int_neg, nat_le, nat_to_int, none, option_case, pair, snd, some,
    tail,
};
use covalence_hol_eval::derived::DerivedRules;

// ============================================================================
// Types.
// ============================================================================

fn char_t() -> Type {
    char_ty()
}

fn int_t() -> Type {
    Type::int()
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

/// `nat × string` — the NP2 nat-parse payload.
fn ns_t() -> Type {
    defs::prod(nat_t(), str_t())
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

/// `int_neg (nat_to_int n)`.
fn neg_wrap(n: Term) -> Term {
    neg(to_int(n))
}

/// `fst p : nat` for `p : nat × string`.
fn fst_ns(p: Term) -> Term {
    Term::app(fst(nat_t(), str_t()), p)
}

/// `snd p : string` for `p : nat × string`.
fn snd_ns(p: Term) -> Term {
    Term::app(snd(nat_t(), str_t()), p)
}

/// `pair n s : nat × string`.
fn pair_ns(n: Term, s: Term) -> Term {
    Term::app(Term::app(pair(nat_t(), str_t()), n), s)
}

/// `some p : option (nat × string)`.
fn some_ns(p: Term) -> Term {
    Term::app(some(ns_t()), p)
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

/// The RHS of an equational theorem.
fn rhs_of(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::int_parse: expected an equation")
        .1
        .clone()
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
// The parser (radix-generic).
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

/// `parse_nat is_digit value t : option (nat × string)` applied.
fn parse_nat_app(is_digit: &Term, value: &Term, t: &Term) -> Term {
    Term::app(parse_nat(is_digit, value), t.clone())
}

/// `cond[option (int × string)] c x y`.
fn cond_opt(c: Term, x: Term, y: Term) -> Term {
    Term::app(Term::app(Term::app(cond(opt_is_t()), c), x), y)
}

/// The `'-'` (minus) branch: `lift_signed true (parse_nat … (tail s))`.
fn minus_branch(is_digit: &Term, value: &Term, s: &Term) -> Term {
    lift_app(
        &Term::bool_lit(true),
        &parse_nat_app(is_digit, value, &tail_s(s)),
    )
}

/// The `'+'` (plus) branch: `lift_signed false (parse_nat … (tail s))`.
fn plus_branch(is_digit: &Term, value: &Term, s: &Term) -> Term {
    lift_app(
        &Term::bool_lit(false),
        &parse_nat_app(is_digit, value, &tail_s(s)),
    )
}

/// The bare (no-sign) branch: `lift_signed false (parse_nat … s)`.
fn bare_branch(is_digit: &Term, value: &Term, s: &Term) -> Term {
    lift_app(&Term::bool_lit(false), &parse_nat_app(is_digit, value, s))
}

/// The inner `cond`: `cond (head_is 43 s) (plus) (bare)`.
fn inner_cond(is_digit: &Term, value: &Term, s: &Term) -> Term {
    cond_opt(
        head_is(43, s),
        plus_branch(is_digit, value, s),
        bare_branch(is_digit, value, s),
    )
}

/// The parser body at `s`: `cond (head_is 45 s) (minus) (cond (head_is 43 s)
/// (plus) (bare))`.
fn parse_body(is_digit: &Term, value: &Term, s: &Term) -> Term {
    cond_opt(
        head_is(45, s),
        minus_branch(is_digit, value, s),
        inner_cond(is_digit, value, s),
    )
}

/// `parse_int_gen is_digit value : string → option (int × string)` — optional
/// sign then a radix-`value` `nat`, lifted to `int`. `'-'` negates, `'+'` /
/// absent stays positive.
pub fn parse_int_gen(is_digit: &Term, value: &Term) -> Term {
    let s = Term::free("s", str_t());
    lam("s", str_t(), parse_body(is_digit, value, &s))
}

/// `parseIntBin : string → option (int × string)` — value in NP1 binary normal
/// form.
pub fn parse_int_bin() -> Term {
    parse_int_gen(&is_digit_bin(), &nat_of_bin_digits())
}

/// `parseIntOct : string → option (int × string)`.
pub fn parse_int_oct() -> Term {
    parse_int_gen(&is_digit_oct(), &nat_of_digits(&digit_val_dec(), &lit(8)))
}

/// `parseInt : string → option (int × string)` — signed **decimal**.
pub fn parse_int() -> Term {
    parse_int_gen(&is_digit_dec(), &nat_of_digits(&digit_val_dec(), &lit(10)))
}

/// `parseIntHex : string → option (int × string)`.
pub fn parse_int_hex() -> Term {
    parse_int_gen(&is_digit_hex(), &nat_of_digits(&digit_val_hex(), &lit(16)))
}

// ============================================================================
// The sign-lift lemmas — how a `nat`-parse result maps to the signed result.
// ============================================================================

/// `⊢ lift_signed neg none = none` — a failed `nat` parse stays a failure.
/// Genuine (hypothesis- and oracle-free).
pub fn lift_none(neg: &Term) -> Result<Thm> {
    case_none(&ns_t(), &opt_is_t(), &none_is(), &map_step(neg))
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
    let p = pair_ns(n.clone(), suf.clone());
    // lift_signed neg (some p) = map_step neg p.
    let cs = case_some(&ns_t(), &opt_is_t(), &none_is(), &map_step(neg), &p)?;
    // β-reduce `map_step neg p`, then collapse `fst (pair n suf)`/`snd …`.
    let red = rhs_of(&cs).reduce()?; // some (pair (signed_val neg (fst p)) (snd p))
    let f = fst_pair(&nat_t(), &str_t(), n, suf)?; // fst p = n
    let s = snd_pair(&nat_t(), &str_t(), n, suf)?; // snd p = suf
    cs.trans(red)?
        .rhs_conv(|t| t.rw_all(&f))?
        .rhs_conv(|t| t.rw_all(&s))
}

/// `⊢ signed_val false n = nat_to_int n` — the positive branch of `cond`.
fn cond_signed_false(n: &Term) -> Result<Thm> {
    crate::init::cond::cond_false(&int_t(), &neg_wrap(n.clone()), &to_int(n.clone()))
}

/// `⊢ signed_val true n = int_neg (nat_to_int n)` — the negative branch.
fn cond_signed_true(n: &Term) -> Result<Thm> {
    crate::init::cond::cond_true(&int_t(), &neg_wrap(n.clone()), &to_int(n.clone()))
}

// ============================================================================
// Sign selection — which leading character fires which branch. The two nested
// `cond`s are resolved head-first via `cond_true`/`cond_false`, which δ-unfold
// only the head `cond` and leave the (redex-containing) branches verbatim.
// ============================================================================

/// `Δ ⊢ parse_int_gen is_digit value s = minus_branch`, given
/// `g : Δ ⊢ head_is 45 s = T`. Genuine relative to `Δ`.
pub fn select_minus(is_digit: &Term, value: &Term, s: &Term, g: &Thm) -> Result<Thm> {
    let beta = Thm::beta_conv(Term::app(parse_int_gen(is_digit, value), s.clone()))?;
    let m = minus_branch(is_digit, value, s);
    let inner = inner_cond(is_digit, value, s);
    let resolved = beta.rewrite(g)?; // parse s = cond T m inner
    let ct = cond_true(&opt_is_t(), &m, &inner)?;
    resolved.trans(ct)
}

/// `Δ ⊢ parse_int_gen is_digit value s = plus_branch`, given
/// `a : head_is 45 s = F` and `b : head_is 43 s = T`. Genuine relative to `Δ`.
pub fn select_plus(is_digit: &Term, value: &Term, s: &Term, a: &Thm, b: &Thm) -> Result<Thm> {
    let beta = Thm::beta_conv(Term::app(parse_int_gen(is_digit, value), s.clone()))?;
    let m = minus_branch(is_digit, value, s);
    let inner = inner_cond(is_digit, value, s);
    // head_is 45 s → F: cond F m inner = inner.
    let outer = beta
        .rewrite(a)?
        .trans(cond_false(&opt_is_t(), &m, &inner)?)?; // parse s = inner
    // inner = cond (head_is 43 s) plus bare; head_is 43 s → T: = plus.
    let p = plus_branch(is_digit, value, s);
    let bare = bare_branch(is_digit, value, s);
    outer.rewrite(b)?.trans(cond_true(&opt_is_t(), &p, &bare)?)
}

/// `Δ ⊢ parse_int_gen is_digit value s = bare_branch`, given
/// `a : head_is 45 s = F` and `b : head_is 43 s = F`. Genuine relative to `Δ`.
pub fn select_bare(is_digit: &Term, value: &Term, s: &Term, a: &Thm, b: &Thm) -> Result<Thm> {
    let beta = Thm::beta_conv(Term::app(parse_int_gen(is_digit, value), s.clone()))?;
    let m = minus_branch(is_digit, value, s);
    let inner = inner_cond(is_digit, value, s);
    let outer = beta
        .rewrite(a)?
        .trans(cond_false(&opt_is_t(), &m, &inner)?)?; // parse s = inner
    let p = plus_branch(is_digit, value, s);
    let bare = bare_branch(is_digit, value, s);
    outer.rewrite(b)?.trans(cond_false(&opt_is_t(), &p, &bare)?)
}

// ============================================================================
// Forward composition — a `nat`-parse `some` result lifts to the signed `int`
// result on the corresponding leading character.
// ============================================================================

/// `⊢ head_is 45 s = T ⟹ parse_nat is_digit value (tail s) = some (pair n suf)
///    ⟹ parse_int_gen is_digit value s = some (pair (int_neg (nat_to_int n))
///    suf)`. Genuine.
pub fn parse_int_neg(is_digit: &Term, value: &Term, s: &Term, n: &Term, suf: &Term) -> Result<Thm> {
    let g_term = head_is(45, s).equals(Term::bool_lit(true))?;
    let g = Thm::assume(g_term.clone())?;
    let sel = select_minus(is_digit, value, s, &g)?; // {g} ⊢ parse s = lift_signed true (parse_nat (tail s))
    let pn_term = parse_nat_app(is_digit, value, &tail_s(s))
        .equals(some_ns(pair_ns(n.clone(), suf.clone())))?;
    let pn = Thm::assume(pn_term.clone())?;
    let lifted = sel.rhs_conv(|t| t.rw_all(&pn))?; // {g,pn} ⊢ parse s = lift_signed true (some (pair n suf))
    lifted
        .trans(lift_neg_some(n, suf)?)?
        .imp_intro(&pn_term)?
        .imp_intro(&g_term)
}

/// `⊢ head_is 45 s = F ⟹ head_is 43 s = T ⟹
///    parse_nat is_digit value (tail s) = some (pair n suf) ⟹
///    parse_int_gen is_digit value s = some (pair (nat_to_int n) suf)`. Genuine.
pub fn parse_int_pos(is_digit: &Term, value: &Term, s: &Term, n: &Term, suf: &Term) -> Result<Thm> {
    let a_term = head_is(45, s).equals(Term::bool_lit(false))?;
    let b_term = head_is(43, s).equals(Term::bool_lit(true))?;
    let a = Thm::assume(a_term.clone())?;
    let b = Thm::assume(b_term.clone())?;
    let sel = select_plus(is_digit, value, s, &a, &b)?;
    let pn_term = parse_nat_app(is_digit, value, &tail_s(s))
        .equals(some_ns(pair_ns(n.clone(), suf.clone())))?;
    let pn = Thm::assume(pn_term.clone())?;
    let lifted = sel.rhs_conv(|t| t.rw_all(&pn))?;
    lifted
        .trans(lift_pos_some(n, suf)?)?
        .imp_intro(&pn_term)?
        .imp_intro(&b_term)?
        .imp_intro(&a_term)
}

/// `⊢ head_is 45 s = F ⟹ head_is 43 s = F ⟹
///    parse_nat is_digit value s = some (pair n suf) ⟹
///    parse_int_gen is_digit value s = some (pair (nat_to_int n) suf)`. Genuine.
pub fn parse_int_bare(
    is_digit: &Term,
    value: &Term,
    s: &Term,
    n: &Term,
    suf: &Term,
) -> Result<Thm> {
    let a_term = head_is(45, s).equals(Term::bool_lit(false))?;
    let b_term = head_is(43, s).equals(Term::bool_lit(false))?;
    let a = Thm::assume(a_term.clone())?;
    let b = Thm::assume(b_term.clone())?;
    let sel = select_bare(is_digit, value, s, &a, &b)?;
    let pn_term =
        parse_nat_app(is_digit, value, s).equals(some_ns(pair_ns(n.clone(), suf.clone())))?;
    let pn = Thm::assume(pn_term.clone())?;
    let lifted = sel.rhs_conv(|t| t.rw_all(&pn))?;
    lifted
        .trans(lift_pos_some(n, suf)?)?
        .imp_intro(&pn_term)?
        .imp_intro(&b_term)?
        .imp_intro(&a_term)
}

// ============================================================================
// String-level bridge: from a sign case's `tail s = consumed ++ rest` to the
// full `s = sign_str ++ consumed ++ rest`.
// ============================================================================

/// `⊢ head_is k s = T ⟹ (∃c. cons c (tail s) = s)` — if `s` starts with the
/// codepoint-`k` char, it is `cons (that char) (tail s)`, so `s = [sign] ++
/// tail s`. Combined with a sign case's `tail s = consumed ++ rest`, this gives
/// the full `s = sign_str ++ consumed ++ rest`. Genuine.
pub fn sign_reconstruct(k: u64, s: &Term) -> Result<Thm> {
    let g_term = head_is(k, s).equals(Term::bool_lit(true))?;
    let g = Thm::assume(g_term.clone())?;

    // Goal: ∃c. cons c (tail s) = s.
    let c = Term::free("__sr_c", char_t());
    let recon = |cc: &Term| -> Result<Term> {
        Term::app(Term::app(defs::cons(char_t()), cc.clone()), tail_s(s)).equals(s.clone())
    };
    let goal_pred = Term::abs(char_t(), subst::close(&recon(&c)?, "__sr_c"));
    let goal = recon(&c)?.exists("__sr_c", char_t())?;

    // head s = some c OR head s = none.
    let head_s = Term::app(head(char_t()), s.clone());
    let oc = option_cases(&char_t(), &head_s)?;
    let (some_ex, none_term) = split_or(oc.concl())?;

    // some branch: from head s = some c, `cons_head_tail` gives cons c (tail s)
    // = s; ∃-introduce c. The `∃`-predicate is applied **unreduced** to match
    // `exists_elim`/`exists_intro`.
    let some_branch = {
        let x = Term::free("__sr_x", char_t());
        let ex_pred = some_ex.as_app().ok_or(Error::NotAnEquation)?.1.clone();
        let px_term = Term::app(ex_pred, x.clone());
        let px = beta_reduce(Thm::assume(px_term.clone())?)?; // {px_term} ⊢ head s = some x
        let recon_x = crate::init::list::cons_head_tail(&char_t(), &x, s)?.imp_elim(px)?; // {px_term} ⊢ cons x (tail s) = s
        let at_wit = beta_expand(&goal_pred, x.clone(), recon_x)?; // ⊢ goal_pred x
        let intro = crate::init::logic::exists_intro(goal_pred.clone(), x.clone(), at_wit)?; // ∃c. cons c (tail s) = s
        let step = intro.imp_intro(&px_term)?.all_intro("__sr_x", char_t())?;
        exists_elim(Thm::assume(some_ex.clone())?, goal.clone(), step)?.imp_intro(&some_ex)?
    };

    // none branch: head s = none ⟹ head_is k s = F, contradicting g.
    let none_branch = {
        let none_asm = Thm::assume(none_term.clone())?; // head s = none
        // head_is k s = option_case false (char_is k) (head s); rewrite head s
        // → none, then `case_none` collapses to false.
        let hd_false = Thm::refl(head_is(k, s))?
            .rhs_conv(|t| t.rw_all(&none_asm))?
            .trans(case_none(
                &char_t(),
                &bool_t(),
                &Term::bool_lit(false),
                &char_is(k),
            )?)?; // head_is k s = F
        // {g} : head_is k s = T ; {none} : head_is k s = F ⟹ T = F ⟹ F.
        let tf = g.clone().sym()?.trans(hd_false)?; // {g,none} ⊢ T = F
        let ff = covalence_hol_eval::fal_from_lit(tf.eq_mp(truth())?)?; // {g,none} ⊢ F
        ff.false_elim(goal.clone())?.imp_intro(&none_term)?
    };

    oc.or_elim(some_branch, none_branch)?.imp_intro(&g_term)
}

// ============================================================================
// The full correctness theorem — hypothesis-free, radix-generic.
// ============================================================================

/// Split a `p ∨ q` conclusion term into `(p, q)`.
fn split_or(t: &Term) -> Result<(Term, Term)> {
    let (or_p, q) = t.as_app().ok_or(Error::NotAnEquation)?;
    let (_or, p) = or_p.as_app().ok_or(Error::NotAnEquation)?;
    Ok((p.clone(), q.clone()))
}

/// The shared body of a successful-parse case: given
/// `select : Δ ⊢ parse_int_gen is_digit value s = lift_signed is_neg (parse_nat
/// is_digit value sub)` and `hyp : {H} ⊢ parse_int_gen is_digit value s = some
/// (pair v rest)`, derive `{H} ∪ Δ ⊢ FACTS`, where `FACTS` is the four-way
/// conjunction (partition of `sub` ∧ all-digits ∧ maximal rest ∧ signed value).
/// `v`, `rest` are the (free) result components.
#[allow(clippy::too_many_arguments)]
fn case_facts(
    is_digit: &Term,
    value: &Term,
    sub: &Term,
    v: &Term,
    rest: &Term,
    is_neg: bool,
    select: &Thm,
    hyp: &Thm,
) -> Result<Thm> {
    let p = parse_nat_app(is_digit, value, sub); // option (nat × string)
    // {H} ∪ Δ ⊢ some (pair v rest) = lift_signed is_neg P.
    let some_eq_m = hyp.clone().sym()?.trans(select.clone())?;

    let oc = option_cases(&ns_t(), &p)?; // (∃x. P = some x) ∨ (P = none)
    let (ex_term, none_term) = split_or(oc.concl())?;

    // ---- some branch: P = some x ----
    // The `∃`-predicate must be applied **unreduced** (`(λx. P = some x) x`) to
    // match `exists_elim`'s unfolded antecedent; β-reduce for local use.
    let x = Term::free("__ip_x", ns_t());
    let ex_pred = ex_term.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let px_term = Term::app(ex_pred, x.clone());
    let px = beta_reduce(Thm::assume(px_term.clone())?)?; // {px_term} ⊢ P = some x

    let nval = fst_ns(x.clone());
    let sval = snd_ns(x.clone());
    // P = some (pair (fst x) (snd x))  (surjective pairing on x).
    let sp = surjective_pairing(&nat_t(), &str_t(), &x)?; // pair (fst x)(snd x) = x
    let p_eq_pair = px.clone().trans(sp.cong_arg(some(ns_t()))?.sym()?)?; // P = some (pair nval sval)

    // some (pair v rest) = lift_signed is_neg (some (pair nval sval)).
    let m_pair = some_eq_m.clone().rhs_conv(|t| t.rw_all(&p_eq_pair))?;
    let lift = if is_neg {
        lift_neg_some(&nval, &sval)?
    } else {
        lift_pos_some(&nval, &sval)?
    };
    let signed = if is_neg {
        neg_wrap(nval.clone())
    } else {
        to_int(nval.clone())
    };
    // some (pair v rest) = some (pair signed sval).
    let sve = m_pair.trans(lift)?;
    let pair_eq = some_inj(
        &is_t(),
        &pair_is(v.clone(), rest.clone()),
        &pair_is(signed.clone(), sval.clone()),
    )?
    .imp_elim(sve)?; // pair v rest = pair signed sval
    let vr = pair_inj(&int_t(), &str_t(), v, rest, &signed, &sval)?.imp_elim(pair_eq)?;
    let v_eq = vr.clone().and_elim_l()?; // v = signed
    let rest_eq = vr.and_elim_r()?; // rest = sval
    let sval_eq_rest = rest_eq.sym()?; // sval = rest

    // parse_nat_correct on `sub`, at (nval, sval).
    let corr = parse_nat_correct(is_digit, value)?
        .all_elim(sub.clone())?
        .all_elim(nval.clone())?
        .all_elim(sval.clone())?
        .imp_elim(p_eq_pair)?; // {px} ⊢ conj4
    let cs = corr.into_conjuncts();
    // f1: sub = cat CF rest ; f2: list_all is_digit CF ; f3: head_is_digit rest = F.
    let f1 = cs[0].clone().rewrite(&sval_eq_rest)?;
    let f2 = cs[1].clone();
    let f3 = cs[2].clone().rewrite(&sval_eq_rest)?;
    // f4: v = signed(value CF)  (rewrite nval → value CF via cs[3]: nval = value CF).
    let f4 = v_eq.rewrite(&cs[3])?;
    let facts = f1.and_intro(f2.and_intro(f3.and_intro(f4)?)?)?; // {H,Δ,px} ⊢ FACTS
    let goal = facts.concl().clone();

    let some_step = facts.imp_intro(&px_term)?.all_intro("__ip_x", ns_t())?;
    let some_thm =
        exists_elim(Thm::assume(ex_term.clone())?, goal.clone(), some_step)?.imp_intro(&ex_term)?;

    // ---- none branch: P = none ⟹ contradiction ----
    let none_asm = Thm::assume(none_term.clone())?;
    let m_none = some_eq_m.rhs_conv(|t| t.rw_all(&none_asm))?; // some (pair v rest) = lift_signed is_neg none
    let contra = m_none.trans(lift_none(&Term::bool_lit(is_neg))?)?; // some (pair v rest) = none
    let ff = some_ne_none(&is_t(), &pair_is(v.clone(), rest.clone()))?.not_elim(contra)?; // ⊢ F
    let none_thm = ff.false_elim(goal.clone())?.imp_intro(&none_term)?;

    oc.or_elim(some_thm, none_thm) // {H} ∪ Δ ⊢ FACTS
}

/// `⊢ ∀s v rest. parse_int_gen is_digit value s = some (pair v rest) ⟹`
/// `  (head_is 45 s = T ⟹ NEG)`
/// `∧ ((head_is 45 s = F ∧ head_is 43 s = T) ⟹ POS)`
/// `∧ ((head_is 45 s = F ∧ head_is 43 s = F) ⟹ BARE)`
///
/// where, with `consumed t = fst (span_digits is_digit t)`:
///
/// - `NEG  = (tail s = cat (consumed (tail s)) rest) ∧ list_all is_digit
///   (consumed (tail s)) ∧ (head_is_digit is_digit rest = F) ∧ v = int_neg
///   (nat_to_int (value (consumed (tail s))))`,
/// - `POS  = …(tail s)… ∧ v = nat_to_int (value (consumed (tail s)))`,
/// - `BARE = (s = cat (consumed s) rest) ∧ … ∧ v = nat_to_int (value (consumed
///   s))`.
///
/// The **complete signed-parser spec**: for each leading-character class, a
/// successful parse splits the post-sign run into a consumed digit prefix and
/// the returned `rest`, the prefix is all digits, `rest` does not start with a
/// digit (maximality), and the value is the signed magnitude. Hypothesis- and
/// oracle-free, for any radix configuration `(is_digit, value)`.
///
/// (The `head_is 45/43 s = T/F` guards are exactly "`s` starts with `'-'` / with
/// `'+'` / with neither"; [`sign_reconstruct`] lifts a sign case's `tail s = …`
/// to the full `s = sign_str ++ consumed ++ rest`. The `consumed`/`value`
/// subterms appear in β-normal form, matching [`parse_nat_correct`].)
pub fn parse_int_correct(is_digit: &Term, value: &Term) -> Result<Thm> {
    let s = Term::free("s", str_t());
    let v = Term::free("v", int_t());
    let rest = Term::free("rest", str_t());
    let tail = tail_s(&s);

    let hyp_term = Term::app(parse_int_gen(is_digit, value), s.clone())
        .equals(some_is(pair_is(v.clone(), rest.clone())))?;
    let hyp = Thm::assume(hyp_term.clone())?;

    // NEG: head_is 45 s = T.
    let g_neg = head_is(45, &s).equals(Term::bool_lit(true))?;
    let neg_c = {
        let g = Thm::assume(g_neg.clone())?;
        let sel = select_minus(is_digit, value, &s, &g)?;
        case_facts(is_digit, value, &tail, &v, &rest, true, &sel, &hyp)?.imp_intro(&g_neg)?
    };

    // POS: head_is 45 s = F ∧ head_is 43 s = T.
    let g_pos = band(
        head_is(45, &s).equals(Term::bool_lit(false))?,
        head_is(43, &s).equals(Term::bool_lit(true))?,
    );
    let pos_c = {
        let gc = Thm::assume(g_pos.clone())?;
        let a = gc.clone().and_elim_l()?;
        let b = gc.and_elim_r()?;
        let sel = select_plus(is_digit, value, &s, &a, &b)?;
        case_facts(is_digit, value, &tail, &v, &rest, false, &sel, &hyp)?.imp_intro(&g_pos)?
    };

    // BARE: head_is 45 s = F ∧ head_is 43 s = F.
    let g_bare = band(
        head_is(45, &s).equals(Term::bool_lit(false))?,
        head_is(43, &s).equals(Term::bool_lit(false))?,
    );
    let bare_c = {
        let gc = Thm::assume(g_bare.clone())?;
        let a = gc.clone().and_elim_l()?;
        let b = gc.and_elim_r()?;
        let sel = select_bare(is_digit, value, &s, &a, &b)?;
        case_facts(is_digit, value, &s, &v, &rest, false, &sel, &hyp)?.imp_intro(&g_bare)?
    };

    neg_c
        .and_intro(pos_c.and_intro(bare_c)?)?
        .imp_intro(&hyp_term)?
        .all_intro("rest", str_t())?
        .all_intro("v", int_t())?
        .all_intro("s", str_t())
}

#[cfg(test)]
mod tests;
