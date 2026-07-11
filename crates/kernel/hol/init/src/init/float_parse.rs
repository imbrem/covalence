//! `float_parse` — **decimal floating-point parsing** (stage FP1) in the
//! HOL-only dialect, over `string := list char`.
//!
//! ```text
//! parseFloat : string → option (floatval × string)
//! ```
//!
//! reads IEEE-style decimal float *syntax* — an optional sign, a required
//! integer part, an optional `'.'`-fraction, and an optional `'e'`/`'E'`
//! exponent (with its own optional sign) — and returns `some (value,
//! remaining-suffix)`, or `none` when the integer part does not start with a
//! digit. It follows the `(value, remaining)` convention the landed
//! `nat`/`int`/`sexpr` parsers established
//! ([`crate::init::nat_parse`], [`crate::init::int_parse`],
//! [`crate::init::sexpr_parse`]) and reuses their digit machinery
//! (`span_digits` / `nat_of_digits` / `is_digit_dec`) verbatim.
//!
//! ## The value representation — an *exact* decimal float
//!
//! `floatval := int × int`, where a pair `(m, e)` denotes the **exact**
//! rational `m · 10ᵉ` (mantissa `m : int`, base-10 exponent `e : int`). This
//! is deliberately an *exact* structured value, not an `f64` bit pattern: a
//! parser-correctness proof wants the true mathematical value, and rounding a
//! decimal to the nearest `f64` is a *separate* concern (recorded as a
//! follow-up in `SKELETONS.md`). Every literal is representable exactly:
//!
//! | source     | mantissa `m` | exp `e` | `m · 10ᵉ` |
//! |------------|--------------|---------|-----------|
//! | `"3.14"`   | `314`        | `-2`    | `3.14`    |
//! | `"1e10"`   | `1`          | `10`    | `10¹⁰`    |
//! | `"-0.5"`   | `-5`         | `-1`    | `-0.5`    |
//! | `"2.5e-3"` | `25`         | `-4`    | `0.0025`  |
//! | `"42"`     | `42`         | `0`     | `42`      |
//!
//! ## How the parts compose
//!
//! With sign bit `neg`, integer-part value `ip : nat`, fraction digits value
//! `fr : nat` over `k` fraction digits, and signed exponent `ex : int`, the
//! [`assemble`]d value is
//!
//! ```text
//! mantissa = ±(ip · 10ᵏ + fr)      exp = ex − k
//! ```
//!
//! so `m · 10ᵉ = ±(ip · 10ᵏ + fr) · 10^(ex−k) = ±(ip + fr / 10ᵏ) · 10^ex` —
//! exactly `(int_part + frac/10ᵏ) · 10^exp`. The **sign-composition** lemmas
//! [`signed_pos`] / [`signed_neg`] and the value lemmas [`assemble_pos`] /
//! [`assemble_neg`] discharge this algebra genuinely (hypothesis- and
//! oracle-free); [`assemble`] on concrete literals reduces to a literal
//! `(int × int)` pair via the `nat`/`int` certificate path.
//!
//! ## The integer subset
//!
//! A pure integer literal is the degenerate float with no fraction and no
//! exponent: `assemble neg ip 0 0 0 = (±ip, 0)`, whose value `±ip · 10⁰ = ±ip`
//! is exactly the `int` the signed-integer parser
//! ([`crate::init::int_parse`]) yields — the "integer ⊂ float" relation
//! ([`float_of_int`], [`int_subset`]), foreshadowing the JSON int-subset
//! proof.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{
    cond, fst, head, int_neg, int_sub, int_zero, list_length, nat_add, nat_le, nat_mul, nat_pow,
    nat_to_int, none, option_case, pair, snd, some, tail,
};

use covalence_hol_eval::derived::DerivedRules;

use crate::init::char::char_ty;
use crate::init::ext::{TermExt, ThmExt};

// ============================================================================
// Types.
// ============================================================================

fn char_t() -> Type {
    char_ty()
}
fn nat_t() -> Type {
    Type::nat()
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

/// `floatval := int × int` — `(mantissa, exp10)`, denoting `mantissa · 10ᵉˣᵖ`.
fn fv_t() -> Type {
    defs::prod(int_t(), int_t())
}

/// `floatval × string` — the parse payload (value, remaining suffix).
fn payload_t() -> Type {
    defs::prod(fv_t(), str_t())
}

/// `option (floatval × string)` — the parse result.
fn opt_t() -> Type {
    defs::option(payload_t())
}

/// `string × string` — a `span_digits` result.
#[cfg(test)]
fn ss_t() -> Type {
    defs::prod(str_t(), str_t())
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
    Term::app(defs::char_code(), c.clone())
}

/// `nat_le a b : bool`.
fn le(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_le(), a), b)
}

fn band(a: Term, b: Term) -> Term {
    crate::HolLightCtx::new().mk_and(a, b)
}

fn bor(a: Term, b: Term) -> Term {
    crate::HolLightCtx::new().mk_or(a, b)
}

/// `nat_add a b`.
fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add(), a), b)
}
/// `nat_mul a b`.
fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_mul(), a), b)
}
/// `nat_pow a b`.
fn pow(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_pow(), a), b)
}
/// `nat_to_int n : int`.
fn to_int(n: Term) -> Term {
    Term::app(nat_to_int(), n)
}
/// `int_neg z : int`.
fn ineg(z: Term) -> Term {
    Term::app(int_neg(), z)
}
/// `int_sub a b : int`.
fn isub(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_sub(), a), b)
}

/// `cond[α] c x y`.
fn cond_app(ty: Type, c: Term, x: Term, y: Term) -> Term {
    Term::app(Term::app(Term::app(cond(ty), c), x), y)
}

/// `pair[α,β] a b`.
fn mk_pair(a_ty: Type, b_ty: Type, a: Term, b: Term) -> Term {
    Term::app(Term::app(pair(a_ty, b_ty), a), b)
}

/// `list_length[char] l : nat`.
fn length(l: Term) -> Term {
    Term::app(list_length(char_t()), l)
}

/// The RHS of an equational theorem (panics if not `⊢ _ = _`).
#[cfg(test)]
fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::float_parse: expected an equation")
        .1
        .clone()
}

// ============================================================================
// The exact-decimal value: `floatval := int × int` and its assembly.
// ============================================================================

/// `signed neg n : int` = `nat_to_int n` if `¬neg`, else
/// `int_neg (nat_to_int n)`.
fn signed(neg: &Term, n: Term) -> Term {
    cond_app(int_t(), neg.clone(), ineg(to_int(n.clone())), to_int(n))
}

/// `fv_mk m e : floatval` — the exact decimal float `m · 10ᵉ`.
pub fn fv_mk(m: Term, e: Term) -> Term {
    mk_pair(int_t(), int_t(), m, e)
}

/// `float_of_int z : floatval` ≡ `(z, 0)` — the degenerate float of an
/// integer (the "integer ⊂ float" embedding: `z · 10⁰ = z`).
pub fn float_of_int(z: Term) -> Term {
    fv_mk(z, int_zero())
}

/// The assembled float value `(±(ip · 10ᵏ + fr), ex − k) : floatval` — the
/// composed mantissa/exp from a parse's parts (`neg` sign, integer value `ip`,
/// fraction value `fr` over `k` digits, signed exponent `ex`). Reduces to a
/// literal `(int × int)` pair on concrete literal parts.
pub fn assemble(neg: &Term, ip: Term, fr: Term, k: Term, ex: Term) -> Term {
    let mant = signed(neg, add(mul(ip, pow(lit(10), k.clone())), fr));
    let exp = isub(ex, to_int(k));
    fv_mk(mant, exp)
}

// ============================================================================
// Sign-composition + value lemmas — the "parts compose correctly" algebra.
// ============================================================================

/// `⊢ signed false n = nat_to_int n` — the positive branch. Genuine.
pub fn signed_pos(n: &Term) -> Result<Thm> {
    crate::init::cond::cond_false(&int_t(), &ineg(to_int(n.clone())), &to_int(n.clone()))
}

/// `⊢ signed true n = int_neg (nat_to_int n)` — the negative branch. Genuine.
pub fn signed_neg(n: &Term) -> Result<Thm> {
    crate::init::cond::cond_true(&int_t(), &ineg(to_int(n.clone())), &to_int(n.clone()))
}

/// `⊢ assemble false ip fr k ex =
///     (nat_to_int (ip·10ᵏ + fr), ex − nat_to_int k)` — a **positive** parse's
/// value: the mantissa is the (unsigned) significand lifted to `int`. Genuine.
pub fn assemble_pos(ip: &Term, fr: &Term, k: &Term, ex: &Term) -> Result<Thm> {
    let neg = covalence_hol_eval::mk_bool(false);
    let n = add(mul(ip.clone(), pow(lit(10), k.clone())), fr.clone());
    let collapse = signed_pos(&n)?; // signed false n = nat_to_int n
    Thm::refl(assemble(
        &neg,
        ip.clone(),
        fr.clone(),
        k.clone(),
        ex.clone(),
    ))?
    .rhs_conv(|t| t.rw_all(&collapse))
}

/// `⊢ assemble true ip fr k ex =
///     (int_neg (nat_to_int (ip·10ᵏ + fr)), ex − nat_to_int k)` — a
/// **negative** parse negates the significand. Genuine.
pub fn assemble_neg(ip: &Term, fr: &Term, k: &Term, ex: &Term) -> Result<Thm> {
    let neg = covalence_hol_eval::mk_bool(true);
    let n = add(mul(ip.clone(), pow(lit(10), k.clone())), fr.clone());
    let collapse = signed_neg(&n)?;
    Thm::refl(assemble(
        &neg,
        ip.clone(),
        fr.clone(),
        k.clone(),
        ex.clone(),
    ))?
    .rhs_conv(|t| t.rw_all(&collapse))
}

/// `⊢ assemble neg ip 0 0 0 = (signed neg ip, 0)` — the **integer subset**:
/// a float with no fraction (`k = 0`, `fr = 0`) and no exponent (`ex = 0`) has
/// value `±ip · 10⁰ = ±ip` (exactly the `int` the signed-integer parser
/// yields), for **any** `ip`. The significand `ip·10⁰ + 0` collapses to `ip` by
/// the `nat` unit laws (`a^0 = 1`, `a·1 = a`, `a + 0 = a`), and the exponent
/// `0 − nat_to_int 0` to `int 0`. Genuine (hypothesis- and oracle-free).
pub fn int_subset(neg: &Term, ip: &Term) -> Result<Thm> {
    // ⊢ ip·10⁰ + 0 = ip, for a general `ip`.
    let sig = add(mul(ip.clone(), pow(lit(10), lit(0))), lit(0));
    let pz = crate::init::nat::pow_zero().all_elim(lit(10))?; // 10⁰ = 1
    let mo = crate::init::nat::mul_one().all_elim(ip.clone())?; // ip·1 = ip
    let az = crate::init::nat::add_zero().all_elim(ip.clone())?; // ip + 0 = ip
    let sig_eq = Thm::refl(sig)?
        .rhs_conv(|t| t.rw_all(&pz))?
        .rhs_conv(|t| t.rw_all(&mo))?
        .rhs_conv(|t| t.rw_all(&az))?;
    // ⊢ 0 − nat_to_int 0 = int 0.
    let exp_eq = isub(int_zero(), to_int(lit(0))).reduce()?;
    Thm::refl(assemble(neg, ip.clone(), lit(0), lit(0), int_zero()))?
        .rhs_conv(|t| t.rw_all(&sig_eq))?
        .rhs_conv(|t| t.rw_all(&exp_eq))
}

// ============================================================================
// The parser.
// ============================================================================

/// `λc. nat_le k (code c) ∧ nat_le (code c) k` — "the char is codepoint `k`".
fn char_is(k: u64) -> Term {
    let c = Term::free("c", char_t());
    lam(
        "c",
        char_t(),
        band(le(lit(k), code(&c)), le(code(&c), lit(k))),
    )
}

/// `option_case false (char_is k) (head s) : bool` — "the first char of `s`
/// exists and is codepoint `k`".
fn head_is(k: u64, s: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(
                option_case(char_t(), bool_t()),
                covalence_hol_eval::mk_bool(false),
            ),
            char_is(k),
        ),
        Term::app(head(char_t()), s.clone()),
    )
}

/// `option_case false is_digit_dec (head s) : bool` — "the first char of `s`
/// is a decimal digit".
fn head_is_digit(s: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(
                option_case(char_t(), bool_t()),
                covalence_hol_eval::mk_bool(false),
            ),
            crate::init::nat_parse::is_digit_dec(),
        ),
        Term::app(head(char_t()), s.clone()),
    )
}

/// `list.tail s : string`.
fn tail_s(s: &Term) -> Term {
    Term::app(tail(char_t()), s.clone())
}

/// `span_digits is_digit_dec s : string × string`.
fn span_dec(s: &Term) -> Term {
    Term::app(
        crate::init::nat_parse::span_digits(&crate::init::nat_parse::is_digit_dec()),
        s.clone(),
    )
}
fn fst_ss(p: Term) -> Term {
    Term::app(fst(str_t(), str_t()), p)
}
fn snd_ss(p: Term) -> Term {
    Term::app(snd(str_t(), str_t()), p)
}

/// `nat_of_digits digit_val_dec 10 run : nat` — the decimal value of a digit
/// run.
fn value_dec(run: Term) -> Term {
    Term::app(
        crate::init::nat_parse::nat_of_digits(&crate::init::nat_parse::digit_val_dec(), &lit(10)),
        run,
    )
}

/// `parseFloat : string → option (floatval × string)` — the decimal-float
/// reader (sign? int-part `.`frac? `[eE]`sign?exp?). `none` iff the integer
/// part does not begin with a digit.
pub fn parse_float() -> Term {
    let s = Term::free("s", str_t());

    // ---- sign ----
    let neg = head_is(45, &s); // '-'
    let is_plus = head_is(43, &s); // '+'
    let s0 = cond_app(
        str_t(),
        neg.clone(),
        tail_s(&s),
        cond_app(str_t(), is_plus, tail_s(&s), s.clone()),
    );

    // ---- integer part ----
    let sp0 = span_dec(&s0);
    let ipart = fst_ss(sp0.clone());
    let s1 = snd_ss(sp0);
    let ip = value_dec(ipart);

    // ---- fraction (optional) ----
    let has_dot = head_is(46, &s1); // '.'
    let sp1 = span_dec(&tail_s(&s1));
    let fdig = fst_ss(sp1.clone());
    let frac = value_dec(fdig.clone());
    let k = length(fdig);
    let frac_p = cond_app(nat_t(), has_dot.clone(), frac, lit(0));
    let k_p = cond_app(nat_t(), has_dot.clone(), k, lit(0));
    let s2 = cond_app(str_t(), has_dot, snd_ss(sp1), s1);

    // ---- exponent (optional) ----
    let has_e = bor(head_is(101, &s2), head_is(69, &s2)); // 'e' / 'E'
    let es = tail_s(&s2);
    let neg_e = head_is(45, &es);
    let is_plus_e = head_is(43, &es);
    let es1 = cond_app(
        str_t(),
        neg_e.clone(),
        tail_s(&es),
        cond_app(str_t(), is_plus_e, tail_s(&es), es.clone()),
    );
    let sp2 = span_dec(&es1);
    let edig = fst_ss(sp2.clone());
    let exp_nat = value_dec(edig);
    let exp_rest = snd_ss(sp2);
    let ex = cond_app(int_t(), has_e.clone(), signed(&neg_e, exp_nat), int_zero());
    let s3 = cond_app(str_t(), has_e, exp_rest, s2);

    // ---- assemble ----
    let value = assemble(&neg, ip, frac_p, k_p, ex);
    let payload = mk_pair(fv_t(), str_t(), value, s3);
    let body = cond_app(
        opt_t(),
        head_is_digit(&s0),
        Term::app(some(payload_t()), payload),
        none(payload_t()),
    );
    lam("s", str_t(), body)
}

// ============================================================================
// The `bytes` parser — the same reader over `bytes := list u8`.
// ============================================================================

/// `bytes := list u8`.
fn bytes_t() -> Type {
    defs::list(defs::u8_ty())
}
/// `floatval × bytes`.
fn payload_b_t() -> Type {
    defs::prod(fv_t(), bytes_t())
}
/// `option (floatval × bytes)`.
fn opt_b_t() -> Type {
    defs::option(payload_b_t())
}
/// `u8 × u8` — a `span_digits_bytes` result.
#[cfg(test)]
fn bb_t() -> Type {
    defs::prod(bytes_t(), bytes_t())
}

/// `u8.toNat b : nat` — a byte's unsigned value.
fn byte_val(b: &Term) -> Term {
    Term::app(defs::int_to_nat(covalence_core::IntTag::U8), b.clone())
}

/// `λb. k ≤ u8.toNat b ∧ u8.toNat b ≤ k` — "the byte is `k`".
fn byte_is(k: u64) -> Term {
    let b = Term::free("b", defs::u8_ty());
    lam(
        "b",
        defs::u8_ty(),
        band(le(lit(k), byte_val(&b)), le(byte_val(&b), lit(k))),
    )
}

/// `option_case false pred (head s) : bool` over `u8`.
fn head_sat_b(pred: &Term, s: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(
                option_case(defs::u8_ty(), bool_t()),
                covalence_hol_eval::mk_bool(false),
            ),
            pred.clone(),
        ),
        Term::app(head(defs::u8_ty()), s.clone()),
    )
}
fn head_is_b(k: u64, s: &Term) -> Term {
    head_sat_b(&byte_is(k), s)
}
fn head_is_digit_b(s: &Term) -> Term {
    head_sat_b(&crate::init::nat_parse_bytes::is_digit_byte_dec(), s)
}
fn tail_b(s: &Term) -> Term {
    Term::app(tail(defs::u8_ty()), s.clone())
}
fn span_dec_b(s: &Term) -> Term {
    Term::app(
        crate::init::nat_parse_bytes::span_digits_bytes(
            &crate::init::nat_parse_bytes::is_digit_byte_dec(),
        ),
        s.clone(),
    )
}
fn fst_bb(p: Term) -> Term {
    Term::app(fst(bytes_t(), bytes_t()), p)
}
fn snd_bb(p: Term) -> Term {
    Term::app(snd(bytes_t(), bytes_t()), p)
}
fn value_dec_b(run: Term) -> Term {
    Term::app(
        crate::init::nat_parse_bytes::nat_of_digits_bytes(
            &crate::init::nat_parse_bytes::digit_val_byte_dec(),
            &lit(10),
        ),
        run,
    )
}
fn length_b(l: Term) -> Term {
    Term::app(list_length(defs::u8_ty()), l)
}

/// `parseFloatBytes : bytes → option (floatval × bytes)` — the byte
/// counterpart of [`parse_float`], reading ASCII float syntax off a `list u8`.
pub fn parse_float_bytes() -> Term {
    let s = Term::free("s", bytes_t());
    let neg = head_is_b(45, &s);
    let is_plus = head_is_b(43, &s);
    let s0 = cond_app(
        bytes_t(),
        neg.clone(),
        tail_b(&s),
        cond_app(bytes_t(), is_plus, tail_b(&s), s.clone()),
    );

    let sp0 = span_dec_b(&s0);
    let ip = value_dec_b(fst_bb(sp0.clone()));
    let s1 = snd_bb(sp0);

    let has_dot = head_is_b(46, &s1);
    let sp1 = span_dec_b(&tail_b(&s1));
    let fdig = fst_bb(sp1.clone());
    let frac = value_dec_b(fdig.clone());
    let k = length_b(fdig);
    let frac_p = cond_app(nat_t(), has_dot.clone(), frac, lit(0));
    let k_p = cond_app(nat_t(), has_dot.clone(), k, lit(0));
    let s2 = cond_app(bytes_t(), has_dot, snd_bb(sp1), s1);

    let has_e = bor(head_is_b(101, &s2), head_is_b(69, &s2));
    let es = tail_b(&s2);
    let neg_e = head_is_b(45, &es);
    let is_plus_e = head_is_b(43, &es);
    let es1 = cond_app(
        bytes_t(),
        neg_e.clone(),
        tail_b(&es),
        cond_app(bytes_t(), is_plus_e, tail_b(&es), es.clone()),
    );
    let sp2 = span_dec_b(&es1);
    let exp_nat = value_dec_b(fst_bb(sp2.clone()));
    let exp_rest = snd_bb(sp2);
    let ex = cond_app(int_t(), has_e.clone(), signed(&neg_e, exp_nat), int_zero());
    let s3 = cond_app(bytes_t(), has_e, exp_rest, s2);

    let value = assemble(&neg, ip, frac_p, k_p, ex);
    let payload = mk_pair(fv_t(), bytes_t(), value, s3);
    let body = cond_app(
        opt_b_t(),
        head_is_digit_b(&s0),
        Term::app(some(payload_b_t()), payload),
        none(payload_b_t()),
    );
    lam("s", bytes_t(), body)
}

// ============================================================================
// Tests.
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// An `int` literal — built by reducing `nat_to_int` (resp. its negation)
    /// so no deprecated int-literal ctor appears (keeps the toHOL literal-ctor
    /// purge ratchet flat).
    fn ilit(v: i64) -> Term {
        let n = lit(v.unsigned_abs());
        let t = if v < 0 { ineg(to_int(n)) } else { to_int(n) };
        rhs(&Thm::refl(t).unwrap().rhs_conv(|x| x.reduce()).unwrap())
    }

    // ---- value layer: the "parts compose correctly" algebra ----

    #[test]
    fn parser_is_well_typed() {
        assert_eq!(
            parse_float().type_of().unwrap(),
            Type::fun(str_t(), opt_t())
        );
    }

    #[test]
    fn sign_lemmas_are_genuine() {
        let n = Term::free("n", nat_t());
        let pos = signed_pos(&n).unwrap();
        let neg = signed_neg(&n).unwrap();
        assert!(pos.hyps().is_empty() && neg.hyps().is_empty());
        assert_eq!(rhs(&pos), to_int(n.clone()));
        assert_eq!(rhs(&neg), ineg(to_int(n)));
    }

    /// `⊢ assemble neg ip fr k ex = <pair literal>` for concrete literal parts.
    /// Collapses the sign `cond` via the sign lemma, then reduces the
    /// arithmetic skeleton to an `(int × int)` literal.
    fn eval_assemble(neg: bool, ip: u64, fr: u64, k: u64, ex: i64) -> Thm {
        let n = add(mul(lit(ip), pow(lit(10), lit(k))), lit(fr));
        let sign_eq = if neg {
            signed_neg(&n).unwrap()
        } else {
            signed_pos(&n).unwrap()
        };
        Thm::refl(assemble(
            &covalence_hol_eval::mk_bool(neg),
            lit(ip),
            lit(fr),
            lit(k),
            ilit(ex),
        ))
        .unwrap()
        .rhs_conv(|t| t.rw_all(&sign_eq))
        .unwrap()
        .rhs_conv(|t| t.reduce())
        .unwrap()
    }

    #[test]
    fn concrete_values_compose() {
        // The five required literals, at the value (mantissa, exp) level.
        // "3.14"   -> (314, -2)
        let t = eval_assemble(false, 3, 14, 2, 0);
        assert!(t.hyps().is_empty());
        assert_eq!(rhs(&t), fv_mk(ilit(314), ilit(-2)));
        // "1e10"   -> (1, 10)     (no fraction: fr=0, k=0; ex=10)
        assert_eq!(
            rhs(&eval_assemble(false, 1, 0, 0, 10)),
            fv_mk(ilit(1), ilit(10))
        );
        // "-0.5"   -> (-5, -1)
        assert_eq!(
            rhs(&eval_assemble(true, 0, 5, 1, 0)),
            fv_mk(ilit(-5), ilit(-1))
        );
        // "2.5e-3" -> (25, -4)    (ip=2, fr=5, k=1, ex=-3 ⇒ exp = -3-1 = -4)
        assert_eq!(
            rhs(&eval_assemble(false, 2, 5, 1, -3)),
            fv_mk(ilit(25), ilit(-4))
        );
        // "42"     -> (42, 0)
        assert_eq!(
            rhs(&eval_assemble(false, 42, 0, 0, 0)),
            fv_mk(ilit(42), ilit(0))
        );
    }

    #[test]
    fn assemble_value_lemmas_are_genuine() {
        let ip = Term::free("ip", nat_t());
        let fr = Term::free("fr", nat_t());
        let k = Term::free("k", nat_t());
        let ex = Term::free("ex", int_t());
        let p = assemble_pos(&ip, &fr, &k, &ex).unwrap();
        let n = assemble_neg(&ip, &fr, &k, &ex).unwrap();
        assert!(p.hyps().is_empty() && n.hyps().is_empty());
        // positive mantissa is `nat_to_int (ip·10ᵏ+fr)`; negative negates it.
        let sig = add(mul(ip.clone(), pow(lit(10), k.clone())), fr.clone());
        let exp = isub(ex.clone(), to_int(k.clone()));
        assert_eq!(rhs(&p), fv_mk(to_int(sig.clone()), exp.clone()));
        assert_eq!(rhs(&n), fv_mk(ineg(to_int(sig)), exp));
    }

    #[test]
    fn integer_subset_is_genuine() {
        // A no-fraction, no-exponent float has value (signed neg ip, 0) — the
        // int the signed-integer parser yields, embedded as a float.
        let ip = Term::free("ip", nat_t());
        for neg in [false, true] {
            let t = int_subset(&covalence_hol_eval::mk_bool(neg), &ip).unwrap();
            assert!(t.hyps().is_empty());
            // value = (signed neg ip, int 0).
            assert_eq!(
                rhs(&t),
                fv_mk(
                    signed(&covalence_hol_eval::mk_bool(neg), ip.clone()),
                    int_zero()
                )
            );
        }
    }

    #[test]
    fn integer_subset_agrees_with_int_value() {
        // For "42": the float mantissa reduces to nat_to_int 42, exactly the
        // `int` value the decimal integer parser produces for the same digits.
        let t = eval_assemble(false, 42, 0, 0, 0);
        // int parser value of "42" = nat_to_int (nat_of_digits ... "42") = 42.
        let int_val = Thm::refl(to_int(lit(42)))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let mant = rhs(&t).as_app().unwrap().0.as_app().unwrap().1.clone();
        assert_eq!(mant, rhs(&int_val));
    }

    // ========================================================================
    // End-to-end concrete parser evaluation — an unfolding harness.
    //
    // No whole-term `reduce` (nested `cond`s with redex branches hit the
    // int_parse wall); instead each named sub-expression of the parser body is
    // proved equal to its concrete value and `rw_all`'d into the running
    // theorem, resolving conditionals one at a time via `cond_true`/`false`.
    // ========================================================================

    use covalence_hol_eval::derived::DerivedRules;

    use crate::init::char::{char_lit, code_mk};
    use crate::init::cond::collapse_conds;
    use crate::init::list::{head_cons, head_nil, tail_cons};
    use crate::init::list_recursion::{cat_cons, cat_nil, length_cons, length_nil};
    use crate::init::logic::prop_eq;
    use crate::init::nat_parse::{
        digit_val_dec, go_cons, go_nil, is_digit_dec, span_cons, span_nil,
    };
    use crate::init::option::{case_none, case_some};
    use crate::init::prod::{fst_pair, snd_pair};

    /// `char.mk k`.
    fn ch(k: u8) -> Term {
        char_lit(k as u64)
    }

    /// A `string` literal from ASCII bytes.
    fn s_term(bytes: &[u8]) -> Term {
        let mut t = defs::nil(char_t());
        for &b in bytes.iter().rev() {
            t = Term::app(Term::app(defs::cons(char_t()), ch(b)), t);
        }
        t
    }

    /// `⊢ char_code (char.mk k) = k`.
    fn code_rw(k: u8) -> Thm {
        code_mk(&lit(k as u64)).unwrap()
    }

    /// The `(a, b)` of a concrete `pair a b` term.
    fn pair_parts(t: &Term) -> (Term, Term) {
        let (fa, b) = t.as_app().unwrap();
        let (_pair, a) = fa.as_app().unwrap();
        (a.clone(), b.clone())
    }

    /// Decide a closed bool whose only opacity is `char.code (char.mk k)` for
    /// the given `ks`: reduce, rewrite codepoints, reduce, then `prop_eq`.
    fn decide(t: &Term, ks: &[u8]) -> (Thm, bool) {
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

    /// `⊢ list.tail (s bytes) = <tail>` for non-empty `bytes`.
    fn eval_tail(bytes: &[u8]) -> Thm {
        tail_cons(&char_t(), &ch(bytes[0]), &s_term(&bytes[1..])).unwrap()
    }

    /// `⊢ option_case F pred (head (s bytes)) = <T|F>` — "the first char
    /// satisfies `pred`". `pred` must be a `char → bool`; `pred_code` is the
    /// codepoint the first char rewrites to (for `decide`).
    fn eval_head(pred: &Term, bytes: &[u8]) -> (Thm, bool) {
        let s = s_term(bytes);
        let oc = Term::app(
            Term::app(
                Term::app(
                    option_case(char_t(), bool_t()),
                    covalence_hol_eval::mk_bool(false),
                ),
                pred.clone(),
            ),
            Term::app(head(char_t()), s),
        );
        if bytes.is_empty() {
            let hn = head_nil(&char_t()).unwrap();
            let cn = case_none(
                &char_t(),
                &bool_t(),
                &covalence_hol_eval::mk_bool(false),
                pred,
            )
            .unwrap();
            let eq = Thm::refl(oc)
                .unwrap()
                .rhs_conv(|x| x.rw_all(&hn))
                .unwrap()
                .trans(cn)
                .unwrap();
            return (eq, false);
        }
        let c0 = ch(bytes[0]);
        let cs0 = s_term(&bytes[1..]);
        let hc = head_cons(&char_t(), &c0, &cs0).unwrap();
        let cse = case_some(
            &char_t(),
            &bool_t(),
            &covalence_hol_eval::mk_bool(false),
            pred,
            &c0,
        )
        .unwrap();
        let (dec, b) = decide(&Term::app(pred.clone(), c0.clone()), &[bytes[0]]);
        let eq = Thm::refl(oc)
            .unwrap()
            .rhs_conv(|x| x.rw_all(&hc))
            .unwrap()
            .trans(cse)
            .unwrap()
            .trans(dec)
            .unwrap();
        (eq, b)
    }

    /// `⊢ list_cat a b = <concrete>` for a concrete char-list `a`.
    fn eval_cat(a: &Term, b: &Term) -> Thm {
        match a
            .as_app()
            .and_then(|(f, tl)| f.as_app().map(|(_, h)| (h.clone(), tl.clone())))
        {
            Some((x, xs)) => {
                let cc = cat_cons(&char_t(), &x, &xs, b).unwrap();
                let cong = eval_cat(&xs, b)
                    .cong_arg(Term::app(defs::cons(char_t()), x))
                    .unwrap();
                cc.trans(cong).unwrap()
            }
            None => cat_nil(&char_t(), b).unwrap(),
        }
    }

    /// `⊢ cat a1 b1 = cat a2 b2` from `⊢ a1=a2` and `⊢ b1=b2`.
    fn cat_cong(a_eq: &Thm, b_eq: &Thm) -> Thm {
        let a2 = rhs(a_eq);
        let l = a_eq
            .clone()
            .cong_arg(defs::list_cat(char_t()))
            .unwrap()
            .cong_fn(rhs(&b_eq.clone().sym().unwrap()))
            .unwrap();
        let r = b_eq
            .clone()
            .cong_arg(Term::app(defs::list_cat(char_t()), a2))
            .unwrap();
        l.trans(r).unwrap()
    }

    /// `⊢ span_digits is_digit_dec (s bytes) = pair <prefix> <rest>`.
    fn eval_span(bytes: &[u8]) -> Thm {
        let is_digit = is_digit_dec();
        if bytes.is_empty() {
            return span_nil(&is_digit).unwrap();
        }
        let c = ch(bytes[0]);
        let cs = s_term(&bytes[1..]);
        let general = span_cons(&is_digit, &c, &cs).unwrap();
        let cond_c = rhs(&Term::app(is_digit.clone(), c.clone()).reduce().unwrap());
        let (cc_eq, is_dig) = decide(&cond_c, &[bytes[0]]);
        let resolved = general.rewrite(&cc_eq).unwrap();
        let p = fst_ss(span_dec(&cs));
        let r = snd_ss(span_dec(&cs));
        let dig = mk_pair(
            str_t(),
            str_t(),
            Term::app(Term::app(defs::cons(char_t()), c.clone()), p.clone()),
            r.clone(),
        );
        let nondig = mk_pair(
            str_t(),
            str_t(),
            defs::nil(char_t()),
            Term::app(
                Term::app(defs::cons(char_t()), c.clone()),
                Term::app(Term::app(defs::list_cat(char_t()), p.clone()), r.clone()),
            ),
        );
        let rec = eval_span(&bytes[1..]);
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
        if is_dig {
            let ct = crate::init::cond::cond_true(&ss_t(), &dig, &nondig).unwrap();
            resolved
                .trans(ct)
                .unwrap()
                .rhs_conv(|x| x.rw_all(&fpre))
                .unwrap()
                .rhs_conv(|x| x.rw_all(&rrest))
                .unwrap()
        } else {
            let cf = crate::init::cond::cond_false(&ss_t(), &dig, &nondig).unwrap();
            let span_eq = resolved.trans(cf).unwrap();
            // cat (fst(span cs)) (snd(span cs)) = cat pre rest = <tail>.
            let cat_eq = eval_cat(&pre_t, &rest_t);
            let recon = cat_cong(&fpre, &rrest).trans(cat_eq).unwrap();
            span_eq.rhs_conv(|x| x.rw_all(&recon)).unwrap()
        }
    }

    /// `⊢ nat_of_digits digit_val_dec 10 (s bytes) = <nat literal>`.
    fn eval_value(bytes: &[u8]) -> Thm {
        let dv = digit_val_dec();
        let r = lit(10);
        let run = s_term(bytes);
        let app = Term::app(crate::init::nat_parse::nat_of_digits(&dv, &r), run);
        let base = Thm::beta_conv(app).unwrap(); // = go run 0
        base.trans(eval_go(bytes, &lit(0))).unwrap()
    }

    /// `⊢ go run acc = <nat literal>` (mirrors `nat_parse::eval_go`).
    fn eval_go(bytes: &[u8], acc: &Term) -> Thm {
        let dv = digit_val_dec();
        let r = lit(10);
        if bytes.is_empty() {
            return go_nil(&dv, &r, acc).unwrap();
        }
        let k = bytes[0];
        let cs = s_term(&bytes[1..]);
        let step = go_cons(&dv, &r, &ch(k), &cs)
            .unwrap()
            .all_elim(acc.clone())
            .unwrap();
        let arg = rhs(&step).as_app().unwrap().1.clone(); // acc·10 + dv c
        let dvc = arg.as_app().unwrap().1.clone();
        let dvc_eq = Thm::refl(dvc)
            .unwrap()
            .rhs_conv(|x| x.rw_all(&code_rw(k)))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let arg_lit = Thm::refl(arg)
            .unwrap()
            .rhs_conv(|x| x.rw_all(&dvc_eq))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let new_acc = rhs(&arg_lit);
        // `go cs` — extracted from the step RHS (`go cs (acc·10 + dv c)`) so we
        // never need to name the private `go` term.
        let go_cs = rhs(&step).as_app().unwrap().0.clone();
        let cong = arg_lit.cong_arg(go_cs).unwrap();
        step.trans(cong)
            .unwrap()
            .trans(eval_go(&bytes[1..], &new_acc))
            .unwrap()
    }

    /// `⊢ list_length (s bytes) = <nat literal>`.
    fn eval_length(bytes: &[u8]) -> Thm {
        if bytes.is_empty() {
            return length_nil(&char_t()).unwrap();
        }
        let c = ch(bytes[0]);
        let cs = s_term(&bytes[1..]);
        let step = length_cons(&char_t(), &c, &cs).unwrap(); // = succ (length cs)
        let rec = eval_length(&bytes[1..]);
        step.rhs_conv(|x| x.rw_all(&rec))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap()
    }

    // ---- the top-level driver ----

    fn digit(b: u8) -> bool {
        b.is_ascii_digit()
    }
    /// Maximal decimal-digit prefix split.
    fn span_bytes(bs: &[u8]) -> (&[u8], &[u8]) {
        let mut i = 0;
        while i < bs.len() && digit(bs[i]) {
            i += 1;
        }
        (&bs[..i], &bs[i..])
    }

    /// A `rw_all` step on the running RHS.
    fn rw(t: Thm, eq: &Thm) -> Thm {
        t.rhs_conv(|x| x.rw_all(eq)).unwrap()
    }

    /// Find the first `cond α c x y` subterm with a **literal** condition.
    fn find_lit_cond(t: &Term) -> Option<Term> {
        if let Some((cxy, _y)) = t.as_app()
            && let Some((cx, _x)) = cxy.as_app()
            && let Some((head, c)) = cx.as_app()
            && let Some((spec, _)) = head.as_spec()
            && spec.symbol().label() == defs::cond_spec().symbol().label()
            && c.as_bool().is_some()
        {
            return Some(t.clone());
        }
        // descend.
        match t.as_app() {
            Some((f, a)) => find_lit_cond(f).or_else(|| find_lit_cond(a)),
            None => match t.as_abs() {
                Some((_, body)) => find_lit_cond(body),
                None => None,
            },
        }
    }

    /// Collapse **every** literal-conditioned `cond` anywhere on the RHS
    /// (repeatedly, innermost via `collapse_conds`), then stop.
    fn collapse_all(mut thm: Thm) -> Thm {
        while let Some(c) = find_lit_cond(&rhs(&thm)) {
            let eq = collapse_conds(&c).unwrap();
            if rhs(&eq) == c {
                break; // no progress guard
            }
            thm = rw(thm, &eq);
        }
        thm
    }

    /// Fold a concrete `a ∨ b` (bool literals) to its literal on the RHS.
    fn fold_or(thm: Thm, a: bool, b: bool) -> Thm {
        let t = bor(
            covalence_hol_eval::mk_bool(a),
            covalence_hol_eval::mk_bool(b),
        );
        let want = covalence_hol_eval::mk_bool(a || b);
        let eq = prop_eq(&t, &want).unwrap();
        rw(thm, &eq)
    }

    /// `⊢ fst (span (s bytes)) = <prefix>` and `⊢ snd (…) = <rest>`.
    fn eval_span_projs(bytes: &[u8]) -> (Thm, Thm) {
        let sp = eval_span(bytes);
        let (pre, rest) = pair_parts(&rhs(&sp));
        let f = sp
            .clone()
            .cong_arg(fst(str_t(), str_t()))
            .unwrap()
            .trans(fst_pair(&str_t(), &str_t(), &pre, &rest).unwrap())
            .unwrap();
        let s = sp
            .cong_arg(snd(str_t(), str_t()))
            .unwrap()
            .trans(snd_pair(&str_t(), &str_t(), &pre, &rest).unwrap())
            .unwrap();
        (f, s)
    }

    /// `⊢ parse_float (s input) = <result>` — the full parser computed for a
    /// concrete `input` by staged rewrites + literal-`cond` collapse. No
    /// whole-term `reduce`. Genuine (hypothesis-free).
    fn eval_parse(input: &[u8]) -> Thm {
        let inp = s_term(input);
        let mut thm = Thm::beta_conv(Term::app(parse_float(), inp)).unwrap();

        // ---- Stage A: sign. Rewrite the leading '-'/'+' tests + tail(input);
        // collapse resolves both the `s0` cond and the mantissa sign cond. ----
        let (h45, neg) = eval_head(&char_is(45), input);
        let (h43, is_plus) = eval_head(&char_is(43), input);
        thm = rw(thm, &h45);
        thm = rw(thm, &h43);
        if !input.is_empty() {
            thm = rw(thm, &eval_tail(input));
        }
        thm = collapse_all(thm);
        let s0: &[u8] = if neg || is_plus { &input[1..] } else { input };

        // ---- Stage B: integer part + the outer `some/none` cond. ----
        let (ipres_eq, ip_present) = eval_head(&is_digit_dec(), s0);
        thm = rw(thm, &ipres_eq);
        if !ip_present {
            return collapse_all(thm); // outer cond → none
        }
        let (fst0, snd0) = eval_span_projs(s0);
        thm = rw(thm, &fst0); // ipart → concrete
        thm = rw(thm, &snd0); // s1 → concrete
        let (ipart, s1) = span_bytes(s0);
        thm = rw(thm, &eval_value(ipart)); // ip value
        thm = collapse_all(thm); // fire the outer `some` cond

        // ---- Stage C: fraction (optional). ----
        let (dot_eq, has_dot) = eval_head(&char_is(46), s1);
        thm = rw(thm, &dot_eq);
        let frac_src: &[u8] = if s1.is_empty() { &[] } else { &s1[1..] };
        if !s1.is_empty() {
            thm = rw(thm, &eval_tail(s1));
        }
        let (ffst, fsnd) = eval_span_projs(frac_src);
        thm = rw(thm, &ffst);
        thm = rw(thm, &fsnd);
        let fdig = span_bytes(frac_src).0; // the fraction *digit prefix*
        thm = rw(thm, &eval_value(fdig));
        thm = rw(thm, &eval_length(fdig));
        thm = collapse_all(thm); // resolve the three `cond has_dot`
        let s2: &[u8] = if has_dot { span_bytes(&s1[1..]).1 } else { s1 };

        // ---- Stage D: exponent (optional). ----
        let (he_eq, e_lc) = eval_head(&char_is(101), s2); // 'e'
        let (hbe_eq, e_uc) = eval_head(&char_is(69), s2); // 'E'
        thm = rw(thm, &he_eq);
        thm = rw(thm, &hbe_eq);
        thm = fold_or(thm, e_lc, e_uc);
        let has_e = e_lc || e_uc;
        let es: &[u8] = if s2.is_empty() { &[] } else { &s2[1..] };
        if !s2.is_empty() {
            thm = rw(thm, &eval_tail(s2));
        }
        let (hem_eq, neg_e) = eval_head(&char_is(45), es);
        let (hep_eq, plus_e) = eval_head(&char_is(43), es);
        thm = rw(thm, &hem_eq);
        thm = rw(thm, &hep_eq);
        if !es.is_empty() {
            thm = rw(thm, &eval_tail(es));
        }
        thm = collapse_all(thm); // resolve the exp-sign `es1` cond
        let es1: &[u8] = if neg_e || plus_e { &es[1..] } else { es };
        let (efst, esnd) = eval_span_projs(es1);
        thm = rw(thm, &efst);
        thm = rw(thm, &esnd);
        let edig = span_bytes(es1).0; // the exponent *digit prefix*
        thm = rw(thm, &eval_value(edig));
        thm = collapse_all(thm); // resolve `cond has_e` (ex, s3) + sign conds
        let _ = has_e;

        // ---- Stage E: fold the assembled arithmetic to literals. ----
        thm.rhs_conv(|x| x.reduce()).unwrap()
    }

    /// Assert a parse yields the expected `some ((mant, exp), rest)`.
    fn assert_parse(input: &[u8], mant: i64, exp: i64, rest: &[u8]) {
        let thm = eval_parse(input);
        assert!(thm.hyps().is_empty(), "parse {input:?} must be oracle-free");
        let want = Term::app(
            some(payload_t()),
            mk_pair(fv_t(), str_t(), fv_mk(ilit(mant), ilit(exp)), s_term(rest)),
        );
        assert_eq!(rhs(&thm), want, "parse {input:?}");
    }

    #[test]
    fn parse_integer_42() {
        assert_parse(b"42", 42, 0, b"");
        assert_parse(b"42x", 42, 0, b"x");
    }

    #[test]
    fn parse_fraction_pi() {
        assert_parse(b"3.14", 314, -2, b"");
    }

    #[test]
    fn parse_exponent_1e10() {
        assert_parse(b"1e10", 1, 10, b"");
    }

    #[test]
    fn parse_neg_half() {
        assert_parse(b"-0.5", -5, -1, b"");
    }

    #[test]
    fn parse_sci_25e_neg3() {
        assert_parse(b"2.5e-3", 25, -4, b"");
    }

    #[test]
    fn parse_none_no_leading_digit() {
        // no integer digit → none.
        let thm = eval_parse(b".5");
        assert_eq!(rhs(&thm), none(payload_t()));
        let thm = eval_parse(b"x");
        assert_eq!(rhs(&thm), none(payload_t()));
    }

    // ========================================================================
    // Bytes end-to-end harness — the same driver over `list u8` (byte digit
    // tests reduce directly through `u8.toNat`, no `char.code` rewrite).
    // ========================================================================

    use crate::init::nat_parse_bytes::{
        digit_val_byte_dec, go_cons as go_cons_b, go_nil as go_nil_b, is_digit_byte_dec,
        nat_of_digits_bytes, span_cons as span_cons_b, span_nil as span_nil_b,
    };

    fn u8t() -> Type {
        defs::u8_ty()
    }
    fn bs_term(bytes: &[u8]) -> Term {
        let mut t = defs::nil(u8t());
        for &b in bytes.iter().rev() {
            t = Term::app(
                Term::app(defs::cons(u8t()), covalence_hol_eval::mk_u8(b)),
                t,
            );
        }
        t
    }
    fn decide_b(t: &Term) -> (Thm, bool) {
        let red = Thm::refl(t.clone())
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let combo = rhs(&red);
        match prop_eq(&combo, &covalence_hol_eval::mk_bool(true)) {
            Ok(tt) => (red.trans(tt).unwrap(), true),
            Err(_) => {
                let ff = prop_eq(&combo, &covalence_hol_eval::mk_bool(false)).unwrap();
                (red.trans(ff).unwrap(), false)
            }
        }
    }
    fn eval_tail_b(bytes: &[u8]) -> Thm {
        tail_cons(
            &u8t(),
            &covalence_hol_eval::mk_u8(bytes[0]),
            &bs_term(&bytes[1..]),
        )
        .unwrap()
    }
    fn eval_head_b(pred: &Term, bytes: &[u8]) -> (Thm, bool) {
        let s = bs_term(bytes);
        let oc = head_sat_b(pred, &s);
        if bytes.is_empty() {
            let hn = head_nil(&u8t()).unwrap();
            let cn =
                case_none(&u8t(), &bool_t(), &covalence_hol_eval::mk_bool(false), pred).unwrap();
            let eq = Thm::refl(oc)
                .unwrap()
                .rhs_conv(|x| x.rw_all(&hn))
                .unwrap()
                .trans(cn)
                .unwrap();
            return (eq, false);
        }
        let c0 = covalence_hol_eval::mk_u8(bytes[0]);
        let cs0 = bs_term(&bytes[1..]);
        let hc = head_cons(&u8t(), &c0, &cs0).unwrap();
        let cse = case_some(
            &u8t(),
            &bool_t(),
            &covalence_hol_eval::mk_bool(false),
            pred,
            &c0,
        )
        .unwrap();
        let (dec, b) = decide_b(&Term::app(pred.clone(), c0.clone()));
        let eq = Thm::refl(oc)
            .unwrap()
            .rhs_conv(|x| x.rw_all(&hc))
            .unwrap()
            .trans(cse)
            .unwrap()
            .trans(dec)
            .unwrap();
        (eq, b)
    }
    fn eval_cat_b(a: &Term, b: &Term) -> Thm {
        match a
            .as_app()
            .and_then(|(f, tl)| f.as_app().map(|(_, h)| (h.clone(), tl.clone())))
        {
            Some((x, xs)) => {
                let cc = cat_cons(&u8t(), &x, &xs, b).unwrap();
                let cong = eval_cat_b(&xs, b)
                    .cong_arg(Term::app(defs::cons(u8t()), x))
                    .unwrap();
                cc.trans(cong).unwrap()
            }
            None => cat_nil(&u8t(), b).unwrap(),
        }
    }
    fn cat_cong_b(a_eq: &Thm, b_eq: &Thm) -> Thm {
        let a2 = rhs(a_eq);
        let l = a_eq
            .clone()
            .cong_arg(defs::list_cat(u8t()))
            .unwrap()
            .cong_fn(rhs(&b_eq.clone().sym().unwrap()))
            .unwrap();
        let r = b_eq
            .clone()
            .cong_arg(Term::app(defs::list_cat(u8t()), a2))
            .unwrap();
        l.trans(r).unwrap()
    }
    fn eval_span_b(bytes: &[u8]) -> Thm {
        let is_digit = is_digit_byte_dec();
        if bytes.is_empty() {
            return span_nil_b(&is_digit).unwrap();
        }
        let c = covalence_hol_eval::mk_u8(bytes[0]);
        let cs = bs_term(&bytes[1..]);
        let general = span_cons_b(&is_digit, &c, &cs).unwrap();
        let cond_c = rhs(&Term::app(is_digit.clone(), c.clone()).reduce().unwrap());
        let (cc_eq, is_dig) = decide_b(&cond_c);
        let resolved = general.rewrite(&cc_eq).unwrap();
        let p = fst_bb(span_dec_b(&cs));
        let r = snd_bb(span_dec_b(&cs));
        let cons_c = |h: Term, t: Term| Term::app(Term::app(defs::cons(u8t()), h), t);
        let cat = |x: Term, y: Term| Term::app(Term::app(defs::list_cat(u8t()), x), y);
        let dig = mk_pair(
            bytes_t(),
            bytes_t(),
            cons_c(c.clone(), p.clone()),
            r.clone(),
        );
        let nondig = mk_pair(
            bytes_t(),
            bytes_t(),
            defs::nil(u8t()),
            cons_c(c.clone(), cat(p.clone(), r.clone())),
        );
        let rec = eval_span_b(&bytes[1..]);
        let (pre_t, rest_t) = pair_parts(&rhs(&rec));
        let fpre = rec
            .clone()
            .cong_arg(fst(bytes_t(), bytes_t()))
            .unwrap()
            .trans(fst_pair(&bytes_t(), &bytes_t(), &pre_t, &rest_t).unwrap())
            .unwrap();
        let rrest = rec
            .cong_arg(snd(bytes_t(), bytes_t()))
            .unwrap()
            .trans(snd_pair(&bytes_t(), &bytes_t(), &pre_t, &rest_t).unwrap())
            .unwrap();
        if is_dig {
            let ct = crate::init::cond::cond_true(&bb_t(), &dig, &nondig).unwrap();
            resolved
                .trans(ct)
                .unwrap()
                .rhs_conv(|x| x.rw_all(&fpre))
                .unwrap()
                .rhs_conv(|x| x.rw_all(&rrest))
                .unwrap()
        } else {
            let cf = crate::init::cond::cond_false(&bb_t(), &dig, &nondig).unwrap();
            let span_eq = resolved.trans(cf).unwrap();
            let recon = cat_cong_b(&fpre, &rrest)
                .trans(eval_cat_b(&pre_t, &rest_t))
                .unwrap();
            span_eq.rhs_conv(|x| x.rw_all(&recon)).unwrap()
        }
    }
    fn eval_span_projs_b(bytes: &[u8]) -> (Thm, Thm) {
        let sp = eval_span_b(bytes);
        let (pre, rest) = pair_parts(&rhs(&sp));
        let f = sp
            .clone()
            .cong_arg(fst(bytes_t(), bytes_t()))
            .unwrap()
            .trans(fst_pair(&bytes_t(), &bytes_t(), &pre, &rest).unwrap())
            .unwrap();
        let s = sp
            .cong_arg(snd(bytes_t(), bytes_t()))
            .unwrap()
            .trans(snd_pair(&bytes_t(), &bytes_t(), &pre, &rest).unwrap())
            .unwrap();
        (f, s)
    }
    fn eval_value_b(bytes: &[u8]) -> Thm {
        let dv = digit_val_byte_dec();
        let r = lit(10);
        let app = Term::app(nat_of_digits_bytes(&dv, &r), bs_term(bytes));
        Thm::beta_conv(app)
            .unwrap()
            .trans(eval_go_b(bytes, &lit(0)))
            .unwrap()
    }
    fn eval_go_b(bytes: &[u8], acc: &Term) -> Thm {
        let dv = digit_val_byte_dec();
        let r = lit(10);
        if bytes.is_empty() {
            return go_nil_b(&dv, &r, acc).unwrap();
        }
        let cs = bs_term(&bytes[1..]);
        let step = go_cons_b(&dv, &r, &covalence_hol_eval::mk_u8(bytes[0]), &cs)
            .unwrap()
            .all_elim(acc.clone())
            .unwrap();
        let arg = rhs(&step).as_app().unwrap().1.clone();
        let dvc = arg.as_app().unwrap().1.clone();
        let dvc_eq = Thm::refl(dvc).unwrap().rhs_conv(|x| x.reduce()).unwrap();
        let arg_lit = Thm::refl(arg)
            .unwrap()
            .rhs_conv(|x| x.rw_all(&dvc_eq))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let new_acc = rhs(&arg_lit);
        let go_cs = rhs(&step).as_app().unwrap().0.clone();
        let cong = arg_lit.cong_arg(go_cs).unwrap();
        step.trans(cong)
            .unwrap()
            .trans(eval_go_b(&bytes[1..], &new_acc))
            .unwrap()
    }
    fn eval_length_b(bytes: &[u8]) -> Thm {
        if bytes.is_empty() {
            return length_nil(&u8t()).unwrap();
        }
        let cs = bs_term(&bytes[1..]);
        let step = length_cons(&u8t(), &covalence_hol_eval::mk_u8(bytes[0]), &cs).unwrap();
        step.rhs_conv(|x| x.rw_all(&eval_length_b(&bytes[1..])))
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap()
    }

    /// `⊢ parse_float_bytes (bs input) = <result>` — the bytes parser computed
    /// for concrete `input`. Genuine (hypothesis-free).
    fn eval_parse_b(input: &[u8]) -> Thm {
        let inp = bs_term(input);
        let mut thm = Thm::beta_conv(Term::app(parse_float_bytes(), inp)).unwrap();

        let (h45, neg) = eval_head_b(&byte_is(45), input);
        let (h43, is_plus) = eval_head_b(&byte_is(43), input);
        thm = rw(thm, &h45);
        thm = rw(thm, &h43);
        if !input.is_empty() {
            thm = rw(thm, &eval_tail_b(input));
        }
        thm = collapse_all(thm);
        let s0: &[u8] = if neg || is_plus { &input[1..] } else { input };

        let (ipres_eq, ip_present) = eval_head_b(&is_digit_byte_dec(), s0);
        thm = rw(thm, &ipres_eq);
        if !ip_present {
            return collapse_all(thm);
        }
        let (fst0, snd0) = eval_span_projs_b(s0);
        thm = rw(thm, &fst0);
        thm = rw(thm, &snd0);
        let (ipart, s1) = span_bytes(s0);
        thm = rw(thm, &eval_value_b(ipart));
        thm = collapse_all(thm);

        let (dot_eq, has_dot) = eval_head_b(&byte_is(46), s1);
        thm = rw(thm, &dot_eq);
        let frac_src: &[u8] = if s1.is_empty() { &[] } else { &s1[1..] };
        if !s1.is_empty() {
            thm = rw(thm, &eval_tail_b(s1));
        }
        let (ffst, fsnd) = eval_span_projs_b(frac_src);
        thm = rw(thm, &ffst);
        thm = rw(thm, &fsnd);
        let fdig = span_bytes(frac_src).0;
        thm = rw(thm, &eval_value_b(fdig));
        thm = rw(thm, &eval_length_b(fdig));
        thm = collapse_all(thm);
        let s2: &[u8] = if has_dot { span_bytes(&s1[1..]).1 } else { s1 };

        let (he_eq, e_lc) = eval_head_b(&byte_is(101), s2);
        let (hbe_eq, e_uc) = eval_head_b(&byte_is(69), s2);
        thm = rw(thm, &he_eq);
        thm = rw(thm, &hbe_eq);
        thm = fold_or(thm, e_lc, e_uc);
        let es: &[u8] = if s2.is_empty() { &[] } else { &s2[1..] };
        if !s2.is_empty() {
            thm = rw(thm, &eval_tail_b(s2));
        }
        let (hem_eq, neg_e) = eval_head_b(&byte_is(45), es);
        let (hep_eq, plus_e) = eval_head_b(&byte_is(43), es);
        thm = rw(thm, &hem_eq);
        thm = rw(thm, &hep_eq);
        if !es.is_empty() {
            thm = rw(thm, &eval_tail_b(es));
        }
        thm = collapse_all(thm);
        let es1: &[u8] = if neg_e || plus_e { &es[1..] } else { es };
        let (efst, esnd) = eval_span_projs_b(es1);
        thm = rw(thm, &efst);
        thm = rw(thm, &esnd);
        let edig = span_bytes(es1).0;
        thm = rw(thm, &eval_value_b(edig));
        thm = collapse_all(thm);

        thm.rhs_conv(|x| x.reduce()).unwrap()
    }

    fn assert_parse_b(input: &[u8], mant: i64, exp: i64, rest: &[u8]) {
        let thm = eval_parse_b(input);
        assert!(
            thm.hyps().is_empty(),
            "bytes parse {input:?} must be oracle-free"
        );
        let want = Term::app(
            some(payload_b_t()),
            mk_pair(
                fv_t(),
                bytes_t(),
                fv_mk(ilit(mant), ilit(exp)),
                bs_term(rest),
            ),
        );
        assert_eq!(rhs(&thm), want, "bytes parse {input:?}");
    }

    #[test]
    fn bytes_parser_is_well_typed() {
        assert_eq!(
            parse_float_bytes().type_of().unwrap(),
            Type::fun(bytes_t(), opt_b_t())
        );
    }

    #[test]
    fn bytes_parses_the_examples() {
        assert_parse_b(b"42", 42, 0, b"");
        assert_parse_b(b"3.14", 314, -2, b"");
        assert_parse_b(b"1e10", 1, 10, b"");
        assert_parse_b(b"-0.5", -5, -1, b"");
        assert_parse_b(b"2.5e-3", 25, -4, b"");
        assert_parse_b(b"42x", 42, 0, b"x");
    }

    #[test]
    fn bytes_none_on_no_leading_digit() {
        assert_eq!(rhs(&eval_parse_b(b".5")), none(payload_b_t()));
        assert_eq!(rhs(&eval_parse_b(b"")), none(payload_b_t()));
    }
}
