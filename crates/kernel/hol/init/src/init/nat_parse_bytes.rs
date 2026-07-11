//! `nat_parse_bytes` — the **bytes** counterpart of NP2's string parsers
//! (stage NP3): `parseNatR_bytes : bytes → option (nat × bytes)` over
//! `list u8`, reading ASCII decimal digit **bytes**.
//!
//! `bytes := list u8`, and a digit test is a comparison on the byte's
//! unsigned value `u8.toNat b : nat` (the `int_to_nat` embedding, which
//! reduces to a literal on a concrete `u8`). The build mirrors
//! [`crate::init::nat_parse`] exactly — only the element type (`u8` instead
//! of `char`) and the digit predicate/value (over `u8.toNat` instead of
//! `char.code`) change:
//!
//! - **[`span_digits_bytes`]** — the maximal digit-prefix split
//!   `(consumed, rest)`, a `foldr` (paramorphism-free, reconstructing the
//!   tail with `cat`); clauses [`span_nil`] / [`span_cons`].
//! - **[`nat_of_digits_bytes`]** — the radix-`R` positional value (left fold
//!   into a `nat → nat` accumulator); clauses [`go_nil`] / [`go_cons`].
//! - **[`parse_nat_bytes`]** — `some (value consumed, rest)` when the first
//!   byte is a digit, else `none`.
//! - **[`span_cat`]** — the split is a genuine partition
//!   (`cat prefix rest = l`), proved for any byte digit predicate by
//!   `list`-induction (the `nat_parse` proof, at `u8`).
//!
//! See [`crate::init::nat_parse_agree`] for the theorem relating this to the
//! `string` parser on ASCII-digit input.

use covalence_core::{IntTag, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{
    cons, fst, head, int_to_nat, list_cat, list_foldr, nat_add, nat_le, nat_mul, nat_sub, nil,
    none, option_case, pair, snd, some, u8_ty,
};
use covalence_hol_eval::derived::DerivedRules;

use crate::init::cond::{cond_false, cond_true};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::list_recursion::{cat_cons, cat_nil, foldr_cons, foldr_nil};

// ============================================================================
// Types.
// ============================================================================

fn u8_t() -> Type {
    u8_ty()
}

fn nat_t() -> Type {
    Type::nat()
}

fn bool_t() -> Type {
    Type::bool()
}

/// `bytes := list u8`.
fn bytes_t() -> Type {
    defs::list(u8_t())
}

/// `bytes × bytes` — the `span` result.
fn bb_t() -> Type {
    defs::prod(bytes_t(), bytes_t())
}

/// `nat × bytes` — the `parse` payload.
fn nb_t() -> Type {
    defs::prod(nat_t(), bytes_t())
}

/// `option (nat × bytes)` — the `parse` result.
fn opt_nb_t() -> Type {
    defs::option(nb_t())
}

// ============================================================================
// Small term builders (mirroring `nat_parse`, at `u8`).
// ============================================================================

fn lit(k: u64) -> Term {
    covalence_hol_eval::mk_nat(k)
}

/// `u8.toNat b : nat` — the unsigned value of a byte.
pub fn byte_val_op() -> Term {
    int_to_nat(IntTag::U8)
}

/// `u8.toNat b : nat`.
fn val(b: &Term) -> Term {
    Term::app(byte_val_op(), b.clone())
}

fn le(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_le(), a), b)
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add(), a), b)
}

fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_mul(), a), b)
}

fn sub(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_sub(), a), b)
}

fn band(a: Term, b: Term) -> Term {
    crate::HolLightCtx::new().mk_and(a, b)
}

fn cons_u(c: Term, l: Term) -> Term {
    Term::app(Term::app(cons(u8_t()), c), l)
}

fn nil_u() -> Term {
    nil(u8_t())
}

fn cat(a: Term, b: Term) -> Term {
    Term::app(Term::app(list_cat(u8_t()), a), b)
}

fn pair_bb(a: Term, b: Term) -> Term {
    Term::app(Term::app(pair(bytes_t(), bytes_t()), a), b)
}

fn fst_bb(p: Term) -> Term {
    Term::app(fst(bytes_t(), bytes_t()), p)
}

fn snd_bb(p: Term) -> Term {
    Term::app(snd(bytes_t(), bytes_t()), p)
}

fn cat_cong(a_eq: &Thm, b_eq: &Thm) -> Result<Thm> {
    let a2 = rhs(a_eq);
    let l = a_eq
        .clone()
        .cong_arg(list_cat(u8_t()))?
        .cong_fn(rhs(&b_eq.clone().sym()?))?;
    let r = b_eq.clone().cong_arg(Term::app(list_cat(u8_t()), a2))?;
    l.trans(r)
}

fn cond_app(ty: Type, b: Term, x: Term, y: Term) -> Term {
    Term::app(Term::app(Term::app(defs::cond(ty), b), x), y)
}

fn lam(name: &str, ty: Type, body: Term) -> Term {
    Term::abs(ty, subst::close(&body, name))
}

fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::nat_parse_bytes: expected an equation")
        .1
        .clone()
}

// ============================================================================
// `span_digits_bytes` — the maximal digit-prefix split, as a `foldr`.
// ============================================================================

fn span_step(is_digit: &Term) -> Term {
    let c = Term::free("c", u8_t());
    let acc = Term::free("acc", bb_t());
    let p = fst_bb(acc.clone());
    let r = snd_bb(acc.clone());
    let digit_branch = pair_bb(cons_u(c.clone(), p.clone()), r.clone());
    let rest = cons_u(c.clone(), cat(p, r));
    let nondigit_branch = pair_bb(nil_u(), rest);
    let cnd = cond_app(
        bb_t(),
        Term::app(is_digit.clone(), c.clone()),
        digit_branch,
        nondigit_branch,
    );
    lam("c", u8_t(), lam("acc", bb_t(), cnd))
}

/// `span_digits_bytes is_digit : bytes → (bytes × bytes)` ≡
/// `foldr (span_step is_digit) (pair nil nil)`.
pub fn span_digits_bytes(is_digit: &Term) -> Term {
    Term::app(
        Term::app(list_foldr(u8_t(), bb_t()), span_step(is_digit)),
        pair_bb(nil_u(), nil_u()),
    )
}

fn span_app(is_digit: &Term, l: &Term) -> Term {
    Term::app(span_digits_bytes(is_digit), l.clone())
}

/// `⊢ span_digits_bytes is_digit nil = pair nil nil`.
pub fn span_nil(is_digit: &Term) -> Result<Thm> {
    foldr_nil(
        &u8_t(),
        &bb_t(),
        &span_step(is_digit),
        &pair_bb(nil_u(), nil_u()),
    )
}

/// `⊢ span_digits_bytes is_digit (cons c cs) = cond (is_digit c) …` — the
/// general (unresolved-`cond`) `cons` clause.
pub fn span_cons(is_digit: &Term, c: &Term, cs: &Term) -> Result<Thm> {
    let base = pair_bb(nil_u(), nil_u());
    let fc = foldr_cons(&u8_t(), &bb_t(), &span_step(is_digit), &base, c, cs)?;
    let red = rhs(&fc).reduce()?;
    fc.trans(red)
}

// ============================================================================
// `nat_of_digits_bytes` — the radix-R positional value.
// ============================================================================

fn go_step(digit_val: &Term, radix: &Term) -> Term {
    let c = Term::free("c", u8_t());
    let rec = Term::free("rec", Type::fun(nat_t(), nat_t()));
    let acc = Term::free("acc", nat_t());
    let next = add(
        mul(acc.clone(), radix.clone()),
        Term::app(digit_val.clone(), c.clone()),
    );
    let inner = lam("acc", nat_t(), Term::app(rec.clone(), next));
    lam("c", u8_t(), lam("rec", Type::fun(nat_t(), nat_t()), inner))
}

fn go(digit_val: &Term, radix: &Term) -> Term {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    Term::app(
        Term::app(
            list_foldr(u8_t(), Type::fun(nat_t(), nat_t())),
            go_step(digit_val, radix),
        ),
        id,
    )
}

/// `nat_of_digits_bytes digit_val R : bytes → nat` ≡ `λl. go l 0`.
pub fn nat_of_digits_bytes(digit_val: &Term, radix: &Term) -> Term {
    let l = Term::free("l", bytes_t());
    let applied = Term::app(Term::app(go(digit_val, radix), l.clone()), lit(0));
    lam("l", bytes_t(), applied)
}

/// `⊢ go l acc = acc` at `l = nil`.
pub fn go_nil(digit_val: &Term, radix: &Term, acc: &Term) -> Result<Thm> {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    let fold = foldr_nil(
        &u8_t(),
        &Type::fun(nat_t(), nat_t()),
        &go_step(digit_val, radix),
        &id,
    )?;
    let cong = fold.cong_fn(acc.clone())?;
    let red = rhs(&cong).reduce()?;
    cong.trans(red)
}

/// `⊢ go (cons c cs) acc = go cs (acc·R + digit_val c)`.
pub fn go_cons(digit_val: &Term, radix: &Term, c: &Term, cs: &Term) -> Result<Thm> {
    let id = lam("acc", nat_t(), Term::free("acc", nat_t()));
    let acc = Term::free("acc", nat_t());
    let fc = foldr_cons(
        &u8_t(),
        &Type::fun(nat_t(), nat_t()),
        &go_step(digit_val, radix),
        &id,
        c,
        cs,
    )?;
    let cong = fc.cong_fn(acc.clone())?;
    let red = rhs(&cong).reduce()?;
    cong.trans(red)?.all_intro("acc", nat_t())
}

// ============================================================================
// `parse_nat_bytes` — the assembled parser.
// ============================================================================

fn head_is_digit(is_digit: &Term, l: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(
                option_case(u8_t(), bool_t()),
                covalence_hol_eval::mk_bool(false),
            ),
            is_digit.clone(),
        ),
        Term::app(head(u8_t()), l.clone()),
    )
}

/// `parse_nat_bytes is_digit value : bytes → option (nat × bytes)`.
pub fn parse_nat_bytes(is_digit: &Term, value: &Term) -> Term {
    let l = Term::free("l", bytes_t());
    let sp = span_app(is_digit, &l);
    let v = Term::app(value.clone(), fst_bb(sp.clone()));
    let payload = Term::app(Term::app(pair(nat_t(), bytes_t()), v), snd_bb(sp));
    let body = cond_app(
        opt_nb_t(),
        head_is_digit(is_digit, &l),
        Term::app(some(nb_t()), payload),
        none(nb_t()),
    );
    lam("l", bytes_t(), body)
}

// ============================================================================
// The decimal byte configuration.
// ============================================================================

/// `λb. nat_le lo (u8.toNat b) ∧ nat_le (u8.toNat b) hi` — a contiguous byte
/// range predicate.
fn range_pred(lo: u64, hi: u64) -> Term {
    let b = Term::free("b", u8_t());
    let body = band(le(lit(lo), val(&b)), le(val(&b), lit(hi)));
    lam("b", u8_t(), body)
}

/// `is_digit` for **decimal** ASCII digit bytes — `'0'..='9'` (48..=57).
pub fn is_digit_byte_dec() -> Term {
    range_pred(48, 57)
}

/// `λb. u8.toNat b − 48` — the decimal digit value of a `'0'`-based byte.
pub fn digit_val_byte_dec() -> Term {
    let b = Term::free("b", u8_t());
    lam("b", u8_t(), sub(val(&b), lit(48)))
}

/// `parseNatDec_bytes : bytes → option (nat × bytes)`.
pub fn parse_nat_dec_bytes() -> Term {
    parse_nat_bytes(
        &is_digit_byte_dec(),
        &nat_of_digits_bytes(&digit_val_byte_dec(), &lit(10)),
    )
}

// ============================================================================
// General correctness: the split is a partition (`cat prefix rest = l`), for
// any byte digit predicate. By `list`-induction (the `nat_parse` proof at
// `u8`).
// ============================================================================

use crate::init::eq::{beta_expand, beta_nf_concl, beta_reduce};
use crate::init::nat_div::bool_cases;
use crate::init::prod::{fst_pair, snd_pair};

/// `⊢ ∀l. cat (fst (span_digits_bytes is_digit l)) (snd (…)) = l` — the split
/// is a partition. By `list`-induction on `l`, `bool.cases` on `is_digit c`.
/// Genuine (hypothesis- and oracle-free).
pub fn span_cat(is_digit: &Term) -> Result<Thm> {
    let l = Term::free("l", bytes_t());
    let cat_of = |t: &Term| -> Term {
        let sp = span_app(is_digit, t);
        cat(fst_bb(sp.clone()), snd_bb(sp))
    };
    let motive = {
        let body = cat_of(&l).equals(l.clone())?;
        Term::abs(bytes_t(), subst::close(&body, "l"))
    };

    // base: P nil.
    let base = {
        let sn = span_nil(is_digit)?;
        let f = fst_pair(&bytes_t(), &bytes_t(), &nil_u(), &nil_u())?;
        let s = snd_pair(&bytes_t(), &bytes_t(), &nil_u(), &nil_u())?;
        let lhs = Thm::refl(cat_of(&nil_u()))?
            .rhs_conv(|t| t.rw_all(&sn))?
            .rhs_conv(|t| t.rw_all(&f))?
            .rhs_conv(|t| t.rw_all(&s))?;
        let base_eq = lhs.trans(cat_nil(&u8_t(), &nil_u())?)?;
        beta_expand(&motive, nil_u(), base_eq)?
    };

    // cons_case: ∀c cs. P cs ⟹ P (cons c cs).
    let c = Term::free("c", u8_t());
    let cs = Term::free("cs", bytes_t());
    let cons_case = {
        let consed = cons_u(c.clone(), cs.clone());
        let ante = Term::app(motive.clone(), cs.clone());
        let ih = beta_reduce(Thm::assume(ante.clone())?)?;
        let goal = cat_of(&consed).equals(consed.clone())?;

        let sp_cs = span_app(is_digit, &cs);
        let p = fst_bb(sp_cs.clone());
        let r = snd_bb(sp_cs);
        let general = span_cons(is_digit, &c, &cs)?;
        let cond_c = rhs(&Term::app(is_digit.clone(), c.clone()).reduce()?);

        // b = true (digit).
        let branch_t = {
            let hbt = Thm::assume(cond_c.clone().equals(covalence_hol_eval::mk_bool(true))?)?;
            let digit_branch = pair_bb(cons_u(c.clone(), p.clone()), r.clone());
            let ct = cond_true(
                &bb_t(),
                &digit_branch,
                &pair_bb(nil_u(), cons_u(c.clone(), cat(p.clone(), r.clone()))),
            )?;
            let span_eq = general.clone().rewrite(&hbt)?.trans(ct)?;
            let fp = fst_pair(&bytes_t(), &bytes_t(), &cons_u(c.clone(), p.clone()), &r)?;
            let sp = snd_pair(&bytes_t(), &bytes_t(), &cons_u(c.clone(), p.clone()), &r)?;
            let fst_eq = span_eq
                .clone()
                .cong_arg(fst(bytes_t(), bytes_t()))?
                .trans(fp)?;
            let snd_eq = span_eq.cong_arg(snd(bytes_t(), bytes_t()))?.trans(sp)?;
            let cat_eq = cat_cong(&fst_eq, &snd_eq)?;
            let cc = cat_cons(&u8_t(), &c, &p, &r)?;
            let use_ih = ih.clone().cong_arg(Term::app(cons(u8_t()), c.clone()))?;
            let t1 = cat_eq.trans(cc)?;
            t1.trans(use_ih)?
                .imp_intro(&cond_c.clone().equals(covalence_hol_eval::mk_bool(true))?)?
        };

        // b = false (non-digit).
        let branch_f = {
            let hbf = Thm::assume(cond_c.clone().equals(covalence_hol_eval::mk_bool(false))?)?;
            let x = cons_u(c.clone(), cat(p.clone(), r.clone()));
            let cf = cond_false(
                &bb_t(),
                &pair_bb(cons_u(c.clone(), p.clone()), r.clone()),
                &pair_bb(nil_u(), x.clone()),
            )?;
            let span_eq = general.clone().rewrite(&hbf)?.trans(cf)?;
            let fp = fst_pair(&bytes_t(), &bytes_t(), &nil_u(), &x)?;
            let sp = snd_pair(&bytes_t(), &bytes_t(), &nil_u(), &x)?;
            let fst_eq = span_eq
                .clone()
                .cong_arg(fst(bytes_t(), bytes_t()))?
                .trans(fp)?;
            let snd_eq = span_eq.cong_arg(snd(bytes_t(), bytes_t()))?.trans(sp)?;
            let snd_span = snd_bb(span_app(is_digit, &consed));
            let cat_l = fst_eq
                .cong_arg(list_cat(u8_t()))?
                .cong_fn(snd_span.clone())?;
            let cn = cat_nil(&u8_t(), &snd_span)?;
            let use_ih = ih.clone().cong_arg(Term::app(cons(u8_t()), c.clone()))?;
            let snd_to_cons = snd_eq.trans(use_ih)?;
            cat_l
                .trans(cn)?
                .trans(snd_to_cons)?
                .imp_intro(&cond_c.clone().equals(covalence_hol_eval::mk_bool(false))?)?
        };

        let combined = bool_cases()
            .all_elim(cond_c.clone())?
            .or_elim(branch_t, branch_f)?;
        let _ = goal;
        let p_cons = beta_expand(&motive, consed, combined)?;
        p_cons
            .imp_intro(&ante)?
            .all_intro("cs", bytes_t())?
            .all_intro("c", u8_t())?
    };

    let li = crate::init::list::list_induct(&u8_t(), &motive, base, cons_case)?;
    beta_nf_concl(li)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::cond::collapse_conds;
    use crate::init::logic::prop_eq;

    /// A `bytes` term from raw bytes (each a `u8` literal).
    fn s(bytes: &[u8]) -> Term {
        let mut t = nil_u();
        for &b in bytes.iter().rev() {
            t = cons_u(covalence_hol_eval::mk_u8(b), t);
        }
        t
    }

    /// Decide a closed byte-digit bool term (`is_digit_byte_dec` at a literal
    /// byte), reducing `u8.toNat` and folding.
    fn decide(t: &Term) -> (Thm, bool) {
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

    /// `⊢ go digit_val R (s bytes) acc = <nat literal>` for concrete digit
    /// bytes.
    fn eval_go(dv: &Term, r: &Term, bytes: &[u8], acc: &Term) -> Thm {
        if bytes.is_empty() {
            return go_nil(dv, r, acc).unwrap();
        }
        let b = covalence_hol_eval::mk_u8(bytes[0]);
        let cs = s(&bytes[1..]);
        let step = go_cons(dv, r, &b, &cs)
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
        let cong = arg_lit.cong_arg(Term::app(go(dv, r), cs.clone())).unwrap();
        step.trans(cong)
            .unwrap()
            .trans(eval_go(dv, r, &bytes[1..], &new_acc))
            .unwrap()
    }

    #[test]
    fn span_cat_is_genuine() {
        let thm = span_cat(&is_digit_byte_dec()).unwrap();
        assert!(thm.hyps().is_empty(), "span_cat must be axiom-free");
        assert!(thm.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn go_clauses_are_genuine() {
        let dv = digit_val_byte_dec();
        let r = lit(10);
        let acc = Term::free("a", nat_t());
        let cs = Term::free("cs", bytes_t());
        let c = covalence_hol_eval::mk_u8(b'5');
        assert!(go_nil(&dv, &r, &acc).unwrap().hyps().is_empty());
        assert!(go_cons(&dv, &r, &c, &cs).unwrap().hyps().is_empty());
    }

    #[test]
    fn decimal_byte_value_computes() {
        // "42" (bytes 0x34 0x32) decimal = 42.
        let dv = digit_val_byte_dec();
        let v = eval_go(&dv, &lit(10), b"42", &lit(0));
        assert!(v.hyps().is_empty());
        assert_eq!(rhs(&v), lit(42));
    }

    #[test]
    fn is_digit_byte_decides() {
        // '5' (0x35) is a digit; ' ' (0x20) is not.
        let p = is_digit_byte_dec();
        let (_e5, is5) = decide(&Term::app(p.clone(), covalence_hol_eval::mk_u8(b'5')));
        assert!(is5);
        let (_esp, issp) = decide(&Term::app(p, covalence_hol_eval::mk_u8(b' ')));
        assert!(!issp);
        let _ = collapse_conds; // available for cond-headed digit values
    }

    #[test]
    fn parser_is_well_typed() {
        assert_eq!(
            parse_nat_dec_bytes().type_of().unwrap(),
            Type::fun(bytes_t(), opt_nb_t())
        );
    }
}
