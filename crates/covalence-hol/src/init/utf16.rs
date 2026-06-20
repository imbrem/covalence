//! UTF-16 transcoding: `string ↔ list u16`.
//!
//! The **shell-level UTF-16 codec** over the `char`/`string` substrate
//! ([`init::char`], [`init::string`]), mirroring [`init::utf8`]. The codec
//! constants are shell-defined here (not in the kernel `defs/` catalogue).
//!
//! [`init::char`]: crate::init::char
//! [`init::string`]: crate::init::string
//! [`init::utf8`]: crate::init::utf8
//!
//! ## The encoder
//!
//! ```text
//! utf16EncodeChar : char → list u16        (the per-character encoder)
//! utf16Encode     : string → list u16      (fold over the char list)
//! ```
//!
//! `utf16EncodeChar c` cases on `n = char.code c`:
//!
//! ```text
//!   n < 0x10000   → [n]                                  (BMP, 1 code unit)
//!   else          → [0xD800 + (n-0x10000)/0x400,         (surrogate PAIR)
//!                    0xDC00 + (n-0x10000)%0x400]
//! ```
//!
//! **Note the surrogate twist** (the task's key UTF-16 subtlety): the
//! surrogate code units `0xD800..=0xDFFF` that `char` *excludes* as scalar
//! values ARE valid `u16` code units here — they are exactly what an astral
//! codepoint expands into. The high surrogate is `0xD800 + (n-0x10000)/0x400`
//! and the low surrogate `0xDC00 + (n-0x10000) mod 0x400`.
//!
//! Each unit is wrapped into `u16` by `int.fromNat[u16]`; like UTF-8 the
//! per-character encoder reduces on a *literal* codepoint to a concrete
//! `cons … nil` of `u16` literals ([`encode_char_lit`] — BMP, the
//! surrogate-pair boundaries, an emoji).
//!
//! `utf16Encode s = foldr (λc acc. (encodeChar c) ++ acc) nil (rep s)`; its
//! `nil`/`cons` recursion clauses ([`encode_nil`] / [`encode_cons`]) come
//! through the [`init::list_recursion`] `foldr`/`cat` machinery.
//!
//! [`init::list_recursion`]: crate::init::list_recursion
//!
//! ## What is proved here (genuine — hypothesis- and oracle-free)
//!
//! - the per-character encoder reduction lemmas ([`encode_char_lit`]);
//! - the encoder recursion clauses [`encode_nil`] / [`encode_cons`].
//!
//! ## Deferred (see `init/SKELETONS.md`)
//!
//! The validating decoder `utf16Decode : list u16 → option string` and the
//! full string round-trip by `list-induct` — same prefix-consumption gap as
//! UTF-8 (decode peels exactly one char's code units, 1 for a BMP unit, 2
//! for a well-formed surrogate pair).

use covalence_core::term::IntTag;
use covalence_core::{Error, Result, Term, Thm, Type};

use smol_str::SmolStr;
use std::sync::LazyLock;

use crate::init::char::{char_code, char_lit, char_ty};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::list_recursion::{foldr_cons, foldr_nil};
use crate::init::string::string_spec;

use covalence_core::defs::{
    TermSpec, cons, int_from_nat, list, list_cat, list_foldr, nat_add, nat_div, nat_lt, nat_mod,
    nat_sub, nil,
};

// ============================================================================
// Small term helpers.
// ============================================================================

fn u16_ty() -> Type {
    IntTag::U16.ty()
}

/// `list u16` — the UTF-16 code-unit sequence type.
fn unit_list() -> Type {
    list(u16_ty())
}

fn app2(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

fn lit(k: u64) -> Term {
    Term::nat_lit(k)
}

fn add(a: Term, b: Term) -> Term {
    app2(nat_add(), a, b)
}
fn sub(a: Term, b: Term) -> Term {
    app2(nat_sub(), a, b)
}
fn div(a: Term, k: u64) -> Term {
    app2(nat_div(), a, lit(k))
}
fn modulo(a: Term, k: u64) -> Term {
    app2(nat_mod(), a, lit(k))
}
fn lt(n: Term, k: u64) -> Term {
    app2(nat_lt(), n, lit(k))
}

/// `int.fromNat[u16] v : u16`.
fn unit_of(v: Term) -> Term {
    Term::app(int_from_nat(IntTag::U16), v)
}

fn ucons(b: Term, rest: Term) -> Term {
    app2(cons(u16_ty()), b, rest)
}
fn unil() -> Term {
    nil(u16_ty())
}

fn unit_list_of(units: Vec<Term>) -> Term {
    let mut acc = unil();
    for b in units.into_iter().rev() {
        acc = ucons(b, acc);
    }
    acc
}

// ============================================================================
// The codepoint → `list u16` body.
// ============================================================================

/// `encodeNat n : list u16` — the UTF-16 code-unit list for codepoint `n`.
fn encode_nat_body(n: &Term) -> Term {
    // BMP: [n].
    let bmp = unit_list_of(vec![unit_of(n.clone())]);

    // astral: m = n - 0x10000; [0xD800 + m/0x400, 0xDC00 + m%0x400].
    let m = sub(n.clone(), lit(0x10000));
    let hi = unit_of(add(lit(0xD800), div(m.clone(), 0x400)));
    let lo = unit_of(add(lit(0xDC00), modulo(m, 0x400)));
    let pair = unit_list_of(vec![hi, lo]);

    Term::cond(lt(n.clone(), 0x10000), bmp, pair)
}

// ============================================================================
// `utf16EncodeChar : char → list u16`.
// ============================================================================

fn encode_char_body() -> Term {
    let c = Term::free("c", char_ty());
    let n = Term::app(char_code(), c.clone());
    let body = encode_nat_body(&n);
    Term::abs(char_ty(), covalence_core::subst::close(&body, "c"))
}

/// `utf16EncodeChar : char → list u16` ≡ `λc. encodeNat (char.code c)`.
pub fn encode_char_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = encode_char_body();
        let ty = body
            .type_of()
            .expect("utf16EncodeChar body must type-check to char → list u16");
        TermSpec::new(SmolStr::new_static("utf16.encodeChar"), Some(ty), Some(body))
    });
    LAZY.clone()
}

/// `utf16EncodeChar : char → list u16`.
pub fn encode_char() -> Term {
    Term::term_spec(encode_char_spec(), Vec::new())
}

/// `⊢ utf16EncodeChar (char.mk k) = [u₀, …]` for a literal scalar value `k`
/// — fully reduced to its concrete `u16` code-unit list. Genuine
/// (hypothesis- and oracle-free).
pub fn encode_char_lit(k: u64) -> Result<Thm> {
    let c = char_lit(k);
    // ⊢ char.code (char.mk k) = k (scalar-value premise discharged per literal).
    let code_mk = crate::init::char::code_mk(&Term::nat_lit(k))?;
    let applied = Term::app(encode_char(), c);
    let unfolded = applied
        .delta_all(encode_char_spec().symbol())?
        .rhs_conv(|t| Ok(crate::init::eq::beta_nf(t.clone())))?;
    unfolded
        .rhs_conv(|t| t.rw_all(&code_mk))?
        .rhs_conv(|t| t.reduce())?
        .rhs_conv(crate::init::cond::collapse_conds)
}

// ============================================================================
// `utf16Encode : string → list u16`.
// ============================================================================

fn encode_step() -> Term {
    let c = Term::free("c", char_ty());
    let acc = Term::free("acc", unit_list());
    let ec = Term::app(encode_char(), c.clone());
    let catted = app2(list_cat(u16_ty()), ec, acc.clone());
    let lam_acc = Term::abs(unit_list(), covalence_core::subst::close(&catted, "acc"));
    Term::abs(char_ty(), covalence_core::subst::close(&lam_acc, "c"))
}

fn encode_body() -> Term {
    // λs:string. foldr step nil (rep s)
    let s = Term::free("s", crate::init::string::string_ty());
    let rep_s = Term::app(Term::spec_rep(string_spec(), Vec::new()), s.clone());
    let folded = Term::app(
        Term::app(Term::app(list_foldr(char_ty(), unit_list()), encode_step()), unil()),
        rep_s,
    );
    Term::abs(
        crate::init::string::string_ty(),
        covalence_core::subst::close(&folded, "s"),
    )
}

/// `utf16Encode : string → list u16` ≡
/// `λs. foldr (λc acc. utf16EncodeChar c ++ acc) nil (rep s)`.
pub fn encode_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = encode_body();
        let ty = body
            .type_of()
            .expect("utf16Encode body must type-check to string → list u16");
        TermSpec::new(SmolStr::new_static("utf16.encode"), Some(ty), Some(body))
    });
    LAZY.clone()
}

/// `utf16Encode : string → list u16`.
pub fn encode() -> Term {
    Term::term_spec(encode_spec(), Vec::new())
}

/// `⊢ utf16Encode s = foldr step nil (rep s)` — the δ-unfold (β-reduced).
fn encode_def(s: &Term) -> Result<Thm> {
    Term::app(encode(), s.clone())
        .delta_all(encode_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ utf16Encode string.empty = nil` — encoding the empty string yields
/// the empty code-unit list. Genuine (hypothesis- and oracle-free).
pub fn encode_nil() -> Result<Thm> {
    let empty = crate::init::string::string_empty();
    // utf16Encode empty = foldr step nil (rep empty)
    let def = encode_def(&empty)?;
    // rep empty = nil
    let rep_empty = crate::init::string::string_rep_empty()?;
    let on_nil = def.rhs_conv(|t| t.rw_all(&rep_empty))?;
    // foldr step nil nil = nil
    let base = foldr_nil(&char_ty(), &unit_list(), &encode_step(), &unil())?;
    on_nil.trans(base)
}

/// `⊢ utf16Encode (abs (cons c (rep s))) =
///      (utf16EncodeChar c) ++ utf16Encode s` — the encoder's `cons`
/// recursion clause. Genuine (hypothesis- and oracle-free).
pub fn encode_cons(c: &Term, s: &Term) -> Result<Thm> {
    let rep_s = Term::app(Term::spec_rep(string_spec(), Vec::new()), s.clone()); // rep s
    let consed = app2(cons(char_ty()), c.clone(), rep_s.clone()); // cons c (rep s)
    let s_cons = Term::app(Term::spec_abs(string_spec(), Vec::new()), consed.clone()); // abs (cons c (rep s))

    // utf16Encode s_cons = foldr step nil (rep s_cons)
    let def = encode_def(&s_cons)?;
    // rep s_cons = cons c (rep s)
    let rep_round = crate::init::string::string_rep_abs(&consed)?;
    let on_consed = def.rhs_conv(|t| t.rw_all(&rep_round))?;
    // foldr step nil (cons c (rep s)) = step c (foldr step nil (rep s))
    let fc = foldr_cons(&char_ty(), &unit_list(), &encode_step(), &unil(), c, &rep_s)?;
    // step c (foldr …) β= (encodeChar c) ++ (foldr step nil (rep s))
    let collapse = rhs_of(&fc)?.reduce()?;
    // foldr step nil (rep s) = utf16Encode s   (reverse encode_def)
    let fold_back = encode_def(s)?.sym()?;
    let ec = Term::app(encode_char(), c.clone());
    let cong = fold_back.cong_arg(Term::app(list_cat(u16_ty()), ec))?;

    crate::init::eq::trans_chain([on_consed, fc, collapse, cong])
}

fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u16_lit(v: u16) -> Term {
        Term::u16_lit(v)
    }

    fn assert_encodes(k: u64, expected: &[u16]) {
        let thm = encode_char_lit(k).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "encode_char_lit({k:#x}) is proved, not postulated"
        );
        assert!(thm.has_no_obs(), "encode_char_lit is oracle-free");
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &Term::app(encode_char(), char_lit(k)));
        let want = unit_list_of(expected.iter().map(|&u| u16_lit(u)).collect());
        assert_eq!(rhs, &want, "UTF-16 of {k:#x}");
    }

    #[test]
    fn encode_char_well_typed() {
        assert_eq!(
            encode_char().type_of().unwrap(),
            Type::fun(char_ty(), unit_list())
        );
    }

    #[test]
    fn bmp_single_unit() {
        // 'A' = U+0041 → [0x0041].
        assert_encodes(0x41, &[0x0041]);
        // '€' = U+20AC (BMP) → [0x20AC].
        assert_encodes(0x20AC, &[0x20AC]);
        // U+FFFF (last BMP scalar) → [0xFFFF].
        assert_encodes(0xFFFF, &[0xFFFF]);
        // U+D7FF (last scalar before the surrogate gap) → [0xD7FF].
        assert_encodes(0xD7FF, &[0xD7FF]);
    }

    #[test]
    fn astral_surrogate_pair() {
        // U+10000 (first astral) → [0xD800, 0xDC00].
        assert_encodes(0x10000, &[0xD800, 0xDC00]);
        // '😀' U+1F600 → [0xD83D, 0xDE00].
        assert_encodes(0x1F600, &[0xD83D, 0xDE00]);
        // U+10FFFF (last scalar) → [0xDBFF, 0xDFFF].
        assert_encodes(0x10FFFF, &[0xDBFF, 0xDFFF]);
    }

    #[test]
    fn encode_nil_is_empty() {
        let thm = encode_nil().unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(thm.concl().as_eq().unwrap().1, &unil());
    }

    #[test]
    fn encode_cons_recursion_clause() {
        let c = Term::free("c", char_ty());
        let s = Term::free("s", crate::init::string::string_ty());
        let thm = encode_cons(&c, &s).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let ec = Term::app(encode_char(), c.clone());
        let enc_s = Term::app(encode(), s.clone());
        let expected_rhs = app2(list_cat(u16_ty()), ec, enc_s);
        assert_eq!(thm.concl().as_eq().unwrap().1, &expected_rhs);
    }

    #[test]
    fn encode_string_well_typed() {
        assert_eq!(
            encode().type_of().unwrap(),
            Type::fun(crate::init::string::string_ty(), unit_list())
        );
    }
}
