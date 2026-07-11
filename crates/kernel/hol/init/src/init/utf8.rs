//! UTF-8 transcoding: `string ↔ bytes`.
//!
//! This is the **shell-level UTF-8 codec** over the `char`/`string`/`bytes`
//! substrate ([`init::char`], [`init::string`]). Like [`init::real`], the
//! codec constants live here (shell-defined `TermSpec`s with `SmolStr`
//! symbols), *not* in the kernel `defs/` catalogue — UTF-8 is an *encoding*
//! concern layered on the logical model, not part of it.
//!
//! [`init::char`]: crate::init::char
//! [`init::string`]: crate::init::string
//! [`init::real`]: crate::init::real
//!
//! ## The encoder
//!
//! ```text
//! utf8EncodeChar : char → list u8        (the per-character encoder)
//! utf8Encode     : string → bytes        (fold over the char list)
//! ```
//!
//! `utf8EncodeChar c` cases on the codepoint `n = char.code c`, producing
//! the 1–4 byte UTF-8 sequence (RFC 3629):
//!
//! ```text
//!   n < 0x80      → [n]                                              (1 byte, ASCII)
//!   n < 0x800     → [0xC0+n/64, 0x80+n%64]                           (2 bytes)
//!   n < 0x10000   → [0xE0+n/4096, 0x80+(n/64)%64, 0x80+n%64]         (3 bytes)
//!   else          → [0xF0+n/262144, 0x80+(n/4096)%64,               (4 bytes)
//!                    0x80+(n/64)%64, 0x80+n%64]
//! ```
//!
//! Each byte value is a `nat` arithmetic expression wrapped into `u8` by
//! `int.fromNat[u8]` ([`int_from_nat`]). All of `nat.div`/`nat.mod`/`nat.add`
//! and `int.fromNat[u8]` **reduce on literals**, so `utf8EncodeChar` of a
//! *literal* codepoint reduces all the way to a concrete `cons … nil` of
//! `u8` literals (the per-character reduction lemmas below — ASCII, 2-, 3-,
//! and 4-byte cases, including `€` and an astral codepoint).
//!
//! `utf8Encode s = abs (foldr (λc acc. (encodeChar c) ++ acc) nil (rep s))`
//! folds the per-character encodings, concatenating left-to-right. Its
//! `nil`/`cons` recursion clauses ([`encode_nil`], [`encode_cons`]) are
//! proved through the [`init::list_recursion`] `foldr`/`cat` machinery.
//!
//! [`init::list_recursion`]: crate::init::list_recursion
//!
//! ## What is proved here (genuine — hypothesis- and oracle-free)
//!
//! - the per-character encoder reduction lemmas at literal codepoints
//!   ([`encode_char_lit`]);
//! - the string-encoder recursion clauses [`encode_nil`] / [`encode_cons`].
//!
//! ## Deferred (see `init/SKELETONS.md`)
//!
//! The validating decoder `utf8Decode : bytes → option string` and the full
//! string round-trip `⊢ utf8Decode (utf8Encode s) = some s` by `list-induct`
//! — the cons case needs a "decode peels exactly one char's bytes off the
//! front" lemma whose proof is a large `nat`-range case analysis. The
//! per-character round-trip + the induction skeleton are the tractable core
//! delivered now; the prefix-consumption step is the skeleton.

use covalence_core::term::IntTag;
use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use smol_str::SmolStr;
use std::sync::LazyLock;

use crate::init::char::{char_code, char_ty};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::list_recursion::{foldr_cons, foldr_nil};

use covalence_hol_eval::defs::{
    TermSpec, cons, int_from_nat, list, list_cat, nat_add, nat_div, nat_lt, nat_mod, nil, option,
};

use crate::init::string::string_spec;

// ============================================================================
// Small term helpers.
// ============================================================================

fn u8_ty() -> Type {
    IntTag::U8.ty()
}

/// `u8` element list type (`list u8`), the carrier of `bytes`.
fn byte_list() -> Type {
    list(u8_ty())
}

fn app2(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

/// `nat.lit k`.
fn lit(k: u64) -> Term {
    covalence_hol_eval::mk_nat(k)
}

/// `a + b` on `nat`.
fn add(a: Term, b: Term) -> Term {
    app2(nat_add(), a, b)
}

/// `a / k` on `nat` (literal divisor).
fn div(a: Term, k: u64) -> Term {
    app2(nat_div(), a, lit(k))
}

/// `a mod k` on `nat` (literal modulus).
fn modulo(a: Term, k: u64) -> Term {
    app2(nat_mod(), a, lit(k))
}

/// `n < k` on `nat`.
fn lt(n: Term, k: u64) -> Term {
    app2(nat_lt(), n, lit(k))
}

/// `int.fromNat[u8] v : u8` — wrap a `nat` byte value into `u8`.
fn byte(v: Term) -> Term {
    Term::app(int_from_nat(IntTag::U8), v)
}

/// `cons (b : u8) (rest : list u8)`.
fn ucons(b: Term, rest: Term) -> Term {
    app2(cons(u8_ty()), b, rest)
}

/// `nil : list u8`.
fn unil() -> Term {
    nil(u8_ty())
}

/// A `list u8` literal `[b₀, b₁, …]`.
fn byte_list_of(bytes: Vec<Term>) -> Term {
    let mut acc = unil();
    for b in bytes.into_iter().rev() {
        acc = ucons(b, acc);
    }
    acc
}

// ============================================================================
// The codepoint → bytes body (a `list u8`), as a nested `cond` over ranges.
// ============================================================================

/// `encodeNat n : list u8` — the raw UTF-8 byte list for a codepoint `n`,
/// the nested-`cond` range encoder. `n` is a free `nat` here; the body is
/// reused both as the encoder's definition and as the per-literal reduction
/// target.
fn encode_nat_body(n: &Term) -> Term {
    // continuation byte 0x80 + (m mod 64).
    let cont = |m: Term| byte(add(lit(0x80), modulo(m, 64)));

    // 1-byte: [n].
    let one = byte_list_of(vec![byte(n.clone())]);

    // 2-byte: [0xC0 + n/64, 0x80 + n%64].
    let two = byte_list_of(vec![
        byte(add(lit(0xC0), div(n.clone(), 64))),
        cont(n.clone()),
    ]);

    // 3-byte: [0xE0 + n/4096, 0x80 + (n/64)%64, 0x80 + n%64].
    let three = byte_list_of(vec![
        byte(add(lit(0xE0), div(n.clone(), 4096))),
        cont(div(n.clone(), 64)),
        cont(n.clone()),
    ]);

    // 4-byte: [0xF0 + n/262144, 0x80 + (n/4096)%64, 0x80 + (n/64)%64, 0x80 + n%64].
    let four = byte_list_of(vec![
        byte(add(lit(0xF0), div(n.clone(), 0x40000))),
        cont(div(n.clone(), 4096)),
        cont(div(n.clone(), 64)),
        cont(n.clone()),
    ]);

    // if n < 0x80 then one
    // else if n < 0x800 then two
    // else if n < 0x10000 then three
    // else four
    Term::cond(
        lt(n.clone(), 0x80),
        one,
        Term::cond(
            lt(n.clone(), 0x800),
            two,
            Term::cond(lt(n.clone(), 0x10000), three, four),
        ),
    )
}

// ============================================================================
// `utf8EncodeChar : char → list u8`.
// ============================================================================

fn encode_char_body() -> Term {
    // λc:char. encodeNat (char.code c)
    let c = Term::free("c", char_ty());
    let n = Term::app(char_code(), c.clone());
    let body = encode_nat_body(&n);
    Term::abs(char_ty(), covalence_core::subst::close(&body, "c"))
}

/// `utf8EncodeChar : char → list u8` ≡ `λc. encodeNat (char.code c)` — the
/// per-character UTF-8 encoder, a shell-level defined constant.
pub fn encode_char_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = encode_char_body();
        let ty = body
            .type_of()
            .expect("utf8EncodeChar body must type-check to char → list u8");
        TermSpec::new(SmolStr::new_static("utf8.encodeChar"), Some(ty), Some(body))
    });
    LAZY.clone()
}

/// `utf8EncodeChar : char → list u8`.
pub fn encode_char() -> Term {
    Term::term_spec(encode_char_spec(), Vec::new())
}

/// `utf8EncodeChar (char.mk k)` reduced to its concrete `u8` byte list, for
/// a literal codepoint `k` that is a Unicode scalar value. Returns
/// `⊢ utf8EncodeChar (char.mk k) = [b₀, …]` — fully reduced (δ-unfold the
/// encoder + `char.mk`/`char.code`, then `reduce`, which decides the `cond`
/// range tests and folds the `nat` byte arithmetic + `int.fromNat[u8]`).
///
/// Genuine: hypothesis- and oracle-free. The single per-character anchor the
/// round-trip rests on (`reduce` denotes the byte sequence exactly).
pub fn encode_char_lit(k: u64) -> Result<Thm> {
    let c = crate::init::char::char_lit(k); // char.mk k
    let applied = Term::app(encode_char(), c);
    // ⊢ char.code (char.mk k) = k — the conditional codepoint round-trip,
    // with the scalar-value premise discharged by `prop_eq` (decided per
    // literal; errors on surrogates / out-of-range).
    let code_mk = crate::init::char::code_mk(&covalence_hol_eval::mk_nat(k))?;
    // δ-unfold the encoder and β-reduce the applied λ (so the bound `c` is
    // replaced by `char.mk k`), rewrite `char.code (char.mk k) → k`, then
    // reduce: the `cond` range tests fold and the byte arithmetic +
    // `int.fromNat[u8]` compute to `u8` literals.
    let unfolded = applied
        .delta_all(encode_char_spec().symbol())?
        .rhs_conv(|t| Ok(crate::init::eq::beta_nf(t.clone())))?;
    // After rewriting the codepoint and reducing, the `nat.lt` range tests
    // fold to `T`/`F` and the byte arithmetic computes; the only thing left
    // is collapsing the (defined-constant) `cond`s, which `reduce` does not
    // do — drive them with the `init::cond` clauses.
    unfolded
        .rhs_conv(|t| t.rw_all(&code_mk))?
        .rhs_conv(|t| t.reduce())?
        .rhs_conv(crate::init::cond::collapse_conds)
}

// ============================================================================
// `utf8Encode : string → bytes`.
// ============================================================================

/// The fold step `λc:char. λacc:list u8. (utf8EncodeChar c) ++ acc`.
fn encode_step() -> Term {
    let c = Term::free("c", char_ty());
    let acc = Term::free("acc", byte_list());
    let ec = Term::app(encode_char(), c.clone());
    let catted = app2(list_cat(u8_ty()), ec, acc.clone());
    let lam_acc = Term::abs(byte_list(), covalence_core::subst::close(&catted, "acc"));
    Term::abs(char_ty(), covalence_core::subst::close(&lam_acc, "c"))
}

fn encode_body() -> Term {
    // λs:string. abs[bytes] (foldr step nil (rep[string] s))
    let s = Term::free("s", crate::init::string::string_ty());
    let rep_s = Term::app(Term::spec_rep(string_spec(), Vec::new()), s.clone());
    let folded = Term::app(
        Term::app(
            Term::app(
                covalence_hol_eval::defs::list_foldr(char_ty(), byte_list()),
                encode_step(),
            ),
            unil(),
        ),
        rep_s,
    );
    let bytes_abs = Term::app(
        Term::spec_abs(covalence_hol_eval::defs::bytes_spec(), Vec::new()),
        folded,
    );
    Term::abs(
        crate::init::string::string_ty(),
        covalence_core::subst::close(&bytes_abs, "s"),
    )
}

/// `utf8Encode : string → bytes` ≡
/// `λs. abs (foldr (λc acc. utf8EncodeChar c ++ acc) nil (rep s))` — the
/// string UTF-8 encoder, a shell-level defined constant.
pub fn encode_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = encode_body();
        let ty = body
            .type_of()
            .expect("utf8Encode body must type-check to string → bytes");
        TermSpec::new(SmolStr::new_static("utf8.encode"), Some(ty), Some(body))
    });
    LAZY.clone()
}

/// `utf8Encode : string → bytes`.
pub fn encode() -> Term {
    Term::term_spec(encode_spec(), Vec::new())
}

// ============================================================================
// `utf8EncodeBytes : list char → list u8` — the carrier-level encoder (the
// raw fold, no `string`/`bytes` newtype wrappers). This is the form the
// `.cov` homomorphism theorem reasons about: `utf8Encode = abs ∘
// utf8EncodeBytes ∘ rep`, so a structural fact about `utf8EncodeBytes`
// transports to `utf8Encode`.
// ============================================================================

fn encode_bytes_body() -> Term {
    // λcs:list char. foldr step nil cs
    let cs = Term::free("cs", list(char_ty()));
    let folded = Term::app(
        Term::app(
            Term::app(
                covalence_hol_eval::defs::list_foldr(char_ty(), byte_list()),
                encode_step(),
            ),
            unil(),
        ),
        cs.clone(),
    );
    Term::abs(list(char_ty()), covalence_core::subst::close(&folded, "cs"))
}

/// `utf8EncodeBytes : list char → list u8` ≡ `λcs. foldr step nil cs` — the
/// carrier-level UTF-8 encoder.
pub fn encode_bytes_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = encode_bytes_body();
        let ty = body
            .type_of()
            .expect("utf8EncodeBytes body must type-check to list char → list u8");
        TermSpec::new(
            SmolStr::new_static("utf8.encodeBytes"),
            Some(ty),
            Some(body),
        )
    });
    LAZY.clone()
}

/// `utf8EncodeBytes : list char → list u8`.
pub fn encode_bytes() -> Term {
    Term::term_spec(encode_bytes_spec(), Vec::new())
}

/// `⊢ utf8EncodeBytes cs = foldr step nil cs` — the δ-unfold (β-reduced).
fn encode_bytes_def(cs: &Term) -> Result<Thm> {
    Term::app(encode_bytes(), cs.clone())
        .delta_all(encode_bytes_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ utf8EncodeBytes nil = nil` — the carrier encoder's `nil` clause.
/// Genuine (hypothesis- and oracle-free).
pub fn encode_bytes_nil() -> Result<Thm> {
    let def = encode_bytes_def(&nil(char_ty()))?; // = foldr step nil nil
    let base = foldr_nil(&char_ty(), &byte_list(), &encode_step(), &unil())?;
    def.trans(base)
}

/// `⊢ utf8EncodeBytes (cons c cs) = (utf8EncodeChar c) ++ utf8EncodeBytes cs`
/// — the carrier encoder's `cons` clause. Genuine (hypothesis- and
/// oracle-free).
pub fn encode_bytes_cons(c: &Term, cs: &Term) -> Result<Thm> {
    let consed = app2(cons(char_ty()), c.clone(), cs.clone());
    let def = encode_bytes_def(&consed)?; // = foldr step nil (cons c cs)
    let fc = foldr_cons(&char_ty(), &byte_list(), &encode_step(), &unil(), c, cs)?;
    let collapse = rhs_of(&fc)?.reduce()?; // step c (foldr …) β= (encodeChar c) ++ (foldr …)
    let fold_back = encode_bytes_def(cs)?.sym()?; // foldr step nil cs = utf8EncodeBytes cs
    let ec = Term::app(encode_char(), c.clone());
    let cong = fold_back.cong_arg(Term::app(list_cat(u8_ty()), ec))?;
    crate::init::eq::trans_chain([def, fc, collapse, cong])
}

/// The `list u8` carrier behind `utf8Encode s`, i.e. the fold itself:
/// `foldr step nil (rep s)`. The encoder is `abs` of this.
fn encode_carrier(rep_s: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(
                covalence_hol_eval::defs::list_foldr(char_ty(), byte_list()),
                encode_step(),
            ),
            unil(),
        ),
        rep_s.clone(),
    )
}

/// `⊢ rep (utf8Encode s) = foldr step nil (rep s)` — the carrier of the
/// encoder's `bytes` result is the raw fold over the character carrier. The
/// bridge through the `bytes` newtype seam (`rep ∘ abs = id`), used by the
/// recursion clauses below.
fn encode_rep(s: &Term) -> Result<Thm> {
    let rep_s = Term::app(Term::spec_rep(string_spec(), Vec::new()), s.clone());
    // rep (utf8Encode s) = rep (abs (foldr step nil (rep s)))   [δ + β]
    let rep_enc = Term::app(
        Term::spec_rep(covalence_hol_eval::defs::bytes_spec(), Vec::new()),
        Term::app(encode(), s.clone()),
    );
    let unfold = Thm::refl(rep_enc)?.rhs_conv(|t| t.rw_all(&encode_def(s)?))?;
    // rep (abs carrier) = carrier   [bytes newtype round-trip]
    let collapse = crate::init::string::bytes_rep_abs(&encode_carrier(&rep_s))?;
    unfold.trans(collapse)
}

/// `⊢ utf8Encode s = abs (foldr step nil (rep s))` — just the δ-unfold of
/// the encoder constant (β-reduced).
fn encode_def(s: &Term) -> Result<Thm> {
    Term::app(encode(), s.clone())
        .delta_all(encode_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ rep (utf8Encode string.empty) = nil` — encoding the empty string
/// yields the empty byte carrier. Genuine (hypothesis- and oracle-free):
/// the carrier is `foldr step nil (rep empty) = foldr step nil nil = nil`.
pub fn encode_nil() -> Result<Thm> {
    let empty = crate::init::string::string_empty();
    // rep (utf8Encode empty) = foldr step nil (rep empty)
    let rep_enc = encode_rep(&empty)?;
    // rep empty = nil  (string newtype seam)
    let rep_empty = crate::init::string::string_rep_empty()?;
    // foldr step nil (rep empty) = foldr step nil nil
    let to_nil = rep_enc.rhs_conv(|t| t.rw_all(&rep_empty))?;
    // foldr step nil nil = nil
    let base = foldr_nil(&char_ty(), &byte_list(), &encode_step(), &unil())?;
    to_nil.trans(base)
}

/// `⊢ rep (utf8Encode (abs (cons c (rep s)))) =
///      (utf8EncodeChar c) ++ rep (utf8Encode s)` — the encoder's `cons`
/// recursion clause, at the carrier level. Genuine (hypothesis- and
/// oracle-free): `foldr step nil (cons c cs) = step c (foldr step nil cs) =
/// (encodeChar c) ++ (foldr step nil cs)`, and the inner fold folds back to
/// `rep (utf8Encode (abs cs))`.
///
/// Stated at the carrier level (over `rep`) because `string`'s `cons`
/// constructor goes through the `abs`/`rep` seam; `c : char`, `s : string`.
pub fn encode_cons(c: &Term, s: &Term) -> Result<Thm> {
    let cs = Term::app(Term::spec_rep(string_spec(), Vec::new()), s.clone()); // rep s : list char
    let consed = app2(cons(char_ty()), c.clone(), cs.clone()); // cons c (rep s)
    let s_cons = Term::app(Term::spec_abs(string_spec(), Vec::new()), consed.clone()); // abs (cons c (rep s))

    // rep (utf8Encode s_cons) = foldr step nil (rep s_cons)
    let rep_enc = encode_rep(&s_cons)?;
    // rep s_cons = cons c (rep s)   (string newtype round-trip)
    let rep_round = crate::init::string::string_rep_abs(&consed)?;
    // foldr step nil (rep s_cons) = foldr step nil (cons c (rep s))
    let on_consed = rep_enc.rhs_conv(|t| t.rw_all(&rep_round))?;
    // foldr step nil (cons c (rep s)) = step c (foldr step nil (rep s))
    let fc = foldr_cons(&char_ty(), &byte_list(), &encode_step(), &unil(), c, &cs)?;
    // step c (foldr step nil (rep s)) β= (encodeChar c) ++ (foldr step nil (rep s))
    let collapse = rhs_of(&fc)?.reduce()?;
    // foldr step nil (rep s) = rep (utf8Encode s)   (reverse of encode_rep s)
    let fold_back = encode_rep(s)?.sym()?;
    // (encodeChar c) ++ (foldr …) = (encodeChar c) ++ (rep (utf8Encode s))
    let ec = Term::app(encode_char(), c.clone());
    let cong = fold_back.cong_arg(Term::app(list_cat(u8_ty()), ec))?;

    crate::init::eq::trans_chain([on_consed, fc, collapse, cong])
}

// ============================================================================
// Decoder (ASCII fragment) + the per-character round-trip.
//
// The full validating `utf8Decode : bytes → option string` and the inductive
// string round-trip are deferred (see `init/SKELETONS.md`): the multi-byte
// continuation-byte validation + codepoint reassembly is a large `nat`-range
// case analysis, and the string round-trip needs a "decode peels exactly one
// char's bytes off the front" lemma. What is genuine *now* is the **single
// ASCII byte** decode and its round-trip — the per-character anchor.
// ============================================================================

/// `decodeAscii1 : list u8 → option char` ≡
/// `λl. optionCase none (λb. cond (toNat b < 0x80) (some (char.mk (toNat b)))
///                            none) (head l)` — decode the first character of
/// a byte list, **restricted to the ASCII (1-byte) case**: `none` on the
/// empty list or a non-ASCII lead byte, else the scalar `char.mk (toNat b)`.
/// A shell-level defined constant (the carrier-level decoder; the `bytes`
/// wrapper is `λbs. decodeAscii1 (rep bs)`).
/// `λb:u8. cond (toNat b < 0x80) (some (char.mk (toNat b))) none` — the
/// `optionCase` `some`-branch of [`decode_ascii1`]. Factored out so the
/// round-trip's `case_some` application uses the *identical* function term.
fn decode_some_branch() -> Term {
    use covalence_hol_eval::defs::{none, some};
    let b = Term::free("b", u8_ty());
    let to_nat = Term::app(covalence_hol_eval::defs::int_to_nat(IntTag::U8), b.clone());
    let is_ascii = app2(nat_lt(), to_nat.clone(), lit(0x80));
    let mk = Term::app(crate::init::char::char_mk(), to_nat);
    let some_c = Term::app(some(char_ty()), mk);
    let branch = Term::cond(is_ascii, some_c, none(char_ty()));
    Term::abs(u8_ty(), covalence_core::subst::close(&branch, "b"))
}

fn decode_ascii1_body() -> Term {
    use covalence_hol_eval::defs::{head, none, option_case};
    let l = Term::free("l", byte_list());
    let f = decode_some_branch();
    let head_l = Term::app(head(u8_ty()), l.clone());
    let case = Term::app(
        Term::app(
            Term::app(option_case(u8_ty(), option(char_ty())), none(char_ty())),
            f,
        ),
        head_l,
    );
    Term::abs(byte_list(), covalence_core::subst::close(&case, "l"))
}

/// `decodeAscii1 : list u8 → option char` — the ASCII-fragment carrier-level
/// decoder.
pub fn decode_ascii1_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = decode_ascii1_body();
        let ty = body
            .type_of()
            .expect("decodeAscii1 body must type-check to list u8 → option char");
        TermSpec::new(
            SmolStr::new_static("utf8.decodeAscii1"),
            Some(ty),
            Some(body),
        )
    });
    LAZY.clone()
}

/// `decodeAscii1 : list u8 → option char`.
pub fn decode_ascii1() -> Term {
    Term::term_spec(decode_ascii1_spec(), Vec::new())
}

/// `⊢ decodeAscii1 (utf8EncodeChar (char.mk k)) = some (char.mk k)` for a
/// literal **ASCII** scalar value `k` (`k < 0x80`) — the per-character UTF-8
/// round-trip in the ASCII fragment. Genuine: hypothesis- and oracle-free.
///
/// Encoding produces `[u8 k]` ([`encode_char_lit`]); decoding reads its head
/// (`head_cons` ⟹ `some (u8 k)`), the `optionCase` fires the `some` branch,
/// `toNat (u8 k) = k` and `k < 0x80 = T` reduce, the `cond` collapses, and
/// `char.mk (toNat (u8 k)) = char.mk k`. Errors if `k ≥ 0x80` (not ASCII —
/// the round-trip is then a multi-byte fact, deferred).
pub fn decode_ascii1_round_trip(k: u64) -> Result<Thm> {
    if k >= 0x80 {
        return Err(Error::ConnectiveRule(
            "decode_ascii1_round_trip: codepoint is not ASCII (k ≥ 0x80)".into(),
        ));
    }
    // enc : ⊢ utf8EncodeChar (char.mk k) = [u8 k]
    let enc = encode_char_lit(k)?;
    let bytes = rhs_of(&enc)?; // cons (u8 k) nil
    // decodeAscii1 [u8 k] : δ-unfold + β to the optionCase form.
    let unfolded = Term::app(decode_ascii1(), bytes.clone())
        .delta_all(decode_ascii1_spec().symbol())?
        .rhs_conv(|t| Ok(crate::init::eq::beta_nf(t.clone())))?;
    // head [u8 k] = some (u8 k)   (head_cons on the literal cons).
    let byte0 = covalence_hol_eval::mk_u8(k as u8);
    let head_eq = crate::init::list::head_cons(&u8_ty(), &byte0, &unil())?;
    // The `optionCase`'s `some` branch — `λb. cond (toNat b < 0x80)
    // (some (char.mk (toNat b))) none` — needed to fire `case_some`.
    let some_branch = decode_some_branch();
    // optionCase none f (some (u8 k)) = f (u8 k)   (init::option::case_some).
    let case_clause = crate::init::option::case_some(
        &u8_ty(),
        &option(char_ty()),
        &covalence_hol_eval::defs::none(char_ty()),
        &some_branch,
        &byte0,
    )?;
    // Rewrite `head (cons …) → some (u8 k)`, fire `optionCase … (some …) →
    // f (u8 k)`, β-reduce, reduce the arithmetic (`toNat (u8 k) = k`,
    // `k < 0x80 = T`), and collapse the `cond`.
    let decoded = unfolded
        .rhs_conv(|t| t.rw_all(&head_eq))?
        .rhs_conv(|t| t.rw_all(&case_clause))?
        .rhs_conv(|t| Ok(crate::init::eq::beta_nf(t.clone())))?
        .rhs_conv(|t| t.reduce())?
        .rhs_conv(crate::init::cond::collapse_conds)?;
    // Bridge the LHS back through `enc` so it reads
    // `decodeAscii1 (utf8EncodeChar (char.mk k))`.
    let enc_cong = enc.cong_arg(decode_ascii1())?; // decodeAscii1 (encodeChar (mk k)) = decodeAscii1 [u8 k]
    enc_cong.trans(decoded)
}

// ============================================================================
// Small helpers.
// ============================================================================

fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

// ============================================================================
// `text` env + the `utf8.cov` port.
// ============================================================================

/// The `utf8prim` environment imported by `utf8.cov`: the carrier-level
/// encoder `utf8.encodeBytes`, the per-character encoder `utf8.encodeChar`,
/// the `list` operators it rides on (`cons`/`nil`/`cat`), and the
/// **encoder recursion clauses** (`encode_nil`/`encode_cons`) as Rust-proved
/// givens (they cross the `foldr` recursion theorem, so they stay givens —
/// the `list.cov` `listprim` pattern). `utf8.cov` proves a NEW fact over
/// them — the encoder **monoid homomorphism** — by `list-induct`.
pub fn utf8_env() -> crate::script::Env {
    use crate::script::{ConstDef, Env};

    use crate::init::list_recursion::{cat_cons, cat_nil};
    use covalence_hol_eval::defs::nil as defs_nil;

    let cty = char_ty();
    let bty = u8_ty();
    let mut e = Env::empty();
    // encoder ops
    e.define_const("utf8.encodeBytes", ConstDef::Op(encode_bytes()));
    e.define_const("utf8.encodeChar", ConstDef::Op(encode_char()));
    // The homomorphism mixes two `list.cat` instantiations — `list char`
    // (domain) and `list u8` (codomain). A single `'a`-schematic name can't
    // carry both in one proof, so register them under DISTINCT names: `catC`
    // / `consC` / `nilC` on the char list, `catB` on the byte list.
    e.define_const("catC", ConstDef::Op(list_cat(cty.clone())));
    e.define_const("consC", ConstDef::Op(cons(cty.clone())));
    e.define_const("nilC", ConstDef::Op(defs_nil(cty.clone())));
    e.define_const("catB", ConstDef::Op(list_cat(bty.clone())));

    let c = Term::free("c", cty.clone());
    let cs = Term::free("cs", list(cty.clone()));
    let ds = Term::free("ds", list(cty.clone()));
    let close1 = |th: Thm, name: &str, ty: &Type| th.all_intro(name, ty.clone()).unwrap();

    // -- encoder recursion clauses (Rust givens) --
    // encode_nil : utf8.encodeBytes nilC = nilB        (nilB is `nil u8`)
    e.define_lemma("encode_nil", encode_bytes_nil().unwrap());
    // encode_cons : ∀c cs. encodeBytes (consC c cs) = catB (encodeChar c) (encodeBytes cs)
    e.define_lemma(
        "encode_cons",
        close1(
            close1(
                encode_bytes_cons(&c, &cs).unwrap(),
                "cs",
                &list(cty.clone()),
            ),
            "c",
            &cty,
        ),
    );

    // -- char-list append clauses (for the induction's `catC` reasoning) --
    // catC_nil : ∀ds. catC nilC ds = ds
    e.define_lemma(
        "catC_nil",
        close1(cat_nil(&cty, &ds).unwrap(), "ds", &list(cty.clone())),
    );
    // catC_cons : ∀c cs ds. catC (consC c cs) ds = consC c (catC cs ds)
    e.define_lemma(
        "catC_cons",
        close1(
            close1(
                close1(
                    cat_cons(&cty, &c, &cs, &ds).unwrap(),
                    "ds",
                    &list(cty.clone()),
                ),
                "cs",
                &list(cty.clone()),
            ),
            "c",
            &cty,
        ),
    );

    // -- byte-list clauses (codomain) --
    // catB associativity (polymorphic `list.cov` cat_assoc instantiated at u8).
    e.define_lemma(
        "catB_assoc",
        crate::init::list::cov::cat_assoc_cov()
            .inst_tfree("a", bty.clone())
            .unwrap(),
    );
    // catB_nil : ∀ys. catB nilB ys = ys
    let ys = Term::free("ys", list(bty.clone()));
    e.define_lemma(
        "catB_nil",
        close1(cat_nil(&bty, &ys).unwrap(), "ys", &list(bty.clone())),
    );
    e
}

crate::cov_theory! {
    /// UTF-8 encoder structural theorems ported to `utf8.cov`, over `core`,
    /// `listprim` (the `list` seam), and `utf8prim`. Driven by the
    /// `list-induct` tactic.
    pub mod cov from "utf8.cov" {
        import "core" = crate::script::Env::core();
        import "utf8prim" = crate::init::utf8::utf8_env();
        "encode_cat" => pub fn encode_cat_cov;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u8_lit(v: u8) -> Term {
        covalence_hol_eval::mk_u8(v)
    }

    /// Assert `encode_char_lit(k)` reduces to exactly `expected` (a list of
    /// `u8` byte values), and is genuine.
    fn assert_encodes(k: u64, expected: &[u8]) {
        let thm = encode_char_lit(k).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "encode_char_lit({k:#x}) is proved, not postulated"
        );
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(
            lhs,
            &Term::app(encode_char(), crate::init::char::char_lit(k))
        );
        let want = byte_list_of(expected.iter().map(|&b| u8_lit(b)).collect());
        assert_eq!(rhs, &want, "UTF-8 of {k:#x}");
    }

    #[test]
    fn encode_char_well_typed() {
        assert_eq!(
            encode_char().type_of().unwrap(),
            Type::fun(char_ty(), byte_list())
        );
    }

    #[test]
    fn ascii_one_byte() {
        // 'A' = U+0041 → [0x41].
        assert_encodes(0x41, &[0x41]);
        // NUL → [0x00], and the boundary 0x7F → [0x7F].
        assert_encodes(0x00, &[0x00]);
        assert_encodes(0x7F, &[0x7F]);
    }

    #[test]
    fn two_byte() {
        // U+0080 (first 2-byte) → [0xC2, 0x80].
        assert_encodes(0x80, &[0xC2, 0x80]);
        // 'é' = U+00E9 → [0xC3, 0xA9].
        assert_encodes(0xE9, &[0xC3, 0xA9]);
        // U+07FF (last 2-byte) → [0xDF, 0xBF].
        assert_encodes(0x7FF, &[0xDF, 0xBF]);
    }

    #[test]
    fn three_byte() {
        // U+0800 (first 3-byte) → [0xE0, 0xA0, 0x80].
        assert_encodes(0x800, &[0xE0, 0xA0, 0x80]);
        // '€' = U+20AC → [0xE2, 0x82, 0xAC].
        assert_encodes(0x20AC, &[0xE2, 0x82, 0xAC]);
        // U+FFFF (last 3-byte, a scalar) → [0xEF, 0xBF, 0xBF].
        assert_encodes(0xFFFF, &[0xEF, 0xBF, 0xBF]);
    }

    #[test]
    fn four_byte() {
        // U+10000 (first 4-byte) → [0xF0, 0x90, 0x80, 0x80].
        assert_encodes(0x10000, &[0xF0, 0x90, 0x80, 0x80]);
        // '😀' U+1F600 → [0xF0, 0x9F, 0x98, 0x80].
        assert_encodes(0x1F600, &[0xF0, 0x9F, 0x98, 0x80]);
        // U+10FFFF (last scalar) → [0xF4, 0x8F, 0xBF, 0xBF].
        assert_encodes(0x10FFFF, &[0xF4, 0x8F, 0xBF, 0xBF]);
    }

    #[test]
    fn encode_nil_is_empty_carrier() {
        let thm = encode_nil().unwrap();
        assert!(
            thm.hyps().is_empty(),
            "encode_nil is proved, not postulated"
        );
        assert_eq!(thm.concl().as_eq().unwrap().1, &unil());
    }

    #[test]
    fn encode_cons_recursion_clause() {
        let c = Term::free("c", char_ty());
        let s = Term::free("s", crate::init::string::string_ty());
        let thm = encode_cons(&c, &s).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "encode_cons is proved, not postulated"
        );
        // RHS is (encodeChar c) ++ rep (utf8Encode s).
        let ec = Term::app(encode_char(), c.clone());
        let rep_enc_s = Term::app(
            Term::spec_rep(covalence_hol_eval::defs::bytes_spec(), Vec::new()),
            Term::app(encode(), s.clone()),
        );
        let expected_rhs = app2(list_cat(u8_ty()), ec, rep_enc_s);
        assert_eq!(thm.concl().as_eq().unwrap().1, &expected_rhs);
    }

    #[test]
    fn encode_string_well_typed() {
        assert_eq!(
            encode().type_of().unwrap(),
            Type::fun(crate::init::string::string_ty(), Type::bytes())
        );
    }

    #[test]
    fn decode_ascii_round_trips() {
        use covalence_hol_eval::defs::some;
        // ⊢ decodeAscii1 (utf8EncodeChar (char.mk k)) = some (char.mk k) for
        // ASCII k. Genuine per-character round-trip.
        for &k in &[0x00u64, 0x41, 0x7F] {
            let thm = decode_ascii1_round_trip(k).unwrap();
            assert!(
                thm.hyps().is_empty(),
                "decode_ascii1_round_trip({k:#x}) is proved, not postulated"
            );
            let (lhs, rhs) = thm.concl().as_eq().unwrap();
            let enc = Term::app(encode_char(), crate::init::char::char_lit(k));
            assert_eq!(lhs, &Term::app(decode_ascii1(), enc));
            let expected = Term::app(some(char_ty()), crate::init::char::char_lit(k));
            assert_eq!(rhs, &expected, "decode∘encode of {k:#x}");
        }
    }

    #[test]
    fn decode_ascii_rejects_non_ascii() {
        // The ASCII fragment only covers k < 0x80; multi-byte is deferred.
        assert!(decode_ascii1_round_trip(0x80).is_err());
        assert!(decode_ascii1_round_trip(0x20AC).is_err());
    }

    #[test]
    fn encode_bytes_clauses_are_genuine() {
        let c = Term::free("c", char_ty());
        let cs = Term::free("cs", list(char_ty()));
        let en = encode_bytes_nil().unwrap();
        assert!(en.hyps().is_empty());
        assert_eq!(en.concl().as_eq().unwrap().1, &unil());
        let ec = encode_bytes_cons(&c, &cs).unwrap();
        assert!(ec.hyps().is_empty());
    }
}

#[cfg(test)]
mod cov_tests {
    use super::*;

    #[test]
    fn encode_cat_homomorphism_is_genuine() {
        // ⊢ ∀cs ds. encodeBytes (cat cs ds) = cat (encodeBytes cs)
        // (encodeBytes ds) — the encoder monoid homomorphism, proved in
        // `utf8.cov` by `list-induct`. Genuine: hypothesis- and oracle-free.
        let thm = cov::encode_cat_cov();
        assert!(
            thm.hyps().is_empty(),
            "encode_cat is proved, not postulated"
        );
        // It is a `∀cs ds. _ = _` over `list char`.
        assert!(thm.concl().type_of().unwrap().is_bool());
    }
}
