//! `sexpr_parse` — a **fuel-bounded S-expression reader** over `bytes`
//! (`list u8`) producing the carved [`sexpr`](mod@crate::init::inductive::carved)
//! datatype (stage SP1). This is the Lisp/JSON-direction parser: it reads
//! one S-expression off the front of a byte string and returns the value
//! together with the unconsumed suffix — the `(value, remaining)` convention
//! the landed `nat`/`int` parsers established
//! ([`crate::init::nat_parse`], [`crate::init::int_parse`]).
//!
//! ```text
//! parseSexpr : nat → bytes → option (sexpr × bytes)
//! ```
//!
//! ## Grammar
//!
//! - **whitespace** — space (32), tab (9), LF (10), CR (13) — skipped before
//!   every token (via the landed [`span_digits_bytes`] with a whitespace
//!   predicate);
//! - **atom** — a maximal run of non-whitespace, non-parenthesis bytes,
//!   yielding `atom (bytes.abs run)`;
//! - **list** — `'(' e₁ e₂ … eₙ ')'` yielding the `scons`-chain
//!   `scons e₁ (scons e₂ … (scons eₙ snil))` (`snil` for the empty list).
//!
//! ## The fuel recursion
//!
//! S-expression nesting/length is unbounded, so the reader is **not**
//! structural on its input; it is defined by primitive recursion on a `nat`
//! *fuel* bound through the landed `nat` recursor `natRec`
//! ([`crate::init::recursion`]), at result type `bool → bytes → option (sexpr
//! × bytes)`. The boolean **mode** picks the two mutually-recursive readers —
//! `false` reads one expression, `true` reads the tail of a list — so a single
//! `natRec` encodes both. Each recursive call is at one-less fuel; concrete
//! inputs supply fuel ≥ the token count. Exhausted fuel returns `none`.
//!
//! ## What is proved
//!
//! - the **step-unfolding** lemma [`parse_unfold`] (`parseFn (succ n) = …`) and
//!   base [`parse_base`], the reader's defining equations;
//! - **concrete parses** by an unfolding harness (in tests): atoms, flat and
//!   nested lists, the empty list, `none` on malformed/empty input, and that
//!   the unconsumed suffix is returned;
//! - the **structural agreement** theorem [`parsed_cons_struct`]: for a parse
//!   that yields a `scons` node, `consp`/`car`/`cdr` compute to `true`/head/
//!   tail — the parsed list's shape agrees with `car`/`cdr`/`consp`
//!   ([`crate::init::lisp`]).
//!
//! The `string` (list char) counterpart, the ASCII string⇄bytes agreement,
//! the total parse-invariant (`fuel`-monotone success), and reader
//! associativity are recorded as follow-ups in the generated open-work index.

use covalence_core::{IntTag, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{
    bytes_spec, cond, fst, head, int_to_nat, nat_le, nat_rec, none, option_case, pair, snd, some,
    tail,
};
use covalence_hol_eval::derived::DerivedRules;
use covalence_parsing_api::{PrefixInterpretation, SameInterpretation, Span};

use crate::init::ext::ThmExt;
use crate::init::inductive::carved::carved;
use crate::init::nat_parse_bytes::span_digits_bytes;

// ============================================================================
// Types.
// ============================================================================

fn u8_t() -> Type {
    defs::u8_ty()
}

fn bool_t() -> Type {
    Type::bool()
}

/// `bytes := list u8` — the reader's *carrier* input/suffix type (the raw
/// list, as in [`crate::init::nat_parse_bytes`]; distinct from the `bytes`
/// *newtype* an atom's payload wraps).
fn blist_t() -> Type {
    defs::list(u8_t())
}

/// The carved `sexpr` type.
fn tau() -> Type {
    carved().expect("carved sexpr theory builds").tau.clone()
}

/// `sexpr × bytes` — the parse payload (value, remaining suffix).
fn payload_t() -> Type {
    defs::prod(tau(), blist_t())
}

/// `option (sexpr × bytes)` — the parse result.
fn res_t() -> Type {
    defs::option(payload_t())
}

/// `bool → bytes → option (sexpr × bytes)` — the `natRec` result type (the
/// mode-dispatched reader).
fn reader_t() -> Type {
    Type::fun(bool_t(), Type::fun(blist_t(), res_t()))
}

// ============================================================================
// Small term builders.
// ============================================================================

fn lit(k: u64) -> Term {
    covalence_hol_eval::mk_nat(k)
}

fn lam(name: &str, ty: Type, body: Term) -> Term {
    Term::abs(ty, subst::close(&body, name))
}

/// `u8.toNat b : nat` — the unsigned value of a byte.
fn val(b: &Term) -> Term {
    Term::app(int_to_nat(IntTag::U8), b.clone())
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

fn bnot(a: Term) -> Term {
    crate::HolLightCtx::new().mk_not(a)
}

/// `cond[α] c x y`.
fn cond_app(ty: Type, c: Term, x: Term, y: Term) -> Term {
    Term::app(Term::app(Term::app(cond(ty), c), x), y)
}

/// `list.head s : option u8`.
fn head_b(s: &Term) -> Term {
    Term::app(head(u8_t()), s.clone())
}

/// `list.tail s : bytes`.
fn tail_b(s: &Term) -> Term {
    Term::app(tail(u8_t()), s.clone())
}

/// `option.case[u8,bool] false pred (head s) : bool` — "the first byte of `s`
/// exists and satisfies `pred`".
fn head_sat(pred: &Term, s: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(
                option_case(u8_t(), bool_t()),
                covalence_hol_eval::mk_bool(false),
            ),
            pred.clone(),
        ),
        head_b(s),
    )
}

/// `some[sexpr×bytes] p : option (sexpr × bytes)`.
fn some_r(p: Term) -> Term {
    Term::app(some(payload_t()), p)
}

/// `none : option (sexpr × bytes)`.
fn none_r() -> Term {
    none(payload_t())
}

/// `pair[sexpr,bytes] v s : sexpr × bytes`.
fn pair_r(v: Term, s: Term) -> Term {
    Term::app(Term::app(pair(tau(), blist_t()), v), s)
}

/// `fst[sexpr,bytes] p : sexpr`.
fn fst_r(p: &Term) -> Term {
    Term::app(fst(tau(), blist_t()), p.clone())
}

/// `snd[sexpr,bytes] p : bytes`.
fn snd_r(p: &Term) -> Term {
    Term::app(snd(tau(), blist_t()), p.clone())
}

/// `bytes.abs l : bytes` — wrap a `list u8` run into the `bytes` newtype (the
/// carved `atom` constructor's payload type).
fn bytes_abs(l: Term) -> Term {
    Term::app(Term::spec_abs(bytes_spec(), Vec::new()), l)
}

/// `atom (bytes.abs run) : sexpr`.
fn atom_of(run: Term) -> Term {
    Term::app(carved().expect("carved").atom.clone(), bytes_abs(run))
}

/// `snil : sexpr`.
fn snil() -> Term {
    carved().expect("carved").snil.clone()
}

/// `scons h t : sexpr`.
fn scons(h: Term, t: Term) -> Term {
    Term::app(Term::app(carved().expect("carved").scons.clone(), h), t)
}

// ============================================================================
// Byte-class predicates.
// ============================================================================

/// `λb. nat_le k (u8.toNat b) ∧ nat_le (u8.toNat b) k` — "the byte is `k`".
fn byte_is(k: u64) -> Term {
    let b = Term::free("b", u8_t());
    lam("b", u8_t(), band(le(lit(k), val(&b)), le(val(&b), lit(k))))
}

/// `λb. is 9 ∨ is 10 ∨ is 13 ∨ is 32` — the ASCII whitespace predicate
/// (tab / LF / CR / space).
fn is_ws() -> Term {
    let b = Term::free("b", u8_t());
    let is = |k: u64| band(le(lit(k), val(&b)), le(val(&b), lit(k)));
    let body = bor(bor(bor(is(9), is(10)), is(13)), is(32));
    lam("b", u8_t(), body)
}

/// `λb. is 40` — the open-paren predicate (`'('`).
fn is_open() -> Term {
    byte_is(40)
}

/// `λb. is 41` — the close-paren predicate (`')'`).
fn is_close() -> Term {
    byte_is(41)
}

/// `λb. ¬ws b ∧ ¬(b = '(') ∧ ¬(b = ')')` — the atom-byte predicate: a byte
/// that neither delimits nor separates.
fn is_atom() -> Term {
    let b = Term::free("b", u8_t());
    let is = |k: u64| band(le(lit(k), val(&b)), le(val(&b), lit(k)));
    let ws = bor(bor(bor(is(9), is(10)), is(13)), is(32));
    let body = band(bnot(ws), band(bnot(is(40)), bnot(is(41))));
    lam("b", u8_t(), body)
}

// ============================================================================
// Whitespace skipping + atom runs (via the landed `span` machinery).
// ============================================================================

/// `snd (span_digits_bytes is_ws s) : bytes` — `s` with its leading
/// whitespace removed.
fn skip_ws(s: &Term) -> Term {
    snd_bb(Term::app(span_digits_bytes(&is_ws()), s.clone()))
}

/// `fst`/`snd` on a `bytes × bytes` span result.
fn fst_bb(p: Term) -> Term {
    Term::app(fst(blist_t(), blist_t()), p)
}
fn snd_bb(p: Term) -> Term {
    Term::app(snd(blist_t(), blist_t()), p)
}

/// The atom span of `s1`: `span_digits_bytes is_atom s1 : bytes × bytes`.
fn atom_span(s1: &Term) -> Term {
    Term::app(span_digits_bytes(&is_atom()), s1.clone())
}

// ============================================================================
// The mode-dispatched reader body.
// ============================================================================

/// The expression reader body `exprBody rec s`: skip whitespace, then read a
/// list (on `'('`) or a maximal atom run (else `none`).
fn expr_body(rec: &Term, s: &Term) -> Term {
    let s1 = skip_ws(s);
    let sp = atom_span(&s1);
    let run = fst_bb(sp.clone());
    let rest = snd_bb(sp);
    let atom_some = some_r(pair_r(atom_of(run), rest));
    // cond (head is '(') → read list from tail; else cond (head is atom) →
    // atom; else none.
    let inner = cond_app(res_t(), head_sat(&is_atom(), &s1), atom_some, none_r());
    cond_app(
        res_t(),
        head_sat(&is_open(), &s1),
        Term::app(
            Term::app(rec.clone(), covalence_hol_eval::mk_bool(true)),
            tail_b(&s1),
        ),
        inner,
    )
}

/// `option.case[payload,res] none kont r` — the option bind used to thread the
/// element/rest reads of a list.
fn opt_bind(r: Term, kont: Term) -> Term {
    Term::app(
        Term::app(Term::app(option_case(payload_t(), res_t()), none_r()), kont),
        r,
    )
}

/// The list reader body `listBody rec s`: skip whitespace, then close the list
/// on `')'` or read one element and recurse on the tail.
fn list_body(rec: &Term, s: &Term) -> Term {
    let s1 = skip_ws(s);
    let read_elem = Term::app(
        Term::app(rec.clone(), covalence_hol_eval::mk_bool(false)),
        s1.clone(),
    );
    // inner_kont p2 = some (pair (scons <elem> (fst p2)) (snd p2)).
    // outer_kont p1 = bind (rec true (snd p1)) inner_kont, with elem = fst p1.
    let p1 = Term::free("__p1", payload_t());
    let p2 = Term::free("__p2", payload_t());
    let inner_kont = {
        let body = some_r(pair_r(scons(fst_r(&p1), fst_r(&p2)), snd_r(&p2)));
        lam("__p2", payload_t(), body)
    };
    let outer_kont = {
        let rest_read = Term::app(
            Term::app(rec.clone(), covalence_hol_eval::mk_bool(true)),
            snd_r(&p1),
        );
        let body = opt_bind(rest_read, inner_kont);
        lam("__p1", payload_t(), body)
    };
    let cons_branch = opt_bind(read_elem, outer_kont);
    cond_app(
        res_t(),
        head_sat(&is_close(), &s1),
        some_r(pair_r(snil(), tail_b(&s1))),
        cons_branch,
    )
}

// ============================================================================
// The fuel recursor.
// ============================================================================

/// `z := λmode s. none` — the exhausted-fuel base reader.
fn base_reader() -> Term {
    lam("mode", bool_t(), lam("s", blist_t(), none_r()))
}

/// `f := λn rec mode s. cond mode (listBody rec s) (exprBody rec s)` — the
/// `natRec` step: dispatch on the mode bit.
fn step_reader() -> Term {
    // The fuel predecessor `__n` is bound but unused in the body (it only
    // threads through the recursor image `__rec`).
    let rec = Term::free("__rec", reader_t());
    let mode = Term::free("mode", bool_t());
    let s = Term::free("s", blist_t());
    let body = cond_app(
        res_t(),
        mode.clone(),
        list_body(&rec, &s),
        expr_body(&rec, &s),
    );
    let l_s = lam("s", blist_t(), body);
    let l_mode = lam("mode", bool_t(), l_s);
    let l_rec = lam("__rec", reader_t(), l_mode);
    lam("__n", Type::nat(), l_rec)
}

/// `parseFn := natRec z f : nat → bool → bytes → option (sexpr × bytes)` — the
/// fuel-indexed, mode-dispatched reader.
fn parse_fn() -> Term {
    Term::app(Term::app(nat_rec(reader_t()), base_reader()), step_reader())
}

/// `parseSexpr : nat → bytes → option (sexpr × bytes)` — read one
/// S-expression (mode `false`) off the front of a byte string with the given
/// fuel bound.
pub fn parse_sexpr() -> Term {
    let fuel = Term::free("fuel", Type::nat());
    let s = Term::free("s", blist_t());
    let applied = Term::app(
        Term::app(
            Term::app(parse_fn(), fuel.clone()),
            covalence_hol_eval::mk_bool(false),
        ),
        s.clone(),
    );
    lam("fuel", Type::nat(), lam("s", blist_t(), applied))
}

// ============================================================================
// Defining equations.
// ============================================================================

/// The RHS of an equational theorem.
#[cfg(test)]
fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::sexpr_parse: expected an equation")
        .1
        .clone()
}

/// `⊢ parseFn 0 = base_reader` — the exhausted-fuel base equation. Genuine.
pub fn parse_base() -> Result<Thm> {
    crate::init::recursion::rec_holds_proof_at(&reader_t())?
        .all_elim(base_reader())?
        .all_elim(step_reader())?
        .and_elim_l()
}

/// `⊢ parseFn (succ n) = step_reader n (parseFn n)` — the fuel-step equation,
/// with `n` free (so the recursor image `parseFn n` stays opaque). Genuine.
pub fn parse_step(n: &Term) -> Result<Thm> {
    crate::init::recursion::rec_holds_proof_at(&reader_t())?
        .all_elim(base_reader())?
        .all_elim(step_reader())?
        .and_elim_r()?
        .all_elim(n.clone())
}

/// `⊢ parseFn (succ n) mode s = <reduced step body>` — the fuel-step equation
/// applied to a mode and input and β-reduced, keeping the recursor image
/// `parseFn n` opaque (`n` free). This is the reader's one-step unfolding.
pub fn parse_unfold(n: &Term, mode: &Term, s: &Term) -> Result<Thm> {
    parse_step(n)?
        .cong_fn(mode.clone())?
        .cong_fn(s.clone())?
        .reduce_rhs()
}

// ============================================================================
// Structural agreement: a parsed cons node's `consp`/`car`/`cdr`.
// ============================================================================

/// `(⊢ consp (scons h t) = T, ⊢ car (scons h t) = h, ⊢ cdr (scons h t) = t)`
/// — the **structural agreement** facts for a `scons` node (a parsed
/// non-empty list). When a parse yields `scons e rest`, the Lisp destructors
/// agree with the reader's structure: it *is* a cons (`consp = T`), its `car`
/// is the head element `e`, and its `cdr` is the tail list `rest`. Genuine
/// (hypothesis- and oracle-free) — from the carved projection laws
/// ([`mod@crate::init::inductive::carved`]) and [`crate::init::lisp`].
pub fn parsed_cons_struct(h: &Term, t: &Term) -> Result<(Thm, Thm, Thm)> {
    let cs = carved()?;
    let l = crate::init::lisp::lisp()?;
    let consp = l.consp_scons(h, t)?; // consp (scons h t) = T
    let car = cs.proj_scons(false, h, t)?; // car (scons h t) = h
    let cdr = cs.proj_scons(true, h, t)?; // cdr (scons h t) = t
    Ok((consp, car, cdr))
}

// ============================================================================
// A0015 checked interpretation adapter.
// ============================================================================

/// Identity of a Native HOL proof reader.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HolProofReader {
    SExpr,
    Json,
}

/// The theory selected for checked S-expression interpretation.
#[derive(Clone, Debug)]
pub struct HolSExprParseTheory {
    pub parser: Term,
}

impl Default for HolSExprParseTheory {
    fn default() -> Self {
        Self {
            parser: parse_sexpr(),
        }
    }
}

/// Untrusted positive evidence for a Native HOL prefix interpretation.
///
/// The theorem is authoritative only after [`replay_prefix_interpretation`]
/// checks every redundant field and its exact conclusion.
#[derive(Clone, Debug)]
pub struct HolSExprParseWitness {
    pub reader: HolProofReader,
    pub fuel: Term,
    pub source: Vec<u8>,
    pub value: Term,
    pub remainder: Vec<u8>,
    pub theorem: Thm,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HolSExprReplayError {
    WrongReader,
    TheoryMismatch,
    SourceMismatch,
    ValueMismatch,
    InvalidExtent,
    RemainderMismatch,
    HypothesesPresent,
    TheoremMismatch,
}

/// Replay a positive A0015 prefix interpretation against the existing reader.
///
/// Successful replay returns the supplied theorem unchanged, so its statement
/// remains exactly `parseFn fuel false source = some (value, remainder)`.
/// This adapter mints no theorem and treats every host field as untrusted.
///
/// @covalence-api-impl {"api":"A0015","name":"NativeHol carved S-expression checked prefix interpretation","representation":"fuel-bounded list-u8 reader theorem replay"}
pub fn replay_prefix_interpretation(
    theory: &HolSExprParseTheory,
    source: &[u8],
    interpretation: &PrefixInterpretation<Term, HolSExprParseWitness>,
) -> core::result::Result<Thm, HolSExprReplayError> {
    let witness = &interpretation.witness;
    if witness.reader != HolProofReader::SExpr {
        return Err(HolSExprReplayError::WrongReader);
    }
    if theory.parser != parse_sexpr() {
        return Err(HolSExprReplayError::TheoryMismatch);
    }
    if witness.source != source {
        return Err(HolSExprReplayError::SourceMismatch);
    }
    if witness.value != interpretation.value {
        return Err(HolSExprReplayError::ValueMismatch);
    }
    if interpretation.consumed != Span::new(0, interpretation.remainder).unwrap()
        || interpretation.remainder > source.len()
    {
        return Err(HolSExprReplayError::InvalidExtent);
    }
    if witness.remainder != source[interpretation.remainder..] {
        return Err(HolSExprReplayError::RemainderMismatch);
    }
    if !witness.theorem.hyps().is_empty() {
        return Err(HolSExprReplayError::HypothesesPresent);
    }

    let source_term = byte_list_term(source);
    let remainder_term = byte_list_term(&witness.remainder);
    let expected_lhs = Term::app(
        Term::app(
            Term::app(parse_fn(), witness.fuel.clone()),
            covalence_hol_eval::mk_bool(false),
        ),
        source_term,
    );
    let expected_rhs = some_r(pair_r(interpretation.value.clone(), remainder_term));
    let Some((actual_lhs, actual_rhs)) = witness.theorem.concl().as_eq() else {
        return Err(HolSExprReplayError::TheoremMismatch);
    };
    if actual_lhs != &expected_lhs || actual_rhs != &expected_rhs {
        return Err(HolSExprReplayError::TheoremMismatch);
    }
    Ok(witness.theorem.clone())
}

/// Replay both legs of an A0015 same-interpretation witness.
///
/// The certificate is the pair of unchanged reader theorems. Equality of the
/// shared [`SameInterpretation::value`] pins the two legs to the same HOL term;
/// no host equality claim is promoted into a theorem.
pub fn replay_same_interpretation(
    theory: &HolSExprParseTheory,
    left_source: &[u8],
    right_source: &[u8],
    same: &SameInterpretation<Term, HolSExprParseWitness, ()>,
) -> core::result::Result<(Thm, Thm), HolSExprReplayError> {
    let replay_leg = |source: &[u8], witness: &HolSExprParseWitness| {
        let remainder = source
            .len()
            .checked_sub(witness.remainder.len())
            .ok_or(HolSExprReplayError::InvalidExtent)?;
        let interpretation = PrefixInterpretation::new(
            same.value.clone(),
            witness.clone(),
            Span::new(0, remainder).unwrap(),
            remainder,
        )
        .ok_or(HolSExprReplayError::InvalidExtent)?;
        replay_prefix_interpretation(theory, source, &interpretation)
    };
    Ok((
        replay_leg(left_source, &same.left)?,
        replay_leg(right_source, &same.right)?,
    ))
}

fn byte_list_term(bytes: &[u8]) -> Term {
    bytes.iter().rev().fold(defs::nil(u8_t()), |tail, byte| {
        Term::app(
            Term::app(defs::cons(u8_t()), covalence_hol_eval::mk_u8(*byte)),
            tail,
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::cond::{cond_false, cond_true};
    use crate::init::ext::TermExt;
    use crate::init::list::{head_cons, head_nil, tail_cons};
    use crate::init::logic::prop_eq;
    use crate::init::nat::{succ, zero};
    use crate::init::option::{case_none, case_some};
    use crate::init::prod::{fst_pair, snd_pair};

    // -- element-list builders (list u8) --

    fn cons_u(c: Term, l: Term) -> Term {
        Term::app(Term::app(defs::cons(u8_t()), c), l)
    }
    fn nil_u() -> Term {
        defs::nil(u8_t())
    }

    /// A `list u8` term from raw bytes (each a `u8` literal).
    fn bytes_term(bs: &[u8]) -> Term {
        let mut t = nil_u();
        for &b in bs.iter().rev() {
            t = cons_u(covalence_hol_eval::mk_u8(b), t);
        }
        t
    }

    /// `succ^k 0 : nat` — the fuel numeral.
    fn fuel(k: usize) -> Term {
        let mut n = zero();
        for _ in 0..k {
            n = succ(n);
        }
        n
    }

    /// The `(a, b)` of a concrete `pair a b` term.
    fn pair_parts(t: &Term) -> (Term, Term) {
        let (fa, b) = t.as_app().unwrap();
        let (_pair, a) = fa.as_app().unwrap();
        (a.clone(), b.clone())
    }

    /// Match a `cond α c x y` spine → `(c, x, y)`.
    fn split_cond(t: &Term) -> (Term, Term, Term) {
        let (cxy, y) = t.as_app().unwrap();
        let (cx, x) = cxy.as_app().unwrap();
        let (_, c) = cx.as_app().unwrap();
        (c.clone(), x.clone(), y.clone())
    }

    // -- Rust-side reference reader (drives the proof + checks the result) --

    #[derive(Clone, Debug, PartialEq)]
    enum Sv {
        Atom(Vec<u8>),
        Nil,
        Cons(Box<Sv>, Box<Sv>),
    }

    fn is_ws_b(b: u8) -> bool {
        matches!(b, 9 | 10 | 13 | 32)
    }
    fn is_atom_b(b: u8) -> bool {
        !is_ws_b(b) && b != 40 && b != 41
    }
    fn skip_ws_b(bs: &[u8]) -> &[u8] {
        let mut i = 0;
        while i < bs.len() && is_ws_b(bs[i]) {
            i += 1;
        }
        &bs[i..]
    }

    /// Reference expression reader — returns `(value, rest)` or `None`.
    fn ref_expr(bs: &[u8]) -> Option<(Sv, &[u8])> {
        let s1 = skip_ws_b(bs);
        match s1.first() {
            Some(&40) => ref_list(&s1[1..]),
            Some(&b) if is_atom_b(b) => {
                let mut i = 0;
                while i < s1.len() && is_atom_b(s1[i]) {
                    i += 1;
                }
                Some((Sv::Atom(s1[..i].to_vec()), &s1[i..]))
            }
            _ => None,
        }
    }

    /// Reference list-tail reader.
    fn ref_list(bs: &[u8]) -> Option<(Sv, &[u8])> {
        let s1 = skip_ws_b(bs);
        match s1.first() {
            Some(&41) => Some((Sv::Nil, &s1[1..])),
            _ => {
                let (e, s2) = ref_expr(s1)?;
                let (rest, s3) = ref_list(s2)?;
                Some((Sv::Cons(Box::new(e), Box::new(rest)), s3))
            }
        }
    }

    /// The carved-`sexpr` term of a reference value.
    fn to_term(v: &Sv) -> Term {
        match v {
            Sv::Atom(bytes) => atom_of(bytes_term(bytes)),
            Sv::Nil => snil(),
            Sv::Cons(h, t) => scons(to_term(h), to_term(t)),
        }
    }

    // -- primitive resolvers --

    /// `⊢ t = <T|F>` for a closed byte-class bool `t` (reduce + `prop_eq`).
    fn decide_bool(t: &Term) -> (Thm, bool) {
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

    /// `⊢ list_cat a b = <concrete>` for concrete `list u8` `a`.
    fn eval_cat(a: &Term, b: &Term) -> Thm {
        use crate::init::list_recursion::{cat_cons, cat_nil};
        match a
            .as_app()
            .and_then(|(f, tl)| f.as_app().map(|(_, h)| (h.clone(), tl.clone())))
        {
            Some((x, xs)) => {
                let cc = cat_cons(&u8_t(), &x, &xs, b).unwrap();
                let cong = eval_cat(&xs, b)
                    .cong_arg(Term::app(defs::cons(u8_t()), x))
                    .unwrap();
                cc.trans(cong).unwrap()
            }
            None => cat_nil(&u8_t(), b).unwrap(),
        }
    }

    /// `⊢ span_digits_bytes pred (bytes) = pair <run> <rest>`.
    fn eval_span(pred: &Term, bs: &[u8]) -> Thm {
        use crate::init::nat_parse_bytes::{span_cons, span_nil};
        if bs.is_empty() {
            return span_nil(pred).unwrap();
        }
        let c = covalence_hol_eval::mk_u8(bs[0]);
        let cs = bytes_term(&bs[1..]);
        let general = span_cons(pred, &c, &cs).unwrap();
        let cond_c = rhs(&Term::app(pred.clone(), c.clone()).reduce().unwrap());
        let (cc_eq, matched) = decide_bool(&cond_c);
        let resolved = general.rewrite(&cc_eq).unwrap();
        let (_c, x, y) = split_cond(&rhs(&resolved));
        let clause = if matched {
            cond_true(&bb_t(), &x, &y).unwrap()
        } else {
            cond_false(&bb_t(), &x, &y).unwrap()
        };
        let span_eq = resolved.trans(clause).unwrap(); // span (cons c cs) = branch
        // Resolve `fst (span cs)` / `snd (span cs)` in the branch via recursion.
        let rec = eval_span(pred, &bs[1..]);
        let (pre, rest) = pair_parts(&rhs(&rec));
        let fpre = rec
            .clone()
            .cong_arg(fst(blist_t(), blist_t()))
            .unwrap()
            .trans(fst_pair(&blist_t(), &blist_t(), &pre, &rest).unwrap())
            .unwrap();
        let rrest = rec
            .cong_arg(snd(blist_t(), blist_t()))
            .unwrap()
            .trans(snd_pair(&blist_t(), &blist_t(), &pre, &rest).unwrap())
            .unwrap();
        let out = span_eq
            .rhs_conv(|t| t.rw_all(&fpre))
            .unwrap()
            .rhs_conv(|t| t.rw_all(&rrest))
            .unwrap();
        if matched {
            out
        } else {
            // non-match branch holds `cons c (cat pre rest)`; fold `cat pre rest`.
            let recon = eval_cat(&pre, &rest);
            out.rhs_conv(|t| t.rw_all(&recon)).unwrap()
        }
    }

    /// `bb_t` — `bytes × bytes`.
    fn bb_t() -> Type {
        defs::prod(blist_t(), blist_t())
    }

    /// `⊢ skip_ws (bytes) = <rest bytes>` (the suffix past leading whitespace).
    fn eval_skip_ws(bs: &[u8]) -> Thm {
        let sp = eval_span(&is_ws(), bs); // span is_ws bs = pair run rest
        let (run, rest) = pair_parts(&rhs(&sp));
        sp.cong_arg(snd(blist_t(), blist_t()))
            .unwrap()
            .trans(snd_pair(&blist_t(), &blist_t(), &run, &rest).unwrap())
            .unwrap()
    }

    /// `⊢ head_sat pred (bytes) = <T|F>`.
    fn eval_head_sat(pred: &Term, bs: &[u8]) -> (Thm, bool) {
        let s = bytes_term(bs);
        let oc = head_sat(pred, &s);
        if bs.is_empty() {
            let hn = head_nil(&u8_t()).unwrap();
            let cn = case_none(
                &u8_t(),
                &bool_t(),
                &covalence_hol_eval::mk_bool(false),
                pred,
            )
            .unwrap();
            let eq = Thm::refl(oc)
                .unwrap()
                .rhs_conv(|t| t.rw_all(&hn))
                .unwrap()
                .trans(cn)
                .unwrap();
            return (eq, false);
        }
        let c = covalence_hol_eval::mk_u8(bs[0]);
        let cs = bytes_term(&bs[1..]);
        let hc = head_cons(&u8_t(), &c, &cs).unwrap();
        let cse = case_some(
            &u8_t(),
            &bool_t(),
            &covalence_hol_eval::mk_bool(false),
            pred,
            &c,
        )
        .unwrap();
        let (dec, b) = decide_bool(&Term::app(pred.clone(), c.clone()));
        let eq = Thm::refl(oc)
            .unwrap()
            .rhs_conv(|t| t.rw_all(&hc))
            .unwrap()
            .trans(cse)
            .unwrap()
            .trans(dec)
            .unwrap();
        (eq, b)
    }

    /// `⊢ list.tail (bytes) = <tail bytes>`.
    fn eval_tail(bs: &[u8]) -> Thm {
        let c = covalence_hol_eval::mk_u8(bs[0]);
        let cs = bytes_term(&bs[1..]);
        tail_cons(&u8_t(), &c, &cs).unwrap()
    }

    /// The `option (sexpr × bytes)` term of a reference reader result.
    fn to_res(r: &Option<(Sv, &[u8])>) -> Term {
        match r {
            None => none_r(),
            Some((v, rest)) => some_r(pair_r(to_term(v), bytes_term(rest))),
        }
    }

    /// Fire a single top-level β-redex on the RHS.
    fn beta_rhs(thm: Thm) -> Thm {
        thm.rhs_conv(|t| Thm::beta_conv(t.clone())).unwrap()
    }

    /// `⊢ parseFn (fuel k) <mode> (bytes) = <reference result>` — the reader
    /// computed for concrete `k`/`mode`/`bs` by fuel unfolding. `k` must be
    /// large enough (≥ the token count) for the reference reader to succeed;
    /// exhausted fuel yields `none`.
    fn eval(k: usize, mode: bool, bs: &[u8]) -> Thm {
        let mode_lit = covalence_hol_eval::mk_bool(mode);
        let s = bytes_term(bs);
        if k == 0 {
            return parse_base()
                .unwrap()
                .cong_fn(mode_lit)
                .unwrap()
                .cong_fn(s)
                .unwrap()
                .reduce_rhs()
                .unwrap(); // parseFn 0 mode s = none
        }
        // One fuel step (recursor image kept opaque, then instantiated).
        let nf = Term::free("__nf", Type::nat());
        let u = parse_unfold(&nf, &mode_lit, &s)
            .unwrap()
            .inst("__nf", fuel(k - 1))
            .unwrap();
        // Fire the mode dispatch cond.
        let (_c, x, y) = split_cond(&rhs(&u));
        let mode_clause = if mode {
            cond_true(&res_t(), &x, &y).unwrap()
        } else {
            cond_false(&res_t(), &x, &y).unwrap()
        };
        let after = u.trans(mode_clause).unwrap();
        if mode {
            eval_list(k, bs, after)
        } else {
            eval_expr(k, bs, after)
        }
    }

    /// Resolve the expression-reader body.
    fn eval_expr(k: usize, bs: &[u8], after: Thm) -> Thm {
        let s1 = skip_ws_b(bs);
        // Normalise `skip_ws s` → the concrete suffix everywhere.
        let e = after.rhs_conv(|t| t.rw_all(&eval_skip_ws(bs))).unwrap();
        // Decide the '(' test (the outer cond).
        let (open_eq, is_open_first) = eval_head_sat(&is_open(), s1);
        let e = e.rhs_conv(|t| t.rw_all(&open_eq)).unwrap();
        let (_c, x, y) = split_cond(&rhs(&e));
        if is_open_first {
            // Read a list from the tail.
            let e = e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap();
            let e = e.rhs_conv(|t| t.rw_all(&eval_tail(s1))).unwrap();
            let rec = eval(k - 1, true, &s1[1..]);
            e.trans(rec).unwrap()
        } else {
            // Not '('; drop into the atom / none inner cond.
            let e = e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap();
            let (atom_eq, is_atom_first) = eval_head_sat(&is_atom(), s1);
            let e = e.rhs_conv(|t| t.rw_all(&atom_eq)).unwrap();
            let (_c, x, y) = split_cond(&rhs(&e));
            if is_atom_first {
                let e = e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap();
                // Resolve the atom span (fst = run, snd = rest).
                let asp = eval_span(&is_atom(), s1);
                let (run, rest) = pair_parts(&rhs(&asp));
                let fpre = asp
                    .clone()
                    .cong_arg(fst(blist_t(), blist_t()))
                    .unwrap()
                    .trans(fst_pair(&blist_t(), &blist_t(), &run, &rest).unwrap())
                    .unwrap();
                let rrest = asp
                    .cong_arg(snd(blist_t(), blist_t()))
                    .unwrap()
                    .trans(snd_pair(&blist_t(), &blist_t(), &run, &rest).unwrap())
                    .unwrap();
                e.rhs_conv(|t| t.rw_all(&fpre))
                    .unwrap()
                    .rhs_conv(|t| t.rw_all(&rrest))
                    .unwrap()
            } else {
                e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap() // none
            }
        }
    }

    /// Resolve the list-reader body.
    fn eval_list(k: usize, bs: &[u8], after: Thm) -> Thm {
        let s1 = skip_ws_b(bs);
        let e = after.rhs_conv(|t| t.rw_all(&eval_skip_ws(bs))).unwrap();
        let (close_eq, is_close_first) = eval_head_sat(&is_close(), s1);
        let e = e.rhs_conv(|t| t.rw_all(&close_eq)).unwrap();
        let (_c, x, y) = split_cond(&rhs(&e));
        if is_close_first {
            // End of list: `snil`, suffix = tail.
            let e = e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap();
            e.rhs_conv(|t| t.rw_all(&eval_tail(s1))).unwrap()
        } else {
            // Read one element, then the rest of the list.
            let e = e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap();
            // e RHS = option.case none outer_kont (parseFn(fuel k-1) false s1).
            let elem = eval(k - 1, false, s1);
            let e = e.rhs_conv(|t| t.rw_all(&elem)).unwrap();
            match ref_expr(s1) {
                None => {
                    // element failed → whole list fails.
                    let (_, outer_kont, _) = case_scrutinee(&rhs(&e));
                    e.trans(case_none(&payload_t(), &res_t(), &none_r(), &outer_kont).unwrap())
                        .unwrap()
                }
                Some((ev, s2)) => {
                    let p = pair_r(to_term(&ev), bytes_term(s2));
                    let (_, outer_kont, _) = case_scrutinee(&rhs(&e));
                    // fire case_some, β outer_kont, resolve `snd p`.
                    let e = e
                        .trans(
                            case_some(&payload_t(), &res_t(), &none_r(), &outer_kont, &p).unwrap(),
                        )
                        .unwrap();
                    let e = beta_rhs(e); // opt_bind (rec true (snd p)) inner_kont[fst p]
                    // Resolve the element payload `p`: `snd p` = the suffix fed
                    // to the rest-read, `fst p` = the element (captured in
                    // `inner_kont`).
                    let e = e
                        .rhs_conv(|t| {
                            t.rw_all(
                                &snd_pair(&tau(), &blist_t(), &to_term(&ev), &bytes_term(s2))
                                    .unwrap(),
                            )
                        })
                        .unwrap();
                    let e = e
                        .rhs_conv(|t| {
                            t.rw_all(
                                &fst_pair(&tau(), &blist_t(), &to_term(&ev), &bytes_term(s2))
                                    .unwrap(),
                            )
                        })
                        .unwrap();
                    // e RHS = option.case none inner_kont (parseFn(fuel k-1) true s2).
                    let rest = eval(k - 1, true, s2);
                    let e = e.rhs_conv(|t| t.rw_all(&rest)).unwrap();
                    match ref_list(s2) {
                        None => {
                            let (_, inner_kont, _) = case_scrutinee(&rhs(&e));
                            e.trans(
                                case_none(&payload_t(), &res_t(), &none_r(), &inner_kont).unwrap(),
                            )
                            .unwrap()
                        }
                        Some((rv, s3)) => {
                            let q = pair_r(to_term(&rv), bytes_term(s3));
                            let (_, inner_kont, _) = case_scrutinee(&rhs(&e));
                            let e = e
                                .trans(
                                    case_some(&payload_t(), &res_t(), &none_r(), &inner_kont, &q)
                                        .unwrap(),
                                )
                                .unwrap();
                            let e = beta_rhs(e); // some(pair (scons ev (fst q)) (snd q))
                            let e = e
                                .rhs_conv(|t| {
                                    t.rw_all(
                                        &fst_pair(
                                            &tau(),
                                            &blist_t(),
                                            &to_term(&rv),
                                            &bytes_term(s3),
                                        )
                                        .unwrap(),
                                    )
                                })
                                .unwrap();
                            e.rhs_conv(|t| {
                                t.rw_all(
                                    &snd_pair(&tau(), &blist_t(), &to_term(&rv), &bytes_term(s3))
                                        .unwrap(),
                                )
                            })
                            .unwrap()
                        }
                    }
                }
            }
        }
    }

    /// `option.case d f scrut` → `(d, f, scrut)`.
    fn case_scrutinee(t: &Term) -> (Term, Term, Term) {
        let (dfs, scrut) = t.as_app().unwrap();
        let (df, f) = dfs.as_app().unwrap();
        let (_case, d) = df.as_app().unwrap();
        (d.clone(), f.clone(), scrut.clone())
    }

    #[test]
    fn parser_is_well_typed() {
        assert_eq!(
            parse_sexpr().type_of().unwrap(),
            Type::fun(Type::nat(), Type::fun(blist_t(), res_t()))
        );
    }

    #[test]
    fn defining_equations_are_genuine() {
        let n = Term::free("n", Type::nat());
        assert!(parse_base().unwrap().hyps().is_empty());
        assert!(parse_step(&n).unwrap().hyps().is_empty());
    }

    /// Parse `bs` with fuel 30 (mode expr) and check the result matches the
    /// reference reader; return the theorem.
    fn parse_ok(bs: &[u8]) -> Thm {
        let thm = eval(30, false, bs);
        assert!(thm.hyps().is_empty(), "parse of {bs:?} must be oracle-free");
        assert_eq!(rhs(&thm), to_res(&ref_expr(bs)), "parse of {bs:?}");
        thm
    }

    #[test]
    fn parse_atom() {
        // "ab" → atom "ab", rest "".  "ab)" → atom "ab", rest ")".
        parse_ok(b"ab");
        parse_ok(b"ab)");
        parse_ok(b"  ab cd"); // leading whitespace skipped, rest " cd"
    }

    #[test]
    fn parse_none_on_empty_and_close() {
        // empty and a leading ')' both fail to read an expression.
        assert_eq!(rhs(&eval(30, false, b"")), none_r());
        assert_eq!(rhs(&eval(30, false, b")")), none_r());
        assert_eq!(rhs(&eval(5, false, b"")), none_r());
    }

    #[test]
    fn parse_empty_list() {
        // "()" → snil, rest "".
        let thm = parse_ok(b"()");
        assert_eq!(rhs(&thm), some_r(pair_r(snil(), nil_u())));
    }

    #[test]
    fn parse_flat_list() {
        // "(a b c)" → scons a (scons b (scons c snil)).
        let thm = parse_ok(b"(a b c)");
        let want = scons(
            atom_of(bytes_term(b"a")),
            scons(
                atom_of(bytes_term(b"b")),
                scons(atom_of(bytes_term(b"c")), snil()),
            ),
        );
        assert_eq!(rhs(&thm), some_r(pair_r(want, nil_u())));
    }

    #[test]
    fn parse_nested_list() {
        // "(a (b c) d)" — the canonical nesting example.
        parse_ok(b"(a (b c) d)");
        parse_ok(b"((a) b)");
        parse_ok(b"(a (b (c)) d) x"); // trailing " x" returned as the suffix
    }

    #[test]
    fn parse_list_structure_agrees_with_car_cdr_consp() {
        // Parse "(a b)"; its value is `scons (atom a) (scons (atom b) snil)`.
        // The Lisp destructors then agree with the read structure.
        let thm = parse_ok(b"(a b)");
        let tail = scons(atom_of(bytes_term(b"b")), snil());
        let head = atom_of(bytes_term(b"a"));
        let tree = scons(head.clone(), tail.clone());
        assert_eq!(rhs(&thm), some_r(pair_r(tree.clone(), nil_u())));

        // consp tree = T, car tree = atom a, cdr tree = (scons (atom b) snil).
        let (consp, car, cdr) = parsed_cons_struct(&head, &tail).unwrap();
        assert!(consp.hyps().is_empty());
        assert_eq!(
            consp.concl().as_eq().unwrap().1,
            &covalence_hol_eval::mk_bool(true)
        );
        assert_eq!(car.concl().as_eq().unwrap().1, &head);
        assert_eq!(cdr.concl().as_eq().unwrap().1, &tail);
        // and the car of the tail is `atom b`.
        let (_, car_tail, _) = parsed_cons_struct(&atom_of(bytes_term(b"b")), &snil()).unwrap();
        assert_eq!(
            car_tail.concl().as_eq().unwrap().1,
            &atom_of(bytes_term(b"b"))
        );
    }

    #[test]
    fn structural_agreement_is_genuine() {
        // consp/car/cdr of a scons node agree with its head/tail.
        let h = atom_of(bytes_term(b"a"));
        let t = snil();
        let (consp, car, cdr) = parsed_cons_struct(&h, &t).unwrap();
        assert!(consp.hyps().is_empty());
        assert_eq!(
            consp.concl().as_eq().unwrap().1,
            &covalence_hol_eval::mk_bool(true)
        );
        assert_eq!(car.concl().as_eq().unwrap().1, &h);
        assert_eq!(cdr.concl().as_eq().unwrap().1, &t);
    }

    fn checked_prefix(source: &[u8]) -> PrefixInterpretation<Term, HolSExprParseWitness> {
        let theorem = eval(30, false, source);
        let (value, remainder) = ref_expr(source).expect("test source parses");
        let remainder_offset = source.len() - remainder.len();
        let value = to_term(&value);
        PrefixInterpretation::new(
            value.clone(),
            HolSExprParseWitness {
                reader: HolProofReader::SExpr,
                fuel: fuel(30),
                source: source.to_vec(),
                value,
                remainder: remainder.to_vec(),
                theorem,
            },
            Span::new(0, remainder_offset).unwrap(),
            remainder_offset,
        )
        .unwrap()
    }

    #[test]
    fn a0015_adapter_preserves_the_existing_parse_theorem() {
        let source = b" (a (b)) tail";
        let interpretation = checked_prefix(source);
        let replayed =
            replay_prefix_interpretation(&HolSExprParseTheory::default(), source, &interpretation)
                .unwrap();
        assert_eq!(
            replayed.concl(),
            interpretation.witness.theorem.concl(),
            "replay must not restate or remint the proof"
        );
        assert!(replayed.hyps().is_empty());
    }

    #[test]
    fn a0015_per_adapter_checks_both_sources_against_one_value() {
        let left_source = b"(a)";
        let right_source = b" (a)";
        let left = checked_prefix(left_source);
        let right = checked_prefix(right_source);
        assert_eq!(left.value, right.value);
        let same = SameInterpretation {
            value: left.value,
            left: left.witness,
            right: right.witness,
            equivalence: (),
        };
        let (left_theorem, right_theorem) = replay_same_interpretation(
            &HolSExprParseTheory::default(),
            left_source,
            right_source,
            &same,
        )
        .unwrap();
        assert_eq!(left_theorem.concl(), same.left.theorem.concl());
        assert_eq!(right_theorem.concl(), same.right.theorem.concl());
    }

    #[test]
    fn a0015_adapter_rejects_substituted_reader_source_value_and_remainder() {
        let source = b"(a) tail";

        let mut wrong_reader = checked_prefix(source);
        wrong_reader.witness.reader = HolProofReader::Json;
        assert_eq!(
            replay_prefix_interpretation(&HolSExprParseTheory::default(), source, &wrong_reader)
                .unwrap_err(),
            HolSExprReplayError::WrongReader
        );

        let mut wrong_source = checked_prefix(source);
        wrong_source.witness.source = b"(b) tail".to_vec();
        assert_eq!(
            replay_prefix_interpretation(&HolSExprParseTheory::default(), source, &wrong_source)
                .unwrap_err(),
            HolSExprReplayError::SourceMismatch
        );

        let mut wrong_value = checked_prefix(source);
        wrong_value.witness.value = snil();
        assert_eq!(
            replay_prefix_interpretation(&HolSExprParseTheory::default(), source, &wrong_value)
                .unwrap_err(),
            HolSExprReplayError::ValueMismatch
        );

        let mut wrong_remainder = checked_prefix(source);
        wrong_remainder.witness.remainder = b"tail".to_vec();
        assert_eq!(
            replay_prefix_interpretation(&HolSExprParseTheory::default(), source, &wrong_remainder)
                .unwrap_err(),
            HolSExprReplayError::RemainderMismatch
        );
    }

    #[test]
    fn a0015_adapter_rejects_substituted_extent_theory_and_theorem() {
        let source = b"(a) tail";

        let mut wrong_extent = checked_prefix(source);
        wrong_extent.remainder += 1;
        assert_eq!(
            replay_prefix_interpretation(&HolSExprParseTheory::default(), source, &wrong_extent)
                .unwrap_err(),
            HolSExprReplayError::InvalidExtent
        );

        let wrong_theory = HolSExprParseTheory {
            parser: crate::init::json_parse::parse_json(),
        };
        assert_eq!(
            replay_prefix_interpretation(&wrong_theory, source, &checked_prefix(source))
                .unwrap_err(),
            HolSExprReplayError::TheoryMismatch
        );

        let mut wrong_theorem = checked_prefix(source);
        wrong_theorem.witness.theorem = eval(30, false, b"(b) tail");
        assert_eq!(
            replay_prefix_interpretation(&HolSExprParseTheory::default(), source, &wrong_theorem)
                .unwrap_err(),
            HolSExprReplayError::TheoremMismatch
        );

        let mut hypothetical = checked_prefix(source);
        hypothetical.witness.theorem =
            Thm::assume(hypothetical.witness.theorem.concl().clone()).unwrap();
        assert_eq!(
            replay_prefix_interpretation(&HolSExprParseTheory::default(), source, &hypothetical)
                .unwrap_err(),
            HolSExprReplayError::HypothesesPresent
        );
    }
}
