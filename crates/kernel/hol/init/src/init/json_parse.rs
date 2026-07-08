//! `json_parse` — **JSON north-star groundwork** (stage JP): a fuel-bounded
//! reader for the *integer + array* fragment of RFC-8259 JSON, over `bytes`
//! (`list u8`), producing the carved [`sexpr`](mod@crate::init::inductive::carved)
//! datatype as its value carrier — the synergy with the just-landed
//! S-expression reader ([`crate::init::sexpr_parse`]).
//!
//! ```text
//! parseJson : nat → bytes → option (sexpr × bytes)
//! ```
//!
//! ## Scope (this stage): the integer-only + array subset
//!
//! This is a deliberately **well-scoped slice** toward full JSON. The value
//! grammar is:
//!
//! - **number** (integer subset) — a maximal run of digit/`'-'` bytes, read as
//!   `atom (bytes.abs run)` (the literal digits; the semantic `int` value and
//!   the strict `-?(0|[1-9][0-9]*)` production are follow-ups — see
//!   `SKELETONS.md`). Reuses the decimal digit-byte range of the `int`/`nat`
//!   parsers ([`crate::init::nat_parse_bytes::is_digit_byte_dec`]) as its
//!   character class (via the shared conventions, not by editing that module).
//! - **array** — `'[' e₁ … eₙ ']'` yielding the `scons`-chain
//!   `scons e₁ (scons e₂ … snil)` (`snil` for `[]`).
//!
//! Commas and JSON whitespace are treated **uniformly as separators** (skipped
//! before every token): the array reader is then structurally identical to the
//! S-expression list reader — only the delimiter set changes (`[`/`]`/`,`
//! instead of `(`/`)`/whitespace). Strict comma placement, objects, JSON
//! strings, and the `true`/`false`/`null` literals are recorded as
//! `SKELETONS.md` follow-ups; so are a dedicated 6-constructor `JsonValue`
//! datatype and float numbers.
//!
//! ## The fuel recursion (as in [`crate::init::sexpr_parse`])
//!
//! The reader is primitive-recursive on a `nat` *fuel* bound through `natRec`,
//! at result type `bool → bytes → option (sexpr × bytes)`; the boolean **mode**
//! picks the value reader (`false`) or the array-tail reader (`true`).
//!
//! ## What is proved
//!
//! - the defining equations [`parse_base`] / [`parse_step`] / [`parse_unfold`];
//! - **concrete parses** by an unfolding harness (tests): integers, flat and
//!   nested arrays, `[]`, `none` on malformed/empty input, suffix returned;
//! - the **north-star PER** [`same_json`]: the relation `s₁ ~ s₂ ⟺ parseJson
//!   s₁, parseJson s₂ yield the same JSON value` is a genuine **partial
//!   equivalence relation** — [`same_json_sym`] (symmetric) and
//!   [`same_json_trans`] (transitive), with [`same_json_refl_dom`] pinning its
//!   domain (reflexive *exactly* on the parseable strings, so genuinely
//!   partial). All hypothesis- and oracle-free.
//!
//! The `bytes` PER also transports to a `string` PER; that, the strict grammar,
//! the full datatype, and proving the integer subset is a genuine subset of
//! full JSON are `SKELETONS.md` follow-ups.

use covalence_core::{IntTag, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{
    bytes_spec, cond, fst, head, int_to_nat, nat_le, nat_rec, none, option_case, pair, snd, some,
    tail,
};
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::{TermExt, ThmExt};
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

/// `bytes := list u8` — the reader's input/suffix type.
fn blist_t() -> Type {
    defs::list(u8_t())
}

/// The carved `sexpr` type — the JSON value carrier this stage.
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

/// `option sexpr` — the extracted JSON value (`json_value`).
fn opt_val_t() -> Type {
    defs::option(tau())
}

/// `bool → bytes → option (sexpr × bytes)` — the `natRec` result type.
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

/// `u8.toNat b : nat`.
fn val(b: &Term) -> Term {
    Term::app(int_to_nat(IntTag::U8), b.clone())
}

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

/// `option.case[u8,bool] false pred (head s) : bool`.
fn head_sat(pred: &Term, s: &Term) -> Term {
    Term::app(
        Term::app(
            Term::app(option_case(u8_t(), bool_t()), Term::bool_lit(false)),
            pred.clone(),
        ),
        head_b(s),
    )
}

/// `some[sexpr×bytes] p`.
fn some_r(p: Term) -> Term {
    Term::app(some(payload_t()), p)
}

/// `none : option (sexpr × bytes)`.
fn none_r() -> Term {
    none(payload_t())
}

/// `pair[sexpr,bytes] v s`.
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

/// `bytes.abs l : bytes` — wrap a `list u8` run into the `bytes` newtype.
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
// Byte-class predicates (the JSON delimiter set).
// ============================================================================

/// `λb. nat_le k (u8.toNat b) ∧ nat_le (u8.toNat b) k` — "the byte is `k`".
fn byte_is(k: u64) -> Term {
    let b = Term::free("b", u8_t());
    lam("b", u8_t(), band(le(lit(k), val(&b)), le(val(&b), lit(k))))
}

/// `λb. is 9 ∨ is 10 ∨ is 13 ∨ is 32 ∨ is 44` — the JSON **separator**
/// predicate: ASCII whitespace (tab / LF / CR / space) **plus comma** (`,`),
/// so commas are skipped uniformly with whitespace.
fn is_sep() -> Term {
    let b = Term::free("b", u8_t());
    let is = |k: u64| band(le(lit(k), val(&b)), le(val(&b), lit(k)));
    let body = bor(bor(bor(bor(is(9), is(10)), is(13)), is(32)), is(44));
    lam("b", u8_t(), body)
}

/// `λb. is 91` — the open-bracket predicate (`'['`).
fn is_open() -> Term {
    byte_is(91)
}

/// `λb. is 93` — the close-bracket predicate (`']'`).
fn is_close() -> Term {
    byte_is(93)
}

/// `λb. ¬sep b ∧ ¬(b = '[') ∧ ¬(b = ']')` — the number/atom-byte predicate.
fn is_atom() -> Term {
    let b = Term::free("b", u8_t());
    let is = |k: u64| band(le(lit(k), val(&b)), le(val(&b), lit(k)));
    let sep = bor(bor(bor(bor(is(9), is(10)), is(13)), is(32)), is(44));
    let body = band(bnot(sep), band(bnot(is(91)), bnot(is(93))));
    lam("b", u8_t(), body)
}

// ============================================================================
// Separator skipping + atom runs (via the landed `span` machinery).
// ============================================================================

/// `snd (span is_sep s) : bytes` — `s` with leading separators removed.
fn skip_sep(s: &Term) -> Term {
    snd_bb(Term::app(span_digits_bytes(&is_sep()), s.clone()))
}

fn fst_bb(p: Term) -> Term {
    Term::app(fst(blist_t(), blist_t()), p)
}
fn snd_bb(p: Term) -> Term {
    Term::app(snd(blist_t(), blist_t()), p)
}

/// `span is_atom s1 : bytes × bytes` — the number/atom run of `s1`.
fn atom_span(s1: &Term) -> Term {
    Term::app(span_digits_bytes(&is_atom()), s1.clone())
}

// ============================================================================
// The mode-dispatched reader body.
// ============================================================================

/// `valueBody rec s`: skip separators, then read an array (on `'['`) or a
/// maximal number/atom run (else `none`).
fn value_body(rec: &Term, s: &Term) -> Term {
    let s1 = skip_sep(s);
    let sp = atom_span(&s1);
    let run = fst_bb(sp.clone());
    let rest = snd_bb(sp);
    let atom_some = some_r(pair_r(atom_of(run), rest));
    let inner = cond_app(res_t(), head_sat(&is_atom(), &s1), atom_some, none_r());
    cond_app(
        res_t(),
        head_sat(&is_open(), &s1),
        Term::app(Term::app(rec.clone(), Term::bool_lit(true)), tail_b(&s1)),
        inner,
    )
}

/// `option.case[payload,res] none kont r` — the option bind threading list reads.
fn opt_bind(r: Term, kont: Term) -> Term {
    Term::app(
        Term::app(Term::app(option_case(payload_t(), res_t()), none_r()), kont),
        r,
    )
}

/// `arrayBody rec s`: skip separators, then close on `']'` or read one element
/// and recurse.
fn array_body(rec: &Term, s: &Term) -> Term {
    let s1 = skip_sep(s);
    let read_elem = Term::app(Term::app(rec.clone(), Term::bool_lit(false)), s1.clone());
    let p1 = Term::free("__p1", payload_t());
    let p2 = Term::free("__p2", payload_t());
    let inner_kont = {
        let body = some_r(pair_r(scons(fst_r(&p1), fst_r(&p2)), snd_r(&p2)));
        lam("__p2", payload_t(), body)
    };
    let outer_kont = {
        let rest_read = Term::app(Term::app(rec.clone(), Term::bool_lit(true)), snd_r(&p1));
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

/// `f := λn rec mode s. cond mode (arrayBody rec s) (valueBody rec s)`.
fn step_reader() -> Term {
    let rec = Term::free("__rec", reader_t());
    let mode = Term::free("mode", bool_t());
    let s = Term::free("s", blist_t());
    let body = cond_app(
        res_t(),
        mode.clone(),
        array_body(&rec, &s),
        value_body(&rec, &s),
    );
    let l_s = lam("s", blist_t(), body);
    let l_mode = lam("mode", bool_t(), l_s);
    let l_rec = lam("__rec", reader_t(), l_mode);
    lam("__n", Type::nat(), l_rec)
}

/// `parseFn := natRec z f`.
fn parse_fn() -> Term {
    Term::app(Term::app(nat_rec(reader_t()), base_reader()), step_reader())
}

/// `parseJson : nat → bytes → option (sexpr × bytes)` — read one JSON value
/// (mode `false`) off the front of a byte string with the given fuel bound.
pub fn parse_json() -> Term {
    let fuel = Term::free("fuel", Type::nat());
    let s = Term::free("s", blist_t());
    let applied = Term::app(
        Term::app(Term::app(parse_fn(), fuel.clone()), Term::bool_lit(false)),
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
        .expect("init::json_parse: expected an equation")
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

/// `⊢ parseFn (succ n) = step_reader n (parseFn n)` — the fuel-step equation.
/// Genuine.
pub fn parse_step(n: &Term) -> Result<Thm> {
    crate::init::recursion::rec_holds_proof_at(&reader_t())?
        .all_elim(base_reader())?
        .all_elim(step_reader())?
        .and_elim_r()?
        .all_elim(n.clone())
}

/// `⊢ parseFn (succ n) mode s = <reduced step body>` — one-step unfolding.
pub fn parse_unfold(n: &Term, mode: &Term, s: &Term) -> Result<Thm> {
    parse_step(n)?
        .cong_fn(mode.clone())?
        .cong_fn(s.clone())?
        .reduce_rhs()
}

// ============================================================================
// The extracted JSON value + the north-star PER.
// ============================================================================

/// `json_value fuel s : option sexpr` ≡
/// `option.case none (λp. some (fst p)) (parseJson fuel s)` — the parse's
/// **value** with its remaining suffix dropped. Two strings "yield the same
/// JSON value" iff their `json_value`s agree.
pub fn json_value(fuel: &Term, s: &Term) -> Term {
    let p = Term::free("__jp", payload_t());
    let some_fst = lam("__jp", payload_t(), Term::app(some(tau()), fst_r(&p)));
    let scrut = Term::app(Term::app(parse_json(), fuel.clone()), s.clone());
    Term::app(
        Term::app(
            Term::app(option_case(payload_t(), opt_val_t()), none(tau())),
            some_fst,
        ),
        scrut,
    )
}

/// `same_json fuel s1 s2 : bool` ≡
/// `(json_value fuel s1 = json_value fuel s2) ∧ ¬(json_value fuel s1 = none)`
/// — the north-star relation "`s1` and `s2` parse to the same JSON value (and
/// they *do* parse)". A **partial** equivalence relation
/// ([`same_json_sym`] / [`same_json_trans`] / [`same_json_refl_dom`]).
pub fn same_json() -> Term {
    let f = Term::free("__jf", Type::nat());
    let s1 = Term::free("__js1", blist_t());
    let s2 = Term::free("__js2", blist_t());
    let body = same_json_prop(&f, &s1, &s2);
    lam(
        "__jf",
        Type::nat(),
        lam("__js1", blist_t(), lam("__js2", blist_t(), body)),
    )
}

/// The unfolded proposition `same_json fuel s1 s2` computes to.
fn same_json_prop(fuel: &Term, s1: &Term, s2: &Term) -> Term {
    let a = json_value(fuel, s1);
    let b = json_value(fuel, s2);
    let none_v = none(tau());
    let eq_ab = a
        .clone()
        .equals(b)
        .expect("json_parse: option-sexpr equality");
    let a_none = a.equals(none_v).expect("json_parse: value = none");
    band(eq_ab, bnot(a_none))
}

/// `⊢ same_json fuel s1 s2 = same_json_prop fuel s1 s2` — the PER's defining
/// unfolding (three β-steps on the applied lambda). Genuine.
pub fn same_json_unfold(fuel: &Term, s1: &Term, s2: &Term) -> Result<Thm> {
    let head_f = Thm::beta_conv(Term::app(same_json(), fuel.clone()))?;
    let after_s1 = head_f
        .cong_fn(s1.clone())?
        .rhs_conv(|t| Thm::beta_conv(t.clone()))?;
    after_s1
        .cong_fn(s2.clone())?
        .rhs_conv(|t| Thm::beta_conv(t.clone()))
}

/// `⊢ same_json fuel s1 s2 ⟹ same_json fuel s2 s1` — **symmetry**. Genuine
/// (hypothesis- and oracle-free): equality on the extracted value is
/// symmetric, and definedness transports across it.
pub fn same_json_sym(fuel: &Term, s1: &Term, s2: &Term) -> Result<Thm> {
    let b = json_value(fuel, s2);
    let none_v = none(tau());
    let prop12 = same_json_prop(fuel, s1, s2);

    let h = Thm::assume(prop12.clone())?;
    let a_eq_b = h.clone().and_elim_l()?; // {p12} ⊢ a = b
    let not_a_none = h.and_elim_r()?; // {p12} ⊢ ¬(a = none)
    let b_eq_a = a_eq_b.clone().sym()?; // {p12} ⊢ b = a

    // ¬(b = none): assume b = none; then a = b = none, contradiction.
    let q = b.equals(none_v)?;
    let a_none = a_eq_b.trans(Thm::assume(q.clone())?)?; // {p12, q} ⊢ a = none
    let contra = not_a_none.not_elim(a_none)?; // {p12, q} ⊢ F
    let not_b_none = contra.imp_intro(&q)?.not_intro()?; // {p12} ⊢ ¬(b = none)

    let prop21_proof = b_eq_a.and_intro(not_b_none)?; // {p12} ⊢ prop21
    let impl_prop = prop21_proof.imp_intro(&prop12)?; // ⊢ prop12 ⟹ prop21

    lift_impl(impl_prop, &[(fuel, s1, s2), (fuel, s2, s1)])
}

/// `⊢ same_json fuel s1 s2 ⟹ same_json fuel s2 s3 ⟹ same_json fuel s1 s3` —
/// **transitivity**. Genuine: equality on the extracted value is transitive,
/// and definedness is inherited from the first relatum. Curried.
pub fn same_json_trans(fuel: &Term, s1: &Term, s2: &Term, s3: &Term) -> Result<Thm> {
    let prop12 = same_json_prop(fuel, s1, s2);
    let prop23 = same_json_prop(fuel, s2, s3);

    let h12 = Thm::assume(prop12.clone())?;
    let h23 = Thm::assume(prop23.clone())?;
    let a_eq_b = h12.clone().and_elim_l()?; // {p12} ⊢ a = b
    let b_eq_c = h23.and_elim_l()?; // {p23} ⊢ b = c
    let a_eq_c = a_eq_b.trans(b_eq_c)?; // {p12,p23} ⊢ a = c
    let not_a_none = h12.and_elim_r()?; // {p12} ⊢ ¬(a = none)

    let prop13_proof = a_eq_c.and_intro(not_a_none)?; // {p12,p23} ⊢ prop13
    let impl_prop = prop13_proof.imp_intro(&prop23)?.imp_intro(&prop12)?;

    // Lift antecedents/consequent `same_json_prop` back to `same_json`.
    let u12 = same_json_unfold(fuel, s1, s2)?;
    let u23 = same_json_unfold(fuel, s2, s3)?;
    let u13 = same_json_unfold(fuel, s1, s3)?;
    impl_prop
        .rewrite(&u12.sym()?)?
        .rewrite(&u23.sym()?)?
        .rewrite(&u13.sym()?)
}

/// `⊢ ¬(json_value fuel s = none) ⟹ same_json fuel s s` — **reflexivity on
/// the domain**: the PER holds `s ~ s` *exactly* when `s` parses (its
/// `json_value` is `some`), so it is genuinely **partial** (not reflexive on
/// unparseable strings). Genuine.
pub fn same_json_refl_dom(fuel: &Term, s: &Term) -> Result<Thm> {
    let a = json_value(fuel, s);
    let none_v = none(tau());
    let a_none = a.clone().equals(none_v)?;
    let not_a_none = bnot(a_none);

    let h = Thm::assume(not_a_none.clone())?;
    let refl_eq = Thm::refl(a)?; // ⊢ a = a
    let prop_ss = refl_eq.and_intro(h)?; // {¬(a=none)} ⊢ (a=a) ∧ ¬(a=none)
    let impl_prop = prop_ss.imp_intro(&not_a_none)?;

    // Only the consequent is a `same_json_prop`; lift it.
    let uss = same_json_unfold(fuel, s, s)?;
    impl_prop.rewrite(&uss.sym()?)
}

/// Rewrite each listed `same_json_prop(fuel,sᵢ,sⱼ)` occurrence in `thm`'s
/// conclusion back to the applied `same_json fuel sᵢ sⱼ`.
fn lift_impl(thm: Thm, args: &[(&Term, &Term, &Term)]) -> Result<Thm> {
    let mut acc = thm;
    for (fuel, si, sj) in args {
        let u = same_json_unfold(fuel, si, sj)?; // sj = prop
        acc = acc.rewrite(&u.sym()?)?; // prop → sj
    }
    Ok(acc)
}

// ============================================================================
// Structural agreement (reused from the S-expression layer).
// ============================================================================

/// `(⊢ consp (scons h t) = T, ⊢ car (scons h t) = h, ⊢ cdr (scons h t) = t)`
/// for a parsed non-empty array node — the Lisp destructors agree with the
/// reader's structure (from [`crate::init::sexpr_parse::parsed_cons_struct`]).
pub fn parsed_cons_struct(h: &Term, t: &Term) -> Result<(Thm, Thm, Thm)> {
    crate::init::sexpr_parse::parsed_cons_struct(h, t)
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

    fn bytes_term(bs: &[u8]) -> Term {
        let mut t = nil_u();
        for &b in bs.iter().rev() {
            t = cons_u(Term::u8_lit(b), t);
        }
        t
    }

    fn fuel(k: usize) -> Term {
        let mut n = zero();
        for _ in 0..k {
            n = succ(n);
        }
        n
    }

    fn pair_parts(t: &Term) -> (Term, Term) {
        let (fa, b) = t.as_app().unwrap();
        let (_pair, a) = fa.as_app().unwrap();
        (a.clone(), b.clone())
    }

    fn split_cond(t: &Term) -> (Term, Term, Term) {
        let (cxy, y) = t.as_app().unwrap();
        let (cx, x) = cxy.as_app().unwrap();
        let (_, c) = cx.as_app().unwrap();
        (c.clone(), x.clone(), y.clone())
    }

    // -- Rust-side reference reader --

    #[derive(Clone, Debug, PartialEq)]
    enum Sv {
        Atom(Vec<u8>),
        Nil,
        Cons(Box<Sv>, Box<Sv>),
    }

    fn is_sep_b(b: u8) -> bool {
        matches!(b, 9 | 10 | 13 | 32 | 44)
    }
    fn is_atom_b(b: u8) -> bool {
        !is_sep_b(b) && b != 91 && b != 93
    }
    fn skip_sep_b(bs: &[u8]) -> &[u8] {
        let mut i = 0;
        while i < bs.len() && is_sep_b(bs[i]) {
            i += 1;
        }
        &bs[i..]
    }

    fn ref_value(bs: &[u8]) -> Option<(Sv, &[u8])> {
        let s1 = skip_sep_b(bs);
        match s1.first() {
            Some(&91) => ref_array(&s1[1..]),
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

    fn ref_array(bs: &[u8]) -> Option<(Sv, &[u8])> {
        let s1 = skip_sep_b(bs);
        match s1.first() {
            Some(&93) => Some((Sv::Nil, &s1[1..])),
            _ => {
                let (e, s2) = ref_value(s1)?;
                let (rest, s3) = ref_array(s2)?;
                Some((Sv::Cons(Box::new(e), Box::new(rest)), s3))
            }
        }
    }

    fn to_term(v: &Sv) -> Term {
        match v {
            Sv::Atom(bytes) => atom_of(bytes_term(bytes)),
            Sv::Nil => snil(),
            Sv::Cons(h, t) => scons(to_term(h), to_term(t)),
        }
    }

    // -- primitive resolvers --

    fn decide_bool(t: &Term) -> (Thm, bool) {
        let red = Thm::refl(t.clone())
            .unwrap()
            .rhs_conv(|x| x.reduce())
            .unwrap();
        let combo = rhs(&red);
        match prop_eq(&combo, &Term::bool_lit(true)) {
            Ok(tt) => (red.trans(tt).unwrap(), true),
            Err(_) => {
                let ff = prop_eq(&combo, &Term::bool_lit(false)).unwrap();
                (red.trans(ff).unwrap(), false)
            }
        }
    }

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

    fn bb_t() -> Type {
        defs::prod(blist_t(), blist_t())
    }

    fn eval_span(pred: &Term, bs: &[u8]) -> Thm {
        use crate::init::nat_parse_bytes::{span_cons, span_nil};
        if bs.is_empty() {
            return span_nil(pred).unwrap();
        }
        let c = Term::u8_lit(bs[0]);
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
        let span_eq = resolved.trans(clause).unwrap();
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
            let recon = eval_cat(&pre, &rest);
            out.rhs_conv(|t| t.rw_all(&recon)).unwrap()
        }
    }

    fn eval_skip_sep(bs: &[u8]) -> Thm {
        let sp = eval_span(&is_sep(), bs);
        let (run, rest) = pair_parts(&rhs(&sp));
        sp.cong_arg(snd(blist_t(), blist_t()))
            .unwrap()
            .trans(snd_pair(&blist_t(), &blist_t(), &run, &rest).unwrap())
            .unwrap()
    }

    fn eval_head_sat(pred: &Term, bs: &[u8]) -> (Thm, bool) {
        let s = bytes_term(bs);
        let oc = head_sat(pred, &s);
        if bs.is_empty() {
            let hn = head_nil(&u8_t()).unwrap();
            let cn = case_none(&u8_t(), &bool_t(), &Term::bool_lit(false), pred).unwrap();
            let eq = Thm::refl(oc)
                .unwrap()
                .rhs_conv(|t| t.rw_all(&hn))
                .unwrap()
                .trans(cn)
                .unwrap();
            return (eq, false);
        }
        let c = Term::u8_lit(bs[0]);
        let cs = bytes_term(&bs[1..]);
        let hc = head_cons(&u8_t(), &c, &cs).unwrap();
        let cse = case_some(&u8_t(), &bool_t(), &Term::bool_lit(false), pred, &c).unwrap();
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

    fn eval_tail(bs: &[u8]) -> Thm {
        let c = Term::u8_lit(bs[0]);
        let cs = bytes_term(&bs[1..]);
        tail_cons(&u8_t(), &c, &cs).unwrap()
    }

    fn to_res(r: &Option<(Sv, &[u8])>) -> Term {
        match r {
            None => none_r(),
            Some((v, rest)) => some_r(pair_r(to_term(v), bytes_term(rest))),
        }
    }

    fn beta_rhs(thm: Thm) -> Thm {
        thm.rhs_conv(|t| Thm::beta_conv(t.clone())).unwrap()
    }

    /// `⊢ parseFn (fuel k) <mode> (bytes) = <reference result>`.
    fn eval(k: usize, mode: bool, bs: &[u8]) -> Thm {
        let mode_lit = Term::bool_lit(mode);
        let s = bytes_term(bs);
        if k == 0 {
            return parse_base()
                .unwrap()
                .cong_fn(mode_lit)
                .unwrap()
                .cong_fn(s)
                .unwrap()
                .reduce_rhs()
                .unwrap();
        }
        let nf = Term::free("__nf", Type::nat());
        let u = parse_unfold(&nf, &mode_lit, &s)
            .unwrap()
            .inst("__nf", fuel(k - 1))
            .unwrap();
        let (_c, x, y) = split_cond(&rhs(&u));
        let mode_clause = if mode {
            cond_true(&res_t(), &x, &y).unwrap()
        } else {
            cond_false(&res_t(), &x, &y).unwrap()
        };
        let after = u.trans(mode_clause).unwrap();
        if mode {
            eval_array(k, bs, after)
        } else {
            eval_value(k, bs, after)
        }
    }

    fn eval_value(k: usize, bs: &[u8], after: Thm) -> Thm {
        let s1 = skip_sep_b(bs);
        let e = after.rhs_conv(|t| t.rw_all(&eval_skip_sep(bs))).unwrap();
        let (open_eq, is_open_first) = eval_head_sat(&is_open(), s1);
        let e = e.rhs_conv(|t| t.rw_all(&open_eq)).unwrap();
        let (_c, x, y) = split_cond(&rhs(&e));
        if is_open_first {
            let e = e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap();
            let e = e.rhs_conv(|t| t.rw_all(&eval_tail(s1))).unwrap();
            let rec = eval(k - 1, true, &s1[1..]);
            e.trans(rec).unwrap()
        } else {
            let e = e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap();
            let (atom_eq, is_atom_first) = eval_head_sat(&is_atom(), s1);
            let e = e.rhs_conv(|t| t.rw_all(&atom_eq)).unwrap();
            let (_c, x, y) = split_cond(&rhs(&e));
            if is_atom_first {
                let e = e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap();
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
                e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap()
            }
        }
    }

    fn eval_array(k: usize, bs: &[u8], after: Thm) -> Thm {
        let s1 = skip_sep_b(bs);
        let e = after.rhs_conv(|t| t.rw_all(&eval_skip_sep(bs))).unwrap();
        let (close_eq, is_close_first) = eval_head_sat(&is_close(), s1);
        let e = e.rhs_conv(|t| t.rw_all(&close_eq)).unwrap();
        let (_c, x, y) = split_cond(&rhs(&e));
        if is_close_first {
            let e = e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap();
            e.rhs_conv(|t| t.rw_all(&eval_tail(s1))).unwrap()
        } else {
            let e = e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap();
            let elem = eval(k - 1, false, s1);
            let e = e.rhs_conv(|t| t.rw_all(&elem)).unwrap();
            match ref_value(s1) {
                None => {
                    let (_, outer_kont, _) = case_scrutinee(&rhs(&e));
                    e.trans(case_none(&payload_t(), &res_t(), &none_r(), &outer_kont).unwrap())
                        .unwrap()
                }
                Some((ev, s2)) => {
                    let p = pair_r(to_term(&ev), bytes_term(s2));
                    let (_, outer_kont, _) = case_scrutinee(&rhs(&e));
                    let e = e
                        .trans(
                            case_some(&payload_t(), &res_t(), &none_r(), &outer_kont, &p).unwrap(),
                        )
                        .unwrap();
                    let e = beta_rhs(e);
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
                    let rest = eval(k - 1, true, s2);
                    let e = e.rhs_conv(|t| t.rw_all(&rest)).unwrap();
                    match ref_array(s2) {
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
                            let e = beta_rhs(e);
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

    fn case_scrutinee(t: &Term) -> (Term, Term, Term) {
        let (dfs, scrut) = t.as_app().unwrap();
        let (df, f) = dfs.as_app().unwrap();
        let (_case, d) = df.as_app().unwrap();
        (d.clone(), f.clone(), scrut.clone())
    }

    #[test]
    fn parser_is_well_typed() {
        assert_eq!(
            parse_json().type_of().unwrap(),
            Type::fun(Type::nat(), Type::fun(blist_t(), res_t()))
        );
    }

    #[test]
    fn defining_equations_are_genuine() {
        let n = Term::free("n", Type::nat());
        assert!(parse_base().unwrap().hyps().is_empty());
        assert!(parse_step(&n).unwrap().hyps().is_empty());
    }

    fn parse_ok(bs: &[u8]) -> Thm {
        let thm = eval(30, false, bs);
        assert!(thm.hyps().is_empty(), "parse of {bs:?} must be oracle-free");
        assert_eq!(rhs(&thm), to_res(&ref_value(bs)), "parse of {bs:?}");
        thm
    }

    #[test]
    fn parse_integer() {
        parse_ok(b"42");
        parse_ok(b"-5");
        parse_ok(b"123]"); // trailing ']' returned as suffix
    }

    #[test]
    fn parse_none_on_empty_and_close() {
        assert_eq!(rhs(&eval(30, false, b"")), none_r());
        assert_eq!(rhs(&eval(30, false, b"]")), none_r());
        assert_eq!(rhs(&eval(5, false, b"")), none_r());
    }

    #[test]
    fn parse_empty_array() {
        let thm = parse_ok(b"[]");
        assert_eq!(rhs(&thm), some_r(pair_r(snil(), nil_u())));
    }

    #[test]
    fn parse_flat_array() {
        // "[1, 2, 3]" → scons 1 (scons 2 (scons 3 snil)).
        let thm = parse_ok(b"[1, 2, 3]");
        let want = scons(
            atom_of(bytes_term(b"1")),
            scons(
                atom_of(bytes_term(b"2")),
                scons(atom_of(bytes_term(b"3")), snil()),
            ),
        );
        assert_eq!(rhs(&thm), some_r(pair_r(want, nil_u())));
    }

    #[test]
    fn parse_nested_array() {
        parse_ok(b"[1, [2, 3], 4]");
        parse_ok(b"[[1], 2]");
        parse_ok(b"[1, [2, [3]], 4] 9"); // trailing " 9" returned as suffix
    }

    #[test]
    fn parse_array_structure_agrees_with_car_cdr_consp() {
        let thm = parse_ok(b"[1, 2]");
        let tail = scons(atom_of(bytes_term(b"2")), snil());
        let head = atom_of(bytes_term(b"1"));
        let tree = scons(head.clone(), tail.clone());
        assert_eq!(rhs(&thm), some_r(pair_r(tree.clone(), nil_u())));

        let (consp, car, cdr) = parsed_cons_struct(&head, &tail).unwrap();
        assert!(consp.hyps().is_empty());
        assert_eq!(consp.concl().as_eq().unwrap().1, &Term::bool_lit(true));
        assert_eq!(car.concl().as_eq().unwrap().1, &head);
        assert_eq!(cdr.concl().as_eq().unwrap().1, &tail);
    }

    // ------------------------------------------------------------------
    // The north-star PER: partial-equivalence-relation laws.
    // ------------------------------------------------------------------

    #[test]
    fn value_and_per_are_well_typed() {
        let f = Term::free("f", Type::nat());
        let s = Term::free("s", blist_t());
        assert_eq!(json_value(&f, &s).type_of().unwrap(), opt_val_t());
        assert_eq!(
            same_json().type_of().unwrap(),
            Type::fun(
                Type::nat(),
                Type::fun(blist_t(), Type::fun(blist_t(), bool_t()))
            )
        );
    }

    #[test]
    fn per_unfold_is_genuine() {
        let f = Term::free("f", Type::nat());
        let s1 = Term::free("s1", blist_t());
        let s2 = Term::free("s2", blist_t());
        let u = same_json_unfold(&f, &s1, &s2).unwrap();
        assert!(u.hyps().is_empty());
        assert_eq!(rhs(&u), same_json_prop(&f, &s1, &s2));
    }

    /// `same_json fuel s1 s2` (the applied form).
    fn sj(f: &Term, a: &Term, b: &Term) -> Term {
        Term::app(
            Term::app(Term::app(same_json(), f.clone()), a.clone()),
            b.clone(),
        )
    }

    #[test]
    fn per_symmetric_is_genuine() {
        let f = Term::free("f", Type::nat());
        let s1 = Term::free("s1", blist_t());
        let s2 = Term::free("s2", blist_t());
        let thm = same_json_sym(&f, &s1, &s2).unwrap();
        assert!(thm.hyps().is_empty(), "symmetry must be oracle-free");
        // ⊢ same_json f s1 s2 ⟹ same_json f s2 s1.
        let want = crate::HolLightCtx::new().mk_imp(sj(&f, &s1, &s2), sj(&f, &s2, &s1));
        assert_eq!(thm.concl(), &want);
    }

    #[test]
    fn per_transitive_is_genuine() {
        let f = Term::free("f", Type::nat());
        let s1 = Term::free("s1", blist_t());
        let s2 = Term::free("s2", blist_t());
        let s3 = Term::free("s3", blist_t());
        let thm = same_json_trans(&f, &s1, &s2, &s3).unwrap();
        assert!(thm.hyps().is_empty(), "transitivity must be oracle-free");
        let ctx = crate::HolLightCtx::new();
        let want = ctx.mk_imp(
            sj(&f, &s1, &s2),
            ctx.mk_imp(sj(&f, &s2, &s3), sj(&f, &s1, &s3)),
        );
        assert_eq!(thm.concl(), &want);
    }

    #[test]
    fn per_reflexive_on_domain_is_genuine() {
        let f = Term::free("f", Type::nat());
        let s = Term::free("s", blist_t());
        let thm = same_json_refl_dom(&f, &s).unwrap();
        assert!(thm.hyps().is_empty(), "refl-on-domain must be oracle-free");
        // ⊢ ¬(json_value f s = none) ⟹ same_json f s s.
        let ctx = crate::HolLightCtx::new();
        let ante = bnot(json_value(&f, &s).equals(none(tau())).unwrap());
        let want = ctx.mk_imp(ante, sj(&f, &s, &s));
        assert_eq!(thm.concl(), &want);
    }
}
