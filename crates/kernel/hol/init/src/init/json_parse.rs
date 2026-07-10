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
//! - **number** (integer subset) — the *lenient* reader tokenises a maximal run
//!   of digit/`'-'` bytes (`is_atom`), read as `atom (bytes.abs run)`. A
//!   **strict** variant now defines the RFC-8259 integer production
//!   `-?(0|[1-9][0-9]*)` faithfully — see the strict-integer section below
//!   ([`is_json_int`] / [`parse_json_int`]). Reuses the decimal digit-byte range
//!   of the `int`/`nat` parsers
//!   ([`crate::init::nat_parse_bytes::is_digit_byte_dec`]) as its character
//!   class (via the shared conventions, not by editing that module). The
//!   semantic `int` value remains a follow-up (see `SKELETONS.md`).
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
//! - the **strict integer subset** ([`is_json_int`] / [`parse_json_int`]): a
//!   decidable predicate for `-?(0|[1-9][0-9]*)`, the general faithfulness
//!   theorems [`json_int_accepts`] / [`json_int_rejects`] (the strict number
//!   branch fires with the lenient value iff the run is a strict integer), the
//!   concrete accept/reject decisions on `0`/`-7`/`42` vs `01`/`1.5`/`true`/
//!   `1e3`/`-`, and the concrete **subset** witness `parse_json_int s =
//!   parse_json fuel s` on the accepted tokens (strict ⊆ lenient, same value).
//! - the **string PER** [`same_json_str`]: the `bytes` PER transported to
//!   `list char` via the encoder [`str_to_bytes`] (`map (u8_of ∘ char.code)`).
//!   [`same_json_str_sym`] / [`same_json_str_trans`] / [`same_json_str_refl_dom`]
//!   are direct instances of the `bytes` laws at the encoded arguments — genuine
//!   corollaries, hypothesis- and oracle-free.
//! - the **∀-quantified whole-value integer subset** [`parse_json_int_subset`]:
//!   `⊢ ∀ s v r. parse_json_int s = some (v, r) ⟹ parse_json (succ fuel) s =
//!   some (v, r)` — every strict-integer *token* parse is a lenient parse with
//!   the identical value/suffix (both readers skip the same separators and carve
//!   the same maximal `is_atom` run; no array recursion, since `parse_json_int`
//!   is non-recursive). Genuine, discharged against the real readers in tests.
//!
//! The full `JsonValue` datatype, objects/strings/bool/null, float numbers, and
//! a *recursive* strict reader (with its array-structure subset) are
//! `SKELETONS.md` follow-ups.

use covalence_core::{Error, IntTag, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{
    bytes_spec, char_code, char_ty, cond, fst, head, int_from_nat, int_to_nat, list_map, nat_le,
    nat_rec, none, option_case, pair, snd, some, tail,
};
use covalence_hol_eval::derived::DerivedRules;

use crate::init::cond::{cond_false, cond_true};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::carved::carved;
use crate::init::nat_parse_bytes::{is_digit_byte_dec, span_digits_bytes};
use crate::init::option::some_ne_none;

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
// The `string` PER — the north-star relation transported to `list char`.
//
// A `list char` string is encoded as `bytes` by mapping each character to its
// codepoint's byte (`u8_of ∘ char.code`); the `bytes` PER [`same_json`] is then
// reused verbatim. The three string laws are **direct instances** of the bytes
// laws at the encoded arguments — genuine corollaries, no new content.
// ============================================================================

/// `char` — the string's element type.
fn char_t() -> Type {
    char_ty()
}

/// `list char` — the string type (the input of the string PER).
fn str_t() -> Type {
    defs::list(char_t())
}

/// `u8_of n : u8` — wrap a `nat` codepoint into a `u8` (the `int_from_nat U8`
/// embedding, dual to the reader's `val`/`u8.toNat` reification).
fn u8_of(n: Term) -> Term {
    Term::app(int_from_nat(IntTag::U8), n)
}

/// `str_to_bytes : list char → bytes` ≡ `map (λc. u8_of (char.code c))` — the
/// character-string encoder: each character becomes its codepoint's byte.
pub fn str_to_bytes() -> Term {
    let c = Term::free("__c", char_t());
    let enc = lam("__c", char_t(), u8_of(Term::app(char_code(), c)));
    Term::app(list_map(char_t(), u8_t()), enc)
}

/// `str_to_bytes c : bytes` — the encoder applied to a `list char`.
fn str_encode(c: &Term) -> Term {
    Term::app(str_to_bytes(), c.clone())
}

/// `same_json_str fuel c1 c2 : bool` ≡ `same_json fuel (str_to_bytes c1)
/// (str_to_bytes c2)` — the `bytes` north-star PER [`same_json`] transported to
/// character strings. A **partial** equivalence relation
/// ([`same_json_str_sym`] / [`same_json_str_trans`] /
/// [`same_json_str_refl_dom`]).
pub fn same_json_str() -> Term {
    let f = Term::free("__sf", Type::nat());
    let c1 = Term::free("__sc1", str_t());
    let c2 = Term::free("__sc2", str_t());
    let body = same_json_str_prop(&f, &c1, &c2);
    lam(
        "__sf",
        Type::nat(),
        lam("__sc1", str_t(), lam("__sc2", str_t(), body)),
    )
}

/// The applied `same_json fuel (str_to_bytes c1) (str_to_bytes c2)` that
/// `same_json_str fuel c1 c2` computes to.
fn same_json_str_prop(fuel: &Term, c1: &Term, c2: &Term) -> Term {
    Term::app(
        Term::app(Term::app(same_json(), fuel.clone()), str_encode(c1)),
        str_encode(c2),
    )
}

/// `⊢ same_json_str fuel c1 c2 = same_json fuel (str_to_bytes c1)
/// (str_to_bytes c2)` — the defining unfolding (three β-steps). Genuine.
pub fn same_json_str_unfold(fuel: &Term, c1: &Term, c2: &Term) -> Result<Thm> {
    let head_f = Thm::beta_conv(Term::app(same_json_str(), fuel.clone()))?;
    let after_c1 = head_f
        .cong_fn(c1.clone())?
        .rhs_conv(|t| Thm::beta_conv(t.clone()))?;
    after_c1
        .cong_fn(c2.clone())?
        .rhs_conv(|t| Thm::beta_conv(t.clone()))
}

/// `⊢ same_json_str fuel c1 c2 ⟹ same_json_str fuel c2 c1` — **symmetry**, a
/// direct instance of [`same_json_sym`] at the encoded byte strings. Genuine.
pub fn same_json_str_sym(fuel: &Term, c1: &Term, c2: &Term) -> Result<Thm> {
    let bytes = same_json_sym(fuel, &str_encode(c1), &str_encode(c2))?;
    let u12 = same_json_str_unfold(fuel, c1, c2)?;
    let u21 = same_json_str_unfold(fuel, c2, c1)?;
    bytes.rewrite(&u12.sym()?)?.rewrite(&u21.sym()?)
}

/// `⊢ same_json_str fuel c1 c2 ⟹ same_json_str fuel c2 c3 ⟹ same_json_str
/// fuel c1 c3` — **transitivity**, a direct instance of [`same_json_trans`].
/// Genuine. Curried.
pub fn same_json_str_trans(fuel: &Term, c1: &Term, c2: &Term, c3: &Term) -> Result<Thm> {
    let bytes = same_json_trans(fuel, &str_encode(c1), &str_encode(c2), &str_encode(c3))?;
    let u12 = same_json_str_unfold(fuel, c1, c2)?;
    let u23 = same_json_str_unfold(fuel, c2, c3)?;
    let u13 = same_json_str_unfold(fuel, c1, c3)?;
    bytes
        .rewrite(&u12.sym()?)?
        .rewrite(&u23.sym()?)?
        .rewrite(&u13.sym()?)
}

/// `⊢ ¬(json_value fuel (str_to_bytes c) = none) ⟹ same_json_str fuel c c` —
/// **reflexivity on the domain**, a direct instance of [`same_json_refl_dom`]:
/// the string PER holds `c ~ c` exactly when `c`'s encoding parses. Genuine.
pub fn same_json_str_refl_dom(fuel: &Term, c: &Term) -> Result<Thm> {
    let bytes = same_json_refl_dom(fuel, &str_encode(c))?;
    let u = same_json_str_unfold(fuel, c, c)?;
    bytes.rewrite(&u.sym()?)
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

// ============================================================================
// Strict RFC-8259 integer number token — the "integers-only subset, proved a
// genuine subset" north-star (see module docs / `SKELETONS.md`).
//
// The lenient reader above tokenises a *number* as any maximal run of
// non-separator, non-bracket bytes (`is_atom`): `true`, `1.5`, `1e3`, `abc`
// all slip through. This section defines the **strict** integer production
//
//     json-int  ::=  '-'?  ( '0' | [1-9][0-9]* )
//
// as a decidable byte-string predicate [`is_json_int`], a strict number token
// reader [`parse_json_int`] whose number branch fires *only* on a strict
// integer literal, and the faithfulness + subset theorems relating the two.
// ============================================================================

/// `λ_:u8. F` — the constant-`false` byte function (the `none`-branch of the
/// `is_empty`/`nonempty` option eliminators).
fn const_false_u8() -> Term {
    lam("_x", u8_t(), Term::bool_lit(false))
}

/// `λ_:u8. T` — the constant-`true` byte function.
fn const_true_u8() -> Term {
    lam("_x", u8_t(), Term::bool_lit(true))
}

/// `option.case[u8,bool] d f (head l)` — decide a property of `l`'s first byte
/// (or fall back to `d` when `l` is empty). [`head_sat`] is this at `d = F`.
fn opt_head_case(d: Term, f: Term, l: &Term) -> Term {
    Term::app(
        Term::app(Term::app(option_case(u8_t(), bool_t()), d), f),
        head_b(l),
    )
}

/// `λl. option.case T (λ_. F) (head l)` applied — "`l` is empty" (`head l =
/// none`).
fn is_empty(l: &Term) -> Term {
    opt_head_case(Term::bool_lit(true), const_false_u8(), l)
}

/// "`l` is non-empty" (`head l = some _`).
fn nonempty(l: &Term) -> Term {
    opt_head_case(Term::bool_lit(false), const_true_u8(), l)
}

/// `is_json_int : bytes → bool` — the strict integer well-formedness predicate
/// `-?(0 | [1-9][0-9]*)`. After an optional leading `'-'`, the remaining bytes
/// must be a **non-empty all-decimal-digit** run (`span is_digit` consumes all
/// of it) with **no leading zero** (if the first digit is `'0'`, there is no
/// second digit). Genuine decidable term — built from `span`/`head`/`tail` and
/// the propositional connectives, no recursion of its own.
pub fn is_json_int() -> Term {
    let s = Term::free("s", blist_t());
    // Strip an optional leading '-' (byte 45).
    let neg = head_sat(&byte_is(45), &s);
    let body = cond_app(blist_t(), neg, tail_b(&s), s.clone());
    // The digit run of the (sign-stripped) body.
    let sp = Term::app(span_digits_bytes(&is_digit_byte_dec()), body);
    let ds = fst_bb(sp.clone());
    let rest = snd_bb(sp);
    // All consumed ∧ non-empty ∧ no leading zero.
    let no_leading_zero = bor(bnot(head_sat(&byte_is(48), &ds)), is_empty(&tail_b(&ds)));
    let ok = band(is_empty(&rest), band(nonempty(&ds), no_leading_zero));
    lam("s", blist_t(), ok)
}

/// `some (atom run, rest)` — the value the **lenient** number branch
/// ([`value_body`]'s `atom_some`) carves for a run/suffix. The strict reader
/// carves *exactly* this on the tokens it accepts (the subset witness).
fn lenient_num_value(run: &Term, rest: &Term) -> Term {
    some_r(pair_r(atom_of(run.clone()), rest.clone()))
}

/// `json_int_branch run rest ≡ cond (is_json_int run) (some (atom run, rest))
/// none` — the strict number branch: emit the atom value **iff** the run is a
/// strict integer literal.
pub fn json_int_branch(run: &Term, rest: &Term) -> Term {
    let guard = Term::app(is_json_int(), run.clone());
    cond_app(res_t(), guard, lenient_num_value(run, rest), none_r())
}

/// `parse_json_int : bytes → option (sexpr × bytes)` — a strict integer number
/// **token** reader: skip separators, then accept a strict integer literal
/// (`is_json_int`) as `atom (bytes.abs run)`, else `none`. Mirrors the lenient
/// [`value_body`] dispatch (open bracket → not a number → `none`; atom head →
/// number) but guards the number branch with [`is_json_int`]. Non-recursive:
/// it reads one number token, not arrays.
pub fn parse_json_int() -> Term {
    let s = Term::free("s", blist_t());
    let s1 = skip_sep(&s);
    let sp = atom_span(&s1);
    let run = fst_bb(sp.clone());
    let rest = snd_bb(sp);
    let num = json_int_branch(&run, &rest);
    let inner = cond_app(res_t(), head_sat(&is_atom(), &s1), num, none_r());
    let body = cond_app(res_t(), head_sat(&is_open(), &s1), none_r(), inner);
    lam("s", blist_t(), body)
}

/// `⊢ is_json_int run = T ⟹ json_int_branch run rest = some (atom run, rest)`
/// — **acceptance = subset with the same value**: when the run is a strict
/// integer literal the strict number branch carves *exactly* the value the
/// lenient reader carves ([`lenient_num_value`]). Genuine, general (`run`/
/// `rest` free), hypothesis-free after discharge. This is the token-level half
/// of "the integer subset is a genuine subset of the lenient grammar".
pub fn json_int_accepts(run: &Term, rest: &Term) -> Result<Thm> {
    let guard = Term::app(is_json_int(), run.clone());
    let guard_true = guard.equals(Term::bool_lit(true))?;
    let h = Thm::assume(guard_true.clone())?; // {g=T} ⊢ is_json_int run = T
    let val = lenient_num_value(run, rest);
    Thm::refl(json_int_branch(run, rest))?
        .rhs_conv(|t| t.rw_all(&h))? // branch = cond T val none
        .trans(cond_true(&res_t(), &val, &none_r())?)? // = val
        .imp_intro(&guard_true)
}

/// `⊢ is_json_int run = F ⟹ json_int_branch run rest = none` — **rejection**:
/// a non-strict-integer run produces no number value. Genuine, general.
pub fn json_int_rejects(run: &Term, rest: &Term) -> Result<Thm> {
    let guard = Term::app(is_json_int(), run.clone());
    let guard_false = guard.equals(Term::bool_lit(false))?;
    let h = Thm::assume(guard_false.clone())?; // {g=F} ⊢ is_json_int run = F
    let val = lenient_num_value(run, rest);
    Thm::refl(json_int_branch(run, rest))?
        .rhs_conv(|t| t.rw_all(&h))? // branch = cond F val none
        .trans(cond_false(&res_t(), &val, &none_r())?)? // = none
        .imp_intro(&guard_false)
}

// ============================================================================
// The ∀-quantified whole-value integer subset for `parse_json_int`.
//
// `⊢ ∀ s v r. parse_json_int s = some (v, r) ⟹ parse_json (succ fuel) s =
//   some (v, r)` — a strict-integer parse is a lenient parse with the *same*
// value. `parse_json_int` is non-recursive (rejects `[`), so no array
// recursion is needed: both readers skip the *same* separators, compute the
// *same* atom run `fst (atom_span s1)` / suffix `snd (atom_span s1)`, and carve
// `some (atom run, rest)`. The proof extracts the three guard values forced by
// the hypothesis (`is_open` head = F, `is_atom` head = T, `is_json_int run` =
// T) by excluded-middle case analysis (the reject branches make the strict
// reader return `none ≠ some (v, r)`), then fires the shared conds on both
// readers to the common value. Genuine: hypothesis- and oracle-free.
// ============================================================================

/// The right side of `thm`'s conclusion equation.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// Split `cond[τ] c x y` into `(c, x, y)`.
fn cond_parts(t: &Term) -> Result<(Term, Term, Term)> {
    let (cxy, y) = t.as_app().ok_or(Error::NotAnEquation)?;
    let (cx, x) = cxy.as_app().ok_or(Error::NotAnEquation)?;
    let (_cond, c) = cx.as_app().ok_or(Error::NotAnEquation)?;
    Ok((c.clone(), x.clone(), y.clone()))
}

/// `⊢ P = F` from `⊢ ¬P` (the `F` mirror of `ThmExt::eqt_intro`).
fn eqf_intro(not_p: Thm) -> Result<Thm> {
    let p = not_p
        .concl()
        .as_app()
        .ok_or_else(|| Error::ConnectiveRule("eqf_intro: not a ¬".into()))?
        .1
        .clone();
    // `not_elim` concludes the DEFINED `F` (EG3b); the clause statements
    // use the literal `⌜F⌝`, so cross the bridge both ways.
    let pf = covalence_hol_eval::fal_to_lit(not_p.not_elim(Thm::assume(p.clone())?)?)?; // {P} ⊢ ⌜F⌝
    let fp = Thm::assume(Term::bool_lit(false))?.false_elim(p)?; // {⌜F⌝} ⊢ P
    pf.deduct_antisym(fp)?.sym() // ⊢ P = ⌜F⌝
}

/// `⊢ (g = T) ∨ (g = F)` for a boolean term `g` — the excluded-middle split as
/// an equation disjunction, the primitive for firing a symbolic-guard `cond`.
fn bool_cases_eq(g: &Term) -> Result<Thm> {
    let g_t = g.clone().equals(Term::bool_lit(true))?;
    let g_f = g.clone().equals(Term::bool_lit(false))?;
    let ng = g.clone().not()?;
    let left = Thm::assume(g.clone())?
        .eqt_intro()? // {g} ⊢ g = T
        .or_intro_l(g_f.clone())? // {g} ⊢ (g=T) ∨ (g=F)
        .imp_intro(g)?; // ⊢ g ⟹ (g=T) ∨ (g=F)
    let right = eqf_intro(Thm::assume(ng.clone())?)? // {¬g} ⊢ g = F
        .or_intro_r(g_t.clone())? // {¬g} ⊢ (g=T) ∨ (g=F)
        .imp_intro(&ng)?; // ⊢ ¬g ⟹ (g=T) ∨ (g=F)
    Thm::lem(g.clone())?.or_elim(left, right)
}

/// Fire a symbolic-guard `cond`: given `thm : ⊢ LHS = cond g x y` and
/// `guard_eq : ⊢ g = <T|F>`, return `⊢ LHS = (x if T else y)`.
fn fire_cond(thm: Thm, guard_eq: &Thm, ty: &Type) -> Result<Thm> {
    let fired = thm.rhs_conv(|t| t.rw_all(guard_eq))?; // LHS = cond <lit> x y
    let (c, x, y) = cond_parts(&rhs_of(&fired)?)?;
    let clause = if c == Term::bool_lit(true) {
        cond_true(ty, &x, &y)?
    } else {
        cond_false(ty, &x, &y)?
    };
    fired.trans(clause)
}

/// `⊢ parse_json x s = parseFn x false s` — the two β-steps unfolding the
/// [`parse_json`] wrapper at any fuel term `x`.
fn parse_json_app_eq(x: &Term, s: &Term) -> Result<Thm> {
    Thm::beta_conv(Term::app(parse_json(), x.clone()))?
        .cong_fn(s.clone())?
        .rhs_conv(|t| Thm::beta_conv(t.clone()))
}

/// A reject branch: from `ps_none : Δ ⊢ parse_json_int s = none` and the
/// hypothesis `h : {H} ⊢ parse_json_int s = some p`, derive the goal by
/// `some p ≠ none` (vacuously — this guard value cannot occur under `H`).
fn reject_to_goal(h: &Thm, p: &Term, ps_none: Thm, goal_term: &Term) -> Result<Thm> {
    let sp_none = h.clone().sym()?.trans(ps_none)?; // ⊢ some p = none
    let f = some_ne_none(&payload_t(), p)?.not_elim(sp_none)?; // ⊢ F
    f.false_elim(goal_term.clone())
}

/// `⊢ ∀ s v r. parse_json_int s = some (v, r) ⟹ parse_json (succ fuel) s =
/// some (v, r)` — the **whole-value integer subset** theorem: every strict
/// integer token parse is a lenient parse with the identical value/suffix.
/// `fuel` is free (any successor fuel works). Genuine: hypothesis- and
/// oracle-free.
pub fn parse_json_int_subset() -> Result<Thm> {
    let s = Term::free("s", blist_t());
    let v = Term::free("v", tau());
    let r = Term::free("r", blist_t());
    let p = pair_r(v.clone(), r.clone());
    let some_p = some_r(p.clone());
    let fuel = Term::free("fuel", Type::nat());

    // -- PL: parse_json (succ fuel) s reduced to its value-reader form.
    let pu = parse_unfold(&fuel, &Term::bool_lit(false), &s)?; // parseFn X false s = cond F ab vb
    let x_fuel = {
        let lhs = pu.concl().as_eq().ok_or(Error::NotAnEquation)?.0;
        let (a2, _s) = lhs.as_app().ok_or(Error::NotAnEquation)?;
        let (a1, _false) = a2.as_app().ok_or(Error::NotAnEquation)?;
        a1.as_app().ok_or(Error::NotAnEquation)?.1.clone()
    };
    let (_mode, ab, vb) = cond_parts(&rhs_of(&pu)?)?;
    let pl_vb = pu.trans(cond_false(&res_t(), &ab, &vb)?)?; // parseFn X false s = vb
    let pl0 = parse_json_app_eq(&x_fuel, &s)?.trans(pl_vb)?; // ⊢ parse_json X s = vb

    // -- PS: parse_json_int s reduced to its guard-cond tree.
    let ps0 = Thm::beta_conv(Term::app(parse_json_int(), s.clone()))?.reduce_rhs()?;
    let (g1, _n1, ps_inner) = cond_parts(&rhs_of(&ps0)?)?; // cond g1 none inner
    let (g2, ps_num, _n2) = cond_parts(&ps_inner)?; // cond g2 (cond g3 sv none) none
    let (g3, _sv, _n3) = cond_parts(&ps_num)?; // cond g3 sv none

    // -- the goal proposition and the working hypothesis.
    let goal_term =
        Term::app(Term::app(parse_json(), x_fuel.clone()), s.clone()).equals(some_p.clone())?;
    let h_prop = Term::app(parse_json_int(), s.clone()).equals(some_p.clone())?;
    let h = Thm::assume(h_prop.clone())?;

    let t_lit = || Term::bool_lit(true);
    let f_lit = || Term::bool_lit(false);
    let g1_t = g1.clone().equals(t_lit())?;
    let g1_f = g1.clone().equals(f_lit())?;
    let g2_t = g2.clone().equals(t_lit())?;
    let g2_f = g2.clone().equals(f_lit())?;
    let g3_t = g3.clone().equals(t_lit())?;
    let g3_f = g3.clone().equals(f_lit())?;

    let e1f = Thm::assume(g1_f.clone())?;
    let e2t = Thm::assume(g2_t.clone())?;

    // ---- g3 split (under g1=F, g2=T): the value carve vs the strict reject.
    let br_g3_true = {
        let e3t = Thm::assume(g3_t.clone())?;
        // strict reader → sv
        let ps_sv = fire_cond(
            fire_cond(fire_cond(ps0.clone(), &e1f, &res_t())?, &e2t, &res_t())?,
            &e3t,
            &res_t(),
        )?; // parse_json_int s = sv
        // lenient reader → sv
        let pl_sv = fire_cond(fire_cond(pl0.clone(), &e1f, &res_t())?, &e2t, &res_t())?;
        // parse_json X s = sv
        let sv_eq_some_p = ps_sv.sym()?.trans(h.clone())?; // sv = some p
        pl_sv.trans(sv_eq_some_p)?.imp_intro(&g3_t)? // g3=T ⟹ goal
    };
    let br_g3_false = {
        let e3f = Thm::assume(g3_f.clone())?;
        let ps_none = fire_cond(
            fire_cond(fire_cond(ps0.clone(), &e1f, &res_t())?, &e2t, &res_t())?,
            &e3f,
            &res_t(),
        )?; // parse_json_int s = none
        reject_to_goal(&h, &p, ps_none, &goal_term)?.imp_intro(&g3_f)?
    };
    let br_g2_true = bool_cases_eq(&g3)?
        .or_elim(br_g3_true, br_g3_false)?
        .imp_intro(&g2_t)?; // g2=T ⟹ goal

    // ---- g2 reject (under g1=F): is_atom head = F ⟹ strict none.
    let br_g2_false = {
        let e2f = Thm::assume(g2_f.clone())?;
        let ps_none = fire_cond(fire_cond(ps0.clone(), &e1f, &res_t())?, &e2f, &res_t())?;
        reject_to_goal(&h, &p, ps_none, &goal_term)?.imp_intro(&g2_f)?
    };
    let br_g1_false = bool_cases_eq(&g2)?
        .or_elim(br_g2_true, br_g2_false)?
        .imp_intro(&g1_f)?; // g1=F ⟹ goal

    // ---- g1 reject: is_open head = T ⟹ strict none.
    let br_g1_true = {
        let e1t = Thm::assume(g1_t.clone())?;
        let ps_none = fire_cond(ps0.clone(), &e1t, &res_t())?;
        reject_to_goal(&h, &p, ps_none, &goal_term)?.imp_intro(&g1_t)?
    };

    let body = bool_cases_eq(&g1)?
        .or_elim(br_g1_true, br_g1_false)?
        .imp_intro(&h_prop)?; // ⊢ (parse_json_int s = some p) ⟹ goal

    body.all_intro("r", blist_t())?
        .all_intro("v", tau())?
        .all_intro("s", blist_t())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::cond::{cond_false, cond_true};
    use crate::init::ext::TermExt;
    use crate::init::list::{head_cons, head_nil, tail_cons, tail_nil};
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

    // ------------------------------------------------------------------
    // The string PER (transported from the bytes PER).
    // ------------------------------------------------------------------

    /// A `list char` from an ASCII string (`char.mk` at each codepoint).
    fn str_term(s: &str) -> Term {
        let mut t = defs::nil(char_t());
        for ch in s.chars().rev() {
            t = Term::app(
                Term::app(defs::cons(char_t()), crate::init::char::char_lit(ch as u64)),
                t,
            );
        }
        t
    }

    /// `same_json_str fuel c1 c2` (the applied form).
    fn sjs(f: &Term, a: &Term, b: &Term) -> Term {
        Term::app(
            Term::app(Term::app(same_json_str(), f.clone()), a.clone()),
            b.clone(),
        )
    }

    #[test]
    fn str_encoder_and_per_are_well_typed() {
        assert_eq!(
            str_to_bytes().type_of().unwrap(),
            Type::fun(str_t(), blist_t())
        );
        assert_eq!(
            same_json_str().type_of().unwrap(),
            Type::fun(
                Type::nat(),
                Type::fun(str_t(), Type::fun(str_t(), bool_t()))
            )
        );
    }

    #[test]
    fn str_per_unfold_is_genuine() {
        let f = Term::free("f", Type::nat());
        let c1 = Term::free("c1", str_t());
        let c2 = Term::free("c2", str_t());
        let u = same_json_str_unfold(&f, &c1, &c2).unwrap();
        assert!(u.hyps().is_empty());
        assert_eq!(rhs(&u), same_json_str_prop(&f, &c1, &c2));
    }

    #[test]
    fn str_per_symmetric_is_genuine() {
        let f = Term::free("f", Type::nat());
        let c1 = str_term("42");
        let c2 = str_term("[1,2]");
        let thm = same_json_str_sym(&f, &c1, &c2).unwrap();
        assert!(thm.hyps().is_empty(), "string symmetry must be oracle-free");
        let want = crate::HolLightCtx::new().mk_imp(sjs(&f, &c1, &c2), sjs(&f, &c2, &c1));
        assert_eq!(thm.concl(), &want);
    }

    #[test]
    fn str_per_transitive_is_genuine() {
        let f = Term::free("f", Type::nat());
        let c1 = str_term("42");
        let c2 = str_term("[1,2]");
        let c3 = str_term("[]");
        let thm = same_json_str_trans(&f, &c1, &c2, &c3).unwrap();
        assert!(thm.hyps().is_empty(), "string transitivity oracle-free");
        let ctx = crate::HolLightCtx::new();
        let want = ctx.mk_imp(
            sjs(&f, &c1, &c2),
            ctx.mk_imp(sjs(&f, &c2, &c3), sjs(&f, &c1, &c3)),
        );
        assert_eq!(thm.concl(), &want);
    }

    #[test]
    fn str_per_reflexive_on_domain_is_genuine() {
        let f = Term::free("f", Type::nat());
        let c = str_term("42");
        let thm = same_json_str_refl_dom(&f, &c).unwrap();
        assert!(thm.hyps().is_empty(), "string refl-on-domain oracle-free");
        let ctx = crate::HolLightCtx::new();
        let ante = bnot(json_value(&f, &str_encode(&c)).equals(none(tau())).unwrap());
        let want = ctx.mk_imp(ante, sjs(&f, &c, &c));
        assert_eq!(thm.concl(), &want);
    }

    // ------------------------------------------------------------------
    // Strict RFC-8259 integer number token.
    // ------------------------------------------------------------------

    fn is_digit_b(x: u8) -> bool {
        (48..=57).contains(&x)
    }

    fn span_digit_b(bs: &[u8]) -> (&[u8], &[u8]) {
        let mut i = 0;
        while i < bs.len() && is_digit_b(bs[i]) {
            i += 1;
        }
        (&bs[..i], &bs[i..])
    }

    /// Rust reference for `is_json_int`: `-?(0|[1-9][0-9]*)`.
    fn is_json_int_b(run: &[u8]) -> bool {
        let neg = run.first() == Some(&45);
        let body = if neg { &run[1..] } else { run };
        let (ds, rest) = span_digit_b(body);
        rest.is_empty() && !ds.is_empty() && (ds[0] != 48 || ds.len() == 1)
    }

    /// The maximal `is_atom` run of `bs` (the number/atom token the readers
    /// carve).
    fn atom_run_b(bs: &[u8]) -> &[u8] {
        let mut i = 0;
        while i < bs.len() && is_atom_b(bs[i]) {
            i += 1;
        }
        &bs[..i]
    }

    /// `⊢ option.case[u8,bool] d f (head <bs>) = <bool>` + the decided value.
    fn eval_opt_head(d: &Term, f: &Term, bs: &[u8]) -> (Thm, bool) {
        let s = bytes_term(bs);
        let oc = opt_head_case(d.clone(), f.clone(), &s);
        if bs.is_empty() {
            let hn = head_nil(&u8_t()).unwrap();
            let cn = case_none(&u8_t(), &bool_t(), d, f).unwrap(); // = d
            let eq = Thm::refl(oc)
                .unwrap()
                .rhs_conv(|t| t.rw_all(&hn))
                .unwrap()
                .trans(cn)
                .unwrap();
            (eq, d.as_bool().unwrap())
        } else {
            let c = Term::u8_lit(bs[0]);
            let cs = bytes_term(&bs[1..]);
            let hc = head_cons(&u8_t(), &c, &cs).unwrap();
            let cse = case_some(&u8_t(), &bool_t(), d, f, &c).unwrap(); // = f c
            let (dec, b) = decide_bool(&Term::app(f.clone(), c.clone()));
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
    }

    /// `⊢ is_json_int <run> = <bool>` by unfolding the predicate against the
    /// literal, via the `span`/`head`/`tail`/`option.case` clause harness.
    fn eval_is_json_int(bs: &[u8]) -> (Thm, bool) {
        let run = bytes_term(bs);
        let mut e = Thm::beta_conv(Term::app(is_json_int(), run.clone())).unwrap();

        // 1. neg = head_sat (byte_is 45) run
        let (neg_eq, neg) = eval_opt_head(&Term::bool_lit(false), &byte_is(45), bs);
        e = e.rhs_conv(|t| t.rw_all(&neg_eq)).unwrap();

        // 2. body = cond neg (tail run) run
        let x = tail_b(&run);
        let cc = if neg {
            cond_true(&blist_t(), &x, &run).unwrap()
        } else {
            cond_false(&blist_t(), &x, &run).unwrap()
        };
        e = e.rhs_conv(|t| t.rw_all(&cc)).unwrap();
        let body_slice: Vec<u8> = if neg {
            let te = eval_tail(bs); // ⊢ tail run = <bs[1..]>
            e = e.rhs_conv(|t| t.rw_all(&te)).unwrap();
            bs[1..].to_vec()
        } else {
            bs.to_vec()
        };

        // 3. span is_digit body → ds, rest
        let asp = eval_span(&is_digit_byte_dec(), &body_slice);
        let (ds_t, rest_t) = pair_parts(&rhs(&asp));
        e = e.rhs_conv(|t| t.rw_all(&asp)).unwrap();
        e = e
            .rhs_conv(|t| t.rw_all(&fst_pair(&blist_t(), &blist_t(), &ds_t, &rest_t).unwrap()))
            .unwrap();
        e = e
            .rhs_conv(|t| t.rw_all(&snd_pair(&blist_t(), &blist_t(), &ds_t, &rest_t).unwrap()))
            .unwrap();
        let (ds_bytes, rest_bytes) = span_digit_b(&body_slice);

        // 4. the three leaf checks: is_empty rest, nonempty ds, no-leading-zero.
        let (er_eq, _) = eval_opt_head(&Term::bool_lit(true), &const_false_u8(), rest_bytes);
        e = e.rhs_conv(|t| t.rw_all(&er_eq)).unwrap();
        let (ne_eq, _) = eval_opt_head(&Term::bool_lit(false), &const_true_u8(), ds_bytes);
        e = e.rhs_conv(|t| t.rw_all(&ne_eq)).unwrap();
        let (h48_eq, _) = eval_opt_head(&Term::bool_lit(false), &byte_is(48), ds_bytes);
        e = e.rhs_conv(|t| t.rw_all(&h48_eq)).unwrap();
        // is_empty (tail ds)
        let tde = if ds_bytes.is_empty() {
            tail_nil(&u8_t()).unwrap()
        } else {
            eval_tail(ds_bytes)
        };
        e = e.rhs_conv(|t| t.rw_all(&tde)).unwrap();
        let tail_slice: &[u8] = if ds_bytes.is_empty() {
            &[]
        } else {
            &ds_bytes[1..]
        };
        let (et_eq, _) = eval_opt_head(&Term::bool_lit(true), &const_false_u8(), tail_slice);
        e = e.rhs_conv(|t| t.rw_all(&et_eq)).unwrap();

        // 5. decide the band/bor/bnot combination.
        let (dec, result) = decide_bool(&rhs(&e));
        (e.trans(dec).unwrap(), result)
    }

    /// `⊢ parse_json_int <bs> = <reference result>` — the strict number-token
    /// reader unfolded against a literal.
    fn eval_strict(bs: &[u8]) -> Thm {
        let s = bytes_term(bs);
        let mut e = Thm::beta_conv(Term::app(parse_json_int(), s)).unwrap();
        let s1 = skip_sep_b(bs);
        e = e.rhs_conv(|t| t.rw_all(&eval_skip_sep(bs))).unwrap();
        // open? → not a number → none
        let (open_eq, is_open_first) = eval_head_sat(&is_open(), s1);
        e = e.rhs_conv(|t| t.rw_all(&open_eq)).unwrap();
        let (_c, x, y) = split_cond(&rhs(&e));
        if is_open_first {
            return e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap();
        }
        let mut e = e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap();
        // atom head?
        let (atom_eq, is_atom_first) = eval_head_sat(&is_atom(), s1);
        e = e.rhs_conv(|t| t.rw_all(&atom_eq)).unwrap();
        let (_c, x, y) = split_cond(&rhs(&e));
        if !is_atom_first {
            return e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap();
        }
        let mut e = e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap();
        // resolve run/rest, then the strict guard.
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
        e = e.rhs_conv(|t| t.rw_all(&fpre)).unwrap();
        e = e.rhs_conv(|t| t.rw_all(&rrest)).unwrap();
        let run_bytes = atom_run_b(s1);
        let (isint_eq, ok) = eval_is_json_int(run_bytes);
        e = e.rhs_conv(|t| t.rw_all(&isint_eq)).unwrap();
        let (_c, x, y) = split_cond(&rhs(&e));
        if ok {
            e.trans(cond_true(&res_t(), &x, &y).unwrap()).unwrap()
        } else {
            e.trans(cond_false(&res_t(), &x, &y).unwrap()).unwrap()
        }
    }

    #[test]
    fn strict_reader_is_well_typed() {
        assert_eq!(
            parse_json_int().type_of().unwrap(),
            Type::fun(blist_t(), res_t())
        );
        let s = Term::free("s", blist_t());
        assert_eq!(Term::app(is_json_int(), s).type_of().unwrap(), Type::bool());
    }

    /// `is_json_int` decides the strict grammar `-?(0|[1-9][0-9]*)` on each
    /// token, matching the Rust reference. Genuine (hyps-free) equalities.
    #[test]
    fn is_json_int_decides_grammar() {
        for tok in [
            b"0".as_slice(),
            b"-7",
            b"42",
            b"01",
            b"1.5",
            b"true",
            b"1e3",
            b"-",
            b"00",
            b"-0",
            b"007",
        ] {
            let (thm, got) = eval_is_json_int(tok);
            assert!(thm.hyps().is_empty(), "is_json_int {tok:?} must be genuine");
            assert_eq!(got, is_json_int_b(tok), "is_json_int {tok:?}");
            let want = Term::bool_lit(is_json_int_b(tok));
            assert_eq!(rhs(&thm), want, "is_json_int {tok:?} value");
        }
    }

    /// The strict reader accepts exactly the strict integers among the tokens:
    /// `0`, `-7`, `42` carve `some (atom …)`; `01`, `1.5`, `true`, `1e3`, `-`
    /// reject with `none`.
    #[test]
    fn strict_reader_accepts_iff_strict_integer() {
        // accepted
        for tok in [b"0".as_slice(), b"-7", b"42"] {
            let thm = eval_strict(tok);
            assert!(thm.hyps().is_empty(), "strict {tok:?} must be genuine");
            let want = some_r(pair_r(atom_of(bytes_term(tok)), nil_u()));
            assert_eq!(rhs(&thm), want, "strict accepts {tok:?}");
        }
        // rejected
        for tok in [b"01".as_slice(), b"1.5", b"true", b"1e3", b"-"] {
            let thm = eval_strict(tok);
            assert!(thm.hyps().is_empty(), "strict {tok:?} must be genuine");
            assert_eq!(rhs(&thm), none_r(), "strict rejects {tok:?}");
        }
        // an open bracket is not a number token → none.
        assert_eq!(rhs(&eval_strict(b"[1]")), none_r());
    }

    /// `json_int_accepts` / `json_int_rejects` — the general (free-variable)
    /// faithfulness theorems: the strict branch fires with the lenient value
    /// iff the run is a strict integer.
    #[test]
    fn branch_faithfulness_is_genuine() {
        let run = Term::free("run", blist_t());
        let rest = Term::free("rest", blist_t());
        let ctx = crate::HolLightCtx::new();

        let acc = json_int_accepts(&run, &rest).unwrap();
        assert!(acc.hyps().is_empty(), "acceptance must be oracle-free");
        let guard = Term::app(is_json_int(), run.clone());
        let want_acc = ctx.mk_imp(
            guard.clone().equals(Term::bool_lit(true)).unwrap(),
            json_int_branch(&run, &rest)
                .equals(lenient_num_value(&run, &rest))
                .unwrap(),
        );
        assert_eq!(acc.concl(), &want_acc);

        let rej = json_int_rejects(&run, &rest).unwrap();
        assert!(rej.hyps().is_empty(), "rejection must be oracle-free");
        let want_rej = ctx.mk_imp(
            guard.equals(Term::bool_lit(false)).unwrap(),
            json_int_branch(&run, &rest).equals(none_r()).unwrap(),
        );
        assert_eq!(rej.concl(), &want_rej);
    }

    /// The subset relation, concretely against the *real* lenient reader:
    /// every token the strict reader accepts, the lenient reader carves
    /// identically (`parse_json_int s = parse_json fuel s`).
    #[test]
    fn strict_is_subset_of_lenient() {
        for tok in [b"0".as_slice(), b"-7", b"42"] {
            let strict = eval_strict(tok);
            let lenient = eval(30, false, tok);
            assert!(strict.hyps().is_empty() && lenient.hyps().is_empty());
            assert_eq!(rhs(&strict), rhs(&lenient), "same value for {tok:?}");
            // and the shared value is a `some (atom …)`.
            assert_eq!(
                rhs(&strict),
                some_r(pair_r(atom_of(bytes_term(tok)), nil_u()))
            );
        }
    }

    // ------------------------------------------------------------------
    // The ∀-quantified whole-value integer subset.
    // ------------------------------------------------------------------

    #[test]
    fn whole_value_subset_is_genuine() {
        let thm = parse_json_int_subset().unwrap();
        assert!(
            thm.hyps().is_empty(),
            "whole-value subset must be oracle-free"
        );
        // A triple-∀: instantiating all three quantifiers must succeed.
        let s = Term::free("s", blist_t());
        let v = Term::free("v", tau());
        let r = Term::free("r", blist_t());
        let inst = thm
            .all_elim(s.clone())
            .unwrap()
            .all_elim(v.clone())
            .unwrap()
            .all_elim(r.clone())
            .unwrap();
        // The body is the intended implication.
        let some_p = some_r(pair_r(v, r));
        let ante = Term::app(parse_json_int(), s.clone())
            .equals(some_p.clone())
            .unwrap();
        let (imp_a, _imp_c) = inst.concl().as_app().unwrap();
        let (_imp, a) = imp_a.as_app().unwrap();
        assert_eq!(a, &ante, "antecedent is the strict parse hypothesis");
    }

    /// Discharge the ∀ theorem against the *real* readers on `0`/`-7`/`42`,
    /// and confirm a non-integer (`1.5`) strict-rejects (so the subset is
    /// vacuous there).
    #[test]
    fn whole_value_subset_discharges_on_real_readers() {
        const K: usize = 30;
        // Instantiate the free `fuel` so `succ fuel` becomes the concrete
        // `fuel(K)` = `succ (fuel (K-1))`.
        let thm = parse_json_int_subset()
            .unwrap()
            .inst("fuel", fuel(K - 1))
            .unwrap();

        for tok in [b"0".as_slice(), b"-7", b"42"] {
            let strict = eval_strict(tok); // ⊢ parse_json_int [tok] = some(atom tok, nil)
            assert!(strict.hyps().is_empty());
            let vval = atom_of(bytes_term(tok));
            let rval = nil_u();
            let some_vr = some_r(pair_r(vval.clone(), rval.clone()));
            assert_eq!(rhs(&strict), some_vr, "strict value for {tok:?}");

            // Discharge: s := [tok], v := atom tok, r := nil, then MP with the
            // strict parse. Yields the lenient reader's value, hyp-free.
            let lenient = thm
                .clone()
                .all_elim(bytes_term(tok))
                .unwrap()
                .all_elim(vval)
                .unwrap()
                .all_elim(rval)
                .unwrap()
                .imp_elim(strict)
                .unwrap();
            assert!(
                lenient.hyps().is_empty(),
                "discharged subset must be genuine for {tok:?}"
            );
            assert_eq!(rhs(&lenient), some_vr, "lenient value for {tok:?}");

            // The independent *real* lenient reader agrees on the value.
            assert_eq!(rhs(&eval(K, false, tok)), some_vr, "real lenient {tok:?}");
        }

        // A float literal is not a strict integer: the strict reader rejects,
        // so the subset theorem imposes nothing.
        assert_eq!(rhs(&eval_strict(b"1.5")), none_r());
    }
}
