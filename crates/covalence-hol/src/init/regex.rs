//! **Regular expressions on lists**, reified inside HOL, with a `Matches`
//! derivation you can do **induction on** — the foundation for defining
//! actual languages (`docs/metatheory.md` §8; the regex analogue of
//! [`crate::init::prop`]'s propositional object logic).
//!
//! A regex over an alphabet `'a` is the datatype
//!
//! ```text
//!   regex 'a  :=  empty | eps | lit 'a | alt regex regex
//!              |  seq regex regex | star regex
//! ```
//!
//! and a *word* is a `list 'a`. Two judgements are defined over it:
//!
//! - a **denotation** `⟦r⟧ : set (list 'a)` — the language `r` describes,
//!   built from [`crate::init::lang`]'s Kleene-algebra operations over the
//!   **free monoid** `(list 'a, cat, nil)` ([`monoid::list_cat_monoid`]);
//! - a **matching predicate** `Matches r w : bool` — "the word `w` matches
//!   `r`" — defined *impredicatively* as the smallest relation closed under
//!   the seven matching rules, so **induction on a match derivation** is a
//!   single `inst` of the impredicative predicate.
//!
//! The headline theorem is **soundness** ([`soundness`]):
//! `⊢ Matches r w ⟹ mem w ⟦r⟧` — every match witnesses language membership,
//! proved by induction on the match derivation.
//!
//! ## Why the Church / impredicative encoding (the design choice)
//!
//! The generic recursion engine ([`crate::init::inductive`]) builds a
//! recursor for a *directly* recursive, single-recursive-argument datatype.
//! A regex's `alt`/`seq` each have **two** recursive arguments, which the
//! engine cannot yet recurse over. We sidestep that entirely with the
//! [`crate::init::prop`] recipe: encode the syntax as a polymorphic fold over
//! a fresh result type `'r`, and define `Matches` impredicatively. Then:
//!
//! 1. **No engine recursor is needed.** Constructors are folds; distinct
//!    regexes are distinct HOL terms (genuine reified syntax, *not* a shallow
//!    embedding).
//! 2. **Rule induction is `inst`.** `Matches r w := ∀M. Closed M ⟹ M r w`;
//!    induction over a match derivation instantiates the predicate variable
//!    `M` and discharges the `Closed M` obligations — exactly
//!    [`crate::init::prop`]'s `Derivable_Prop` rule induction. The soundness
//!    proof takes `M := λr w. mem w ⟦r⟧`.
//! 3. **Nothing is added to `covalence-core`.** The whole development rides
//!    on existing kernel primitives + the `lang`/`set`/`list` theories.
//!
//! ## What is proved (genuine, hypothesis- and oracle-free)
//!
//! - the constructors [`r_empty`]/[`r_eps`]/[`r_lit`]/[`r_alt`]/[`r_seq`]/
//!   [`r_star`] and the denotation [`denote`];
//! - the **matching rules** as theorems
//!   ([`match_eps`], [`match_lit`], [`match_alt_l`], [`match_alt_r`],
//!   [`match_seq`], [`match_star_nil`], [`match_star_step`]);
//! - **soundness** [`soundness`] — `⊢ Matches r w ⟹ mem w ⟦r⟧`, by rule
//!   induction (all seven cases discharged against the `lang` membership
//!   computations + the star pre-fixpoint
//!   [`lang::star_concat_closed`](crate::init::lang::star_concat_closed)).
//!
//! ## Bytestrings
//!
//! Instantiating the alphabet at `u8` gives regexes over `list u8` (the
//! `bytes` carrier). [`u8_alphabet`] and the [`tests`] worked example show a
//! concrete bytestring regex and its denotation.
//!
//! ## What is deferred (see `SKELETONS.md`)
//!
//! - **`Matches`-completeness** (`mem w ⟦r⟧ ⟹ Matches r w`, the converse of
//!   soundness): needs the least-fixpoint half of the star unfolding.
//! - **Ambiguity** (multiple derivations of one match) and **sexpr
//!   lift/lower**: design-note only — see the module's bottom + the report.

use covalence_core::{Result, Term, Thm, Type};

use crate::init::ext::TermExt;
use crate::init::lang;
use crate::init::monoid::{list_cat_monoid, Monoid};

// ============================================================================
// Type machinery: the carrier `Regex⟨'a, 'r⟩`.
// ============================================================================

/// The element / alphabet type variable `'a` (the canonical polymorphic
/// alphabet; concrete callers pass `u8`, etc.).
#[cfg(test)]
fn aty() -> Type {
    Type::tfree("a")
}

/// The fold result type variable `'r`.
fn rty() -> Type {
    Type::tfree("r")
}

/// `list 'a` — the word type over alphabet `alpha`.
fn word_ty(alpha: &Type) -> Type {
    crate::init::list::list(alpha.clone())
}

/// The six handler slot types, in fold order
/// `empty eps lit alt seq star`, parametric in `'a` (the `lit` payload) and
/// the result type `r`.
fn empty_h_ty(_a: &Type, r: &Type) -> Type {
    r.clone()
}
fn eps_h_ty(_a: &Type, r: &Type) -> Type {
    r.clone()
}
fn lit_h_ty(a: &Type, r: &Type) -> Type {
    Type::fun(a.clone(), r.clone())
}
fn bin_h_ty(_a: &Type, r: &Type) -> Type {
    Type::fun(r.clone(), Type::fun(r.clone(), r.clone()))
}
fn un_h_ty(_a: &Type, r: &Type) -> Type {
    Type::fun(r.clone(), r.clone())
}

/// The six handler binder names + slot-type builders, in fold order.
const HANDLERS: [(&str, fn(&Type, &Type) -> Type); 6] = [
    ("h_empty", empty_h_ty),
    ("h_eps", eps_h_ty),
    ("h_lit", lit_h_ty),
    ("h_alt", bin_h_ty),
    ("h_seq", bin_h_ty),
    ("h_star", un_h_ty),
];

/// `Regex⟨a, r⟩ = r → r → (a→r) → (r→r→r) → (r→r→r) → (r→r) → r` — the type
/// of an encoded regex at alphabet `a` and result type `r`.
fn regex_at(a: &Type, r: &Type) -> Type {
    let mut t = r.clone();
    for (_, slot) in HANDLERS.iter().rev() {
        t = Type::fun(slot(a, r), t);
    }
    t
}

/// `regex 'a` — the canonical polymorphic carrier (result type the free type
/// variable `'r`). The public datatype.
pub fn regex(alpha: Type) -> Type {
    regex_at(&alpha, &rty())
}

/// A free handler variable by name, at alphabet `a` / result type `r`.
fn handler(a: &Type, r: &Type, name: &str) -> Term {
    let ty = HANDLERS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, t)| t(a, r))
        .expect("handler name");
    Term::free(name, ty)
}

/// `λh_empty h_eps h_lit h_alt h_seq h_star. body` — wrap a fold `body : r`
/// in the six handler abstractions, yielding a `Regex⟨a, r⟩` value.
fn close_handlers(a: &Type, r: &Type, body: Term) -> Term {
    let mut t = body;
    for (name, ty) in HANDLERS.iter().rev() {
        t = Term::abs(ty(a, r), covalence_core::subst::close(&t, name));
    }
    t
}

/// Apply an encoded regex `enc : Regex⟨a, r⟩` to the six handlers, producing
/// its fold `: r`. The inverse of [`close_handlers`] up to β.
fn apply_handlers(a: &Type, r: &Type, enc: Term) -> Term {
    let mut t = enc;
    for (name, _) in HANDLERS {
        t = Term::app(t, handler(a, r, name));
    }
    t
}

// ============================================================================
// Constructors (encoding `⌜·⌝`).
//
// Each builds at result type `r`; the public `r_*` builders default to the
// polymorphic `'r`.
// ============================================================================

/// `enc(empty) : Regex⟨a, r⟩` — the empty regex (matches nothing).
pub fn r_empty_at(a: &Type, r: &Type) -> Term {
    close_handlers(a, r, handler(a, r, "h_empty"))
}

/// `enc(eps) : Regex⟨a, r⟩` — the empty-word regex (matches only `nil`).
pub fn r_eps_at(a: &Type, r: &Type) -> Term {
    close_handlers(a, r, handler(a, r, "h_eps"))
}

/// `enc(lit c) : Regex⟨a, r⟩` — a single-character literal.
pub fn r_lit_at(a: &Type, r: &Type, c: Term) -> Term {
    close_handlers(a, r, Term::app(handler(a, r, "h_lit"), c))
}

fn r_bin_at(a: &Type, r: &Type, op: &str, x: Term, y: Term) -> Term {
    let body = Term::app(
        Term::app(handler(a, r, op), apply_handlers(a, r, x)),
        apply_handlers(a, r, y),
    );
    close_handlers(a, r, body)
}

/// `enc(alt x y) : Regex⟨a, r⟩` — alternation (`x | y`).
pub fn r_alt_at(a: &Type, r: &Type, x: Term, y: Term) -> Term {
    r_bin_at(a, r, "h_alt", x, y)
}

/// `enc(seq x y) : Regex⟨a, r⟩` — concatenation (`x y`).
pub fn r_seq_at(a: &Type, r: &Type, x: Term, y: Term) -> Term {
    r_bin_at(a, r, "h_seq", x, y)
}

/// `enc(star x) : Regex⟨a, r⟩` — Kleene star (`x*`).
pub fn r_star_at(a: &Type, r: &Type, x: Term) -> Term {
    close_handlers(a, r, Term::app(handler(a, r, "h_star"), apply_handlers(a, r, x)))
}

/// `enc(empty) : regex 'a`.
pub fn r_empty(alpha: &Type) -> Term {
    r_empty_at(alpha, &rty())
}
/// `enc(eps) : regex 'a`.
pub fn r_eps(alpha: &Type) -> Term {
    r_eps_at(alpha, &rty())
}
/// `enc(lit c) : regex 'a`.
pub fn r_lit(alpha: &Type, c: Term) -> Term {
    r_lit_at(alpha, &rty(), c)
}
/// `enc(alt x y) : regex 'a`.
pub fn r_alt(alpha: &Type, x: Term, y: Term) -> Term {
    r_alt_at(alpha, &rty(), x, y)
}
/// `enc(seq x y) : regex 'a`.
pub fn r_seq(alpha: &Type, x: Term, y: Term) -> Term {
    r_seq_at(alpha, &rty(), x, y)
}
/// `enc(star x) : regex 'a`.
pub fn r_star(alpha: &Type, x: Term) -> Term {
    r_star_at(alpha, &rty(), x)
}

// ============================================================================
// Denotation `⟦·⟧ : regex 'a → set (list 'a)`.
//
// A regex denotes a *language* over the free monoid `(list 'a, cat, nil)`:
// `⟦empty⟧ = ∅`, `⟦eps⟧ = {[]}`, `⟦lit c⟧ = {[c]}`,
// `⟦alt x y⟧ = ⟦x⟧ ∪ ⟦y⟧`, `⟦seq x y⟧ = ⟦x⟧ · ⟦y⟧`, `⟦star x⟧ = ⟦x⟧*`.
//
// Concretely, `⟦r⟧` is the fold `r[set (list a)] · …` — instantiate the
// result type to `set (list a)` and feed the six language-level handlers.
// ============================================================================

/// `set (list a)` — the type a language over alphabet `a` lives in.
fn lang_ty(alpha: &Type) -> Type {
    lang::lang(word_ty(alpha))
}

/// The six concrete language handlers, in fold order, for `⟦·⟧`:
/// `(∅, {[]}, λc. {[c]}, ∪, ·, *)` over the free monoid on `alpha`.
fn lang_handlers(m: &Monoid, alpha: &Type) -> Result<[Term; 6]> {
    let lty = lang_ty(alpha);
    // empty / eps are nullary.
    let h_empty = lang::empty_lang(m)?;
    let h_eps = lang::epsilon(m)?;
    // lit: λc:a. {[c]} = set.singleton (cons c nil).
    let h_lit = {
        let c = Term::free("c", alpha.clone());
        let singleton_word = crate::init::list::cons(alpha.clone())
            .apply(c.clone())?
            .apply(crate::init::list::nil(alpha.clone()))?;
        let sing = Term::app(
            crate::init::set::set_singleton(word_ty(alpha)),
            singleton_word,
        );
        Term::abs(alpha.clone(), covalence_core::subst::close(&sing, "c"))
    };
    // alt: λX Y. X ∪ Y.
    let h_alt = bin_lang(&lty, |x, y| lang::lang_union(m, x, y))?;
    // seq: λX Y. X · Y.
    let h_seq = bin_lang(&lty, |x, y| lang::lang_concat(m, x, y))?;
    // star: λX. X*.
    let h_star = {
        let xv = Term::free("X", lty.clone());
        let body = lang::lang_star(m, &xv)?;
        Term::abs(lty.clone(), covalence_core::subst::close(&body, "X"))
    };
    Ok([h_empty, h_eps, h_lit, h_alt, h_seq, h_star])
}

/// `λX Y. f X Y` for a binary language operation `f`, both args of type `lty`.
fn bin_lang(lty: &Type, f: impl Fn(&Term, &Term) -> Result<Term>) -> Result<Term> {
    let x = Term::free("X", lty.clone());
    let y = Term::free("Y", lty.clone());
    let body = f(&x, &y)?;
    let inner = Term::abs(lty.clone(), covalence_core::subst::close(&body, "Y"));
    Ok(Term::abs(lty.clone(), covalence_core::subst::close(&inner, "X")))
}

/// `⟦r⟧ : set (list a)` — the language denotation of an encoded regex `r`.
/// Instantiates the regex's result type to `set (list a)` and folds with the
/// six language handlers (the *term* `r[set(list a)] ∅ {[]} (…) (∪) (·) (*)`).
/// Accepts `r` at `Regex⟨a, 'r⟩` or `Regex⟨a, set(list a)⟩`.
pub fn denote(alpha: &Type, r: Term) -> Result<Term> {
    let m = list_cat_monoid(alpha.clone());
    let lty = lang_ty(alpha);
    let mut t = covalence_core::subst::subst_tfree_in_term(&r, "r", &lty);
    for h in lang_handlers(&m, alpha)? {
        t = t.apply(h)?;
    }
    Ok(t)
}

// ============================================================================
// `Matches` — the impredicative matching predicate.
//
//   Matches r w := ∀M:regex 'a → list 'a → bool. Closed M ⟹ M r w
//
// where `Closed M` is the conjunction of the seven matching-rule closure
// clauses. Rule induction is `inst M`.
// ============================================================================

/// The type of the impredicative match predicate variable
/// `M : regex 'a → list 'a → bool`.
fn m_ty(alpha: &Type) -> Type {
    Type::fun(regex(alpha.clone()), Type::fun(word_ty(alpha), Type::bool()))
}

/// `M : regex 'a → list 'a → bool` — the predicate variable bound in
/// `Matches`.
fn m_var(alpha: &Type) -> Term {
    Term::free("M", m_ty(alpha))
}

/// `M r w` for the predicate variable `M`.
fn m_at(_alpha: &Type, m: &Term, r: &Term, w: &Term) -> Result<Term> {
    m.clone().apply(r.clone())?.apply(w.clone())
}

/// `nil : list 'a`.
fn nil_w(alpha: &Type) -> Term {
    crate::init::list::nil(alpha.clone())
}

/// `cons c nil : list 'a` — the singleton word `[c]`.
fn singleton_w(alpha: &Type, c: &Term) -> Result<Term> {
    crate::init::list::cons(alpha.clone())
        .apply(c.clone())?
        .apply(nil_w(alpha))
}

/// `cat w1 w2 : list 'a`.
fn cat_w(alpha: &Type, w1: &Term, w2: &Term) -> Result<Term> {
    crate::init::list::list_cat(alpha.clone())
        .apply(w1.clone())?
        .apply(w2.clone())
}

/// The seven closure clauses of `Closed M`, in order, each a `bool` term
/// over fresh regex/word variables; `m_apply` supplies `M · ·`. Returned as a
/// `Vec` to be conjoined.
///
/// 1. `M eps nil`                                              (eps)
/// 2. `∀c. M (lit c) [c]`                                      (lit)
/// 3. `∀x y w. M x w ⟹ M (alt x y) w`                         (alt-left)
/// 4. `∀x y w. M y w ⟹ M (alt x y) w`                         (alt-right)
/// 5. `∀x y w1 w2. M x w1 ⟹ M y w2 ⟹ M (seq x y) (cat w1 w2)` (seq)
/// 6. `∀x. M (star x) nil`                                     (star-nil)
/// 7. `∀x w1 w2. M x w1 ⟹ M (star x) w2 ⟹ M (star x) (cat w1 w2)` (star-step)
fn closure_clauses(
    alpha: &Type,
    m_apply: &dyn Fn(&Term, &Term) -> Result<Term>,
) -> Result<Vec<Term>> {
    let rty_a = regex(alpha.clone());
    let wty = word_ty(alpha);
    let c = Term::free("c", alpha.clone());
    let x = Term::free("x", rty_a.clone());
    let y = Term::free("y", rty_a.clone());
    let w = Term::free("w", wty.clone());
    let w1 = Term::free("w1", wty.clone());
    let w2 = Term::free("w2", wty.clone());

    let mut clauses = Vec::new();

    // 1. eps: M eps nil.
    clauses.push(m_apply(&r_eps(alpha), &nil_w(alpha))?);

    // 2. lit: ∀c. M (lit c) [c].
    clauses.push(
        m_apply(&r_lit(alpha, c.clone()), &singleton_w(alpha, &c)?)?
            .forall("c", alpha.clone())?,
    );

    // 3. alt-left: ∀x y w. M x w ⟹ M (alt x y) w.
    clauses.push(
        m_apply(&x, &w)?
            .imp(m_apply(&r_alt(alpha, x.clone(), y.clone()), &w)?)?
            .forall("w", wty.clone())?
            .forall("y", rty_a.clone())?
            .forall("x", rty_a.clone())?,
    );

    // 4. alt-right: ∀x y w. M y w ⟹ M (alt x y) w.
    clauses.push(
        m_apply(&y, &w)?
            .imp(m_apply(&r_alt(alpha, x.clone(), y.clone()), &w)?)?
            .forall("w", wty.clone())?
            .forall("y", rty_a.clone())?
            .forall("x", rty_a.clone())?,
    );

    // 5. seq: ∀x y w1 w2. M x w1 ⟹ M y w2 ⟹ M (seq x y) (cat w1 w2).
    clauses.push(
        m_apply(&x, &w1)?
            .imp(
                m_apply(&y, &w2)?.imp(
                    m_apply(&r_seq(alpha, x.clone(), y.clone()), &cat_w(alpha, &w1, &w2)?)?,
                )?,
            )?
            .forall("w2", wty.clone())?
            .forall("w1", wty.clone())?
            .forall("y", rty_a.clone())?
            .forall("x", rty_a.clone())?,
    );

    // 6. star-nil: ∀x. M (star x) nil.
    clauses.push(
        m_apply(&r_star(alpha, x.clone()), &nil_w(alpha))?.forall("x", rty_a.clone())?,
    );

    // 7. star-step: ∀x w1 w2. M x w1 ⟹ M (star x) w2 ⟹ M (star x) (cat w1 w2).
    clauses.push(
        m_apply(&x, &w1)?
            .imp(
                m_apply(&r_star(alpha, x.clone()), &w2)?.imp(
                    m_apply(&r_star(alpha, x.clone()), &cat_w(alpha, &w1, &w2)?)?,
                )?,
            )?
            .forall("w2", wty.clone())?
            .forall("w1", wty.clone())?
            .forall("x", rty_a.clone())?,
    );

    Ok(clauses)
}

/// Number of closure clauses (matching rules).
const N_CLAUSES: usize = 7;

/// `Closed M` — the right-nested conjunction of the seven closure clauses.
fn closed(alpha: &Type, m_apply: &dyn Fn(&Term, &Term) -> Result<Term>) -> Result<Term> {
    let clauses = closure_clauses(alpha, m_apply)?;
    let mut iter = clauses.into_iter().rev();
    let mut acc = iter.next().expect("at least one clause");
    for cl in iter {
        acc = cl.and(acc)?;
    }
    Ok(acc)
}

/// `Matches r w := ∀M. Closed M ⟹ M r w` — the impredicative matching
/// predicate. The *only* way to obtain `⊢ Matches r w` is through the
/// [`match_*`](match_eps) derivation constructors (the reified LCF discipline
/// one level up, exactly like [`crate::init::prop::derivable`]).
pub fn matches(alpha: &Type, r: &Term, w: &Term) -> Result<Term> {
    let mvar = m_var(alpha);
    let closed_m = closed(alpha, &|rr, ww| m_at(alpha, &mvar, rr, ww))?;
    let body = closed_m.imp(m_at(alpha, &mvar, r, w)?)?;
    body.forall("M", m_ty(alpha))
}

// ============================================================================
// Matching-rule derivation constructors.
//
// Each opens `∀M. Closed M ⟹ M r w`: assume `Closed M`, extract the matching
// closure clause, apply it (possibly chaining derivability hypotheses for the
// recursive rules), discharge `Closed M`, generalise `M`.
// ============================================================================

/// From a right-nested conjunction of `n` clauses, extract conjunct `k`
/// (0-based). Identical to [`crate::init::prop`]'s `nth_conjunct`.
fn nth_conjunct(mut thm: Thm, k: usize, n: usize) -> Result<Thm> {
    for _ in 0..k {
        thm = thm.and_elim_r()?;
    }
    if k + 1 < n {
        thm.and_elim_l()
    } else {
        Ok(thm)
    }
}

/// `⊢ Matches eps nil` — the empty word matches `eps`. (Rule 1.)
pub fn match_eps(alpha: &Type) -> Result<Thm> {
    let mvar = m_var(alpha);
    let closed_t = closed(alpha, &|rr, ww| m_at(alpha, &mvar, rr, ww))?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed M} ⊢ Closed M
    let clause = nth_conjunct(assumed, 0, N_CLAUSES)?; // {Closed M} ⊢ M eps nil
    clause
        .imp_intro(&closed_t)?
        .all_intro("M", m_ty(alpha))
}

/// `⊢ ∀c. Matches (lit c) [c]` — a literal matches its one-character word.
/// (Rule 2.)
pub fn match_lit(alpha: &Type) -> Result<Thm> {
    let mvar = m_var(alpha);
    let c = Term::free("c", alpha.clone());
    let closed_t = closed(alpha, &|rr, ww| m_at(alpha, &mvar, rr, ww))?;
    let assumed = Thm::assume(closed_t.clone())?;
    let clause = nth_conjunct(assumed, 1, N_CLAUSES)?; // ⊢ ∀c. M (lit c) [c]
    let at_c = clause.all_elim(c.clone())?; // {Closed M} ⊢ M (lit c) [c]
    at_c.imp_intro(&closed_t)?
        .all_intro("M", m_ty(alpha))?
        .all_intro("c", alpha.clone())
}

/// `⊢ Matches x w ⟹ Matches (alt x y) w` — left injection of alternation.
/// (Rule 3.)
pub fn match_alt_l(alpha: &Type, x: &Term, y: &Term, w: &Term) -> Result<Thm> {
    match_unary_rule(alpha, 2, x, w, |c| {
        // clause is ∀x y w. … (outermost x); peel x, y, w.
        c.all_elim(x.clone())?.all_elim(y.clone())?.all_elim(w.clone())
    })
}

/// `⊢ Matches y w ⟹ Matches (alt x y) w` — right injection of alternation.
/// (Rule 4.)
pub fn match_alt_r(alpha: &Type, x: &Term, y: &Term, w: &Term) -> Result<Thm> {
    match_unary_rule(alpha, 3, y, w, |c| {
        c.all_elim(x.clone())?.all_elim(y.clone())?.all_elim(w.clone())
    })
}

/// Shared body for the single-premise recursive rules (alt-left/right):
/// `⊢ Matches sub w ⟹ Matches concl w`. `inst` selects + specialises the
/// matching clause to `⊢ M sub w ⟹ M concl w` under `Closed M`.
fn match_unary_rule(
    alpha: &Type,
    clause_idx: usize,
    sub: &Term,
    w: &Term,
    spec: impl Fn(Thm) -> Result<Thm>,
) -> Result<Thm> {
    let mvar = m_var(alpha);
    let closed_t = closed(alpha, &|rr, ww| m_at(alpha, &mvar, rr, ww))?;
    let assumed = Thm::assume(closed_t.clone())?;
    let clause = nth_conjunct(assumed.clone(), clause_idx, N_CLAUSES)?; // ⊢ ∀x y w. M sub w ⟹ M concl w
    let imp = spec(clause)?; // {Closed M} ⊢ M sub w ⟹ M concl w

    // From `Matches sub w` get `M sub w`, MP, fold to `Matches concl w`.
    let der_sub = Thm::assume(matches(alpha, sub, w)?)?; // {Matches sub w} ⊢ …
    let m_sub = der_sub.all_elim(mvar.clone())?.imp_elim(assumed.clone())?; // {Matches sub w, Closed M} ⊢ M sub w
    let m_concl = imp.imp_elim(m_sub)?; // {…} ⊢ M concl w
    let der_concl = m_concl
        .imp_intro(&closed_t)?
        .all_intro("M", m_ty(alpha))?; // {Matches sub w} ⊢ Matches concl w
    der_concl.imp_intro(&matches(alpha, sub, w)?)
}

/// `⊢ Matches x w1 ⟹ Matches y w2 ⟹ Matches (seq x y) (cat w1 w2)` —
/// matching a concatenation splits the word. (Rule 5.)
pub fn match_seq(alpha: &Type, x: &Term, y: &Term, w1: &Term, w2: &Term) -> Result<Thm> {
    let mvar = m_var(alpha);
    let closed_t = closed(alpha, &|rr, ww| m_at(alpha, &mvar, rr, ww))?;
    let assumed = Thm::assume(closed_t.clone())?;
    let clause = nth_conjunct(assumed.clone(), 4, N_CLAUSES)?; // ⊢ ∀x y w1 w2. M x w1 ⟹ M y w2 ⟹ M (seq x y)(cat w1 w2)
    let imp = clause
        .all_elim(x.clone())?
        .all_elim(y.clone())?
        .all_elim(w1.clone())?
        .all_elim(w2.clone())?; // {Closed M} ⊢ M x w1 ⟹ M y w2 ⟹ M (seq x y)(cat w1 w2)

    let der_x = Thm::assume(matches(alpha, x, w1)?)?;
    let m_x = der_x.all_elim(mvar.clone())?.imp_elim(assumed.clone())?; // {…} ⊢ M x w1
    let der_y = Thm::assume(matches(alpha, y, w2)?)?;
    let m_y = der_y.all_elim(mvar.clone())?.imp_elim(assumed.clone())?; // {…} ⊢ M y w2

    let m_seq = imp.imp_elim(m_x)?.imp_elim(m_y)?; // {…} ⊢ M (seq x y)(cat w1 w2)
    let der_seq = m_seq
        .imp_intro(&closed_t)?
        .all_intro("M", m_ty(alpha))?; // {Matches x w1, Matches y w2} ⊢ Matches (seq x y)(cat w1 w2)
    der_seq
        .imp_intro(&matches(alpha, y, w2)?)?
        .imp_intro(&matches(alpha, x, w1)?)
}

/// `⊢ Matches (star x) nil` — the star matches the empty word. (Rule 6.)
pub fn match_star_nil(alpha: &Type, x: &Term) -> Result<Thm> {
    let mvar = m_var(alpha);
    let closed_t = closed(alpha, &|rr, ww| m_at(alpha, &mvar, rr, ww))?;
    let assumed = Thm::assume(closed_t.clone())?;
    let clause = nth_conjunct(assumed, 5, N_CLAUSES)?; // ⊢ ∀x. M (star x) nil
    let at_x = clause.all_elim(x.clone())?; // {Closed M} ⊢ M (star x) nil
    at_x.imp_intro(&closed_t)?.all_intro("M", m_ty(alpha))
}

/// `⊢ Matches x w1 ⟹ Matches (star x) w2 ⟹ Matches (star x) (cat w1 w2)` —
/// one more iteration of the star. (Rule 7.)
pub fn match_star_step(alpha: &Type, x: &Term, w1: &Term, w2: &Term) -> Result<Thm> {
    let mvar = m_var(alpha);
    let closed_t = closed(alpha, &|rr, ww| m_at(alpha, &mvar, rr, ww))?;
    let assumed = Thm::assume(closed_t.clone())?;
    let clause = nth_conjunct(assumed.clone(), 6, N_CLAUSES)?; // ⊢ ∀x w1 w2. M x w1 ⟹ M (star x) w2 ⟹ M (star x)(cat w1 w2)
    let imp = clause
        .all_elim(x.clone())?
        .all_elim(w1.clone())?
        .all_elim(w2.clone())?;

    let star_x = r_star(alpha, x.clone());
    let der_x = Thm::assume(matches(alpha, x, w1)?)?;
    let m_x = der_x.all_elim(mvar.clone())?.imp_elim(assumed.clone())?;
    let der_sw = Thm::assume(matches(alpha, &star_x, w2)?)?;
    let m_sw = der_sw.all_elim(mvar.clone())?.imp_elim(assumed.clone())?;

    let m_step = imp.imp_elim(m_x)?.imp_elim(m_sw)?; // {…} ⊢ M (star x)(cat w1 w2)
    let der_step = m_step
        .imp_intro(&closed_t)?
        .all_intro("M", m_ty(alpha))?;
    der_step
        .imp_intro(&matches(alpha, &star_x, w2)?)?
        .imp_intro(&matches(alpha, x, w1)?)
}

// ============================================================================
// Soundness — `⊢ Matches r w ⟹ mem w ⟦r⟧`, by rule induction.
// ============================================================================

/// `set.mem[list a] w L : bool` — word membership in a language.
fn mem(alpha: &Type, w: &Term, l: &Term) -> Term {
    Term::app(
        Term::app(crate::init::set::set_mem(word_ty(alpha)), w.clone()),
        l.clone(),
    )
}

/// `⊢ Matches r w ⟹ mem w ⟦r⟧` for arbitrary encoded regex `r` and word `w`
/// (free variables) — **soundness** of matching against the denotation.
///
/// **Proof.** Instantiate the impredicative predicate
/// `M := λr w. mem w ⟦r⟧` in `Matches r w = ∀M. Closed M ⟹ M r w`. This
/// reduces the goal to discharging `Closed (λr w. mem w ⟦r⟧)`, i.e. proving
/// each matching rule holds with `mem`-into-denotation in place of `M`:
///
/// - **eps** `mem nil ⟦eps⟧ = mem nil {[]}` — `(nil = nil)` is `T`
///   ([`lang::mem_epsilon`](crate::init::lang::mem_epsilon));
/// - **lit** `mem [c] ⟦lit c⟧ = mem [c] {[c]}` — `([c]=[c])` is `T`
///   ([`set::mem_singleton`](crate::init::set::mem_singleton));
/// - **alt** `mem w ⟦x⟧ ⟹ mem w (⟦x⟧∪⟦y⟧)` — `or_intro` after
///   [`lang::mem_union`](crate::init::set::mem_union) (and the right form);
/// - **seq** `mem w1⟦x⟧ ⟹ mem w2⟦y⟧ ⟹ mem (cat w1 w2)(⟦x⟧·⟦y⟧)` — witness
///   the concat existential ([`lang::mem_concat`](crate::init::lang::mem_concat))
///   at `w1, w2`;
/// - **star-nil** `mem nil ⟦x⟧*` — `nil∈ε⊆⟦x⟧*`
///   ([`lang::star_contains_epsilon`](crate::init::lang::star_contains_epsilon));
/// - **star-step** `mem w1⟦x⟧ ⟹ mem w2⟦x⟧* ⟹ mem (cat w1 w2)⟦x⟧*` — `cat w1
///   w2 ∈ ⟦x⟧·⟦x⟧* ⊆ ⟦x⟧*`, the pre-fixpoint
///   [`lang::star_concat_closed`](crate::init::lang::star_concat_closed).
///
/// Returns `⊢ Matches r w ⟹ mem w ⟦r⟧`, both `r`, `w` free.
pub fn soundness(alpha: &Type) -> Result<Thm> {
    let r = Term::free("r", regex(alpha.clone()));
    let w = Term::free("w", word_ty(alpha));
    soundness_at(alpha, &r, &w)
}

/// Substitute the fold result type `'r := set (list a)` in a term — the only
/// instance the denotation needs (mirrors [`crate::init::prop`]'s
/// `inst_tfree_term`).
fn inst_r(alpha: &Type, t: &Term) -> Term {
    covalence_core::subst::subst_tfree_in_term(t, "r", &lang_ty(alpha))
}

/// Soundness for *specific* `r`, `w`. The whole proof runs at the denotation
/// instance `'r := set (list a)`: the `Matches`/`Closed` machinery is
/// polymorphic in the fold result `'r`, but the predicate `D = λr w. mem w
/// ⟦r⟧` lives at `set (list a)`, so we instantiate the statement there before
/// `all_elim`-ing `D` (exactly [`crate::init::prop::soundness_at`]'s move).
///
/// Returns `⊢ Matches r w ⟹ mem w ⟦r⟧` at `'r := set (list a)`.
pub fn soundness_at(alpha: &Type, r: &Term, w: &Term) -> Result<Thm> {
    let wty = word_ty(alpha);
    let rty_set = regex_at(alpha, &lang_ty(alpha)); // regex 'a at 'r := set(list a)

    // The instantiation predicate D := λr w. mem w ⟦r⟧, the regex argument at
    // result type `set (list a)`.
    let big_r = Term::free("r", rty_set.clone());
    let big_w = Term::free("w", wty.clone());
    let den_body = mem(alpha, &big_w, &denote(alpha, big_r.clone())?); // mem w ⟦r⟧
    let inner = Term::abs(wty.clone(), covalence_core::subst::close(&den_body, "w"));
    let d_pred = Term::abs(rty_set.clone(), covalence_core::subst::close(&inner, "r"));

    // The regex / word at the denotation instance.
    let r_set = inst_r(alpha, r);
    let matches_set = inst_r(alpha, &matches(alpha, r, w)?);

    // ⊢ Matches r w ⟹ (Closed D ⟹ D r w)   (all_elim D on the ∀M).
    let assumed = Thm::assume(matches_set.clone())?; // {Matches r w} ⊢ Matches r w
    let specialized = assumed.all_elim(d_pred.clone())?; // {…} ⊢ Closed D ⟹ D r w

    // Discharge `Closed D`.
    let closed_d = discharge_closed(alpha, &d_pred)?; // ⊢ Closed D
    let d_rw = specialized.imp_elim(closed_d)?; // {Matches r w} ⊢ D r w

    // D r w → β → mem w ⟦r⟧.
    let d_app = d_pred.clone().apply(r_set.clone())?.apply(w.clone())?;
    let to_mem = crate::init::eq::beta_nf(d_app); // ⊢ D r w = mem w ⟦r⟧
    let d_rw_beta = to_mem.eq_mp(d_rw)?; // {Matches r w} ⊢ mem w ⟦r⟧
    d_rw_beta.imp_intro(&matches_set)
}

/// Prove `⊢ Closed D` where `D = λr w. mem w ⟦r⟧`, clause by clause, in the
/// same order as [`closed`].
fn discharge_closed(alpha: &Type, d_pred: &Term) -> Result<Thm> {
    let m = list_cat_monoid(alpha.clone());
    // All regexes here live at the denotation instance `'r := set (list a)`
    // (so `d_pred : regex⟨a, set(list a)⟩ → … ` applies cleanly).
    let rset = lang_ty(alpha);
    // β-bridge: ⊢ D r w = mem w ⟦r⟧.
    let d_eq_mem = |rr: &Term, ww: &Term| -> Result<Thm> {
        let app = d_pred.clone().apply(rr.clone())?.apply(ww.clone())?;
        Ok(crate::init::eq::beta_nf(app)) // ⊢ D r w = mem w ⟦r⟧
    };
    // Re-fold a `⊢ mem w ⟦r⟧` proof to `⊢ D r w`.
    let to_d = |rr: &Term, ww: &Term, pf: Thm| -> Result<Thm> {
        d_eq_mem(rr, ww)?.sym()?.eq_mp(pf)
    };

    let mut clause_thms: Vec<Thm> = Vec::new();

    // 1. eps: D eps nil. ⟦eps⟧ = ε, mem nil ε = (nil = nil) = T.
    {
        let eps = r_eps_at(alpha, &rset);
        let nil = nil_w(alpha);
        let mem_eps = lang::mem_epsilon(&m, &nil)?; // ⊢ mem nil ε = (nil = unit)
        // ⟦eps⟧ = ε definitionally (denote folds h_eps = epsilon); but we
        // must connect `mem nil ⟦eps⟧` to `mem nil ε`. denote(eps) β-reduces
        // to ε, so `mem nil ⟦eps⟧` and `mem nil ε` are the SAME term.
        let mem_eps2 = rewrite_mem_to_denote(alpha, &m, &eps, &nil, mem_eps)?;
        clause_thms.push(to_d(&eps, &nil, mem_eps2)?);
    }

    // 2. lit: ∀c. D (lit c) [c]. ⟦lit c⟧ = {[c]}, mem [c] {[c]} = ([c]=[c]) = T.
    {
        let c = Term::free("c", alpha.clone());
        let lit = r_lit_at(alpha, &rset, c.clone());
        let word = singleton_w(alpha, &c)?;
        let mem_sing = crate::init::set::mem_singleton(&word_ty(alpha), &word, &word)?; // ⊢ mem [c] {[c]} = ([c]=[c])
        let proof = rewrite_mem_singleton_to_denote(alpha, &m, &lit, &word, mem_sing)?;
        clause_thms.push(to_d(&lit, &word, proof)?.all_intro("c", alpha.clone())?);
    }

    // 3. alt-left: ∀x y w. D x w ⟹ D (alt x y) w.
    clause_thms.push(discharge_alt(alpha, &m, d_pred, true)?);
    // 4. alt-right.
    clause_thms.push(discharge_alt(alpha, &m, d_pred, false)?);
    // 5. seq.
    clause_thms.push(discharge_seq(alpha, &m, d_pred)?);
    // 6. star-nil.
    clause_thms.push(discharge_star_nil(alpha, &m, d_pred)?);
    // 7. star-step.
    clause_thms.push(discharge_star_step(alpha, &m, d_pred)?);

    // Conjoin right-nested, matching `closed`.
    let mut iter = clause_thms.into_iter().rev();
    let mut acc = iter.next().expect("clauses");
    for cl in iter {
        acc = cl.and_intro(acc)?;
    }
    Ok(acc)
}

// -- per-clause discharge helpers (defined below; see soundness §) ------------

include!("regex_soundness.rs");

// ============================================================================
// Bytestring specialization.
// ============================================================================

/// The byte alphabet `u8` — regexes over `u8` match `bytes` / `list u8`.
pub fn u8_alphabet() -> Type {
    covalence_core::defs::u8_ty()
}

// ============================================================================
// DESIGN NOTE — the path to ambiguity + sexpr lift/lower (the next stage)
// ============================================================================
//
// This module gives the *recognition* semantics (a word matches a regex iff it
// is in the denoted language). Two follow-ons, deferred to `SKELETONS.md`:
//
// ## Ambiguity (multiple derivations of one match)
//
// `Matches r w` is a *propositional* judgement: it records only *that* `w`
// matches, not *how*. Ambiguity ("how many ways?") needs a **proof-relevant**
// counterpart `Parse r w : type`, the type of *parse trees* for `w` against
// `r` — the categorification of `Matches` (replace `bool` by a `type`/`set`
// of derivations, `∨`→coproduct, `seq`→split-indexed product, `star`→list of
// sub-parses). Concretely, reify a `ParseTree 'a` datatype (the same Church
// recipe: `pt_eps | pt_lit | pt_inl | pt_inr | pt_seq | pt_star_nil |
// pt_star_cons`) and a *yield* function `yield : ParseTree → list 'a`;
// `Matches r w ⟺ ∃ t. wf r t ∧ yield t = w`, and **`r` is ambiguous at `w`
// iff two distinct well-formed trees share that yield**. The impredicative
// `Matches` here is exactly the propositional truncation `∃t. …` of that
// proof-relevant `Parse`, so it is the right substrate to build on (no rework:
// add `Parse`/`yield` alongside, prove the truncation theorem). The
// `seq`-split and `star`-iteration are where ambiguity is born — they are
// already the two rules whose *witnesses* (the `cat`-split `w = w₁·w₂` and the
// star unfolding) are non-unique, so the parse-tree layer just stops
// projecting them away.
//
// ## Lift / lower from sexprs (`init::sexpr`, defined concurrently)
//
// `init::sexpr` reifies the universal syntax carrier `SExpr` (atom/snil/scons,
// same Church encoding). A surface regex is most naturally *written* as an
// `SExpr` — e.g. `(seq (alt (lit a) (lit b)) (star (lit c)))` — so the bridge
// is a pair:
//
//   - **lower** `regex_of_sexpr : SExpr → option (regex 'a)` — a partial
//     parse of the `SExpr` grammar into a `regex` value (fails on
//     ill-formed input; this is the *untrusted driver*, like the SpecTec
//     lowering — it produces a kernel `regex` term the kernel re-checks);
//   - **lift** `sexpr_of_regex : regex 'a → SExpr` — the total round-trip
//     printer (a `regex`-fold into the `scons`/`atom` carrier), giving the
//     coherence `lower ∘ lift = some` (a provable theorem once `SExpr`
//     recursion lands).
//
// We deliberately **do not depend on `init::sexpr` yet** (it is in flight): the
// `regex` datatype here is self-contained (alphabet-polymorphic Church
// encoding), and the `SExpr` bridge attaches on top without touching this
// module — `regex_of_sexpr` consumes `SExpr` and emits the `r_*` constructors,
// `sexpr_of_regex` is a `denote`-shaped fold into `atom`/`scons`. The interface
// is: atoms carry the `lit` payload (`bytes`-encoded), and the head atom of
// each `scons` spine names the constructor (`empty`/`eps`/`lit`/`alt`/`seq`/
// `star`). That is the same convention `prop`/`sexpr` already use, so the two
// reified object logics share one carrier.

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> Type {
        aty()
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "expected a hypothesis-free theorem");
        assert!(thm.has_no_obs(), "expected an oracle-free theorem");
    }

    #[test]
    fn constructors_are_distinct_and_typed() {
        let a = alpha();
        let c = Term::free("c", a.clone());
        let ty = regex(a.clone());
        assert_eq!(r_empty(&a).type_of().unwrap(), ty);
        assert_eq!(r_eps(&a).type_of().unwrap(), ty);
        assert_eq!(r_lit(&a, c.clone()).type_of().unwrap(), ty);
        assert_eq!(r_alt(&a, r_eps(&a), r_empty(&a)).type_of().unwrap(), ty);
        assert_eq!(r_seq(&a, r_eps(&a), r_empty(&a)).type_of().unwrap(), ty);
        assert_eq!(r_star(&a, r_eps(&a)).type_of().unwrap(), ty);
        // Distinct syntax: empty ≠ eps ≠ (eps | empty) ≠ (eps eps) ≠ eps*.
        assert_ne!(r_empty(&a), r_eps(&a));
        assert_ne!(r_eps(&a), r_alt(&a, r_eps(&a), r_empty(&a)));
        assert_ne!(
            r_alt(&a, r_eps(&a), r_empty(&a)),
            r_seq(&a, r_eps(&a), r_empty(&a))
        );
        assert_ne!(r_star(&a, r_eps(&a)), r_eps(&a));
    }

    #[test]
    fn denote_is_well_typed() {
        let a = alpha();
        let c = Term::free("c", a.clone());
        for r in [
            r_empty(&a),
            r_eps(&a),
            r_lit(&a, c.clone()),
            r_alt(&a, r_eps(&a), r_lit(&a, c.clone())),
            r_seq(&a, r_lit(&a, c.clone()), r_eps(&a)),
            r_star(&a, r_lit(&a, c.clone())),
        ] {
            let den = denote(&a, r).unwrap();
            assert_eq!(den.type_of().unwrap(), lang_ty(&a));
        }
    }

    #[test]
    fn match_rules_are_genuine() {
        let a = alpha();
        let x = Term::free("x", regex(a.clone()));
        let y = Term::free("y", regex(a.clone()));
        let w = Term::free("w", word_ty(&a));
        let w1 = Term::free("w1", word_ty(&a));
        let w2 = Term::free("w2", word_ty(&a));
        for thm in [
            match_eps(&a).unwrap(),
            match_lit(&a).unwrap(),
            match_alt_l(&a, &x, &y, &w).unwrap(),
            match_alt_r(&a, &x, &y, &w).unwrap(),
            match_seq(&a, &x, &y, &w1, &w2).unwrap(),
            match_star_nil(&a, &x).unwrap(),
            match_star_step(&a, &x, &w1, &w2).unwrap(),
        ] {
            assert_genuine(&thm);
        }
    }

    #[test]
    fn match_eps_has_expected_shape() {
        let a = alpha();
        let thm = match_eps(&a).unwrap();
        assert_eq!(thm.concl(), &matches(&a, &r_eps(&a), &nil_w(&a)).unwrap());
    }

    #[test]
    fn soundness_is_genuine() {
        let a = alpha();
        let thm = soundness(&a).unwrap();
        assert_genuine(&thm);
        // Conclusion is `Matches r w ⟹ mem w ⟦r⟧`, at the denotation instance
        // `'r := set (list a)`. Build at the polymorphic `'r`, then instantiate
        // (exactly as `soundness_at` does).
        let r = Term::free("r", regex(a.clone()));
        let w = Term::free("w", word_ty(&a));
        let r_set = inst_r(&a, &r);
        let expected = inst_r(&a, &matches(&a, &r, &w).unwrap())
            .imp(mem(&a, &w, &denote(&a, r_set).unwrap()))
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn pipeline_eps_matches_and_is_sound() {
        // Build a derivation `⊢ Matches eps nil`, then chain soundness to get
        // `⊢ mem nil ⟦eps⟧`. Soundness lives at `'r := set (list a)`, so
        // instantiate the (polymorphic) derivation there first.
        let a = alpha();
        let der = match_eps(&a)
            .unwrap()
            .inst_tfree("r", lang_ty(&a))
            .unwrap();
        let snd = soundness_at(&a, &r_eps(&a), &nil_w(&a)).unwrap();
        let mem_thm = snd.imp_elim(der).unwrap(); // ⊢ mem nil ⟦eps⟧
        assert_genuine(&mem_thm);
    }

    #[test]
    fn bytestring_alphabet_regex() {
        // A bytestring regex: `(0x61 | 0x62) 0x63*` over u8 — matches an 'a' or
        // 'b' followed by any number of 'c's. Just exercise the builders +
        // denotation typecheck at the byte alphabet.
        let a = u8_alphabet();
        let byte = |k: u8| Term::u8_lit(k);
        let re = r_seq(
            &a,
            r_alt(&a, r_lit(&a, byte(0x61)), r_lit(&a, byte(0x62))),
            r_star(&a, r_lit(&a, byte(0x63))),
        );
        assert_eq!(re.type_of().unwrap(), regex(a.clone()));
        let den = denote(&a, re).unwrap();
        assert_eq!(den.type_of().unwrap(), lang_ty(&a));
        // Soundness specialises to the byte alphabet.
        let snd = soundness(&a).unwrap();
        assert_genuine(&snd);
    }

    #[test]
    fn bytestring_worked_derivation() {
        // A worked example at the byte alphabet: derive `⊢ Matches (lit 0x61)
        // [0x61]` (the byte 'a' matches the literal regex 'a'), then chain
        // soundness to obtain `⊢ mem [0x61] ⟦lit 0x61⟧` — a genuine membership
        // fact about the byte-string language the regex denotes.
        let a = u8_alphabet();
        let byte_a = Term::u8_lit(0x61);
        let lit_a = r_lit(&a, byte_a.clone());
        let word = singleton_w(&a, &byte_a).unwrap(); // [0x61] : list u8

        // ⊢ ∀c. Matches (lit c) [c], specialised at c := 0x61.
        let der = match_lit(&a)
            .unwrap()
            .all_elim(byte_a.clone())
            .unwrap()
            .inst_tfree("r", lang_ty(&a))
            .unwrap();
        assert_genuine(&der);

        // soundness ∘ derivation: ⊢ mem [0x61] ⟦lit 0x61⟧.
        let snd = soundness_at(&a, &lit_a, &word).unwrap();
        let mem_thm = snd.imp_elim(der).unwrap();
        assert_genuine(&mem_thm);
    }
}
