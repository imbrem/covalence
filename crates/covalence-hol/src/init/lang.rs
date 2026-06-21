//! `lang` — **formal languages over a monoid**, the first step toward the
//! temporal/modal logics (LTL/CTL/CTL*).
//!
//! A *language* over a monoid `M = (μ, op, unit)` is a **set of words** — a
//! value of type `set μ`, i.e. a subset of `M`'s carrier. Concatenation of
//! languages lifts `M`'s operation pointwise; together with union and the
//! Kleene star this is the algebraic backbone of regular expressions, a
//! **Kleene algebra**.
//!
//! This module is *generic in the monoid model*, exactly like
//! [`crate::init::monoid`]: every operation and law is parameterised by a
//! [`Monoid`] value carrying the model's `op`/`unit` and the three law
//! theorems. Swap the model — `(nat,+,0)`, `(list,append,nil)`,
//! `(α→α,∘,id)` — and the *same* definitions and proofs become facts about
//! a different alphabet's words.
//!
//! # Representation
//!
//! A language is a `set μ`. Building on [`crate::init::set`], the operations
//! are:
//!
//! ```text
//!   empty_lang        := ∅                                    (set.empty)
//!   epsilon           := { unit }                             (set.singleton unit)
//!   lang_union L₁ L₂  := L₁ ∪ L₂                              (set.union)
//!   lang_concat L₁ L₂ := { w | ∃x y. x∈L₁ ∧ y∈L₂ ∧ w = op x y }
//!   lang_star L       := smallest L* with ε ⊆ L* and L·L* ⊆ L*
//! ```
//!
//! Concatenation and star are *new* predicate-built sets (`set.mk …`); the
//! rest are re-exported `set` operators. Every membership computation
//! bottoms out in [`crate::init::set::mem_mk`] — the kernel's witness-free
//! subtype round-trip — so nothing here is postulated.
//!
//! # What is proved (genuine, hypothesis- and oracle-free)
//!
//! - [`mem_concat`] — `mem w (L₁·L₂) = ∃x y. mem x L₁ ∧ mem y L₂ ∧ w = op x y`,
//!   the defining membership computation;
//! - [`mem_epsilon`] — `mem w ε = (w = unit)`;
//! - the **union** Kleene-algebra fragment (`lang_union` is `set.union`, so
//!   commutativity / associativity / idempotence / `∅`-identity are the set
//!   theorems re-exported: [`union_comm`], [`union_assoc`], [`union_idem`],
//!   [`union_empty`]);
//! - [`concat_empty_l`] / [`concat_empty_r`] — `∅·L = ∅`, `L·∅ = ∅`
//!   (the empty language annihilates concatenation), proved with the new
//!   generic existential tactics ([`logic::exists_false`] /
//!   [`logic::exists_cong`](crate::init::logic::exists_cong));
//! - [`mem_star`] — `mem w L* = ∀S. Closed L S ⟹ mem w S`, the star's
//!   defining membership; and [`star_contains_epsilon`] — `ε ⊆ L*` (one
//!   half of the star unfolding's closure direction).
//!
//! # What is deferred (see `SKELETONS.md`)
//!
//! - **`concat_assoc`** and the **`epsilon` concat identities** (`ε·L = L`,
//!   `L·ε = L`) at the term level. The *one-point* existential rule
//!   `⊢ (∃x. x = t ∧ P x) = P t` is now available
//!   ([`logic::exists_one_point`](crate::init::logic::exists_one_point)); what
//!   remains is reshaping the concat membership formula
//!   `∃x ∃y. (x=unit ∧ mem y L) ∧ w=op x y` into the one-point shape and
//!   applying the monoid `left_id` / `right_id` / `assoc` under the surviving
//!   `∃`. The body-rewriter
//!   [`logic::exists_cong`](crate::init::logic::exists_cong) is the seed.
//! - **`concat` over `union` distribution** at the term level (same ∃-pushing
//!   gap; the membership identity is a propositional tautology over the atoms
//!   once concat membership is unfolded).
//! - The **full star unfolding** `L* = ε ∪ L·L*` and the **least-fixpoint
//!   half** (`L* ⊆ S` for any `S` closed under ε and `L·`): induction over the
//!   impredicative star — `star_contains_epsilon` proves the `ε ⊆ L*` part of
//!   the closure direction; the rest awaits the existential one-point rule and
//!   the concat-closure lemma.

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::monoid::Monoid;
use crate::init::set::{
    mem_mk, set, set_empty, set_mem, set_mk, set_singleton, set_subset, set_union,
};

// ============================================================================
// The monoid carrier and small builders.
// ============================================================================

/// `set μ` — the type of a language over a monoid whose carrier is `mu`.
pub fn lang(mu: Type) -> Type {
    set(mu)
}

/// `set.mem[μ] w L : bool` — word membership in a language.
fn mem(mu: &Type, w: &Term, l: &Term) -> Term {
    Term::app(Term::app(set_mem(mu.clone()), w.clone()), l.clone())
}

/// `set.union[μ] L₁ L₂ : set μ`.
fn union(mu: &Type, a: &Term, b: &Term) -> Term {
    Term::app(Term::app(set_union(mu.clone()), a.clone()), b.clone())
}

/// The carrier type `μ` of a monoid, read off its `unit` term.
fn carrier(m: &Monoid) -> Result<Type> {
    m.unit().type_of()
}

// ============================================================================
// Operations.
// ============================================================================

/// `empty_lang : set μ` — the empty language `∅` (no words). The `∅` of the
/// underlying [`set`] theory.
pub fn empty_lang(m: &Monoid) -> Result<Term> {
    Ok(set_empty(carrier(m)?))
}

/// `epsilon : set μ` — the language `{ unit }` containing exactly the empty
/// word `unit`. The multiplicative identity of [`lang_concat`].
pub fn epsilon(m: &Monoid) -> Result<Term> {
    let mu = carrier(m)?;
    Ok(Term::app(set_singleton(mu), m.unit().clone()))
}

/// `lang_union L₁ L₂ : set μ` — set union of two languages. Plain
/// [`set::set_union`](crate::init::set::set_union).
pub fn lang_union(m: &Monoid, a: &Term, b: &Term) -> Result<Term> {
    Ok(union(&carrier(m)?, a, b))
}

/// `lang_concat L₁ L₂ : set μ` — the concatenation
/// `{ w | ∃x y. x∈L₁ ∧ y∈L₂ ∧ w = op x y }`: every word obtained by
/// concatenating a word of `L₁` with a word of `L₂` under the monoid `op`.
///
/// Built as `set.mk (λw. ∃x. ∃y. mem x L₁ ∧ mem y L₂ ∧ w = op x y)`.
pub fn lang_concat(m: &Monoid, a: &Term, b: &Term) -> Result<Term> {
    let mu = carrier(m)?;
    let pred = concat_pred(m, a, b)?;
    Ok(Term::app(set_mk(mu), pred))
}

/// `λw. ∃x. ∃y. mem x a ∧ mem y b ∧ w = op x y` — the membership predicate
/// of `lang_concat a b`, abstracted in the word `w`.
fn concat_pred(m: &Monoid, a: &Term, b: &Term) -> Result<Term> {
    let mu = carrier(m)?;
    let w = Term::free("_lc_w", mu.clone());
    let body = concat_body(m, &w, a, b)?;
    Ok(Term::abs(
        mu.clone(),
        covalence_core::subst::close(&body, "_lc_w"),
    ))
}

/// `∃x. ∃y. mem x a ∧ mem y b ∧ w = op x y` — the membership *formula* for a
/// concrete word `w` (open in `w`, the existentials over fresh `x`, `y`).
fn concat_body(m: &Monoid, w: &Term, a: &Term, b: &Term) -> Result<Term> {
    let mu = carrier(m)?;
    let x = Term::free("_lc_x", mu.clone());
    let y = Term::free("_lc_y", mu.clone());
    let op_xy = m.op().clone().apply(x.clone())?.apply(y.clone())?;
    let conj = mem(&mu, &x, a)
        .and(mem(&mu, &y, b))?
        .and(w.clone().equals(op_xy)?)?;
    conj.exists("_lc_y", mu.clone())?.exists("_lc_x", mu)
}

// ============================================================================
// Membership computations — the genuine computational surface.
// ============================================================================

/// `⊢ set.mem w (lang_concat a b) = (∃x y. mem x a ∧ mem y b ∧ w = op x y)`.
///
/// The defining membership computation of concatenation, proved by pushing
/// membership through `set.mk` with [`mem_mk`] and β-reducing the predicate
/// — exactly the `init::set` `mem_*` recipe, here over the concat predicate.
pub fn mem_concat(m: &Monoid, w: &Term, a: &Term, b: &Term) -> Result<Thm> {
    let mu = carrier(m)?;
    let pred = concat_pred(m, a, b)?;
    // mem w (set.mk pred) = pred w  (mem_mk), then pred w →β the ∃-formula.
    let lhs = mem_mk(&mu, w, &pred)?; // ⊢ mem w (mk pred) = pred w
    let reduced = rhs_of(&lhs)?.reduce()?; // ⊢ pred w = body[w]
    lhs.trans(reduced)
}

/// `⊢ set.mem w epsilon = (w = unit)` — a word is in `ε` iff it is the empty
/// word. `epsilon = set.singleton unit`, so this is `set`'s
/// [`mem_singleton`](crate::init::set::mem_singleton) at `unit`.
pub fn mem_epsilon(m: &Monoid, w: &Term) -> Result<Thm> {
    let mu = carrier(m)?;
    crate::init::set::mem_singleton(&mu, w, m.unit())
}

/// `⊢ set.mem w empty_lang = F` — no word is in `∅`. `set`'s
/// [`mem_empty`](crate::init::set::mem_empty).
pub fn mem_empty_lang(m: &Monoid, w: &Term) -> Result<Thm> {
    let mu = carrier(m)?;
    crate::init::set::mem_empty(&mu, w)
}

// ============================================================================
// Union Kleene-algebra fragment — re-exported `set` theorems.
//
// `lang_union` *is* `set.union`, so the additive commutative-idempotent
// monoid `(∪, ∅)` laws are exactly the set-algebra theorems, restated for
// the language reading.
// ============================================================================

/// `⊢ (L₁ ∪ L₂) ∪ L₃ = L₁ ∪ (L₂ ∪ L₃)` — union of languages is associative.
pub use crate::init::set::union_assoc;
/// `⊢ L₁ ∪ L₂ = L₂ ∪ L₁` — union of languages is commutative.
pub use crate::init::set::union_comm;
/// `⊢ L ∪ ∅ = L` — the empty language is a unit for union.
pub use crate::init::set::union_empty;
/// `⊢ L ∪ L = L` — union of languages is idempotent.
pub use crate::init::set::union_idem;

// ============================================================================
// Concatenation annihilation by ∅ — genuine via membership extensionality.
// ============================================================================

/// `⊢ lang_concat empty_lang L = empty_lang` — `∅ · L = ∅`: the empty
/// language left-annihilates concatenation. A word in `∅·L` needs a word
/// `x ∈ ∅`, impossible, so the membership formula is unsatisfiable (`F`).
pub fn concat_empty_l(m: &Monoid, l: &Term) -> Result<Thm> {
    let empty = empty_lang(m)?;
    annihilate(m, &lang_concat(m, &empty, l)?, &empty, |w| {
        // mem w (∅·L) = ∃x y. mem x ∅ ∧ … ; the left conjunct is F.
        let unfold = mem_concat(m, w, &empty, l)?; // ⊢ mem w (∅·L) = ∃x y. …
        // The ∃-formula is false: any witness `x` gives `mem x ∅ = F`.
        let ex_false = concat_exists_false(m, w, &empty, l, ConjSlot::Left)?; // ⊢ (∃…) = F
        unfold.trans(ex_false)
    })
}

/// `⊢ lang_concat L empty_lang = empty_lang` — `L · ∅ = ∅`: the empty
/// language right-annihilates concatenation. Symmetric to [`concat_empty_l`]
/// — the `mem y ∅ = F` conjunct kills the membership formula.
pub fn concat_empty_r(m: &Monoid, l: &Term) -> Result<Thm> {
    let empty = empty_lang(m)?;
    annihilate(m, &lang_concat(m, l, &empty)?, &empty, |w| {
        let unfold = mem_concat(m, w, l, &empty)?;
        let ex_false = concat_exists_false(m, w, l, &empty, ConjSlot::RightMem)?;
        unfold.trans(ex_false)
    })
}

/// Which membership conjunct of the concat body is `∅`-driven (and so `F`).
#[derive(Clone, Copy)]
enum ConjSlot {
    /// `mem x a` (the first conjunct) is false — used for `∅ · L`.
    Left,
    /// `mem y b` (the left of the second conjunct) is false — for `L · ∅`.
    RightMem,
}

/// Prove `⊢ src = empty_lang` from a per-word proof that `mem w src = F`.
/// `mem w ∅ = F` too, so the memberships agree pointwise and [`set::ext`]
/// closes.
fn annihilate(
    m: &Monoid,
    src: &Term,
    empty: &Term,
    mem_src_false: impl Fn(&Term) -> Result<Thm>,
) -> Result<Thm> {
    let mu = carrier(m)?;
    let w = Term::free("_lc_w", mu.clone());
    let src_f = mem_src_false(&w)?; // ⊢ mem w src = F
    let empty_f = mem_empty_lang(m, &w)?; // ⊢ mem w ∅ = F
    let mem_eq = src_f.trans(empty_f.sym()?)?; // ⊢ mem w src = mem w ∅
    let all = mem_eq.all_intro("_lc_w", mu.clone())?;
    crate::init::set::ext(&mu, src, empty, all)
}

/// `⊢ (∃x y. mem x a ∧ mem y b ∧ w = op x y) = F` when one of `a`, `b` is
/// `∅` (so its membership conjunct is `F`). Built with the generic
/// existential tactics: prove the *inner* conjunction false everywhere
/// (`⊢ ∀y. conj = F`), lift through the inner `∃y` with
/// [`logic::exists_false`], abstract over `y`'s sibling, then lift through
/// the outer `∃x` the same way.
fn concat_exists_false(m: &Monoid, w: &Term, a: &Term, b: &Term, slot: ConjSlot) -> Result<Thm> {
    let mu = carrier(m)?;
    let x = Term::free("_lc_x", mu.clone());
    let y = Term::free("_lc_y", mu.clone());
    let op_xy = m.op().clone().apply(x.clone())?.apply(y.clone())?;
    // The inner conjunction `mem x a ∧ mem y b ∧ w = op x y` (open in x, y).
    let conj = mem(&mu, &x, a)
        .and(mem(&mu, &y, b))?
        .and(w.clone().equals(op_xy)?)?;

    // The `∅`-membership conjunct, rewritten to `F`, gives `{conj} ⊢ F`.
    let assume_conj = Thm::assume(conj.clone())?;
    // `conj` is left-associated: `(mem x a ∧ mem y b) ∧ (w = op x y)`.
    let to_f = match slot {
        ConjSlot::Left => {
            let mem_false = crate::init::set::mem_empty(&mu, &x)?; // ⊢ mem x ∅ = F
            mem_false.eq_mp(assume_conj.and_elim_l()?.and_elim_l()?)? // {conj} ⊢ F
        }
        ConjSlot::RightMem => {
            let mem_false = crate::init::set::mem_empty(&mu, &y)?; // ⊢ mem y ∅ = F
            mem_false.eq_mp(assume_conj.and_elim_l()?.and_elim_r()?)? // {conj} ⊢ F
        }
    };
    // `⊢ conj = F` (by deductive antisymmetry against ex falso).
    let conj_eq_f = false_eq_of(&conj, to_f)?;

    // Inner ∃y: `⊢ ∀y. conj = F`  →  `⊢ (∃y. conj) = F`.
    let inner_all = conj_eq_f.all_intro("_lc_y", mu.clone())?;
    let inner = crate::init::logic::exists_false(&mu, inner_all)?; // ⊢ (∃y. conj) = F

    // Outer ∃x: `⊢ ∀x. (∃y. conj) = F`  →  `⊢ (∃x ∃y. conj) = F`.
    let outer_all = inner.all_intro("_lc_x", mu.clone())?;
    crate::init::logic::exists_false(&mu, outer_all)
}

/// `⊢ p = F` from `⊢ F ⟹ p`-free input: given `pf : Γ ⊢ F` under the single
/// hypothesis `p` (i.e. `pf : {p} ⊢ F`), and that `F ⟹ p` by ex falso,
/// deductive antisymmetry yields `⊢ p = F`.
fn false_eq_of(p: &Term, pf_p_to_false: Thm) -> Result<Thm> {
    let false_t = Term::bool_lit(false);
    // {F} ⊢ p  (ex falso).
    let from_false = Thm::assume(false_t.clone())?.false_elim(p.clone())?;
    // `{F}⊢p` & `{p}⊢F`  ⟹  `⊢ p = F`.
    from_false.deduct_antisym(pf_p_to_false)
}

// ============================================================================
// Kleene star — the impredicative least fixpoint.
// ============================================================================
//
// `L*` is the *smallest* language `S` that contains `ε` and is closed under
// `concat L` (`L · S ⊆ S`). We encode "smallest such" impredicatively,
// exactly as `init::prop` encodes `Derivable_Prop` — no new type definition,
// no recursor:
//
//   lang_star L := { w | ∀S. (ε ⊆ S ∧ L·S ⊆ S) ⟹ w ∈ S }
//
// so `mem w L*` unfolds to `∀S. Closed L S ⟹ mem w S`, where
// `Closed L S := subset ε S ∧ subset (L·S) S`. Two consequences are then
// pure HOL:
//
//   - `ε ⊆ L*`            (every closed `S` contains `ε`, so does the ∩)
//   - `L · L* ⊆ L*`       (L* is itself closed — the fixpoint is a *pre*-fixpoint)
//
// giving the **closure direction** `ε ∪ L·L* ⊆ L*` of the unfolding. The
// reverse `L* ⊆ ε ∪ L·L*` is the genuine least-fixpoint / induction half —
// deferred (see `SKELETONS.md`).

/// `subset[μ] s t : bool`.
fn subset(mu: &Type, s: &Term, t: &Term) -> Term {
    Term::app(Term::app(set_subset(mu.clone()), s.clone()), t.clone())
}

/// `Closed L S := subset ε S ∧ subset (L · S) S` — the closure predicate on a
/// candidate language `S`: it contains `ε` and is closed under left
/// concatenation by `L`.
fn closed_pred(m: &Monoid, l: &Term, s: &Term) -> Result<Term> {
    let mu = carrier(m)?;
    let eps = epsilon(m)?;
    let l_s = lang_concat(m, l, s)?;
    subset(&mu, &eps, s).and(subset(&mu, &l_s, s))
}

/// `λw. ∀S. Closed L S ⟹ mem w S` — the membership predicate of
/// `lang_star L`, abstracted in the word `w`.
fn star_pred(m: &Monoid, l: &Term) -> Result<Term> {
    let mu = carrier(m)?;
    let s = Term::free("_ls_S", lang(mu.clone()));
    let w = Term::free("_ls_w", mu.clone());
    let body = closed_pred(m, l, &s)?
        .imp(mem(&mu, &w, &s))?
        .forall("_ls_S", lang(mu.clone()))?;
    Ok(Term::abs(
        mu.clone(),
        covalence_core::subst::close(&body, "_ls_w"),
    ))
}

/// `lang_star L : set μ` — the Kleene closure
/// `{ w | ∀S. Closed L S ⟹ mem w S }`, the smallest language containing `ε`
/// and closed under `concat L`.
pub fn lang_star(m: &Monoid, l: &Term) -> Result<Term> {
    let mu = carrier(m)?;
    Ok(Term::app(set_mk(mu), star_pred(m, l)?))
}

/// `⊢ set.mem w (lang_star L) = (∀S. Closed L S ⟹ mem w S)` — the defining
/// membership computation of the Kleene star. Same `mem_mk` + β recipe as
/// [`mem_concat`].
pub fn mem_star(m: &Monoid, w: &Term, l: &Term) -> Result<Thm> {
    let mu = carrier(m)?;
    let pred = star_pred(m, l)?;
    let lhs = mem_mk(&mu, w, &pred)?; // ⊢ mem w (mk pred) = pred w
    let reduced = rhs_of(&lhs)?.reduce()?; // ⊢ pred w = body[w]
    lhs.trans(reduced)
}

/// `⊢ subset epsilon (lang_star L)` — `ε ⊆ L*`: the empty word is in the
/// Kleene star. Genuine. The membership of any `w ∈ ε` in `L*` follows
/// because every closed `S` contains `ε` (the first conjunct of `Closed`),
/// so `w ∈ ε ⊆ S`.
pub fn star_contains_epsilon(m: &Monoid, l: &Term) -> Result<Thm> {
    let mu = carrier(m)?;
    let eps = epsilon(m)?;
    let star = lang_star(m, l)?;
    let v = Term::free("_se_w", mu.clone());

    // Goal per point: mem v ε ⟹ mem v L*.
    let mem_v_eps = mem(&mu, &v, &eps);
    let assume_eps = Thm::assume(mem_v_eps.clone())?; // {mem v ε} ⊢ mem v ε

    // mem v L* = ∀S. Closed L S ⟹ mem v S ; we prove the rhs then refold.
    // `mem_star` and `closed_pred`/`mem` here build the body the same way,
    // so the canonical forall matches structurally.
    let star_unfold = mem_star(m, &v, l)?; // ⊢ mem v L* = (∀S. Closed L S ⟹ mem v S)

    // Fix a closed `S`, assume `Closed L S`, derive `mem v S` from `mem v ε`
    // and `ε ⊆ S`.
    let s = Term::free("_se_S", lang(mu.clone()));
    let closed_s = closed_pred(m, l, &s)?;
    let assume_closed = Thm::assume(closed_s.clone())?; // {Closed L S} ⊢ Closed L S
    let eps_sub_s = assume_closed.and_elim_l()?; // {Closed L S} ⊢ ε ⊆ S
    // ε ⊆ S gives mem v ε ⟹ mem v S; apply to mem v ε.
    let imp_v = crate::init::set::subset_elim(&mu, &eps, &s, eps_sub_s)?.all_elim(v.clone())?;
    let mem_v_s = imp_v.imp_elim(assume_eps.clone())?; // {mem v ε, Closed L S} ⊢ mem v S
    let body = mem_v_s
        .imp_intro(&closed_s)? // {mem v ε} ⊢ Closed L S ⟹ mem v S
        .all_intro("_se_S", lang(mu.clone()))?; // {mem v ε} ⊢ ∀S. …
    // Refold to `mem v L*`.
    let mem_v_star = star_unfold.sym()?.eq_mp(body)?; // {mem v ε} ⊢ mem v L*
    let pointwise = mem_v_star
        .imp_intro(&mem_v_eps)?
        .all_intro("_se_w", mu.clone())?;
    crate::init::set::subset_intro(&mu, &eps, &star, pointwise)
}

/// `⊢ subset (lang_concat L (lang_star L)) (lang_star L)` —
/// `L · L* ⊆ L*`: the Kleene star is a **pre-fixpoint** of `λX. ε ∪ L·X`,
/// i.e. it is closed under one more `L`-step. Genuine (hypothesis- and
/// oracle-free). This is the second half of the *closure direction* of the
/// star unfolding (the first being [`star_contains_epsilon`]); the reverse
/// least-fixpoint half stays deferred (see `SKELETONS.md`).
///
/// **Proof.** Pointwise: assume `w ∈ L·L*`. By [`mem_concat`] this is
/// `∃x y. x∈L ∧ y∈L* ∧ w = op x y`. Fix an arbitrary closed `S`
/// (`ε ⊆ S ∧ L·S ⊆ S`). Then `y∈L*` gives `y∈S` (the star membership
/// specialised at `S`), so `x∈L ∧ y∈S` re-packs (by `mem_concat` reversed)
/// to `op x y ∈ L·S`, and `L·S ⊆ S` yields `op x y = w ∈ S`. As `S` was an
/// arbitrary closed language, `w ∈ L*`.
pub fn star_concat_closed(m: &Monoid, l: &Term) -> Result<Thm> {
    let mu = carrier(m)?;
    let star = lang_star(m, l)?;
    let concat = lang_concat(m, l, &star)?;
    let w = Term::free("_sc_w", mu.clone());

    // mem w (L·L*) = ∃x y. mem x L ∧ mem y L* ∧ w = op x y.
    let unfold = mem_concat(m, &w, l, &star)?;
    let assume_mem = Thm::assume(mem(&mu, &w, &concat))?; // {mem w (L·L*)} ⊢ mem w (L·L*)
    let ex = unfold.eq_mp(assume_mem)?; // {…} ⊢ ∃x y. …

    // Goal of the ∃-elims: `mem w L*`.
    let goal = mem(&mu, &w, &star);

    // Inner step (over y): from `mem x L ∧ mem y L* ∧ w = op x y` conclude
    // `mem w L*`. We then ∃-elim y, abstract x, ∃-elim x. We use the SAME
    // builder `concat_body` that `mem_concat` unfolded to, so the `conj` term
    // and the predicates extracted from `ex` agree structurally (the bound
    // factor words are `_lc_x`, `_lc_y`).
    let x = Term::free("_lc_x", mu.clone());
    let y = Term::free("_lc_y", mu.clone());
    let op_xy = m.op().clone().apply(x.clone())?.apply(y.clone())?;
    let conj = mem(&mu, &x, l)
        .and(mem(&mu, &y, &star))?
        .and(w.clone().equals(op_xy.clone())?)?;
    let h = Thm::assume(conj.clone())?; // {conj} ⊢ conj
    let mem_x_l = h.clone().and_elim_l()?.and_elim_l()?; // {conj} ⊢ mem x L
    let mem_y_star = h.clone().and_elim_l()?.and_elim_r()?; // {conj} ⊢ mem y L*
    let w_eq = h.and_elim_r()?; // {conj} ⊢ w = op x y

    // Under an arbitrary closed `S`: derive `mem w S`.
    let s = Term::free("_sc_S", lang(mu.clone()));
    let closed_s = closed_pred(m, l, &s)?;
    let assume_closed = Thm::assume(closed_s.clone())?; // {Closed L S} ⊢ Closed L S
    let l_s_sub_s = assume_closed.clone().and_elim_r()?; // {…} ⊢ (L·S) ⊆ S

    // y ∈ L* and Closed L S ⟹ y ∈ S, via the star membership at S.
    let star_unfold = mem_star(m, &y, l)?; // ⊢ mem y L* = ∀S. Closed L S ⟹ mem y S
    let y_forall = star_unfold.eq_mp(mem_y_star)?; // {conj} ⊢ ∀S. Closed L S ⟹ mem y S
    let mem_y_s = y_forall
        .all_elim(s.clone())?
        .imp_elim(assume_closed.clone())?; // {conj, Closed L S} ⊢ mem y S

    // op x y ∈ L·S, by mem_concat reversed with witnesses x, y. We assemble
    // the existential body directly from `concat_body` (the very term
    // `mem_concat` unfolds to), then re-fold via the equation — so the
    // witnessed proof matches the canonical form the kernel built.
    let mem_opxy_ls = {
        let unfold_ls = mem_concat(m, &op_xy, l, &s)?; // ⊢ mem (op x y)(L·S) = ∃u ∃v. mem u L ∧ mem v S ∧ op x y = op u v
        // The canonical body `concat_body` produces, with `u,v` the *bound*
        // factor words (vars `_lc_x`, `_lc_y`) and the target word `op_xy`
        // FIXED on the equation's left. Witnessing `u := x`, `v := y` makes
        // the equation `op x y = op x y`, dischargeable by refl.
        // Bound-var placeholders `__u`,`__v` are deliberately DISTINCT from
        // the witness words `_sc_x`,`_sc_y` so that closing over them never
        // captures the fixed target word `op_xy = op _sc_x _sc_y` on the
        // equation's left.
        let uu = Term::free("__u", mu.clone());
        let vv = Term::free("__v", mu.clone());
        let body = |u: &Term, v: &Term| -> Result<Term> {
            let op_uv = m.op().clone().apply(u.clone())?.apply(v.clone())?;
            mem(&mu, u, l)
                .and(mem(&mu, v, &s))?
                .and(op_xy.clone().equals(op_uv)?)
        };
        // ⊢ body[x, y]  (the equation `op x y = op x y`, by refl).
        let at_xy = mem_x_l
            .clone()
            .and_intro(mem_y_s.clone())?
            .and_intro(Thm::refl(op_xy.clone())?)?; // {conj,Closed} ⊢ mem x L ∧ mem y S ∧ op x y = op x y

        // Inner ∃v: predicate `λv. body[x, v]` (bind `v = __v`, `x`/`op_xy` fixed).
        let inner_pred = Term::abs(
            mu.clone(),
            covalence_core::subst::close(&body(&x, &vv)?, "__v"),
        );
        let at_y = crate::init::eq::beta_expand(&inner_pred, y.clone(), at_xy)?; // ⊢ inner_pred y
        let inner_ex = crate::init::logic::exists_intro(inner_pred, y.clone(), at_y)?; // ⊢ ∃v. body[x, v]

        // Outer ∃u: predicate `λu. ∃v. body[u, v]` (bind `u = __u`).
        let outer_body = body(&uu, &vv)?.exists("__v", mu.clone())?; // ∃v. body[u, v]  (open in u = __u)
        let outer_pred = Term::abs(mu.clone(), covalence_core::subst::close(&outer_body, "__u"));
        let at_x = crate::init::eq::beta_expand(&outer_pred, x.clone(), inner_ex)?; // ⊢ outer_pred x
        let outer_ex = crate::init::logic::exists_intro(outer_pred, x.clone(), at_x)?; // ⊢ ∃u ∃v. …
        unfold_ls.sym()?.eq_mp(outer_ex)? // {conj,Closed} ⊢ mem (op x y)(L·S)
    };

    // (L·S) ⊆ S applied: op x y ∈ S.
    let mem_opxy_s = crate::init::set::subset_elim(&mu, &lang_concat(m, l, &s)?, &s, l_s_sub_s)?
        .all_elim(op_xy.clone())?
        .imp_elim(mem_opxy_ls)?; // {conj, Closed L S} ⊢ mem (op x y) S

    // mem w S from mem (op x y) S by rewriting `op x y → w` (w_eq reversed).
    let mem_w_s = mem_opxy_s.rewrite(&w_eq.clone().sym()?)?; // {conj, Closed L S} ⊢ mem w S

    // Discharge `Closed L S`, ∀-close S, fold to `mem w L*`.
    let body_star = mem_w_s
        .imp_intro(&closed_s)? // {conj} ⊢ Closed L S ⟹ mem w S
        .all_intro("_sc_S", lang(mu.clone()))?; // {conj} ⊢ ∀S. …
    let mem_w_star = mem_star(m, &w, l)?.sym()?.eq_mp(body_star)?; // {conj} ⊢ mem w L*

    // ∃-elim y then x. `exists_elim` wants its `step` antecedent in the
    // *applied* predicate form `pred y` (β-redex), not the reduced `conj`.
    // The inner predicate is `λy. conj` (binder `_lc_y`, mirroring
    // `concat_body`); the inner step is `∀y. (λy. conj) y ⟹ goal`. We get
    // there by assuming the applied form, β-reducing to `conj` to reuse the
    // proof, then re-`imp_intro` the *un-reduced* antecedent.
    let inner_pred = Term::abs(mu.clone(), covalence_core::subst::close(&conj, "_lc_y"));
    let inner_applied = Term::app(inner_pred.clone(), y.clone()); // (λy. conj) y
    let inner_step = {
        // `mem_w_star` has hyp `conj`; the step needs hyp `(λy. conj) y`.
        // Discharge `conj`, then re-supply it from the β-reduced applied hyp.
        mem_w_star
            .clone()
            .imp_intro(&conj)? // ⊢ conj ⟹ goal   (conj discharged)
            .imp_elim(crate::init::eq::beta_reduce(Thm::assume(
                inner_applied.clone(),
            )?)?)? // {(λy.conj) y} ⊢ goal
            .imp_intro(&inner_applied)? // ⊢ (λy. conj) y ⟹ goal
            .all_intro("_lc_y", mu.clone())? // ⊢ ∀y. (λy. conj) y ⟹ goal
    };
    // `∃y. conj` as a term — the body of the outer existential.
    let inner_ex_term = conj.clone().exists("_lc_y", mu.clone())?;

    // step_outer : ∀x. (∃y. conj) ⟹ goal — for a fixed x, ∃-elim `∃y. conj`.
    // The OUTER predicate is `λx. ∃y. conj`; its applied form is the
    // β-redex `(λx. ∃y. conj) x`.
    let outer_pred = Term::abs(
        mu.clone(),
        covalence_core::subst::close(&inner_ex_term, "_lc_x"),
    );
    let outer_applied = Term::app(outer_pred.clone(), x.clone()); // (λx. ∃y. conj) x
    let step_outer = {
        // For a fixed x: from `∃y. conj` get goal by the inner ∃-elim.
        let assume_inner = Thm::assume(inner_ex_term.clone())?; // {∃y. conj} ⊢ ∃y. conj
        let got = crate::init::logic::exists_elim(assume_inner, goal.clone(), inner_step)?; // {∃y. conj} ⊢ goal
        // Re-introduce in the applied form `(λx. ∃y. conj) x`.
        got.imp_intro(&inner_ex_term)? // ⊢ (∃y. conj) ⟹ goal
            .imp_elim(crate::init::eq::beta_reduce(Thm::assume(
                outer_applied.clone(),
            )?)?)? // {(λx.…) x} ⊢ goal
            .imp_intro(&outer_applied)? // ⊢ (λx. ∃y. conj) x ⟹ goal
            .all_intro("_lc_x", mu.clone())? // ⊢ ∀x. (λx. ∃y. conj) x ⟹ goal
    };
    let mem_w_star_final = crate::init::logic::exists_elim(ex, goal.clone(), step_outer)?; // {mem w (L·L*)} ⊢ mem w L*

    // pointwise ⟹, ∀-close, subset_intro.
    let pointwise = mem_w_star_final
        .imp_intro(&mem(&mu, &w, &concat))?
        .all_intro("_sc_w", mu.clone())?;
    crate::init::set::subset_intro(&mu, &concat, &star, pointwise)
}

// ============================================================================
// Small accessors.
// ============================================================================

/// Right-hand side of an equational theorem.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

// ============================================================================
// `langprim` env + the `lang.cov` port.
// ============================================================================

/// The `langprim` environment imported by `lang.cov`.
///
/// The union fragment of the language algebra is *monoid-agnostic* — union,
/// `∅`, membership, and `⊆` are plain `set` operations, schematic in one word
/// type `'a` — so those operators and seam lemmas are registered at the type
/// variable `'a` exactly like [`crate::init::set::set_env`]. This keeps the
/// union laws `lang.cov` proves identical (same conclusion, same `'a`) to the
/// Rust [`union_comm`] / … that `lang.rs` re-exports from `set`.
///
/// The model-specific layer (`lang.epsilon` = `{ unit }`, the empty word
/// `unit`, and the `mem_epsilon` membership equation `mem w ε = (w = unit)`)
/// is registered at the *concrete* model carrier `μ` from `m`, so a downstream
/// `.cov` that needs the unit-language facts can reach them. Swapping `m`
/// swaps that layer — the [`crate::init::monoid::monoid_env`] model-genericity
/// pattern, here for languages.
///
/// **Operators**
///
/// - `lang.empty`   — `∅`  (schematic `'a`)
/// - `lang.union`   — `∪`  (schematic `'a`)
/// - `set.mem`      — word membership  (schematic `'a`)
/// - `set.subset`   — language inclusion `⊆`  (schematic `'a`)
/// - `lang.epsilon` — `{ unit }`  (at the model carrier `μ`)
/// - `unit`         — the empty word  (at the model carrier `μ`)
///
/// `lang.concat` / `lang.star` are *not* operators (they are `set.mk`
/// predicate-built sets, not curried heads), so they are unbuilt-in `.cov`;
/// their facts stay Rust-proved givens above.
///
/// **Lemmas** (Rust-proved givens, universally quantified)
///
/// - `mem_empty`     : ∀x. mem x ∅ = F                          (`'a`)
/// - `mem_union`     : ∀x s t. mem x (s ∪ t) = (mem x s ∨ mem x t)  (`'a`)
/// - `ext`           : ∀s t. (∀x. mem x s = mem x t) ⟹ s = t    (`'a`)
/// - `subset_unfold` : ∀s t. (s ⊆ t) = (∀x. mem x s ⟹ mem x t)   (`'a`)
/// - `mem_epsilon`   : ∀w. mem w ε = (w = unit)                  (at `μ`)
pub fn lang_env(m: &Monoid) -> crate::script::Env {
    use crate::script::{ConstDef, Env};
    let a = Type::tfree("a");
    let sa = set(a.clone());
    let mut e = Env::empty();

    // -- monoid-agnostic union fragment, schematic at `'a` -------------------
    e.define_const("lang.empty", ConstDef::Op(set_empty(a.clone())));
    e.define_const("lang.union", ConstDef::Op(set_union(a.clone())));
    e.define_const("set.mem", ConstDef::Op(set_mem(a.clone())));
    e.define_const("set.subset", ConstDef::Op(set_subset(a.clone())));

    let x = Term::free("x", a.clone());
    let s = Term::free("s", sa.clone());
    let t = Term::free("t", sa.clone());

    // mem_empty : ⊢ ∀x. mem x ∅ = F
    e.define_lemma(
        "mem_empty",
        crate::init::set::mem_empty(&a, &x)
            .expect("lang_env: mem_empty")
            .all_intro("x", a.clone())
            .expect("lang_env: ∀ mem_empty"),
    );
    // mem_union : ⊢ ∀x s t. mem x (s ∪ t) = (mem x s ∨ mem x t)
    e.define_lemma(
        "mem_union",
        crate::init::set::mem_union(&a, &x, &s, &t)
            .expect("lang_env: mem_union")
            .all_intro("t", sa.clone())
            .expect("lang_env: ∀t mem_union")
            .all_intro("s", sa.clone())
            .expect("lang_env: ∀s mem_union")
            .all_intro("x", a.clone())
            .expect("lang_env: ∀x mem_union"),
    );
    // ext : ⊢ ∀s t. (∀x. mem x s = mem x t) ⟹ s = t
    let h = mem(&a, &x, &s)
        .equals(mem(&a, &x, &t))
        .expect("lang_env: mem eq")
        .forall("x", a.clone())
        .expect("lang_env: ∀ mem eq");
    e.define_lemma(
        "ext",
        crate::init::set::ext(&a, &s, &t, Thm::assume(h.clone()).unwrap())
            .expect("lang_env: ext")
            .imp_intro(&h)
            .expect("lang_env: ext imp")
            .all_intro("t", sa.clone())
            .expect("lang_env: ∀t ext")
            .all_intro("s", sa.clone())
            .expect("lang_env: ∀s ext"),
    );
    // subset_unfold : ⊢ ∀s t. subset s t = (∀x. mem x s ⟹ mem x t)
    e.define_lemma(
        "subset_unfold",
        crate::init::set::subset_unfold(&a, &s, &t)
            .expect("lang_env: subset_unfold")
            .all_intro("t", sa.clone())
            .expect("lang_env: ∀t subset_unfold")
            .all_intro("s", sa.clone())
            .expect("lang_env: ∀s subset_unfold"),
    );

    // -- model-specific layer at the concrete carrier `μ` --------------------
    let mu = carrier(m).expect("lang_env: monoid carrier");
    let w = Term::free("w", mu.clone());
    e.define_const(
        "lang.epsilon",
        ConstDef::Op(epsilon(m).expect("lang_env: epsilon")),
    );
    e.define_const("unit", ConstDef::Op(m.unit().clone()));
    // mem_epsilon : ⊢ ∀w. mem w ε = (w = unit)
    e.define_lemma(
        "mem_epsilon",
        mem_epsilon(m, &w)
            .expect("lang_env: mem_epsilon")
            .all_intro("w", mu.clone())
            .expect("lang_env: ∀ mem_epsilon"),
    );
    e
}

crate::cov_theory! {
    /// Language Kleene-algebra theorems ported to `lang.cov`, over `core` +
    /// `logic` + the `langprim` env at the `(nat, +, 0)` model. The union laws
    /// match the Rust [`union_comm`] / [`union_assoc`] / [`union_idem`] /
    /// [`union_empty`] (re-derived extensionally over the language `mem_union`
    /// given); `union_empty_l`, `subset_union_l`, and `subset_refl` are NEW
    /// theorems with no `lang.rs` counterpart.
    pub mod cov from "lang.cov" {
        import "core" = crate::script::Env::core();
        import "logic" = crate::init::logic::cov::env();
        import "langprim" = crate::init::lang::lang_env(&crate::init::monoid::nat_add_monoid());
        "union_comm"     => pub fn union_comm_cov;
        "union_assoc"    => pub fn union_assoc_cov;
        "union_idem"     => pub fn union_idem_cov;
        "union_empty"    => pub fn union_empty_cov;
        "union_empty_l"  => pub fn union_empty_l_cov;
        "subset_union_l" => pub fn subset_union_l_cov;
        "subset_refl"    => pub fn subset_refl_cov;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::monoid::nat_add_monoid;

    /// A genuine theorem: hypothesis-free and oracle-free.
    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "expected a hypothesis-free theorem");
        assert!(thm.has_no_obs(), "expected an oracle-free theorem");
    }

    fn word(name: &str) -> Term {
        Term::free(name, Type::nat())
    }

    fn langvar(name: &str) -> Term {
        Term::free(name, lang(Type::nat()))
    }

    #[test]
    fn operations_are_well_typed() {
        let m = nat_add_monoid();
        let l1 = langvar("L1");
        let l2 = langvar("L2");
        assert_eq!(
            empty_lang(&m).unwrap().type_of().unwrap(),
            lang(Type::nat())
        );
        assert_eq!(epsilon(&m).unwrap().type_of().unwrap(), lang(Type::nat()));
        assert_eq!(
            lang_union(&m, &l1, &l2).unwrap().type_of().unwrap(),
            lang(Type::nat())
        );
        assert_eq!(
            lang_concat(&m, &l1, &l2).unwrap().type_of().unwrap(),
            lang(Type::nat())
        );
        assert_eq!(
            lang_star(&m, &l1).unwrap().type_of().unwrap(),
            lang(Type::nat())
        );
    }

    #[test]
    fn mem_concat_computes_the_existential() {
        let m = nat_add_monoid();
        let (w, l1, l2) = (word("w"), langvar("L1"), langvar("L2"));
        let thm = mem_concat(&m, &w, &l1, &l2).unwrap();
        assert_genuine(&thm);
        // lhs is `mem w (L1·L2)`; rhs is `∃x y. mem x L1 ∧ mem y L2 ∧ w = x+y`.
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let mu = Type::nat();
        assert_eq!(lhs, &mem(&mu, &w, &lang_concat(&m, &l1, &l2).unwrap()));
        assert_eq!(rhs, &concat_body(&m, &w, &l1, &l2).unwrap());
    }

    #[test]
    fn mem_epsilon_is_unit_equation() {
        let m = nat_add_monoid();
        let w = word("w");
        let thm = mem_epsilon(&m, &w).unwrap();
        assert_genuine(&thm);
        // mem w ε = (w = 0).
        let (_, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(rhs, &w.clone().equals(Term::nat_lit(0u32)).unwrap());
    }

    #[test]
    fn empty_lang_has_no_members() {
        let m = nat_add_monoid();
        let thm = mem_empty_lang(&m, &word("w")).unwrap();
        assert_genuine(&thm);
        assert_eq!(rhs_of(&thm).unwrap(), Term::bool_lit(false));
    }

    #[test]
    fn concat_empty_left_annihilates() {
        let m = nat_add_monoid();
        let l = langvar("L");
        let thm = concat_empty_l(&m, &l).unwrap();
        assert_genuine(&thm);
        // ∅·L = ∅.
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let empty = empty_lang(&m).unwrap();
        assert_eq!(lhs, &lang_concat(&m, &empty, &l).unwrap());
        assert_eq!(rhs, &empty);
    }

    #[test]
    fn concat_empty_right_annihilates() {
        let m = nat_add_monoid();
        let l = langvar("L");
        let thm = concat_empty_r(&m, &l).unwrap();
        assert_genuine(&thm);
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let empty = empty_lang(&m).unwrap();
        assert_eq!(lhs, &lang_concat(&m, &l, &empty).unwrap());
        assert_eq!(rhs, &empty);
    }

    #[test]
    fn union_laws_are_the_set_theorems() {
        // The union Kleene-algebra fragment is genuine (re-exported `set`).
        for thm in [union_comm(), union_assoc(), union_idem(), union_empty()] {
            assert_genuine(&thm);
            assert!(thm.concl().as_eq().is_some());
        }
    }

    #[test]
    fn mem_star_computes_the_forall() {
        let m = nat_add_monoid();
        let (w, l) = (word("w"), langvar("L"));
        let thm = mem_star(&m, &w, &l).unwrap();
        assert_genuine(&thm);
        // lhs is `mem w L*`; rhs is a ∀-headed term.
        let (lhs, _rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &mem(&Type::nat(), &w, &lang_star(&m, &l).unwrap()));
    }

    #[test]
    fn star_contains_epsilon_is_genuine() {
        let m = nat_add_monoid();
        let l = langvar("L");
        let thm = star_contains_epsilon(&m, &l).unwrap();
        assert_genuine(&thm);
        // ⊢ subset ε L*.
        let mu = Type::nat();
        let expected = subset(&mu, &epsilon(&m).unwrap(), &lang_star(&m, &l).unwrap());
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn star_concat_closed_is_genuine() {
        let m = nat_add_monoid();
        let l = langvar("L");
        let thm = star_concat_closed(&m, &l).unwrap();
        assert_genuine(&thm);
        // ⊢ subset (L · L*) L*.
        let mu = Type::nat();
        let star = lang_star(&m, &l).unwrap();
        let expected = subset(&mu, &lang_concat(&m, &l, &star).unwrap(), &star);
        assert_eq!(thm.concl(), &expected);
    }

    // -- model-genericity: the SAME builders over a different monoid --------

    #[test]
    fn concat_empty_l_over_multiplicative_monoid() {
        // The identical proof, now about (nat, ×, 1) words.
        let m = crate::init::monoid::nat_mul_monoid();
        let l = langvar("L");
        let thm = concat_empty_l(&m, &l).unwrap();
        assert_genuine(&thm);
        let empty = empty_lang(&m).unwrap();
        assert_eq!(
            thm.concl().as_eq().unwrap(),
            (&lang_concat(&m, &empty, &l).unwrap(), &empty)
        );
    }

    // -- the `lang.cov` port: union Kleene-algebra over the `langprim` env ----

    /// The union laws ported to `lang.cov` must state *exactly* what the Rust
    /// `lang::union_*` (re-exported from `set`) state — same conclusion.
    #[test]
    fn lang_cov_union_laws_match_rust() {
        assert_eq!(cov::union_comm_cov().concl(), super::union_comm().concl());
        assert_eq!(cov::union_assoc_cov().concl(), super::union_assoc().concl());
        assert_eq!(cov::union_idem_cov().concl(), super::union_idem().concl());
        assert_eq!(cov::union_empty_cov().concl(), super::union_empty().concl());
    }

    /// Every ported union law is genuine — hypothesis- and oracle-free.
    #[test]
    fn lang_cov_ports_are_genuine() {
        for thm in [
            cov::union_comm_cov(),
            cov::union_assoc_cov(),
            cov::union_idem_cov(),
            cov::union_empty_cov(),
        ] {
            assert_genuine(&thm);
            assert!(thm.concl().as_eq().is_some());
        }
    }

    /// The NEW `lang.cov` theorems (no `lang.rs` counterpart) are genuine and
    /// have the expected shapes.
    #[test]
    fn lang_cov_new_theorems_are_genuine() {
        // union_empty_l : ⊢ ∅ ∪ s = s (an equation).
        let uel = cov::union_empty_l_cov();
        assert_genuine(&uel);
        assert!(uel.concl().as_eq().is_some());

        // subset_refl : ⊢ s ⊆ s (a `subset` atom, not an equation).
        let sr = cov::subset_refl_cov();
        assert_genuine(&sr);
        assert!(sr.concl().as_eq().is_none());

        // subset_union_l : ⊢ s ⊆ s ∪ t.
        let sul = cov::subset_union_l_cov();
        assert_genuine(&sul);
        assert!(sul.concl().as_eq().is_none());
    }

    /// `union_empty_l` really is the left dual of `union_empty`: applying it to
    /// the empty language gives the same `∅ ∪ ∅ = ∅` as the right law.
    #[test]
    fn lang_cov_union_empty_l_is_the_left_dual() {
        // The two laws are distinct statements (lhs `∅ ∪ s` vs `s ∪ ∅`)…
        let l_law = cov::union_empty_l_cov();
        let r_law = super::union_empty();
        assert_ne!(l_law.concl(), r_law.concl());
        // …but both are genuine `set.union`-headed equations ending in `s`.
        let (_, l_rhs) = l_law.concl().as_eq().unwrap();
        let (_, r_rhs) = r_law.concl().as_eq().unwrap();
        assert_eq!(l_rhs, r_rhs); // both reduce the union to the bare `s`.
    }
}
