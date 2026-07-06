//! Per-clause discharge helpers for `discharge_closed` (soundness rule
//! induction). A private submodule of [`super`] (`regex/mod.rs`); `use
//! super::*` pulls in the parent's private `denote`/`mem`/`r_*_at`/`lang_ty`/
//! `regex_at`/`nil_w`/`cat_w`/`word_ty` items that these helpers build on.
//!
//! Each helper proves a `⊢ Closed`-clause with the predicate `D = λr w. mem w
//! ⟦r⟧` in place of `M`, i.e. that the matching rule is *sound* against the
//! denotation. The recurring move: `⟦C sub…⟧` β-reduces to the corresponding
//! `lang` operation over the sub-denotations (the denotation is a fold), so
//! every clause bottoms out in a `lang`/`set` membership computation.

use super::*;
use covalence_hol_eval::derived::DerivedRules;

/// `⊢ ⟦r⟧ = nf` — β-normal form of a regex denotation (a `lang` term).
fn denote_nf(alpha: &Type, r: &Term) -> Result<Thm> {
    Ok(crate::init::eq::beta_nf(denote(alpha, r.clone())?))
}

/// The β-normal form term of `⟦r⟧`.
fn denote_val(alpha: &Type, r: &Term) -> Result<Term> {
    Ok(denote_nf(alpha, r)?
        .concl()
        .as_eq()
        .expect("beta_nf eq")
        .1
        .clone())
}

/// `eps` clause: `⊢ mem nil ⟦eps⟧`, given `mem_eps : ⊢ mem nil ε = (nil =
/// unit)` (the `lang` epsilon membership). `⟦eps⟧` β-reduces to `ε`, and
/// `unit = nil`, so the RHS is `nil = nil = T`.
pub(super) fn rewrite_mem_to_denote(
    _alpha: &Type,
    _m: &Monoid,
    _eps: &Term,
    nil: &Term,
    mem_eps: Thm,
) -> Result<Thm> {
    // mem_eps : ⊢ mem nil ε = (nil = unit)   (unit = nil here), so its RHS is
    // `nil = nil` = `T`, giving `⊢ mem nil ε`. Since `to_d` β-normalizes
    // `D eps nil` *fully* (collapsing `⟦eps⟧ → ε`), the proof it consumes is
    // exactly `mem nil ε`, no denote bridging needed.
    let refl = Thm::refl(nil.clone())?; // ⊢ nil = nil
    mem_eps.sym()?.eq_mp(refl) // ⊢ mem nil ε
}

/// `lit` clause (per `c`): `⊢ mem [c] ⟦lit c⟧`, given `mem_sing : ⊢ mem [c]
/// {[c]} = ([c] = [c])`. `⟦lit c⟧` β-reduces to `{[c]}`; the RHS is reflexive.
pub(super) fn rewrite_mem_singleton_to_denote(
    _alpha: &Type,
    _m: &Monoid,
    _lit: &Term,
    word: &Term,
    mem_sing: Thm,
) -> Result<Thm> {
    // mem_sing : ⊢ mem [c] {[c]} = ([c] = [c]). RHS is reflexive → `⊢ mem [c]
    // {[c]}`. `to_d` β-normalizes `D (lit c) [c]` fully (`⟦lit c⟧ → {[c]}`),
    // so this fully-reduced membership is exactly what it consumes.
    let refl = Thm::refl(word.clone())?; // ⊢ [c] = [c]
    mem_sing.sym()?.eq_mp(refl) // ⊢ mem [c] {[c]}
}

/// `alt-left`/`alt-right` clause: `⊢ ∀x y w. D sub w ⟹ D (alt x y) w`, where
/// `sub` is `x` (left) or `y` (right). `⟦alt x y⟧` β-reduces to `⟦x⟧ ∪ ⟦y⟧`;
/// membership unfolds to `mem w ⟦x⟧ ∨ mem w ⟦y⟧` via `mem_union`, and we
/// `or_intro` the matching side.
pub(super) fn discharge_alt(alpha: &Type, _m: &Monoid, d_pred: &Term, left: bool) -> Result<Thm> {
    let rset = lang_ty(alpha);
    let rty_a = regex_at(alpha, &rset);
    let wty = word_ty(alpha);
    let x = Term::free("x", rty_a.clone());
    let y = Term::free("y", rty_a.clone());
    let w = Term::free("w", wty.clone());
    let alt = r_alt_at(alpha, &rset, x.clone(), y.clone());
    let sub = if left { x.clone() } else { y.clone() };

    // D r w β= mem w ⟦r⟧.
    let d_eq = |r: &Term| -> Result<Thm> {
        let app = d_pred.clone().apply(r.clone())?.apply(w.clone())?;
        Ok(crate::init::eq::beta_nf(app)) // ⊢ D r w = mem w ⟦r⟧
    };

    // Assume `D sub w`, i.e. `mem w ⟦sub⟧` (after β).
    let d_sub_t = d_pred.clone().apply(sub.clone())?.apply(w.clone())?;
    let assume_d_sub = Thm::assume(d_sub_t.clone())?; // {D sub w} ⊢ D sub w
    let mem_sub = d_eq(&sub)?.eq_mp(assume_d_sub)?; // {D sub w} ⊢ mem w ⟦sub⟧

    // ⟦alt x y⟧ = ⟦x⟧ ∪ ⟦y⟧  (β); build the union membership.
    let den_x = denote_val(alpha, &x)?;
    let den_y = denote_val(alpha, &y)?;
    let mem_union = crate::init::set::mem_union(&wty, &w, &den_x, &den_y)?; // ⊢ mem w (⟦x⟧∪⟦y⟧) = (mem w ⟦x⟧ ∨ mem w ⟦y⟧)

    // ⊢ mem w ⟦x⟧ ∨ mem w ⟦y⟧, by or_intro on the assumed side.
    let disj = if left {
        mem_sub.or_intro_l(mem(alpha, &w, &den_y))? // mem w ⟦x⟧ ∨ mem w ⟦y⟧
    } else {
        mem_sub.or_intro_r(mem(alpha, &w, &den_x))?
    };
    // Fold the union: mem w (⟦x⟧∪⟦y⟧). `D (alt x y) w` β-normalizes *fully*
    // to this same `mem w (⟦x⟧∪⟦y⟧)` (the denotation fold collapses
    // `⟦alt x y⟧ → ⟦x⟧∪⟦y⟧`), so no further bridging to `⟦alt x y⟧` is needed.
    let mem_alt = mem_union.sym()?.eq_mp(disj)?; // {D sub w} ⊢ mem w (⟦x⟧∪⟦y⟧)

    // Re-fold to `D (alt x y) w`, discharge `D sub w`, ∀-close.
    let d_alt = d_eq(&alt)?.sym()?.eq_mp(mem_alt)?; // {D sub w} ⊢ D (alt x y) w
    d_alt
        .imp_intro(&d_sub_t)?
        .all_intro("w", wty)?
        .all_intro("y", rty_a.clone())?
        .all_intro("x", rty_a)
}

/// `seq` clause: `⊢ ∀x y w1 w2. D x w1 ⟹ D y w2 ⟹ D (seq x y) (cat w1 w2)`.
/// `⟦seq x y⟧` β-reduces to `⟦x⟧ · ⟦y⟧`; membership in a concat is the
/// existential `∃u v. mem u ⟦x⟧ ∧ mem v ⟦y⟧ ∧ (cat w1 w2) = op u v` — witness
/// `u := w1`, `v := w2` (the equation `cat w1 w2 = cat w1 w2` by refl).
pub(super) fn discharge_seq(alpha: &Type, m: &Monoid, d_pred: &Term) -> Result<Thm> {
    let rset = lang_ty(alpha);
    let rty_a = regex_at(alpha, &rset);
    let wty = word_ty(alpha);
    let x = Term::free("x", rty_a.clone());
    let y = Term::free("y", rty_a.clone());
    let w1 = Term::free("w1", wty.clone());
    let w2 = Term::free("w2", wty.clone());
    let seq = r_seq_at(alpha, &rset, x.clone(), y.clone());
    let cat = cat_w(alpha, &w1, &w2)?;

    let d_eq = |r: &Term, w: &Term| -> Result<Thm> {
        let app = d_pred.clone().apply(r.clone())?.apply(w.clone())?;
        Ok(crate::init::eq::beta_nf(app))
    };

    // Assume D x w1, D y w2 → mem w1 ⟦x⟧, mem w2 ⟦y⟧.
    let d_x_t = d_pred.clone().apply(x.clone())?.apply(w1.clone())?;
    let d_y_t = d_pred.clone().apply(y.clone())?.apply(w2.clone())?;
    let mem_x = d_eq(&x, &w1)?.eq_mp(Thm::assume(d_x_t.clone())?)?; // {D x w1} ⊢ mem w1 ⟦x⟧
    let mem_y = d_eq(&y, &w2)?.eq_mp(Thm::assume(d_y_t.clone())?)?; // {D y w2} ⊢ mem w2 ⟦y⟧

    let den_x = denote_val(alpha, &x)?;
    let den_y = denote_val(alpha, &y)?;

    // mem (cat w1 w2) (⟦x⟧·⟦y⟧) = ∃u v. mem u ⟦x⟧ ∧ mem v ⟦y⟧ ∧ cat w1 w2 = op u v.
    let mem_concat = lang::mem_concat(m, &cat, &den_x, &den_y)?;

    // Build the existential witness at u := w1, v := w2 — matching the
    // canonical `concat_body` shape (bound vars `_lc_x`, `_lc_y`).
    let u = Term::free("_lc_x", wty.clone());
    let v = Term::free("_lc_y", wty.clone());
    let body = |uu: &Term, vv: &Term| -> Result<Term> {
        let op_uv = m.op().clone().apply(uu.clone())?.apply(vv.clone())?;
        mem(alpha, uu, &den_x)
            .and(mem(alpha, vv, &den_y))?
            .and(cat.clone().equals(op_uv)?)
    };
    // ⊢ body[w1, w2]: mem w1 ⟦x⟧ ∧ mem w2 ⟦y⟧ ∧ cat w1 w2 = cat w1 w2 (refl).
    let at_w = mem_x
        .clone()
        .and_intro(mem_y.clone())?
        .and_intro(Thm::refl(cat.clone())?)?;

    // Inner ∃v: λv. body[w1, v].
    let inner_pred = Term::abs(
        wty.clone(),
        covalence_core::subst::close(&body(&w1, &v)?, "_lc_y"),
    );
    let at_v = crate::init::eq::beta_expand(&inner_pred, w2.clone(), at_w)?;
    let inner_ex = crate::init::logic::exists_intro(inner_pred, w2.clone(), at_v)?; // ⊢ ∃v. body[w1, v]

    // Outer ∃u: λu. ∃v. body[u, v].
    let outer_body = body(&u, &v)?.exists("_lc_y", wty.clone())?;
    let outer_pred = Term::abs(
        wty.clone(),
        covalence_core::subst::close(&outer_body, "_lc_x"),
    );
    let at_u = crate::init::eq::beta_expand(&outer_pred, w1.clone(), inner_ex)?;
    let outer_ex = crate::init::logic::exists_intro(outer_pred, w1.clone(), at_u)?; // ⊢ ∃u v. …

    // Fold to mem (cat w1 w2) (⟦x⟧·⟦y⟧). `D (seq x y)(cat w1 w2)`
    // β-normalizes fully to this, so no `⟦seq x y⟧` bridging is needed.
    let mem_seq = mem_concat.sym()?.eq_mp(outer_ex)?; // {D x w1, D y w2} ⊢ mem (cat w1 w2)(⟦x⟧·⟦y⟧)

    // Re-fold to D (seq x y)(cat w1 w2), discharge, ∀-close.
    let d_seq = d_eq(&seq, &cat)?.sym()?.eq_mp(mem_seq)?;
    d_seq
        .imp_intro(&d_y_t)?
        .imp_intro(&d_x_t)?
        .all_intro("w2", wty.clone())?
        .all_intro("w1", wty)?
        .all_intro("y", rty_a.clone())?
        .all_intro("x", rty_a)
}

/// `star-nil` clause: `⊢ ∀x. D (star x) nil`. `⟦star x⟧` β-reduces to `⟦x⟧*`;
/// `nil ∈ ε ⊆ ⟦x⟧*` via [`lang::star_contains_epsilon`] + the epsilon
/// membership.
pub(super) fn discharge_star_nil(alpha: &Type, m: &Monoid, d_pred: &Term) -> Result<Thm> {
    let rset = lang_ty(alpha);
    let rty_a = regex_at(alpha, &rset);
    let wty = word_ty(alpha);
    let x = Term::free("x", rty_a.clone());
    let star = r_star_at(alpha, &rset, x.clone());
    let nil = nil_w(alpha);
    let den_x = denote_val(alpha, &x)?;

    let d_eq = |r: &Term, w: &Term| -> Result<Thm> {
        let app = d_pred.clone().apply(r.clone())?.apply(w.clone())?;
        Ok(crate::init::eq::beta_nf(app))
    };

    // nil ∈ ε: mem nil ε = (nil = unit) = T (unit = nil).
    let mem_eps = lang::mem_epsilon(m, &nil)?; // ⊢ mem nil ε = (nil = unit)
    let mem_nil_eps = mem_eps.sym()?.eq_mp(Thm::refl(nil.clone())?)?; // ⊢ mem nil ε

    // ε ⊆ ⟦x⟧*, so mem nil ε ⟹ mem nil ⟦x⟧*.
    let sub = lang::star_contains_epsilon(m, &den_x)?; // ⊢ subset ε ⟦x⟧*
    let eps = lang::epsilon(m)?;
    let star_lang = lang::lang_star(m, &den_x)?;
    let imp = crate::init::set::subset_elim(&wty, &eps, &star_lang, sub)?.all_elim(nil.clone())?;
    let mem_nil_star = imp.imp_elim(mem_nil_eps)?; // ⊢ mem nil ⟦x⟧*

    // `D (star x) nil` β-normalizes fully to `mem nil ⟦x⟧*`, so no bridge.
    let d_star = d_eq(&star, &nil)?.sym()?.eq_mp(mem_nil_star)?;
    d_star.all_intro("x", rty_a)
}

/// `star-step` clause: `⊢ ∀x w1 w2. D x w1 ⟹ D (star x) w2 ⟹ D (star x) (cat
/// w1 w2)`. `⟦star x⟧` β-reduces to `⟦x⟧*`; `cat w1 w2 ∈ ⟦x⟧ · ⟦x⟧* ⊆ ⟦x⟧*`
/// via [`lang::star_concat_closed`] (the pre-fixpoint) + the concat
/// membership witness.
pub(super) fn discharge_star_step(alpha: &Type, m: &Monoid, d_pred: &Term) -> Result<Thm> {
    let rset = lang_ty(alpha);
    let rty_a = regex_at(alpha, &rset);
    let wty = word_ty(alpha);
    let x = Term::free("x", rty_a.clone());
    let w1 = Term::free("w1", wty.clone());
    let w2 = Term::free("w2", wty.clone());
    let star = r_star_at(alpha, &rset, x.clone());
    let cat = cat_w(alpha, &w1, &w2)?;
    let den_x = denote_val(alpha, &x)?;
    let star_lang = lang::lang_star(m, &den_x)?;
    let concat_ls = lang::lang_concat(m, &den_x, &star_lang)?;

    let d_eq = |r: &Term, w: &Term| -> Result<Thm> {
        let app = d_pred.clone().apply(r.clone())?.apply(w.clone())?;
        Ok(crate::init::eq::beta_nf(app))
    };

    // D x w1 → mem w1 ⟦x⟧ ; D (star x) w2 → mem w2 ⟦star x⟧ → mem w2 ⟦x⟧*.
    let d_x_t = d_pred.clone().apply(x.clone())?.apply(w1.clone())?;
    let d_sw_t = d_pred.clone().apply(star.clone())?.apply(w2.clone())?;
    let mem_x = d_eq(&x, &w1)?.eq_mp(Thm::assume(d_x_t.clone())?)?; // {D x w1} ⊢ mem w1 ⟦x⟧
    // `D (star x) w2` β-normalizes fully to `mem w2 ⟦x⟧*`.
    let mem_w2_star = d_eq(&star, &w2)?.eq_mp(Thm::assume(d_sw_t.clone())?)?; // {D (star x) w2} ⊢ mem w2 ⟦x⟧*

    // cat w1 w2 ∈ ⟦x⟧ · ⟦x⟧*: witness u := w1, v := w2.
    let mem_concat = lang::mem_concat(m, &cat, &den_x, &star_lang)?; // ⊢ mem (cat)(⟦x⟧·⟦x⟧*) = ∃u v. …
    let u = Term::free("_lc_x", wty.clone());
    let v = Term::free("_lc_y", wty.clone());
    let body = |uu: &Term, vv: &Term| -> Result<Term> {
        let op_uv = m.op().clone().apply(uu.clone())?.apply(vv.clone())?;
        mem(alpha, uu, &den_x)
            .and(mem(alpha, vv, &star_lang))?
            .and(cat.clone().equals(op_uv)?)
    };
    let at_w = mem_x
        .clone()
        .and_intro(mem_w2_star.clone())?
        .and_intro(Thm::refl(cat.clone())?)?;
    let inner_pred = Term::abs(
        wty.clone(),
        covalence_core::subst::close(&body(&w1, &v)?, "_lc_y"),
    );
    let at_v = crate::init::eq::beta_expand(&inner_pred, w2.clone(), at_w)?;
    let inner_ex = crate::init::logic::exists_intro(inner_pred, w2.clone(), at_v)?;
    let outer_body = body(&u, &v)?.exists("_lc_y", wty.clone())?;
    let outer_pred = Term::abs(
        wty.clone(),
        covalence_core::subst::close(&outer_body, "_lc_x"),
    );
    let at_u = crate::init::eq::beta_expand(&outer_pred, w1.clone(), inner_ex)?;
    let outer_ex = crate::init::logic::exists_intro(outer_pred, w1.clone(), at_u)?;
    let mem_cat_concat = mem_concat.sym()?.eq_mp(outer_ex)?; // {…} ⊢ mem (cat)(⟦x⟧·⟦x⟧*)

    // ⟦x⟧·⟦x⟧* ⊆ ⟦x⟧* (pre-fixpoint), so mem (cat) ⟦x⟧*.
    let sub = lang::star_concat_closed(m, &den_x)?; // ⊢ subset (⟦x⟧·⟦x⟧*) ⟦x⟧*
    let imp =
        crate::init::set::subset_elim(&wty, &concat_ls, &star_lang, sub)?.all_elim(cat.clone())?;
    let mem_cat_star = imp.imp_elim(mem_cat_concat)?; // {…} ⊢ mem (cat) ⟦x⟧*

    // Re-fold to D (star x)(cat w1 w2) (β-normalizes fully to mem (cat) ⟦x⟧*),
    // discharge both, ∀-close.
    let d_step = d_eq(&star, &cat)?.sym()?.eq_mp(mem_cat_star)?;
    d_step
        .imp_intro(&d_sw_t)?
        .imp_intro(&d_x_t)?
        .all_intro("w2", wty.clone())?
        .all_intro("w1", wty)?
        .all_intro("x", rty_a)
}
