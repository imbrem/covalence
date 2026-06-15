//! `list` theorems: the `defs/list.rs` catalogue re-exported, plus the
//! first **computational foundation block** for lists — the `abs`/`rep`
//! seam, the finiteness facts that gate it, and the empty-list element
//! computations. Same abstraction-barrier shape as [`init::stream`] and
//! [`init::set`].
//!
//! [`init::stream`]: crate::init::stream
//! [`init::set`]: crate::init::set
//!
//! ## What `list α` is
//!
//! `list α := stream (option α) where finite` — the **subtype** of
//! `stream (option α)` carved by the selector predicate
//! [`finite`](crate::init::stream::finite) (eventually-`none` streams).
//! The constructors funnel through the kernel coercions
//! `abs : stream (option α) → list α` and `rep : list α → stream (option
//! α)`; e.g. `nil ≡ abs (streamConst none)`. **Downstream list proofs
//! must not see that** — they should reason through the element-access
//! lemmas exposed here ([`index_nil`], [`head_nil`], …), never `abs` /
//! `rep` directly.
//!
//! ## The finiteness gate
//!
//! Unlike `stream`/`set` (newtypes, predicate `λ_. T`), `list` is a
//! genuine subtype, so the carrier-side round-trip
//! [`Thm::spec_rep_abs_fwd`] is *conditional*: `⊢ finite s ⟹ rep (abs s)
//! = s`. Every computation that peeks inside a constructor must first
//! discharge `finite` of the underlying stream. For `nil` that stream is
//! `streamConst none`, finite by [`finite_const_none`] — so the empty-list
//! facts are reachable now with no further machinery, and all are genuine
//! (hypothesis- and oracle-free).
//!
//! ## Not yet here (see `SKELETONS.md`)
//!
//! The `cons`-side computations (`index`/`head`/`tail` of `cons x xs`)
//! need `finite (cons-stream)` — a finiteness-*preservation* proof that
//! rests on `nat` ordering theory (`nat_le` successor lemmas) not yet
//! developed in [`init::nat`]. The structural recursors
//! [`list_foldr`] / [`list_foldl`] are pinned by Hilbert-ε selector
//! predicates; discharging their defining equations needs a **list
//! recursion theorem** (the analogue of [`crate::init::recursion`] for
//! `nat`). Both — together with list extensionality / induction and the
//! `length`/`cat`/`map`/`filter`/`flatten` facts that ride on them — are
//! recorded as skeletons.
//!
//! [`init::nat`]: crate::init::nat

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::eq::beta_expand;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::exists_intro;
use crate::init::stream::{const_at, head_const};

// Re-export the `defs/list.rs` term catalogue (the `*_spec` handles stay
// in `covalence_core::defs`, reached via the blanket re-export there).
pub use covalence_core::defs::{
    cons, head, list, list_cat, list_filter, list_flatten, list_foldl, list_foldr, list_index,
    list_length, list_map, list_repeat, list_skip, list_take, nil, tail,
};

use covalence_core::defs::{
    finite, finite_spec, head_spec, list_index_spec, list_spec, nat_le, none, option, stream_const,
};

// ============================================================================
// Term helpers (private — the public surface is the lemmas + builders).
// ============================================================================

fn nat() -> Type {
    Type::nat()
}

fn zero() -> Term {
    Term::nat_lit(covalence_types::Nat::zero())
}

/// `streamConst none : stream (option α)` — the carrier stream behind
/// `nil`, i.e. the everywhere-`none` stream.
fn const_none(alpha: &Type) -> Term {
    Term::app(stream_const(option(alpha.clone())), none(alpha.clone()))
}

/// `list.index[α] n xs : option α` — element access as a builder.
fn index(alpha: &Type, n: &Term, xs: &Term) -> Term {
    Term::app(Term::app(list_index(alpha.clone()), n.clone()), xs.clone())
}

// ============================================================================
// THE SEAM — the only code aware that `list` is a subtype of
// `stream (option α)` carved by `finite`.
//
//   abs : stream (option α) → list α      rep : list α → stream (option α)
//
// `rep (abs s) = s` is *conditional* on `finite s` (the subtype's
// selector predicate, stored on `list_spec` as the `finite` Spec leaf —
// so the `spec_rep_abs_fwd` premise is exactly `finite s`, dischargeable
// by a `⊢ finite s` theorem with no δ-bridging).
// ============================================================================

/// `⊢ rep (abs s) = s`, given `fin : ⊢ finite s` — the carrier-side
/// round-trip for `list`, with the subtype premise discharged. From the
/// kernel's conditional [`Thm::spec_rep_abs_fwd`].
fn rep_abs_finite(alpha: &Type, s: &Term, fin: Thm) -> Result<Thm> {
    Thm::spec_rep_abs_fwd(list_spec(), vec![alpha.clone()], s.clone())?.imp_elim(fin)
}

// ============================================================================
// Finiteness facts.
// ============================================================================

/// `⊢ finite (streamConst none)` — the everywhere-`none` stream is
/// finite (bound `N := 0`; the body `streamAt (streamConst none) n =
/// none` holds at *every* `n` by [`const_at`], so the
/// `nat_le 0 n` antecedent is discharged vacuously). The finiteness
/// witness that gates the `nil` computations.
pub fn finite_const_none(alpha: &Type) -> Result<Thm> {
    let opt = option(alpha.clone());
    let cst = const_none(alpha);

    // ⊢ finite cst = (∃N. ∀n. nat_le N n ⟹ streamAt cst n = none)
    let unfold = Term::app(finite(alpha.clone()), cst.clone())
        .delta_all(finite_spec().symbol())?
        .rhs_conv(|t| t.reduce())?;
    let ex = rhs_of(&unfold)?; // ∃N. body
    let pred = ex.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λN. body

    // ⊢ body[0/N] — the consequent holds at every `n`, so imp_intro the
    // (vacuous) `nat_le 0 n` antecedent and ∀-close.
    let n = Term::free("n", nat());
    let at_n = const_at(&opt, &none(alpha.clone()), &n)?; // ⊢ streamAt cst n = none
    let le_0_n = Term::app(Term::app(nat_le(), zero()), n.clone());
    let body_at_0 = at_n.imp_intro(&le_0_n)?.all_intro("n", nat())?;

    // ⊢ pred 0, then ∃-introduce and bridge back to `finite cst`.
    let at_pred = beta_expand(&pred, zero(), body_at_0)?; // ⊢ pred 0
    let exists = exists_intro(pred, zero(), at_pred)?; // ⊢ ∃N. body
    unfold.sym()?.eq_mp(exists) // ⊢ finite cst
}

/// `⊢ ∃s. finite s` — the `finite` predicate is inhabited (witness
/// `streamConst none`). The non-emptiness fact that the subtype's
/// witness-free back-direction law ([`Thm::spec_rep_abs_back`]) needs to
/// recover `finite (rep xs)` for an arbitrary `xs : list α` — the bridge
/// to the `cons`-side computations once they land.
pub fn finite_nonempty(alpha: &Type) -> Result<Thm> {
    exists_intro(
        finite(alpha.clone()),
        const_none(alpha),
        finite_const_none(alpha)?,
    )
}

// ============================================================================
// Element access — the high-level computational surface.
// ============================================================================

/// `⊢ list.index n xs = streamAt (rep xs) n` — unfold indexing to the raw
/// carrier-stream access (no constructor involved, so `xs` stays opaque).
/// The bridge every per-constructor `index_*` lemma builds on.
pub fn index_unfold(alpha: &Type, n: &Term, xs: &Term) -> Result<Thm> {
    index(alpha, n, xs)
        .delta_all(list_index_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ list.index n nil = none` — the empty list has no elements. Genuine:
/// hypothesis- and oracle-free.
pub fn index_nil(alpha: &Type, n: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let cst = const_none(alpha);

    // listIndex n nil = streamAt (rep nil) n
    let idx = index_unfold(alpha, n, &nil(alpha.clone()))?;
    // nil = abs (streamConst none)
    let nil_u = nil(alpha.clone()).delta()?;
    // rep (abs (streamConst none)) = streamConst none
    let ra = rep_abs_finite(alpha, &cst, finite_const_none(alpha)?)?;
    // streamAt (streamConst none) n = none
    let cst_at = const_at(&opt, &none(alpha.clone()), n)?;

    // Rewrite `nil → abs cst`, then collapse `rep (abs cst) → cst`, then
    // evaluate the constant-stream access.
    idx.rhs_conv(|t| t.rw_all(&nil_u))?
        .rhs_conv(|t| t.rw_all(&ra))?
        .trans(cst_at)
}

/// `⊢ list.head nil = none` — the head of the empty list is `none`.
/// Genuine: hypothesis- and oracle-free.
pub fn head_nil(alpha: &Type) -> Result<Thm> {
    let opt = option(alpha.clone());
    let cst = const_none(alpha);

    // head nil = streamHead (rep nil)
    let h = Term::app(head(alpha.clone()), nil(alpha.clone()))
        .delta_all(head_spec().symbol())?
        .rhs_conv(|t| t.reduce())?;
    let nil_u = nil(alpha.clone()).delta()?; // nil = abs cst
    let ra = rep_abs_finite(alpha, &cst, finite_const_none(alpha)?)?; // rep (abs cst) = cst
    let head_c = head_const(&opt, &none(alpha.clone()))?; // streamHead cst = none

    h.rhs_conv(|t| t.rw_all(&nil_u))?
        .rhs_conv(|t| t.rw_all(&ra))?
        .trans(head_c)
}

// ============================================================================
// High-level term builders (pure construction — no proof).
// ============================================================================

/// `cons e₁ (cons e₂ (… nil))` — the list literal over `elems`, folding
/// [`cons`] right over [`nil`]. Errors if any element's type disagrees
/// with `alpha`.
pub fn list_of(alpha: &Type, elems: Vec<Term>) -> Result<Term> {
    let mut acc = nil(alpha.clone());
    for e in elems.into_iter().rev() {
        acc = cons(alpha.clone()).apply(e)?.apply(acc)?;
    }
    Ok(acc)
}

// ============================================================================
// Small helpers.
// ============================================================================

/// The right-hand side of an equational theorem's conclusion.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> Type {
        Type::tfree("a")
    }

    fn nat_lit(n: u32) -> Term {
        Term::nat_lit(covalence_types::Nat::from_inner(n.into()))
    }

    #[test]
    fn finite_const_none_is_genuine() {
        let thm = finite_const_none(&alpha()).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "finite_const_none is proved, not postulated"
        );
        assert!(thm.has_no_obs(), "finite_const_none is oracle-free");
        let expected = Term::app(finite(alpha()), const_none(&alpha()));
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn finite_nonempty_is_genuine() {
        let thm = finite_nonempty(&alpha()).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // ⊢ ∃s. finite s
        let expected = Term::app(
            covalence_core::defs::exists(crate::init::stream::stream(option(alpha()))),
            finite(alpha()),
        );
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn index_unfold_exposes_carrier_access() {
        let n = Term::free("n", nat());
        let xs = Term::free("xs", list(alpha()));
        let thm = index_unfold(&alpha(), &n, &xs).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, _rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &index(&alpha(), &n, &xs));
    }

    #[test]
    fn index_nil_is_none_polymorphic() {
        let n = Term::free("n", nat());
        let thm = index_nil(&alpha(), &n).unwrap();
        assert!(thm.hyps().is_empty(), "index_nil is proved, not postulated");
        assert!(thm.has_no_obs(), "index_nil is oracle-free");
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &index(&alpha(), &n, &nil(alpha())));
        assert_eq!(rhs, &none(alpha()));
    }

    #[test]
    fn index_nil_at_a_concrete_index() {
        // listIndex 3 nil = none, with a literal index.
        let thm = index_nil(&alpha(), &nat_lit(3)).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(rhs_of(&thm).unwrap(), none(alpha()));
    }

    #[test]
    fn head_nil_is_none() {
        let thm = head_nil(&alpha()).unwrap();
        assert!(thm.hyps().is_empty(), "head_nil is proved, not postulated");
        assert!(thm.has_no_obs(), "head_nil is oracle-free");
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &Term::app(head(alpha()), nil(alpha())));
        assert_eq!(rhs, &none(alpha()));
    }

    #[test]
    fn list_of_builds_nested_cons() {
        let a = alpha();
        let x = Term::free("x", a.clone());
        let y = Term::free("y", a.clone());
        // [x, y] = cons x (cons y nil)
        let built = list_of(&a, vec![x.clone(), y.clone()]).unwrap();
        let expected = Term::app(
            Term::app(cons(a.clone()), x),
            Term::app(Term::app(cons(a.clone()), y), nil(a.clone())),
        );
        assert_eq!(built, expected);
        assert_eq!(built.type_of().unwrap(), list(a));
    }

    #[test]
    fn list_of_empty_is_nil() {
        assert_eq!(list_of(&alpha(), vec![]).unwrap(), nil(alpha()));
    }
}
