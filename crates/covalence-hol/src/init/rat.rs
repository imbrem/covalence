//! `rat` theorems: the `defs/rat.rs` catalogue re-exported, plus the
//! quotient scaffolding for HOL `rat := (int × int.pos) / ~` — mirroring
//! how [`init::int`] pairs the `int` definitions with the Grothendieck
//! quotient machinery, one level up.
//!
//! [`init::int`]: crate::init::int
//!
//! ## The construction
//!
//! A pair `(a, b) : int × int.pos` represents the rational `a / b` with a
//! strictly-positive denominator (so it is always nonzero and the sign
//! lives in the numerator), and pairs are identified by
//! cross-multiplication:
//!
//! ```text
//!     (a, b) ~ (c, d)  ⟺  a · d = c · b
//! ```
//!
//! `rat` is the quotient of `prod int int.pos` by that relation; the
//! carrier is `(prod int int.pos) → bool` (a class is the set of
//! equivalent numerator/denominator pairs). The bridge between a
//! representative pair and its class reuses the generic
//! [`init::quotient`](crate::init::quotient) machinery exactly as `int`
//! does over `nat × nat`.
//!
//! ## Status
//!
//! This module is built up in layers, mirroring `init::int`:
//!
//! - **Quotient relation.** [`rat_rel`] is the cross-multiplication
//!   relation, structurally the term `defs/rat.rs` quotients by.
//!   [`rat_rel_refl`] / [`rat_rel_symm`] are **proved** (`int`-equation
//!   `refl` / `sym`); [`rat_rel_trans`] is **postulated** — it is the one
//!   piece that needs `int` *multiplicative cancellation by a positive*,
//!   an `int` fact not yet discharged (see `SKELETONS.md`).
//! - **Maps in.** [`of_int`] (`a ↦ a/1`) and [`of_nat`] (`= of_int ∘
//!   nat.toInt`, by composition) embed the integers and naturals.
//! - **Ring / order.** The field operations ([`rat_zero`], [`rat_one`],
//!   [`rat_add`], [`rat_neg`], [`rat_mul`]) and the strict order
//!   ([`rat_lt`]) are defined at the representative level; the ordered-
//!   field axioms over them are **postulated** (same audit-trail style as
//!   `init::int`), pending the quotient derivations.
//! - **Density.** [`dense`] — `∀x y. x < y ⟹ ∃z. x < z ∧ z < y` — is
//!   **derived** from the two mediant-inequality postulates via the
//!   mediant `(a+c)/(b+d)`, the witness that needs no division.

use covalence_core::defs::{fst, int_pos_spec, int_pos_ty, prod, snd};
use covalence_core::{Result, Term, Thm, Type, subst};

use crate::init::ext::TermExt;
use crate::init::{int, nat};

// Re-export the `defs/rat.rs` catalogue (the type handles + the declared
// `ratLe` order constant; bodies stay in `covalence_core::defs`).
pub use covalence_core::defs::{rat_le, rat_le_spec, rat_spec, rat_ty};

// ============================================================================
// Small term helpers (private — the public surface is theorems / maps)
// ============================================================================

/// `rat` — the rationals type.
fn rat() -> Type {
    rat_ty()
}

/// `int × int.pos` — the numerator/denominator representative carrier.
fn ip_pair() -> Type {
    prod(Type::int(), int_pos_ty())
}

/// `fst p : int` — the numerator of a representative pair.
fn num(p: &Term) -> Term {
    Term::app(fst(Type::int(), int_pos_ty()), p.clone())
}

/// `rep (snd p) : int` — the (positive) denominator of a representative
/// pair, coerced from `int.pos` down to its underlying `int`.
fn den(p: &Term) -> Term {
    let d_pos = Term::app(snd(Type::int(), int_pos_ty()), p.clone());
    let rep = Term::spec_rep(int_pos_spec(), Vec::new());
    Term::app(rep, d_pos)
}

/// `a · b` on `int`.
fn imul(a: Term, b: Term) -> Term {
    Term::app(Term::app(int::int_mul(), a), b)
}

/// `λp q. num p · den q = num q · den p` — the cross-multiplication
/// relation carving `rat`. Structurally the same term `defs/rat.rs`
/// quotients by.
pub fn rat_rel() -> Term {
    let pair_ty = ip_pair();
    let (p, q) = (Term::free("p", pair_ty.clone()), Term::free("q", pair_ty.clone()));
    let body = imul(num(&p), den(&q))
        .equals(imul(num(&q), den(&p)))
        .expect("rat_rel: body");
    let inner = Term::abs(pair_ty.clone(), covalence_core::subst::close(&body, "q"));
    Term::abs(pair_ty, covalence_core::subst::close(&inner, "p"))
}

/// `rat_rel p q` as an (un-reduced) application — the shape
/// [`quotient::class_intro`](crate::init::quotient::class_intro) reads
/// its relation in.
fn rel_app(p: &Term, q: &Term) -> Term {
    Term::app(Term::app(rat_rel(), p.clone()), q.clone())
}

/// `mkRat p ≔ abs (λq. rat_rel p q)` — the rational whose class is `[p]`,
/// for a representative pair term `p : int × int.pos`.
fn mk_rat(p: &Term) -> Term {
    crate::init::quotient::mk_class(&rat_spec(), &[], &ip_pair(), &rat_rel(), p)
}

/// `⊢ rat_rel p q` → `⊢ <β-reduced cross-mult equation>`.
fn reduce_rel(thm: Thm) -> Result<Thm> {
    thm.concl().reduce()?.eq_mp(thm)
}

/// `⊢ <β-reduced cross-mult equation>` → `⊢ rat_rel p q`, for the given
/// application.
fn expand_rel(eq: Thm, app: &Term) -> Result<Thm> {
    app.reduce()?.sym()?.eq_mp(eq)
}

/// `1 : int.pos` — the abstraction of the `int` literal `1`. The
/// canonical denominator for the integer / rational embeddings.
fn one_pos() -> Term {
    Term::app(Term::spec_abs(int_pos_spec(), Vec::new()), Term::int_lit(1i128))
}

/// `pair a b : int × int.pos`.
fn ip(a: Term, b: Term) -> Term {
    Term::app(
        Term::app(covalence_core::defs::pair(Type::int(), int_pos_ty()), a),
        b,
    )
}

/// Postulate a `rat` axiom: `{t} ⊢ t`. The self-hypothesis is the audit
/// trail — every proof built on it carries it, flagging the unproved leaf
/// until the quotient derivation discharges it (cf. `init::int::axiom`).
fn axiom(t: Term) -> Thm {
    Thm::assume(t).expect("init::rat::axiom: term must be bool-typed")
}

/// Universally close `body` over the named representative-pair variables,
/// outermost first.
fn forall_pair(vars: &[&str], body: Term) -> Term {
    let mut t = body;
    for name in vars.iter().rev() {
        t = t.forall(name, ip_pair()).expect("forall_pair: bind variable");
    }
    t
}

// ============================================================================
// `rat_rel` is an equivalence
// ============================================================================
//
// `refl` / `symm` are pure `int`-equation manipulations of the cross-
// multiplication body and are **proved** outright. `trans` is the one
// piece that needs `int` *multiplicative cancellation by a positive*
// denominator (from `a·d = c·b` and `c·f = e·d`, cancel `d` to reach
// `a·f = e·b`); that `int` fact is not yet discharged, so `trans` is a
// postulate (`SKELETONS.md`).

cached_thm! {
    /// `⊢ ∀p. rat_rel p p` — reflexivity (`num p · den p = num p · den p`).
    pub fn rat_rel_refl() -> Thm {
        rat_rel_refl_impl().expect("rat_rel_refl")
    }
}
fn rat_rel_refl_impl() -> Result<Thm> {
    let p = Term::free("p", ip_pair());
    let reduced = Thm::refl(imul(num(&p), den(&p)))?;
    expand_rel(reduced, &rel_app(&p, &p))?.all_intro("p", ip_pair())
}

cached_thm! {
    /// `⊢ ∀p q. rat_rel p q ⟹ rat_rel q p` — symmetry (`sym` of the
    /// defining cross-multiplication equation).
    pub fn rat_rel_symm() -> Thm {
        rat_rel_symm_impl().expect("rat_rel_symm")
    }
}
fn rat_rel_symm_impl() -> Result<Thm> {
    let (p, q) = (Term::free("p", ip_pair()), Term::free("q", ip_pair()));
    let hyp = rel_app(&p, &q);
    let flipped = reduce_rel(Thm::assume(hyp.clone())?)?.sym()?; // ⊢ num q·den p = num p·den q
    expand_rel(flipped, &rel_app(&q, &p))?
        .imp_intro(&hyp)?
        .all_intro("q", ip_pair())?
        .all_intro("p", ip_pair())
}

cached_thm! {
    /// `⊢ ∀p q r. rat_rel p q ⟹ rat_rel q r ⟹ rat_rel p r` —
    /// transitivity.
    ///
    /// **Postulated** (audit hyp). The derivation: from `num p · den q =
    /// num q · den p` and `num q · den r = num r · den q`, multiply the
    /// first by `den r` and the second by `den p`, commute/associate so
    /// the common `num q · den q · den r` factor matches, giving
    /// `(num p · den r) · den q = (num r · den p) · den q`, then cancel
    /// `den q` (strictly positive, hence nonzero) — the `int`
    /// multiplicative cancellation that is not yet a proved `int` fact.
    pub fn rat_rel_trans() -> Thm {
        let (p, q, r) = (
            Term::free("p", ip_pair()),
            Term::free("q", ip_pair()),
            Term::free("r", ip_pair()),
        );
        let pr = rel_app(&p, &r);
        let body = rel_app(&p, &q)
            .imp(rel_app(&q, &r).imp(pr).expect("rat_rel_trans inner"))
            .expect("rat_rel_trans");
        axiom(forall_pair(&["p", "q", "r"], body))
    }
}

// ============================================================================
// Maps in: ℤ ↪ ℚ and ℕ ↪ ℚ (the latter by composition)
// ============================================================================

/// `of_int : int → rat` ≡ `λa. mkRat (a, 1)` — the ring embedding of the
/// integers (numerator `a`, denominator `1`).
pub fn of_int() -> Term {
    let a = Term::free("a", Type::int());
    let body = mk_rat(&ip(a.clone(), one_pos()));
    Term::abs(Type::int(), subst::close(&body, "a"))
}

/// `of_nat : nat → rat` ≡ `λn. of_int (nat.toInt n)` — the embedding of
/// the naturals, **by composition** through `of_int` and the nat→int
/// coercion.
pub fn of_nat() -> Term {
    let n = Term::free("n", Type::nat());
    let body = Term::app(of_int(), Term::app(nat::nat_to_int(), n.clone()));
    Term::abs(Type::nat(), subst::close(&body, "n"))
}

cached_thm! {
    /// `⊢ ∀n. of_nat n = of_int (nat.toInt n)` — the naturals embed
    /// through the integers (the defining composition, by β).
    pub fn of_nat_via_int() -> Thm {
        of_nat_via_int_impl().expect("of_nat_via_int")
    }
}
fn of_nat_via_int_impl() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let redex = Term::app(of_nat(), n.clone()); // (λn. of_int (toInt n)) n
    Thm::beta_conv(redex)?.all_intro("n", Type::nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rat_ty_matches_the_catalogue() {
        // The re-exported `rat` type is the `defs/rat.rs` one, and not bool.
        assert_eq!(rat(), covalence_core::defs::rat_ty());
        assert!(!rat().is_bool());
    }

    #[test]
    fn rat_rel_is_a_binary_relation_on_pairs() {
        // rat_rel : (int×int.pos) → (int×int.pos) → bool.
        let expected = Type::fun(
            ip_pair(),
            Type::fun(ip_pair(), Type::bool()),
        );
        assert_eq!(rat_rel().type_of().unwrap(), expected);
    }

    #[test]
    fn rel_app_reduces_to_a_cross_multiplication() {
        // rat_rel (a,1) (c,1)  β-reduces to  a·den(c,1) = c·den(a,1).
        let p = ip(Term::int_lit(2i128), one_pos());
        let q = ip(Term::int_lit(3i128), one_pos());
        let reduced = rel_app(&p, &q).reduce().unwrap();
        // The reduct is a bool equation between two int products.
        let rhs = reduced.concl().as_eq().unwrap().1;
        assert!(rhs.as_eq().is_some(), "reduct is `_ · _ = _ · _`");
    }

    #[test]
    fn mk_rat_is_a_rational() {
        let p = ip(Term::int_lit(5i128), one_pos());
        assert_eq!(mk_rat(&p).type_of().unwrap(), rat());
    }

    #[test]
    fn rat_rel_refl_and_symm_are_genuine() {
        // refl / symm are proved outright (no hypotheses).
        for t in [rat_rel_refl(), rat_rel_symm()] {
            assert!(t.hyps().is_empty(), "rat_rel refl/symm are proved");
            assert!(t.concl().type_of().unwrap().is_bool());
        }
        let (p, q) = (Term::free("p", ip_pair()), Term::free("q", ip_pair()));
        assert_eq!(rat_rel_refl().all_elim(p.clone()).unwrap().concl(), &rel_app(&p, &p));
        let symm = rat_rel_symm()
            .all_elim(p.clone())
            .unwrap()
            .all_elim(q.clone())
            .unwrap();
        assert_eq!(symm.concl(), &rel_app(&p, &q).imp(rel_app(&q, &p)).unwrap());
    }

    #[test]
    fn rat_rel_trans_is_a_self_flagged_postulate() {
        let t = rat_rel_trans();
        assert!(t.concl().type_of().unwrap().is_bool());
        assert!(
            t.hyps().iter().any(|h| h == t.concl()),
            "the postulate carries itself as a hypothesis"
        );
    }

    #[test]
    fn class_intro_lifts_rat_rel_to_a_class_equation() {
        // With symm proved and trans postulated, the forward quotient law
        // lifts a `~`-fact to a rat-class equation over the real spec.
        use crate::init::quotient;
        let (p, q) = (Term::free("p", ip_pair()), Term::free("q", ip_pair()));
        let ab = Thm::assume(rel_app(&p, &q)).unwrap();
        let lifted = quotient::class_intro(
            &rat_spec(),
            &[],
            &ip_pair(),
            &rat_rel_symm(),
            &rat_rel_trans(),
            ab,
        )
        .expect("class_intro on rat_rel");
        let (l, r) = lifted.concl().as_eq().expect("lifted to a class equation");
        assert_eq!(l, &mk_rat(&p));
        assert_eq!(r, &mk_rat(&q));
        assert!(lifted.hyps().iter().any(|h| h == &rel_app(&p, &q)));
    }

    #[test]
    fn maps_have_the_expected_types() {
        assert_eq!(of_int().type_of().unwrap(), Type::fun(Type::int(), rat()));
        assert_eq!(of_nat().type_of().unwrap(), Type::fun(Type::nat(), rat()));
    }

    #[test]
    fn of_nat_factors_through_of_int() {
        // ∀n. of_nat n = of_int (nat.toInt n); specialise to a concrete n.
        let n = Term::free("k", Type::nat());
        let inst = of_nat_via_int().all_elim(n.clone()).unwrap();
        let lhs = Term::app(of_nat(), n.clone());
        let rhs = Term::app(of_int(), Term::app(nat::nat_to_int(), n));
        // of_nat_via_int is a β-fact: genuine, hypothesis-free.
        assert!(of_nat_via_int().hyps().is_empty());
        let (l, r) = inst.concl().as_eq().unwrap();
        assert_eq!(l, &lhs);
        assert_eq!(r, &rhs);
    }
}
