//! `list` theorems: the `defs/list.rs` catalogue re-exported, plus the
//! full **structural foundation** for lists — the `abs`/`rep` seam, the
//! selector facts that gate it, the per-constructor element computations,
//! constructor freeness, extensionality, and the **list induction
//! principle**. The recursion theorem and the `list_foldr` discharge ride
//! on top in [`crate::init::list_recursion`].
//!
//! [`init::stream`]: mod@crate::init::stream
//! [`init::set`]: mod@crate::init::set
//!
//! ## What `list α` is
//!
//! `list α := stream (option α) where (finite ∧ contiguous)` — the
//! **subtype** of `stream (option α)` carved by `list_pred`: streams
//! that are finite (eventually `none`) **and** contiguous (`s i = none ⟹
//! s (succ i) = none`, no interior holes). The constructors funnel through
//! the kernel coercions `abs : stream (option α) → list α` and `rep : list
//! α → stream (option α)`; e.g. `nil ≡ abs (streamConst none)`,
//! `cons x xs ≡ abs (streamMk (consStream x xs))`. **Downstream list
//! proofs must not see that** — they reason through the element-access
//! lemmas ([`index_nil`], [`index_cons_zero`], [`head_cons`], …) and the
//! structural laws, never `abs` / `rep` directly.
//!
//! ## Why contiguity (exhaustiveness)
//!
//! The contiguity conjunct is what makes `nil` / `cons` **exhaustive**.
//! Under a `finite`-only predicate a stream like `[none, some a, none, …]`
//! would be a `list α` value reachable by *neither* constructor (head
//! `none`, so not a `cons`; but `index 1 = some a ≠ none`, so not `nil`),
//! and list induction would be **false**. With contiguity every list is
//! `nil` (empty prefix) or `cons x xs` (a `some` head over a shorter
//! contiguous tail). See [`defs::list_spec`](covalence_hol_eval::defs::list_spec).
//!
//! ## The selector gate
//!
//! Unlike `stream`/`set` (newtypes, predicate `λ_. T`), `list` is a
//! genuine subtype, so the carrier-side round-trip
//! [`Thm::spec_rep_abs_fwd`] is *conditional* on the selector. Every
//! computation that peeks inside a constructor first discharges
//! `list_predicate` of the underlying stream — [`pred_const_none`] for
//! `nil`, [`pred_cons`] for `cons x xs`, [`pred_rep`] for an arbitrary
//! `rep l`. All are genuine (hypothesis- and oracle-free).
//!
//! ## What is here (all genuine)
//!
//! - **Selector facts**: [`pred_const_none`] / [`pred_cons`] / [`pred_rep`]
//!   (+ the `finite_*` / `contig_*` conjuncts), [`pred_nonempty`].
//! - **Element computations**: [`index_nil`] / [`index_cons_zero`] /
//!   [`index_cons_succ`], [`head_nil`] / [`head_cons`], [`tail_cons`],
//!   [`index_tail`].
//! - **Freeness**: [`cons_inj`], [`nil_ne_cons`].
//! - **Extensionality / reconstruction**: [`list_ext`], [`head_index0`],
//!   [`cons_head_tail`], [`nil_from_allnone`], [`allnone_from_head_none`].
//! - **Induction**: [`list_induct`] — `P nil ⟹ (∀x xs. P xs ⟹ P (cons x
//!   xs)) ⟹ ∀l. P l`, by a finiteness-bound `nat`-induction.
//!
//! The **recursion theorem**, the `list_foldr` discharge, and the
//! `foldr`/`length`/`cat` nil/cons recursion clauses are in
//! [`crate::init::list_recursion`] (the `list` [`Inductive`] adapter feeding
//! the generic engine). `list_foldl` / the `map`/`filter`/`flatten` clauses
//! remain — see `SKELETONS.md`.
//!
//! ## The `.cov` port
//!
//! [`list_env`] exposes the seam lemmas (element computations, freeness, and
//! the `foldr`/`length`/`cat` clauses) as `∀`-quantified GIVENS, and
//! `list.cov` (the [`cov`] module) re-exports them as first-class theorems
//! **and proves new list facts** over them — the append monoid laws
//! (`cat_nil_r`, `cat_assoc`), the length homomorphism (`length_cat`), and
//! `cat_cons_singleton` — by structural induction through the **`list-induct`
//! tactic** (registered in `core`, backed by the genuine [`list_induct`]).
//!
//! [`Inductive`]: crate::init::inductive::Inductive
//! [`init::nat`]: crate::init::nat

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;

use crate::init::eq::{beta_expand, trans_chain};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{exists_elim, exists_intro};
use crate::init::stream::{const_at, head_const, stream_at, stream_head, stream_mk, stream_tail};

// Re-export the `defs/list.rs` term catalogue (the `*_spec` handles stay
// in `covalence_hol_eval::defs`, reached via the blanket re-export there).
pub use covalence_hol_eval::defs::{
    cons, head, list, list_cat, list_filter, list_flatten, list_foldl, list_foldr, list_index,
    list_length, list_map, list_repeat, list_skip, list_take, nil, tail,
};

use covalence_hol_eval::defs::{
    finite, finite_spec, head_spec, list_index_spec, list_spec, nat_le, nat_rec, nat_succ, none,
    option, some, stream_const, tail_spec,
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

/// `succ n : nat`.
fn succ(n: Term) -> Term {
    Term::app(nat_succ(), n)
}

/// `λname:ty. body` — close the named free var, matching `hol::pub_abs`
/// (the binder convention `defs/list.rs` uses, so reconstructed terms
/// match `cons_body` exactly).
fn lam(name: &str, ty: Type, body: Term) -> Term {
    Term::abs(ty, covalence_core::subst::close(&body, name))
}

/// `rep xs : stream (option α)` — the carrier stream of a list.
fn rep_of(alpha: &Type, xs: &Term) -> Term {
    Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs.clone())
}

/// `streamMk g : stream (option α)`.
fn mk_stream(alpha: &Type, g: &Term) -> Term {
    Term::app(stream_mk(option(alpha.clone())), g.clone())
}

/// `⊢ natRec (some x) f 0 = some x` — the base equation of the cons
/// stream's underlying `natRec`, at the concrete `z = some x`, `f`. Uses
/// the polymorphic recursion theorem at result type `option α`.
fn nat_rec_zero(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let (z, f) = cons_rec_zf(alpha, x, xs);
    crate::init::recursion::rec_holds_proof_at(&option(alpha.clone()))?
        .all_elim(z)?
        .all_elim(f)?
        .and_elim_l()
}

/// `⊢ natRec (some x) f (succ k) = f k (natRec (some x) f k)` — the step
/// equation, at the concrete `z = some x`, `f`, result type `option α`.
fn nat_rec_succ(alpha: &Type, x: &Term, xs: &Term, k: &Term) -> Result<Thm> {
    let (z, f) = cons_rec_zf(alpha, x, xs);
    crate::init::recursion::rec_holds_proof_at(&option(alpha.clone()))?
        .all_elim(z)?
        .all_elim(f)?
        .and_elim_r()?
        .all_elim(k.clone())
}

/// The `(z, f)` pair of the cons-stream's `natRec`: `z = some x`,
/// `f = λk _. streamAt (rep xs) k`.
fn cons_rec_zf(alpha: &Type, x: &Term, xs: &Term) -> (Term, Term) {
    let opt = option(alpha.clone());
    let z = Term::app(some(alpha.clone()), x.clone());
    let rep_xs = rep_of(alpha, xs);
    let k = Term::free("k", nat());
    let at_k = Term::app(Term::app(stream_at(opt.clone()), rep_xs), k);
    let f = lam("k", nat(), Term::abs(opt, at_k));
    (z, f)
}

/// `streamAt (streamMk g) n` for the cons stream `g`.
fn at_mk_g(alpha: &Type, g: &Term, n: &Term) -> Term {
    Term::app(
        Term::app(stream_at(option(alpha.clone())), mk_stream(alpha, g)),
        n.clone(),
    )
}

/// From `tail : {body[N]} ⊢ ∀n. nat_le N n ⟹ streamAt (rep xs) n = none`,
/// derive `{body[N]} ⊢ ∀n. nat_le (succ N) n ⟹ streamAt (streamMk g) n =
/// none`, where `g = consStream x xs`. By case-analysis on `n` (via
/// `nat_induct`, IH unused): `n = 0` discharged by `not_succ_le_zero`;
/// `n = succ k` uses `le_succ_succ` to get `nat_le N k`, the cons-stream's
/// `succ` computation, and the tail body at `k`.
fn bound_all(alpha: &Type, x: &Term, xs: &Term, g: &Term, big_n: &Term, tail: &Thm) -> Result<Thm> {
    let opt = option(alpha.clone());
    let succ_n = succ(big_n.clone());

    // motive m ≔ nat_le (succ N) m ⟹ streamAt (streamMk g) m = none.
    let m = Term::free("m", nat());
    let motive_at = |t: &Term| -> Result<Term> {
        let le = Term::app(Term::app(nat_le(), succ_n.clone()), t.clone());
        let none_eq = at_mk_g(alpha, g, t).equals(none(alpha.clone()))?;
        le.imp(none_eq)
    };
    let motive = Term::abs(nat(), covalence_core::subst::close(&motive_at(&m)?, "m"));

    // base: motive 0 — premise `nat_le (succ N) 0` is absurd.
    let base = {
        let prem = Term::app(Term::app(nat_le(), succ_n.clone()), zero());
        let absurd = crate::init::nat::not_succ_le_zero()
            .all_elim(big_n.clone())? // ¬(nat_le (succ N) 0)
            .not_elim(Thm::assume(prem.clone())?)?; // {prem} ⊢ F
        let none_eq = at_mk_g(alpha, g, &zero()).equals(none(alpha.clone()))?;
        let body0 = absurd.false_elim(none_eq)?.imp_intro(&prem)?; // ⊢ motive-body[0]
        beta_expand(&motive, zero(), body0)? // ⊢ motive 0
    };

    // step: ∀k. motive k ⟹ motive (succ k) — IH unused.
    let step = {
        let k = Term::free("k", nat());
        let prem = Term::app(Term::app(nat_le(), succ_n.clone()), succ(k.clone()));
        // nat_le (succ N) (succ k) = nat_le N k, so {prem} ⊢ nat_le N k.
        let le_collapse = crate::init::nat::le_succ_succ()
            .all_elim(big_n.clone())?
            .all_elim(k.clone())?; // ⊢ (nat_le (succ N) (succ k)) = (nat_le N k)
        let le_n_k = le_collapse.eq_mp(Thm::assume(prem.clone())?)?; // {prem} ⊢ nat_le N k

        // streamAt (streamMk g) (succ k) = g (succ k) = streamAt (rep xs) k.
        let at_g = crate::init::stream::at_mk(&opt, g, &succ(k.clone()))?; // ⊢ streamAt (streamMk g) (succ k) = g (succ k)
        let g_succ = cons_stream_succ(alpha, x, xs, &k)?; // ⊢ g (succ k) = streamAt (rep xs) k
        // tail body at k: nat_le N k ⟹ streamAt (rep xs) k = none.
        let tail_k = tail.clone().all_elim(k.clone())?; // ⊢ nat_le N k ⟹ streamAt (rep xs) k = none
        let rep_none = tail_k.imp_elim(le_n_k)?; // {prem, body[N]} ⊢ streamAt (rep xs) k = none

        let chain = trans_chain([at_g, g_succ, rep_none])?; // {prem, body[N]} ⊢ streamAt (streamMk g) (succ k) = none
        let body_sk = chain.imp_intro(&prem)?; // {body[N]} ⊢ motive-body[succ k]

        // Re-wrap into applied `motive k ⟹ motive (succ k)`.
        let conseq = beta_expand(&motive, succ(k.clone()), body_sk)?; // {body[N]} ⊢ motive (succ k)
        let ante = Term::app(motive.clone(), k.clone());
        // Add the (unused) IH antecedent. `nat_induct` wants the bare
        // `motive k ⟹ motive (succ k)` (it ∀-closes internally).
        conseq.imp_intro(&ante)?
    };

    let all = crate::init::ext::nat_induct(base, step)?; // {body[N]} ⊢ ∀m. motive m
    // β-reduce the body so it reads as the `finite`-body at bound `succ N`.
    let inst = all.all_elim(m.clone())?;
    crate::init::eq::beta_reduce(inst)?.all_intro("m", nat())
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

/// The list selector predicate `λs. finite s ∧ contiguous s`,
/// instantiated at `alpha` (the `list_spec` `tm`, with the generic `a`
/// replaced by `alpha`).
fn list_pred_op(alpha: &Type) -> Term {
    let poly = list_spec()
        .tm()
        .expect("list_spec carries a selector predicate")
        .clone();
    covalence_core::subst::subst_tfree_in_term(&poly, "a", alpha)
}

/// `list_predicate s` (applied form) — the subtype premise the kernel's
/// `spec_rep_abs_fwd` discharges.
fn list_pred(alpha: &Type, s: &Term) -> Term {
    Term::app(list_pred_op(alpha), s.clone())
}

/// `⊢ list_predicate s` from `fin : ⊢ finite s` and `contig : ⊢ ∀i.
/// streamAt s i = none ⟹ streamAt s (succ i) = none` — assemble the two
/// selector conjuncts and β-fold into the applied predicate.
fn prove_list_pred(alpha: &Type, s: &Term, fin: Thm, contig: Thm) -> Result<Thm> {
    let conj = fin.and_intro(contig)?; // ⊢ finite s ∧ contiguous s
    beta_expand(&list_pred_op(alpha), s.clone(), conj) // ⊢ list_predicate s
}

/// `⊢ rep (abs s) = s`, given `pred : ⊢ list_predicate s` — the
/// carrier-side round-trip for `list`, with the (now finite-∧-contiguous)
/// subtype premise discharged. From the kernel's conditional
/// [`Thm::spec_rep_abs_fwd`].
fn rep_abs_pred(alpha: &Type, s: &Term, pred: Thm) -> Result<Thm> {
    Thm::spec_rep_abs_fwd(list_spec(), vec![alpha.clone()], s.clone())?.imp_elim(pred)
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

/// `⊢ ∀i. streamAt (streamConst none) i = none ⟹ streamAt (streamConst
/// none) (succ i) = none` — the everywhere-`none` stream is contiguous
/// (the consequent holds outright, by [`const_at`]).
fn contig_const_none(alpha: &Type) -> Result<Thm> {
    let opt = option(alpha.clone());
    let i = Term::free("i", nat());
    let at_i = const_at(&opt, &none(alpha.clone()), &i)?; // streamAt cst i = none
    let at_si = const_at(&opt, &none(alpha.clone()), &succ(i.clone()))?; // streamAt cst (succ i) = none
    // The consequent holds unconditionally, so imp_intro the antecedent.
    let ante = at_i.concl().clone();
    at_si.imp_intro(&ante)?.all_intro("i", nat())
}

/// `⊢ list_predicate (streamConst none)` — `nil`'s carrier stream
/// satisfies the full list selector (finite ∧ contiguous).
pub fn pred_const_none(alpha: &Type) -> Result<Thm> {
    prove_list_pred(
        alpha,
        &const_none(alpha),
        finite_const_none(alpha)?,
        contig_const_none(alpha)?,
    )
}

/// `⊢ ∃s. list_predicate s` — the list selector predicate is inhabited
/// (witness `streamConst none`). The non-emptiness fact the subtype's
/// witness-free back-direction law ([`Thm::spec_rep_abs_back`]) needs to
/// recover `list_predicate (rep xs)` for an arbitrary `xs : list α`.
pub fn pred_nonempty(alpha: &Type) -> Result<Thm> {
    exists_intro(
        list_pred_op(alpha),
        const_none(alpha),
        pred_const_none(alpha)?,
    )
}

/// `⊢ list_predicate (rep xs)` for any `xs : list α` — the carrier stream
/// behind a list satisfies the full list selector (finite ∧ contiguous).
/// Derived without a hypothesis: instantiate the witness-free back-law
/// [`Thm::spec_rep_abs_back`] at `a := rep xs`, discharge its premise
/// `rep (abs (rep xs)) = rep xs` via the unconditional `abs (rep xs) = xs`
/// ([`Thm::spec_abs_rep`]), then kill the spurious `¬∃s. list_predicate s`
/// disjunct with [`pred_nonempty`].
pub fn pred_rep(alpha: &Type, xs: &Term) -> Result<Thm> {
    let rep = Term::spec_rep(list_spec(), vec![alpha.clone()]);
    let rep_xs = Term::app(rep.clone(), xs.clone());

    // back: ⊢ rep (abs (rep xs)) = rep xs ⟹ (P (rep xs) ∨ ¬∃x. P x)
    let back = Thm::spec_rep_abs_back(list_spec(), vec![alpha.clone()], rep_xs.clone())?;

    // Premise: rep (abs (rep xs)) = rep xs, from abs (rep xs) = xs by cong.
    let abs_rep = Thm::spec_abs_rep(list_spec(), vec![alpha.clone()], xs.clone())?; // abs (rep xs) = xs
    let prem = abs_rep.cong_arg(rep)?; // rep (abs (rep xs)) = rep xs
    let disj = back.imp_elim(prem)?; // P (rep xs) ∨ ¬∃x. P x

    // Eliminate the disjunction. Left: the goal `P (rep xs)` directly.
    // Right: the negated existential contradicts `pred_nonempty`.
    let goal = list_pred(alpha, &rep_xs); // list_predicate (rep xs)

    // Peel the right disjunct `¬(∃x. P x)` from `disj`, exactly as the
    // kernel built it (η-expanded predicate), and re-prove that `∃` with a
    // matching witness so `not_elim` sees identical terms.
    let not_some = disj.concl().as_app().ok_or(Error::NotAnEquation)?.1.clone(); // ¬∃x. P x
    let some_x = not_some.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // ∃x. P x
    let pred_eta = some_x.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λx. P x

    // ⊢ ∃x. P x via witness `streamConst none`.
    let cst = const_none(alpha);
    let at_w = beta_expand(&pred_eta, cst.clone(), pred_const_none(alpha)?)?; // ⊢ (λx. P x) (streamConst none)
    let some_proof = exists_intro(pred_eta, cst, at_w)?; // ⊢ ∃x. P x

    let left = Thm::assume(goal.clone())?.imp_intro(&goal)?; // ⊢ P (rep xs) ⟹ goal
    let contra = Thm::assume(not_some.clone())?.not_elim(some_proof)?; // {¬∃x} ⊢ F
    let right = contra.false_elim(goal.clone())?.imp_intro(&not_some)?; // ⊢ ¬∃x ⟹ goal
    disj.or_elim(left, right)
}

/// `⊢ finite (rep xs)` for any `xs : list α` — extracted from
/// [`pred_rep`] (the first conjunct of the list selector).
pub fn finite_rep(alpha: &Type, xs: &Term) -> Result<Thm> {
    // Unfold `list_predicate (rep xs)` to `finite (rep xs) ∧ contiguous`.
    let conj = beta_reduce_pred(alpha, pred_rep(alpha, xs)?)?;
    conj.and_elim_l()
}

/// `⊢ ∀i. streamAt (rep xs) i = none ⟹ streamAt (rep xs) (succ i) = none`
/// — the contiguity of a list's carrier stream (second conjunct of the
/// selector), extracted from [`pred_rep`].
pub fn contig_rep(alpha: &Type, xs: &Term) -> Result<Thm> {
    let conj = beta_reduce_pred(alpha, pred_rep(alpha, xs)?)?;
    conj.and_elim_r()
}

/// β-reduce `⊢ list_predicate s` to `⊢ finite s ∧ contiguous s`.
fn beta_reduce_pred(_alpha: &Type, pred: Thm) -> Result<Thm> {
    crate::init::eq::beta_reduce(pred)
}

// ============================================================================
// The `cons` carrier stream and its finiteness.
//
//   cons x xs = abs (streamMk (consStream x xs))
//   consStream x xs = λn. natRec (some x) (λk _. streamAt (rep xs) k) n
//
// so the cons-stream is `some x` at index 0 and `(rep xs)` shifted up by
// one afterwards. `finite (consStream x xs)` follows from `finite (rep xs)`
// by bumping the witness bound `N ↦ succ N` (the order step `nat_le N k`
// from `nat_le (succ N) (succ k)`).
// ============================================================================

/// `λn. natRec (some x) (λk _. streamAt (rep xs) k) n` — the carrier
/// stream behind `cons x xs`, as a builder (matches `cons_body` in
/// `defs/list.rs`).
fn cons_stream(alpha: &Type, x: &Term, xs: &Term) -> Term {
    let opt = option(alpha.clone());
    let rep_xs = Term::app(Term::spec_rep(list_spec(), vec![alpha.clone()]), xs.clone());
    let k = Term::free("k", nat());
    let at_k = Term::app(Term::app(stream_at(opt.clone()), rep_xs), k);
    let f = lam("k", nat(), Term::abs(opt.clone(), at_k));
    let n = Term::free("n", nat());
    let some_x = Term::app(some(alpha.clone()), x.clone());
    let rec = Term::app(Term::app(Term::app(nat_rec(opt), some_x), f), n);
    lam("n", nat(), rec)
}

/// `⊢ consStream x xs 0 = some x` — the cons-stream's head value, by the
/// `natRec` base equation.
fn cons_stream_zero(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    // (λn. natRec (some x) f n) 0 = natRec (some x) f 0 = some x.
    let g = cons_stream(alpha, x, xs);
    let applied = Term::app(g, zero()); // (λn. …) 0
    let beta = applied.reduce()?; // ⊢ (λn. natRec … n) 0 = natRec … 0
    let base = nat_rec_zero(alpha, x, xs)?; // ⊢ natRec … 0 = some x
    beta.trans(base)
}

/// `⊢ consStream x xs (succ k) = streamAt (rep xs) k` — the cons-stream's
/// tail value at `succ k`, by the `natRec` step equation.
fn cons_stream_succ(alpha: &Type, x: &Term, xs: &Term, k: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let g = cons_stream(alpha, x, xs);
    let applied = Term::app(g, succ(k.clone())); // (λn. …) (succ k)
    let beta = applied.reduce()?; // ⊢ … = natRec … (succ k)
    let step = nat_rec_succ(alpha, x, xs, k)?; // ⊢ natRec … (succ k) = (λk _. streamAt (rep xs) k) k (natRec … k)
    let rhs = rhs_of(&step)?.reduce()?; // β: collapse to streamAt (rep xs) k
    let _ = opt;
    trans_chain([beta, step, rhs])
}

/// `⊢ finite (consStream x xs)`, for any `xs : list α`. From
/// [`finite_rep`] (the tail is finite at bound `N`): the cons-stream is
/// `none` at every `n ≥ succ N`, because for such `n = succ k` with
/// `k ≥ N` the value is `streamAt (rep xs) k = none`.
pub fn finite_cons(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let g = cons_stream(alpha, x, xs);

    // From `finite (rep xs)`, peel its bound `N` with the eventually-none body.
    let fin_rep = finite_rep(alpha, xs)?; // ⊢ finite (rep xs)
    let unfold = Term::app(finite(alpha.clone()), rep_of(alpha, xs))
        .delta_all(finite_spec().symbol())?
        .rhs_conv(|t| t.reduce())?; // ⊢ finite (rep xs) = (∃N. ∀n. nat_le N n ⟹ streamAt (rep xs) n = none)
    let ex = unfold.clone().eq_mp(fin_rep)?; // ⊢ ∃N. body[N]

    // Goal: ∃M. ∀n. nat_le M n ⟹ streamAt (streamMk g) n = none, i.e.
    // `finite (streamMk g)`. We pick M := succ N inside the ∃-elim.
    let goal_finite = Term::app(finite(alpha.clone()), mk_stream(alpha, &g));
    let goal_unfold = goal_finite
        .clone()
        .delta_all(finite_spec().symbol())?
        .rhs_conv(|t| t.reduce())?; // ⊢ finite (streamMk g) = (∃M. …)
    let goal_ex = rhs_of(&goal_unfold)?; // ∃M. ∀n. nat_le M n ⟹ streamAt (streamMk g) n = none

    // exists_elim over `ex`: assume the *applied* hypothesis `pred N`
    // (`exists_elim` matches the antecedent in applied form), β-reduce it
    // to the readable `body[N]` to do the work.
    let big_n = Term::free("N", nat());
    let ex_pred = ex.concl().as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λN. body[N]
    let applied_hyp = Term::app(ex_pred.clone(), big_n.clone()); // (λN. body) N
    let assumed = crate::init::eq::beta_reduce(Thm::assume(applied_hyp.clone())?)?; // {pred N} ⊢ body[N]

    // Build `∀n. nat_le (succ N) n ⟹ streamAt (streamMk g) n = none` under the assumption.
    let body_at_succ_n = bound_all(alpha, x, xs, &g, &big_n, &assumed)?;

    // ∃M-introduce at M := succ N, then bridge back to `finite (streamMk g)`.
    let goal_pred = goal_ex.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λM. …
    let at_pred = beta_expand(&goal_pred, succ(big_n.clone()), body_at_succ_n)?; // {pred N} ⊢ goal_pred (succ N)
    let ex_m = exists_intro(goal_pred, succ(big_n.clone()), at_pred)?; // {pred N} ⊢ ∃M. …

    // Discharge the `∃N. pred N` with exists_elim (applied antecedent).
    let step = ex_m.imp_intro(&applied_hyp)?.all_intro("N", nat())?; // ⊢ ∀N. pred N ⟹ (∃M. …)
    let _ = opt;
    let got_ex = exists_elim(ex, goal_ex, step)?; // ⊢ ∃M. …
    goal_unfold.sym()?.eq_mp(got_ex) // ⊢ finite (streamMk g)
}

/// `⊢ ∀i. streamAt (streamMk g) i = none ⟹ streamAt (streamMk g) (succ i)
/// = none`, where `g = consStream x xs` — the cons stream is **contiguous**
/// (preserves the tail's contiguity). By case analysis on `i` (via
/// `nat_induct`, IH unused): at `i = 0` the head is `some x ≠ none` so the
/// antecedent is absurd; at `i = succ k` it reduces to the tail's
/// contiguity ([`contig_rep`]) at `k`.
pub fn contig_cons(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let g = cons_stream(alpha, x, xs);

    // motive i ≔ streamAt (streamMk g) i = none ⟹ streamAt (streamMk g) (succ i) = none.
    let iv = Term::free("i", nat());
    let motive_at = |t: &Term| -> Result<Term> {
        let at_t = at_mk_g(alpha, &g, t).equals(none(alpha.clone()))?;
        let at_st = at_mk_g(alpha, &g, &succ(t.clone())).equals(none(alpha.clone()))?;
        at_t.imp(at_st)
    };
    let motive = Term::abs(nat(), covalence_core::subst::close(&motive_at(&iv)?, "i"));

    // base i=0: streamAt (streamMk g) 0 = some x ≠ none, so the antecedent
    // is refutable; discharge vacuously.
    let base = {
        let at0 = crate::init::stream::at_mk(&opt, &g, &zero())?; // streamAt (streamMk g) 0 = g 0
        let g0 = cons_stream_zero(alpha, x, xs)?; // g 0 = some x
        let at0_some = at0.trans(g0)?; // streamAt (streamMk g) 0 = some x
        let prem = at_mk_g(alpha, &g, &zero()).equals(none(alpha.clone()))?; // streamAt (streamMk g) 0 = none
        // {prem} ⊢ some x = none, contradiction.
        let some_none = at0_some.sym()?.trans(Thm::assume(prem.clone())?)?; // {prem} ⊢ some x = none
        let f = crate::init::option::some_ne_none(alpha, x)?.not_elim(some_none)?; // {prem} ⊢ F
        let conseq = at_mk_g(alpha, &g, &succ(zero())).equals(none(alpha.clone()))?;
        let body0 = f.false_elim(conseq)?.imp_intro(&prem)?;
        beta_expand(&motive, zero(), body0)?
    };

    // step k: assume streamAt (streamMk g) (succ k) = none; show streamAt
    // (streamMk g) (succ (succ k)) = none. Reduce both to `rep xs` via the
    // cons-stream `succ` computation, then use `contig_rep` at `k`. IH unused.
    let step = {
        let k = Term::free("k", nat());
        // streamAt (streamMk g) (succ k) = streamAt (rep xs) k.
        let lhs_eq = trans_chain([
            crate::init::stream::at_mk(&opt, &g, &succ(k.clone()))?, // = g (succ k)
            cons_stream_succ(alpha, x, xs, &k)?,                     // = streamAt (rep xs) k
        ])?;
        // streamAt (streamMk g) (succ (succ k)) = streamAt (rep xs) (succ k).
        let rhs_eq = trans_chain([
            crate::init::stream::at_mk(&opt, &g, &succ(succ(k.clone())))?, // = g (succ (succ k))
            cons_stream_succ(alpha, x, xs, &succ(k.clone()))?, // = streamAt (rep xs) (succ k)
        ])?;
        let prem = at_mk_g(alpha, &g, &succ(k.clone())).equals(none(alpha.clone()))?;
        // {prem} ⊢ streamAt (rep xs) k = none.
        let rep_k_none = lhs_eq.sym()?.trans(Thm::assume(prem.clone())?)?;
        // contig_rep at k: streamAt (rep xs) k = none ⟹ streamAt (rep xs) (succ k) = none.
        let contig_k = contig_rep(alpha, xs)?.all_elim(k.clone())?;
        let rep_sk_none = contig_k.imp_elim(rep_k_none)?; // {prem} ⊢ streamAt (rep xs) (succ k) = none
        // streamAt (streamMk g) (succ (succ k)) = none.
        let conseq = rhs_eq.trans(rep_sk_none)?;
        let body_sk = conseq.imp_intro(&prem)?; // {} ⊢ motive-body[succ k]
        let conseq_wrap = beta_expand(&motive, succ(k.clone()), body_sk)?; // ⊢ motive (succ k)
        let ante = Term::app(motive.clone(), k.clone());
        conseq_wrap.imp_intro(&ante)? // motive k ⟹ motive (succ k)
    };

    let all = crate::init::ext::nat_induct(base, step)?; // ⊢ ∀i. motive i
    crate::init::eq::beta_reduce(all.all_elim(iv.clone())?)?.all_intro("i", nat())
}

/// `⊢ list_predicate (streamMk (consStream x xs))` — the cons carrier
/// stream satisfies the full list selector (finite ∧ contiguous), for any
/// `xs : list α`. The premise `rep_cons` discharges.
pub fn pred_cons(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let g = cons_stream(alpha, x, xs);
    let made = mk_stream(alpha, &g);
    prove_list_pred(
        alpha,
        &made,
        finite_cons(alpha, x, xs)?,
        contig_cons(alpha, x, xs)?,
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
    let ra = rep_abs_pred(alpha, &cst, pred_const_none(alpha)?)?;
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
    let ra = rep_abs_pred(alpha, &cst, pred_const_none(alpha)?)?; // rep (abs cst) = cst
    let head_c = head_const(&opt, &none(alpha.clone()))?; // streamHead cst = none

    h.rhs_conv(|t| t.rw_all(&nil_u))?
        .rhs_conv(|t| t.rw_all(&ra))?
        .trans(head_c)
}

// ============================================================================
// `cons`-side element access.
// ============================================================================

/// `⊢ rep (cons x xs) = streamMk (consStream x xs)` — the carrier stream
/// behind `cons x xs`, with the list selector discharged by [`pred_cons`].
fn rep_cons(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let g = cons_stream(alpha, x, xs);
    let made = mk_stream(alpha, &g);
    // cons x xs = abs (streamMk g)  (δ-unfold the cons head, β the spine).
    let cons_u = crate::init::eq::delta_head(&Term::app(
        Term::app(cons(alpha.clone()), x.clone()),
        xs.clone(),
    ))?
    .rhs_conv(|t| t.reduce())?; // ⊢ cons x xs = abs (streamMk g)
    // rep (abs (streamMk g)) = streamMk g
    let ra = rep_abs_pred(alpha, &made, pred_cons(alpha, x, xs)?)?;
    // rep (cons x xs) = rep (abs (streamMk g)) = streamMk g
    let rep = Term::spec_rep(list_spec(), vec![alpha.clone()]);
    cons_u.cong_arg(rep)?.trans(ra)
}

/// `⊢ list.index 0 (cons x xs) = some x` — the head element of a
/// non-empty list. Genuine: hypothesis- and oracle-free.
pub fn index_cons_zero(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let g = cons_stream(alpha, x, xs);

    // listIndex 0 (cons x xs) = streamAt (rep (cons x xs)) 0
    let idx = index_unfold(
        alpha,
        &zero(),
        &cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?,
    )?;
    let rc = rep_cons(alpha, x, xs)?; // rep (cons x xs) = streamMk g
    let at_g = crate::init::stream::at_mk(&opt, &g, &zero())?; // streamAt (streamMk g) 0 = g 0
    let g0 = cons_stream_zero(alpha, x, xs)?; // g 0 = some x

    idx.rhs_conv(|t| t.rw_all(&rc))? // streamAt (streamMk g) 0
        .trans(at_g)? // = g 0
        .trans(g0) // = some x
}

/// `⊢ list.index (succ k) (cons x xs) = list.index k xs` — indexing past
/// the head recurses into the tail (the `cons`-side recursor equation for
/// indexing). Genuine: hypothesis- and oracle-free.
pub fn index_cons_succ(alpha: &Type, x: &Term, xs: &Term, k: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let g = cons_stream(alpha, x, xs);

    // listIndex (succ k) (cons x xs) = streamAt (rep (cons x xs)) (succ k)
    let idx = index_unfold(
        alpha,
        &succ(k.clone()),
        &cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?,
    )?;
    let rc = rep_cons(alpha, x, xs)?; // rep (cons x xs) = streamMk g
    let at_g = crate::init::stream::at_mk(&opt, &g, &succ(k.clone()))?; // streamAt (streamMk g) (succ k) = g (succ k)
    let gk = cons_stream_succ(alpha, x, xs, k)?; // g (succ k) = streamAt (rep xs) k
    // streamAt (rep xs) k = list.index k xs (the unfold, reversed).
    let unfold_k = index_unfold(alpha, k, xs)?.sym()?; // streamAt (rep xs) k = list.index k xs

    trans_chain([
        idx.rhs_conv(|t| t.rw_all(&rc))?, // = streamAt (streamMk g) (succ k)
        at_g,                             // = g (succ k)
        gk,                               // = streamAt (rep xs) k
        unfold_k,                         // = list.index k xs
    ])
}

/// `⊢ list.head (cons x xs) = some x` — the head of a non-empty list.
/// Genuine: hypothesis- and oracle-free.
pub fn head_cons(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let g = cons_stream(alpha, x, xs);
    let consed = cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?;

    // head (cons x xs) = streamHead (rep (cons x xs))
    let h = Term::app(head(alpha.clone()), consed)
        .delta_all(head_spec().symbol())?
        .rhs_conv(|t| t.reduce())?;
    let rc = rep_cons(alpha, x, xs)?; // rep (cons x xs) = streamMk g
    // streamHead (streamMk g) = streamAt (streamMk g) 0 = g 0 = some x.
    let head_eq =
        crate::init::eq::delta_head(&Term::app(stream_head(opt.clone()), mk_stream(alpha, &g)))?
            .rhs_conv(|t| t.reduce())?; // streamHead (streamMk g) = streamAt (streamMk g) 0
    let at_g = crate::init::stream::at_mk(&opt, &g, &zero())?; // streamAt (streamMk g) 0 = g 0
    let g0 = cons_stream_zero(alpha, x, xs)?; // g 0 = some x

    trans_chain([
        h.rhs_conv(|t| t.rw_all(&rc))?, // streamHead (streamMk g)
        head_eq,                        // = streamAt (streamMk g) 0
        at_g,                           // = g 0
        g0,                             // = some x
    ])
}

/// `⊢ tail (cons x xs) = xs` — dropping the head of `cons x xs` recovers
/// `xs` (the `cons`-side recursor equation for `tail`). Genuine:
/// hypothesis- and oracle-free. Proved through **stream extensionality**:
/// the tail of the cons carrier stream is pointwise equal to `rep xs`.
pub fn tail_cons(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let g = cons_stream(alpha, x, xs);
    let made = mk_stream(alpha, &g);
    let consed = cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?;

    // tail (cons x xs) = abs (streamTail (rep (cons x xs)))  (δ-unfold tail).
    let tail_u = Term::app(tail(alpha.clone()), consed)
        .delta_all(tail_spec().symbol())?
        .rhs_conv(|t| t.reduce())?; // ⊢ tail (cons x xs) = abs (streamTail (rep (cons x xs)))

    // streamTail (rep (cons x xs)) = streamTail (streamMk g) via rep_cons.
    let rc = rep_cons(alpha, x, xs)?; // rep (cons x xs) = streamMk g
    let tail_stream_eq = rc.cong_arg(stream_tail(opt.clone()))?; // streamTail (rep (cons x xs)) = streamTail (streamMk g)

    // Pointwise: streamAt (streamTail (streamMk g)) n = streamAt (rep xs) n.
    let n = Term::free("n", nat());
    let tail_at = crate::init::stream::tail_at(&opt, &made, &n)?; // streamAt (streamTail (streamMk g)) n = streamAt (streamMk g) (succ n)
    let at_g = crate::init::stream::at_mk(&opt, &g, &succ(n.clone()))?; // streamAt (streamMk g) (succ n) = g (succ n)
    let g_succ = cons_stream_succ(alpha, x, xs, &n)?; // g (succ n) = streamAt (rep xs) n
    let pointwise = trans_chain([tail_at, at_g, g_succ])?; // ⊢ streamAt (streamTail (streamMk g)) n = streamAt (rep xs) n

    // Stream extensionality: streamTail (streamMk g) = rep xs.
    let tailed = Term::app(stream_tail(opt.clone()), made);
    let streams_eq = crate::init::stream::ext(&opt, &tailed, &rep_of(alpha, xs), "n", pointwise)?; // streamTail (streamMk g) = rep xs

    // abs (streamTail (rep (cons x xs))) = abs (streamTail (streamMk g))
    //                                    = abs (rep xs) = xs.
    let abs = Term::spec_abs(list_spec(), vec![alpha.clone()]);
    let abs_eq = tail_stream_eq.trans(streams_eq)?.cong_arg(abs)?; // abs (streamTail (rep (cons x xs))) = abs (rep xs)
    let abs_rep = Thm::spec_abs_rep(list_spec(), vec![alpha.clone()], xs.clone())?; // abs (rep xs) = xs

    tail_u.trans(abs_eq)?.trans(abs_rep)
}

// ============================================================================
// `index`/`tail` interplay + the `nil` characterization — the pieces the
// list induction principle is assembled from.
// ============================================================================

/// `⊢ list.index i (tail l) = list.index (succ i) l` — indexing the tail
/// shifts up by one. Genuine: hypothesis- and oracle-free.
pub fn index_tail(alpha: &Type, i: &Term, l: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let tailed = Term::app(tail(alpha.clone()), l.clone());

    // index i (tail l) = streamAt (rep (tail l)) i.
    let idx = index_unfold(alpha, i, &tailed)?;
    // rep (tail l) = streamTail (rep l): tail l = abs (streamTail (rep l)),
    // and rep collapses through the (finite ∧ contiguous) round-trip.
    let rt = rep_tail(alpha, l)?; // rep (tail l) = streamTail (rep l)
    // streamAt (streamTail (rep l)) i = streamAt (rep l) (succ i).
    let shift = crate::init::stream::tail_at(&opt, &rep_of(alpha, l), i)?;
    // streamAt (rep l) (succ i) = index (succ i) l (reverse unfold).
    let unfold = index_unfold(alpha, &succ(i.clone()), l)?.sym()?;

    trans_chain([
        idx.rhs_conv(|t| t.rw_all(&rt))?, // streamAt (streamTail (rep l)) i
        shift,                            // = streamAt (rep l) (succ i)
        unfold,                           // = index (succ i) l
    ])
}

/// `⊢ rep (tail l) = streamTail (rep l)` — the carrier stream of `tail l`,
/// with the list selector for `streamTail (rep l)` discharged by
/// [`pred_streamtail`].
fn rep_tail(alpha: &Type, l: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let st = Term::app(stream_tail(opt.clone()), rep_of(alpha, l));
    // tail l = abs (streamTail (rep l))  (δ-unfold the tail head, β the spine).
    let tail_u = Term::app(tail(alpha.clone()), l.clone())
        .delta_all(tail_spec().symbol())?
        .rhs_conv(|t| t.reduce())?; // tail l = abs (streamTail (rep l))
    let ra = rep_abs_pred(alpha, &st, pred_streamtail(alpha, l)?)?; // rep (abs (streamTail (rep l))) = streamTail (rep l)
    let rep = Term::spec_rep(list_spec(), vec![alpha.clone()]);
    tail_u.cong_arg(rep)?.trans(ra)
}

/// `⊢ list_predicate (streamTail (rep l))` — the tail of a list's carrier
/// is itself a list-carrier (finite ∧ contiguous), for any `l : list α`.
fn pred_streamtail(alpha: &Type, l: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let repl = rep_of(alpha, l);
    let st = Term::app(stream_tail(opt.clone()), repl.clone());

    // Contiguity: ∀i. streamAt (streamTail (rep l)) i = none ⟹ ... (succ i) = none.
    // `streamAt (streamTail (rep l)) i = streamAt (rep l) (succ i)`, so this is
    // exactly `contig_rep l` at `succ i`.
    let contig = {
        let i = Term::free("i", nat());
        let at_i = crate::init::stream::tail_at(&opt, &repl, &i)?; // streamAt (streamTail (rep l)) i = streamAt (rep l) (succ i)
        let at_si = crate::init::stream::tail_at(&opt, &repl, &succ(i.clone()))?; // ... (succ i) = streamAt (rep l) (succ (succ i))
        let contig_si = contig_rep(alpha, l)?.all_elim(succ(i.clone()))?; // streamAt (rep l)(succ i)=none ⟹ streamAt (rep l)(succ(succ i))=none
        // Rewrite antecedent/consequent through the tail_at equations.
        let prem = at_i
            .concl()
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .0
            .clone()
            .equals(none(alpha.clone()))?;
        let h = Thm::assume(prem.clone())?; // streamAt (streamTail (rep l)) i = none
        let rep_si_none = at_i.sym()?.trans(h)?; // streamAt (rep l)(succ i) = none
        let rep_ssi_none = contig_si.imp_elim(rep_si_none)?; // streamAt (rep l)(succ(succ i)) = none
        let tail_si_none = at_si.trans(rep_ssi_none)?; // streamAt (streamTail (rep l))(succ i) = none
        tail_si_none.imp_intro(&prem)?.all_intro("i", nat())?
    };

    // Finite: ∃M. ∀n. nat_le M n ⟹ streamAt (streamTail (rep l)) n = none.
    // Use the same bound `N` as `rep l`: streamAt (streamTail (rep l)) n =
    // streamAt (rep l) (succ n), and `nat_le N n ⟹ nat_le N (succ n)`.
    let finite = finite_streamtail(alpha, l)?;

    prove_list_pred(alpha, &st, finite, contig)
}

/// `⊢ finite (streamTail (rep l))`.
fn finite_streamtail(alpha: &Type, l: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    let repl = rep_of(alpha, l);
    let st = Term::app(stream_tail(opt.clone()), repl.clone());

    // From `finite (rep l)`, peel its bound N.
    let fin = finite_rep(alpha, l)?;
    let unfold = Term::app(finite(alpha.clone()), repl.clone())
        .delta_all(finite_spec().symbol())?
        .rhs_conv(|t| t.reduce())?;
    let ex = unfold.eq_mp(fin)?; // ∃N. ∀n. nat_le N n ⟹ streamAt (rep l) n = none

    let goal_finite = Term::app(finite(alpha.clone()), st.clone());
    let goal_unfold = goal_finite
        .delta_all(finite_spec().symbol())?
        .rhs_conv(|t| t.reduce())?;
    let goal_ex = rhs_of(&goal_unfold)?; // ∃M. ∀n. nat_le M n ⟹ streamAt (streamTail (rep l)) n = none

    let big_n = Term::free("N", nat());
    let ex_pred = ex.concl().as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let applied_hyp = Term::app(ex_pred, big_n.clone());
    let assumed = crate::init::eq::beta_reduce(Thm::assume(applied_hyp.clone())?)?; // {pred N} ⊢ ∀n. nat_le N n ⟹ streamAt (rep l) n = none

    // Build ∀n. nat_le N n ⟹ streamAt (streamTail (rep l)) n = none (same bound N).
    let n = Term::free("n", nat());
    let tail_at = crate::init::stream::tail_at(&opt, &repl, &n)?; // streamAt (streamTail (rep l)) n = streamAt (rep l) (succ n)
    // nat_le N n ⟹ nat_le N (succ n): from le_succ_self + transitivity.
    let le_n = Term::app(Term::app(nat_le(), big_n.clone()), n.clone());
    let h_le = Thm::assume(le_n.clone())?;
    let n_le_sn = crate::init::nat::le_succ_self().all_elim(n.clone())?; // nat_le n (succ n)
    let le_n_sn = crate::init::nat::le_trans()
        .all_elim(big_n.clone())?
        .all_elim(n.clone())?
        .all_elim(succ(n.clone()))?
        .imp_elim(h_le.clone())?
        .imp_elim(n_le_sn)?; // {nat_le N n} ⊢ nat_le N (succ n)
    let body_sn = assumed.all_elim(succ(n.clone()))?.imp_elim(le_n_sn)?; // {pred N, nat_le N n} ⊢ streamAt (rep l)(succ n)=none
    let tail_none = tail_at.trans(body_sn)?; // streamAt (streamTail (rep l)) n = none
    let body = tail_none.imp_intro(&le_n)?.all_intro("n", nat())?; // {pred N} ⊢ ∀n. nat_le N n ⟹ ...

    let goal_pred = goal_ex.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let at_pred = beta_expand(&goal_pred, big_n.clone(), body)?;
    let ex_m = exists_intro(goal_pred, big_n.clone(), at_pred)?; // {pred N} ⊢ ∃M. …
    let step = ex_m.imp_intro(&applied_hyp)?.all_intro("N", nat())?;
    let got_ex = exists_elim(ex, goal_ex, step)?;
    goal_unfold.sym()?.eq_mp(got_ex)
}

/// `⊢ list.head l = list.index 0 l` — the head is the 0-th element.
/// Genuine: hypothesis- and oracle-free.
pub fn head_index0(alpha: &Type, l: &Term) -> Result<Thm> {
    let opt = option(alpha.clone());
    // head l = streamHead (rep l) = streamAt (rep l) 0.
    let h = Term::app(head(alpha.clone()), l.clone())
        .delta_all(head_spec().symbol())?
        .rhs_conv(|t| t.reduce())?; // head l = streamHead (rep l)
    let head_at =
        crate::init::eq::delta_head(&Term::app(stream_head(opt.clone()), rep_of(alpha, l)))?
            .rhs_conv(|t| t.reduce())?; // streamHead (rep l) = streamAt (rep l) 0
    // index 0 l = streamAt (rep l) 0  (reverse unfold).
    let idx = index_unfold(alpha, &zero(), l)?.sym()?; // streamAt (rep l) 0 = index 0 l
    trans_chain([h, head_at, idx])
}

/// `⊢ head l = some a ⟹ cons a (tail l) = l` — **list reconstruction**:
/// a list whose head is `some a` is `cons a` of its tail. Genuine:
/// hypothesis- and oracle-free. Proved by [`list_ext`]: indexing
/// `cons a (tail l)` matches `l` at every position (head at `0` via the
/// hypothesis + [`head_index0`], the rest via [`index_cons_succ`] +
/// [`index_tail`]).
pub fn cons_head_tail(alpha: &Type, a: &Term, l: &Term) -> Result<Thm> {
    let some_a = Term::app(some(alpha.clone()), a.clone());
    let hyp = Term::app(head(alpha.clone()), l.clone()).equals(some_a.clone())?; // head l = some a
    let h = Thm::assume(hyp.clone())?;

    let tl = Term::app(tail(alpha.clone()), l.clone());
    let consed = cons(alpha.clone()).apply(a.clone())?.apply(tl.clone())?;

    // Pointwise `index i (cons a (tail l)) = index i l`, by cases on i.
    let iv = Term::free("i", nat());
    let motive_at =
        |t: &Term| -> Result<Term> { index(alpha, t, &consed).equals(index(alpha, t, l)) };
    let motive = Term::abs(nat(), covalence_core::subst::close(&motive_at(&iv)?, "i"));

    // base i=0: index 0 (cons a (tail l)) = some a = head l = index 0 l.
    let base = {
        let cz = index_cons_zero(alpha, a, &tl)?; // index 0 (cons a (tail l)) = some a
        let head0 = head_index0(alpha, l)?; // head l = index 0 l
        // some a = head l (from hyp, reversed), then = index 0 l.
        let eq0 = cz.trans(h.clone().sym()?)?.trans(head0)?; // {hyp} ⊢ index 0 (...) = index 0 l
        beta_expand(&motive, zero(), eq0)?
    };

    // step k: index (succ k) (cons a (tail l)) = index k (tail l) = index (succ k) l. IH unused.
    let step = {
        let k = Term::free("k", nat());
        let cs = index_cons_succ(alpha, a, &tl, &k)?; // index (succ k) (cons a (tail l)) = index k (tail l)
        let it = index_tail(alpha, &k, l)?; // index k (tail l) = index (succ k) l
        let eq_sk = cs.trans(it)?; // index (succ k) (...) = index (succ k) l
        let conseq = beta_expand(&motive, succ(k.clone()), eq_sk)?; // ⊢ motive (succ k)
        let ante = Term::app(motive.clone(), k.clone());
        conseq.imp_intro(&ante)?
    };

    let all = crate::init::ext::nat_induct(base, step)?; // {hyp} ⊢ ∀i. motive i
    let pointwise = crate::init::eq::beta_reduce(all.all_elim(iv.clone())?)?; // {hyp} ⊢ index i (...) = index i l
    let eq = list_ext(alpha, &consed, l, "i", pointwise)?; // {hyp} ⊢ cons a (tail l) = l
    eq.imp_intro(&hyp)
}

/// `⊢ index i l = none ⟹ index (succ i) l = none` — the **contiguity**
/// of a list, phrased at the `index` surface (the `contig_rep` carrier
/// fact unfolded through `index = streamAt ∘ rep`).
fn index_contig(alpha: &Type, i: &Term, l: &Term) -> Result<Thm> {
    // contig_rep l at i: streamAt (rep l) i = none ⟹ streamAt (rep l) (succ i) = none.
    let contig_i = contig_rep(alpha, l)?.all_elim(i.clone())?;
    let idx_i = index_unfold(alpha, i, l)?; // index i l = streamAt (rep l) i
    let idx_si = index_unfold(alpha, &succ(i.clone()), l)?; // index (succ i) l = streamAt (rep l) (succ i)
    // Rewrite the carrier implication to the `index` surface.
    let prem = index(alpha, i, l).equals(none(alpha.clone()))?; // index i l = none
    let h = Thm::assume(prem.clone())?;
    let carrier_none = idx_i.clone().sym()?.trans(h)?; // streamAt (rep l) i = none
    let carrier_sn = contig_i.imp_elim(carrier_none)?; // streamAt (rep l) (succ i) = none
    let idx_sn = idx_si.trans(carrier_sn)?; // index (succ i) l = none
    idx_sn.imp_intro(&prem)
}

/// `⊢ head l = none ⟹ (∀i. index i l = none)` — by contiguity, a `none`
/// head forces every element `none`. Genuine: hypothesis- and oracle-free.
pub fn allnone_from_head_none(alpha: &Type, l: &Term) -> Result<Thm> {
    let hyp = Term::app(head(alpha.clone()), l.clone()).equals(none(alpha.clone()))?; // head l = none
    let h = Thm::assume(hyp.clone())?;

    // motive i ≔ index i l = none.
    let iv = Term::free("i", nat());
    let motive = Term::abs(
        nat(),
        covalence_core::subst::close(&index(alpha, &iv, l).equals(none(alpha.clone()))?, "i"),
    );

    // base: index 0 l = none (from head l = none via head_index0).
    let base = {
        let head0 = head_index0(alpha, l)?; // head l = index 0 l
        let idx0_none = head0.sym()?.trans(h.clone())?; // {hyp} ⊢ index 0 l = none
        beta_expand(&motive, zero(), idx0_none)?
    };
    // step k: index k l = none ⟹ index (succ k) l = none (contiguity). IH-driven.
    let step = {
        let k = Term::free("k", nat());
        let contig_k = index_contig(alpha, &k, l)?; // index k l = none ⟹ index (succ k) l = none
        // re-wrap into applied motive form.
        let ante = Term::app(motive.clone(), k.clone());
        let ih = crate::init::eq::beta_reduce(Thm::assume(ante.clone())?)?; // {motive k} ⊢ index k l = none
        let conseq_body = contig_k.imp_elim(ih)?; // {motive k} ⊢ index (succ k) l = none
        let conseq = beta_expand(&motive, succ(k.clone()), conseq_body)?; // {motive k} ⊢ motive (succ k)
        conseq.imp_intro(&ante)?
    };
    let all = crate::init::ext::nat_induct(base, step)?; // {hyp} ⊢ ∀i. motive i
    let allnone = crate::init::eq::beta_reduce(all.all_elim(iv.clone())?)?.all_intro("i", nat())?; // {hyp} ⊢ ∀i. index i l = none
    allnone.imp_intro(&hyp)
}

/// `⊢ (∀i. index i l = none) ⟹ l = nil` — a list with no elements is
/// `nil`. Genuine: hypothesis- and oracle-free. By [`list_ext`] against
/// [`index_nil`].
pub fn nil_from_allnone(alpha: &Type, l: &Term) -> Result<Thm> {
    let i = Term::free("i", nat());
    let allnone = index(alpha, &i, l)
        .equals(none(alpha.clone()))?
        .forall("i", nat())?;
    let h = Thm::assume(allnone.clone())?;

    // Pointwise index i l = none = index i nil.
    let at_i = h.all_elim(i.clone())?; // index i l = none
    let in_nil = index_nil(alpha, &i)?; // index i nil = none
    let pointwise = at_i.trans(in_nil.sym()?)?; // index i l = index i nil
    let eq = list_ext(alpha, l, &nil(alpha.clone()), "i", pointwise)?; // l = nil
    eq.imp_intro(&allnone)
}

/// `⊢ l = m`, given `pointwise : ⊢ index i l = index i m` with `i =
/// Free(name, nat)` not free in `l` / `m` — **list extensionality**.
/// `index = λn xs. streamAt (rep xs) n`, so a pointwise index equality is
/// a pointwise carrier equality; [`stream::ext`](crate::init::stream::ext) lifts it to `rep l = rep
/// m`, and `abs (rep ·) = ·` bridges back.
pub fn list_ext(alpha: &Type, l: &Term, m: &Term, name: &str, pointwise: Thm) -> Result<Thm> {
    let opt = option(alpha.clone());
    let i = Term::free(name, nat());
    // index i l = streamAt (rep l) i, index i m = streamAt (rep m) i.
    let il = index_unfold(alpha, &i, l)?; // index i l = streamAt (rep l) i
    let im = index_unfold(alpha, &i, m)?; // index i m = streamAt (rep m) i
    let carrier_pw = il.sym()?.trans(pointwise)?.trans(im)?; // streamAt (rep l) i = streamAt (rep m) i

    // Stream extensionality on the carriers, then bridge through abs.
    let reps_eq =
        crate::init::stream::ext(&opt, &rep_of(alpha, l), &rep_of(alpha, m), name, carrier_pw)?; // rep l = rep m
    let abs = Term::spec_abs(list_spec(), vec![alpha.clone()]);
    let abs_eq = reps_eq.cong_arg(abs)?; // abs (rep l) = abs (rep m)
    let ar_l = Thm::spec_abs_rep(list_spec(), vec![alpha.clone()], l.clone())?; // abs (rep l) = l
    let ar_m = Thm::spec_abs_rep(list_spec(), vec![alpha.clone()], m.clone())?; // abs (rep m) = m
    ar_l.sym()?.trans(abs_eq)?.trans(ar_m)
}

// ============================================================================
// `list` freeness — constructor distinctness + injectivity. These feed
// the generic inductive engine's `Inductive::distinct` / `injective`.
// ============================================================================

/// `⊢ ¬(nil = cons x xs)` — `nil` and `cons` are distinct constructors.
/// Genuine: hypothesis- and oracle-free. From `head nil = none` and
/// `head (cons x xs) = some x`, an equality would force `none = some x`,
/// contradicting [`some_ne_none`](crate::init::option::some_ne_none).
pub fn nil_ne_cons(alpha: &Type, x: &Term, xs: &Term) -> Result<Thm> {
    let consed = cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?;
    let eq = nil(alpha.clone()).equals(consed.clone())?;

    // Under H : nil = cons x xs, transport heads to `none = some x`.
    let h = Thm::assume(eq.clone())?;
    let head_op = head(alpha.clone());
    let heads_eq = h.cong_arg(head_op)?; // {H} ⊢ head nil = head (cons x xs)
    let hn = head_nil(alpha)?; // head nil = none
    let hc = head_cons(alpha, x, xs)?; // head (cons x xs) = some x
    let none_some = hn.sym()?.trans(heads_eq)?.trans(hc)?; // {H} ⊢ none = some x

    // ¬(some x = none) contradicts it (orient via sym).
    let f = crate::init::option::some_ne_none(alpha, x)?.not_elim(none_some.sym()?)?; // {H} ⊢ F
    f.imp_intro(&eq)?.not_intro() // ⊢ ¬(nil = cons x xs)
}

/// `⊢ (cons x xs = cons y ys) ⟹ (x = y ∧ xs = ys)` — `cons` is
/// injective. Genuine: hypothesis- and oracle-free. The head equality
/// gives `x = y` through [`some_inj`](crate::init::option::some_inj); the
/// tail equality gives `xs = ys` through [`tail_cons`].
pub fn cons_inj(alpha: &Type, x: &Term, xs: &Term, y: &Term, ys: &Term) -> Result<Thm> {
    let cxs = cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?;
    let cys = cons(alpha.clone()).apply(y.clone())?.apply(ys.clone())?;
    let eq = cxs.clone().equals(cys.clone())?;
    let h = Thm::assume(eq.clone())?;

    // Heads: head (cons x xs) = head (cons y ys), i.e. some x = some y.
    let heads_eq = h.clone().cong_arg(head(alpha.clone()))?; // {H} ⊢ head (cons x xs) = head (cons y ys)
    let some_xy = head_cons(alpha, x, xs)?
        .sym()?
        .trans(heads_eq)?
        .trans(head_cons(alpha, y, ys)?)?; // {H} ⊢ some x = some y
    let x_eq_y = crate::init::option::some_inj(alpha, x, y)?.imp_elim(some_xy)?; // {H} ⊢ x = y

    // Tails: tail (cons x xs) = tail (cons y ys), i.e. xs = ys.
    let tails_eq = h.cong_arg(tail(alpha.clone()))?; // {H} ⊢ tail (cons x xs) = tail (cons y ys)
    let xs_eq_ys = tail_cons(alpha, x, xs)?
        .sym()?
        .trans(tails_eq)?
        .trans(tail_cons(alpha, y, ys)?)?; // {H} ⊢ xs = ys

    x_eq_y.and_intro(xs_eq_ys)?.imp_intro(&eq)
}

// ============================================================================
// List induction.
// ============================================================================

/// `λl. (∀i. nat_le N i ⟹ index i l = none) ⟹ P l` — the bound-`N`
/// auxiliary motive for the [`list_induct`] inner induction. `P` is the
/// user motive (`p : list α → bool`).
fn aux_motive(alpha: &Type, p: &Term, big_n: &Term) -> Result<Term> {
    let l = Term::free("__l", list(alpha.clone()));
    let i = Term::free("i", nat());
    let le = Term::app(Term::app(nat_le(), big_n.clone()), i.clone());
    let none_eq = index(alpha, &i, &l).equals(none(alpha.clone()))?;
    let premise = le.imp(none_eq)?.forall("i", nat())?;
    let body = premise.imp(Term::app(p.clone(), l.clone()))?;
    Ok(Term::abs(
        list(alpha.clone()),
        covalence_core::subst::close(&body, "__l"),
    ))
}

/// `⊢ P l`, given `pl_nil : ⊢ P nil` and `allnone : ⊢ ∀i. index i l =
/// none` — rewrite `P nil` along `nil = l` (from [`nil_from_allnone`]).
fn p_of_nil_list(alpha: &Type, p: &Term, l: &Term, pl_nil: &Thm, allnone: Thm) -> Result<Thm> {
    let l_eq_nil = nil_from_allnone(alpha, l)?.imp_elim(allnone)?; // l = nil
    // P nil, rewritten by nil = l (l_eq_nil reversed).
    let p_cong = l_eq_nil.sym()?.cong_arg(p.clone())?; // P nil = P l
    p_cong.eq_mp(pl_nil.clone())
}

/// **List induction.** `⊢ ∀l. P l`, given `pl_nil : ⊢ P nil` and
/// `cons_case : ⊢ ∀x xs. P xs ⟹ P (cons x xs)`, where `p = P : list α →
/// bool`. Genuine: hypothesis- and oracle-free (given hypothesis-free
/// premises).
///
/// Proof: an inner `nat`-induction on a finiteness bound `N` establishes
/// `Aux(N) ≜ ∀l. (∀i. N ≤ i ⟹ index i l = none) ⟹ P l`. The base `N=0`
/// forces every element `none`, so `l = nil`. The step splits on `head l`
/// (`option_cases`): a `none` head propagates ([`allnone_from_head_none`])
/// to `l = nil`; a `some a` head reconstructs `l = cons a (tail l)`
/// ([`cons_head_tail`]), with `P (tail l)` from the `IH` (the tail's bound
/// drops to `M`) and the `cons` case. Finally `finite_rep` supplies the
/// bound for an arbitrary `l`.
pub fn list_induct(alpha: &Type, p: &Term, pl_nil: Thm, cons_case: Thm) -> Result<Thm> {
    // --- the inner induction: ⊢ ∀N. Aux(N) ---
    // Aux(0): premise (∀i. nat_le 0 i ⟹ index i l = none) gives every i
    // (le_zero), so l = nil, so P l.
    let l = Term::free("__l", list(alpha.clone()));
    let aux0_motive = aux_motive(alpha, p, &zero())?;
    let aux0 = {
        let i = Term::free("i", nat());
        let premise = {
            let le = Term::app(Term::app(nat_le(), zero()), i.clone());
            le.imp(index(alpha, &i, &l).equals(none(alpha.clone()))?)?
                .forall("i", nat())?
        };
        let h = Thm::assume(premise.clone())?;
        // ∀i. index i l = none, discharging the vacuous `nat_le 0 i`.
        let le_0_i = crate::init::nat::le_zero().all_elim(i.clone())?; // nat_le 0 i
        let at_i = h.all_elim(i.clone())?.imp_elim(le_0_i)?; // index i l = none
        let allnone = at_i.all_intro("i", nat())?;
        let pl = p_of_nil_list(alpha, p, &l, &pl_nil, allnone)?; // {premise} ⊢ P l
        let body = pl.imp_intro(&premise)?; // ⊢ premise ⟹ P l  (= Aux(0) body at l)
        let at_l = beta_expand(&aux0_motive, l.clone(), body)?; // ⊢ aux0_motive l
        at_l.all_intro("__l", list(alpha.clone()))? // ⊢ ∀l. aux0_motive l (applied form)
    };

    // Build the inner-induction motive `λN. ∀l. Aux(N) l` (a predicate on N).
    let inner_motive = {
        let n = Term::free("N", nat());
        let body = Term::app(
            aux_motive(alpha, p, &n)?,
            Term::free("__l", list(alpha.clone())),
        )
        .forall("__l", list(alpha.clone()))?;
        Term::abs(nat(), covalence_core::subst::close(&body, "N"))
    };

    // base for the inner nat_induct: inner_motive 0 = ∀l. Aux(0) l.
    let inner_base = beta_expand(&inner_motive, zero(), aux0)?;

    // step: ∀M. (∀l. Aux(M) l) ⟹ (∀l. Aux(succ M) l).
    let inner_step = {
        let m = Term::free("M", nat());
        let ih_term = Term::app(inner_motive.clone(), m.clone()); // inner_motive M
        let ih = crate::init::eq::beta_reduce(Thm::assume(ih_term.clone())?)?; // {IH} ⊢ ∀l. Aux(M) l

        let aux_sm = aux_step(alpha, p, &m, &cons_case, &pl_nil, &ih)?; // {IH} ⊢ ∀l. Aux(succ M) l
        let conseq = beta_expand(&inner_motive, succ(m.clone()), aux_sm)?; // {IH} ⊢ inner_motive (succ M)
        conseq.imp_intro(&ih_term)?
    };

    let inner = crate::init::ext::nat_induct(inner_base, inner_step)?; // ⊢ ∀N. inner_motive N

    // --- close over an arbitrary l: get the bound from finite_rep ---
    // ∀l. (∀i. nat_le N i ⟹ index i l = none) ⟹ P l, at each N.
    let aux_at = |n: &Term| -> Result<Thm> {
        crate::init::eq::beta_reduce(inner.clone().all_elim(n.clone())?)
    };

    // For arbitrary l: finite (rep l) ≡ ∃N. ∀i. nat_le N i ⟹ index i l = none.
    let pl = {
        let fin = finite_rep(alpha, &l)?; // finite (rep l)
        // finite (rep l) = ∃N. ∀n. nat_le N n ⟹ streamAt (rep l) n = none.
        let unfold = Term::app(finite(alpha.clone()), rep_of(alpha, &l))
            .delta_all(finite_spec().symbol())?
            .rhs_conv(|t| t.reduce())?;
        let ex = unfold.eq_mp(fin)?; // ∃N. ∀n. nat_le N n ⟹ streamAt (rep l) n = none

        // exists_elim: from the bound N, Aux(N) gives P l.
        let ex_pred = ex.concl().as_app().ok_or(Error::NotAnEquation)?.1.clone();
        let n = Term::free("N", nat());
        let applied = Term::app(ex_pred, n.clone());
        let body_carrier = crate::init::eq::beta_reduce(Thm::assume(applied.clone())?)?; // {pred N} ⊢ ∀i. nat_le N i ⟹ streamAt (rep l) i = none
        // Convert the carrier form to the `index` form (under the free `j`).
        let body_n = carrier_body_to_index(alpha, &l, &n, body_carrier)?; // {pred N} ⊢ ∀i. nat_le N i ⟹ index i l = none
        let aux_n = crate::init::eq::beta_reduce(aux_at(&n)?.all_elim(l.clone())?)?; // Aux(N) at l (β-reduced)
        let pl = aux_n.imp_elim(body_n)?; // {pred N} ⊢ P l
        let goal_pl = Term::app(p.clone(), l.clone());
        let step = pl.imp_intro(&applied)?.all_intro("N", nat())?;
        exists_elim(ex, goal_pl, step)? // ⊢ P l
    };

    pl.all_intro("__l", list(alpha.clone()))
}

/// The inner-induction **step body**: `⊢ ∀l. Aux(succ M) l`, given the
/// `IH = ⊢ ∀l. Aux(M) l`, the `cons_case`, and `pl_nil`. Split on `head l`.
fn aux_step(
    alpha: &Type,
    p: &Term,
    m: &Term,
    cons_case: &Thm,
    pl_nil: &Thm,
    ih: &Thm,
) -> Result<Thm> {
    let l = Term::free("__l", list(alpha.clone()));
    let aux_motive_sm = aux_motive(alpha, p, &succ(m.clone()))?;

    // The Aux(succ M) premise at l.
    let i = Term::free("i", nat());
    let premise = {
        let le = Term::app(Term::app(nat_le(), succ(m.clone())), i.clone());
        le.imp(index(alpha, &i, &l).equals(none(alpha.clone()))?)?
            .forall("i", nat())?
    };
    let h_prem = Thm::assume(premise.clone())?;

    let goal_pl = Term::app(p.clone(), l.clone());

    // Case split on head l: (∃a. head l = some a) ∨ (head l = none).
    let head_l = Term::app(head(alpha.clone()), l.clone());
    let cs = crate::init::option::option_cases(alpha, &head_l)?;

    // --- some-branch: head l = some a ⟹ P l ---
    let some_disj = cs
        .concl()
        .as_app()
        .and_then(|(orp, _)| orp.as_app().map(|(_, x)| x.clone()))
        .ok_or(Error::NotAnEquation)?;
    let none_disj = cs
        .concl()
        .as_app()
        .map(|(_, r)| r.clone())
        .ok_or(Error::NotAnEquation)?;

    let some_branch = {
        // ∃a. head l = some a — assume it; a fresh, head l = some a.
        let some_pred = some_disj.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λa. head l = some a
        let a = Term::free("__a", alpha.clone());
        let applied = Term::app(some_pred.clone(), a.clone());
        let head_some = crate::init::eq::beta_reduce(Thm::assume(applied.clone())?)?; // {applied} ⊢ head l = some a

        // l = cons a (tail l).
        let recon = cons_head_tail(alpha, &a, &l)?.imp_elim(head_some)?; // {applied} ⊢ cons a (tail l) = l

        // P (tail l) from IH: tail l's bound drops to M.
        let p_tail = {
            // ∀i. nat_le M i ⟹ index i (tail l) = none.
            let tl = Term::app(tail(alpha.clone()), l.clone());
            let j = Term::free("i", nat());
            let le_m_j = Term::app(Term::app(nat_le(), m.clone()), j.clone());
            let hj = Thm::assume(le_m_j.clone())?; // nat_le M j
            // nat_le M j ⟹ nat_le (succ M) (succ j) (le_succ_succ).
            let le_ss = crate::init::nat::le_succ_succ()
                .all_elim(m.clone())?
                .all_elim(j.clone())?; // (nat_le (succ M)(succ j)) = (nat_le M j)
            let le_sm_sj = le_ss.sym()?.eq_mp(hj)?; // {nat_le M j} ⊢ nat_le (succ M)(succ j)
            // premise at (succ j): index (succ j) l = none.
            let idx_sj_none = h_prem
                .clone()
                .all_elim(succ(j.clone()))?
                .imp_elim(le_sm_sj)?; // index (succ j) l = none
            // index j (tail l) = index (succ j) l, so index j (tail l) = none.
            let it = index_tail(alpha, &j, &l)?; // index j (tail l) = index (succ j) l
            let idx_tail_none = it.trans(idx_sj_none)?; // index j (tail l) = none
            let tail_premise = idx_tail_none.imp_intro(&le_m_j)?.all_intro("i", nat())?; // ∀i. nat_le M i ⟹ index i (tail l) = none
            // IH at tail l.
            let aux_m_tail = crate::init::eq::beta_reduce(ih.clone().all_elim(tl.clone())?)?; // Aux(M) at (tail l)
            aux_m_tail.imp_elim(tail_premise)? // {premise} ⊢ P (tail l)
        };

        // cons_case: P (tail l) ⟹ P (cons a (tail l)).
        let tl = Term::app(tail(alpha.clone()), l.clone());
        let cc = cons_case
            .clone()
            .all_elim(a.clone())?
            .all_elim(tl.clone())?; // P (tail l) ⟹ P (cons a (tail l))
        let p_cons = cc.imp_elim(p_tail)?; // {premise, applied} ⊢ P (cons a (tail l))
        // Rewrite by cons a (tail l) = l.
        let pl = recon.cong_arg(p.clone())?.eq_mp(p_cons)?; // {premise, applied} ⊢ P l
        // discharge applied, ∀-close a, exists_elim.
        let inner_step = pl.imp_intro(&applied)?.all_intro("__a", alpha.clone())?;
        exists_elim(Thm::assume(some_disj.clone())?, goal_pl.clone(), inner_step)?
            .imp_intro(&some_disj)? // ⊢ (∃a. head l = some a) ⟹ P l
    };

    // --- none-branch: head l = none ⟹ P l (l = nil) ---
    let none_branch = {
        let h_none = Thm::assume(none_disj.clone())?; // head l = none
        let allnone = allnone_from_head_none(alpha, &l)?.imp_elim(h_none)?; // ∀i. index i l = none
        let pl = p_of_nil_list(alpha, p, &l, pl_nil, allnone)?; // {none_disj} ⊢ P l
        pl.imp_intro(&none_disj)? // ⊢ (head l = none) ⟹ P l
    };

    // Combine: P l (under {premise}).
    let pl = cs.or_elim(some_branch, none_branch)?; // {premise} ⊢ P l
    let body = pl.imp_intro(&premise)?; // ⊢ premise ⟹ P l  (Aux(succ M) body)
    let at_l = beta_expand(&aux_motive_sm, l.clone(), body)?;
    at_l.all_intro("__l", list(alpha.clone()))
}

/// Convert `⊢ ∀i. nat_le N i ⟹ streamAt (rep l) i = none` to `⊢ ∀i.
/// nat_le N i ⟹ index i l = none` — open the `∀i` at a free `j`, rewrite
/// the carrier access `streamAt (rep l) j` to `index j l` (now `j` is
/// free, so the rewrite is a plain transitivity), and re-close.
fn carrier_body_to_index(alpha: &Type, l: &Term, big_n: &Term, body: Thm) -> Result<Thm> {
    let j = Term::free("__j", nat());
    let opened = body.all_elim(j.clone())?; // nat_le N j ⟹ streamAt (rep l) j = none
    // Under the assumption `nat_le N j`, get `index j l = none`.
    let le = Term::app(Term::app(nat_le(), big_n.clone()), j.clone());
    let h = Thm::assume(le.clone())?;
    let carrier_none = opened.imp_elim(h)?; // {nat_le N j} ⊢ streamAt (rep l) j = none
    let idx = index_unfold(alpha, &j, l)?; // index j l = streamAt (rep l) j
    let idx_none = idx.trans(carrier_none)?; // index j l = none
    idx_none.imp_intro(&le)?.all_intro("__j", nat())
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

// ============================================================================
// `listprim` env + the `list.cov` port.
// ============================================================================

/// The `listprim` environment imported by `list.cov`: the `list` operators
/// (`nil`/`cons`/`head`/`tail`/`index`/`length`/`cat`/`foldr`, plus the
/// `option` constructors `some`/`none`) and the **seam** lemmas — the
/// per-constructor element computations, constructor freeness, the
/// `foldr`/`length`/`cat` recursion clauses — in universally-quantified form.
///
/// These cross the `abs`/`rep` subtype boundary (and the `list_foldr`
/// recursion theorem) in Rust, so they stay Rust-proved givens (the `set.cov`
/// `setprim` / `nat.cov` `natrec` pattern). `list.cov` proves the structural
/// theorems over them and never touches `abs`/`rep` — and uses the
/// `list-induct` tactic (the genuine [`list_induct`] theorem, registered in
/// `core`) for the inductive proofs.
///
/// Everything is schematic in one element type `'a` (and a result type `'b`
/// for the `foldr` clause), matching `set.cov`'s monomorphic-at-`'a` style.
pub fn list_env() -> crate::script::Env {
    use crate::init::list_recursion::{
        cat_cons, cat_nil, foldr_cons, foldr_nil, length_cons, length_nil,
    };
    use crate::script::{ConstDef, Env};
    use covalence_hol_eval::defs::{nat_succ, some};

    let a = Type::tfree("a");
    let b = Type::tfree("b");
    let la = list(a.clone());
    let mut e = Env::empty();

    // operators (monomorphic at `'a` / `'b`)
    e.define_const("list.nil", ConstDef::Op(nil(a.clone())));
    e.define_const("list.cons", ConstDef::Op(cons(a.clone())));
    e.define_const("list.head", ConstDef::Op(head(a.clone())));
    e.define_const("list.tail", ConstDef::Op(tail(a.clone())));
    e.define_const("list.index", ConstDef::Op(list_index(a.clone())));
    e.define_const("list.length", ConstDef::Op(list_length(a.clone())));
    e.define_const("list.cat", ConstDef::Op(list_cat(a.clone())));
    e.define_const("list.foldr", ConstDef::Op(list_foldr(a.clone(), b.clone())));
    e.define_const("option.some", ConstDef::Op(some(a.clone())));
    e.define_const("option.none", ConstDef::Op(none(a.clone())));

    let x = Term::free("x", a.clone());
    let y = Term::free("y", a.clone());
    let xs = Term::free("xs", la.clone());
    let ys = Term::free("ys", la.clone());
    let n = Term::free("n", nat());
    let k = Term::free("k", nat());
    let z = Term::free("z", b.clone());
    let f2 = Term::free("f", Type::fun(a.clone(), Type::fun(b.clone(), b.clone())));

    let close1 = |th: Thm, name: &str, ty: &Type| th.all_intro(name, ty.clone()).unwrap();

    // -- element computations --
    // index_nil : ∀n. index n nil = none
    e.define_lemma("index_nil", close1(index_nil(&a, &n).unwrap(), "n", &nat()));
    // index_cons_zero : ∀x xs. index 0 (cons x xs) = some x
    e.define_lemma(
        "index_cons_zero",
        close1(
            close1(index_cons_zero(&a, &x, &xs).unwrap(), "xs", &la),
            "x",
            &a,
        ),
    );
    // index_cons_succ : ∀k x xs. index (succ k) (cons x xs) = index k xs
    e.define_lemma(
        "index_cons_succ",
        close1(
            close1(
                close1(index_cons_succ(&a, &x, &xs, &k).unwrap(), "xs", &la),
                "x",
                &a,
            ),
            "k",
            &nat(),
        ),
    );
    // head_nil : head nil = none
    e.define_lemma("head_nil", head_nil(&a).unwrap());
    // head_cons : ∀x xs. head (cons x xs) = some x
    e.define_lemma(
        "head_cons",
        close1(close1(head_cons(&a, &x, &xs).unwrap(), "xs", &la), "x", &a),
    );
    // tail_cons : ∀x xs. tail (cons x xs) = xs
    e.define_lemma(
        "tail_cons",
        close1(close1(tail_cons(&a, &x, &xs).unwrap(), "xs", &la), "x", &a),
    );

    // -- freeness --
    // nil_ne_cons : ∀x xs. ¬(nil = cons x xs)
    e.define_lemma(
        "nil_ne_cons",
        close1(
            close1(nil_ne_cons(&a, &x, &xs).unwrap(), "xs", &la),
            "x",
            &a,
        ),
    );
    // cons_inj : ∀x xs y ys. (cons x xs = cons y ys) ⟹ (x = y ∧ xs = ys)
    e.define_lemma(
        "cons_inj",
        close1(
            close1(
                close1(
                    close1(cons_inj(&a, &x, &xs, &y, &ys).unwrap(), "ys", &la),
                    "y",
                    &a,
                ),
                "xs",
                &la,
            ),
            "x",
            &a,
        ),
    );

    // -- foldr recursion clauses (at `'a`/`'b`) --
    // foldr_nil : ∀f z. foldr f z nil = z
    e.define_lemma(
        "foldr_nil",
        close1(
            close1(foldr_nil(&a, &b, &f2, &z).unwrap(), "z", &b),
            "f",
            &f2.type_of().unwrap(),
        ),
    );
    // foldr_cons : ∀f z x xs. foldr f z (cons x xs) = f x (foldr f z xs)
    e.define_lemma(
        "foldr_cons",
        close1(
            close1(
                close1(
                    close1(foldr_cons(&a, &b, &f2, &z, &x, &xs).unwrap(), "xs", &la),
                    "x",
                    &a,
                ),
                "z",
                &b,
            ),
            "f",
            &f2.type_of().unwrap(),
        ),
    );

    // -- length / cat clauses --
    // length_nil : length nil = 0
    e.define_lemma("length_nil", length_nil(&a).unwrap());
    // length_cons : ∀x xs. length (cons x xs) = succ (length xs)
    e.define_lemma(
        "length_cons",
        close1(
            close1(length_cons(&a, &x, &xs).unwrap(), "xs", &la),
            "x",
            &a,
        ),
    );
    // cat_nil : ∀ys. cat nil ys = ys
    e.define_lemma("cat_nil", close1(cat_nil(&a, &ys).unwrap(), "ys", &la));
    // cat_cons : ∀x xs ys. cat (cons x xs) ys = cons x (cat xs ys)
    e.define_lemma(
        "cat_cons",
        close1(
            close1(
                close1(cat_cons(&a, &x, &xs, &ys).unwrap(), "ys", &la),
                "xs",
                &la,
            ),
            "x",
            &a,
        ),
    );
    let _ = nat_succ; // (succ is provided by `core`)
    e
}

crate::cov_theory! {
    /// `list` structural theorems ported to `list.cov`, over `core` + the
    /// `listprim` seam env. The `list-induct` tactic (in `core`) drives the
    /// inductive proofs.
    pub mod cov from "list.cov" {
        import "core" = crate::script::Env::core();
        import "natrec" = crate::init::nat::natrec_env();
        import "listprim" = crate::init::list::list_env();
        "index_cons_zero" => pub fn index_cons_zero_cov;
        "head_cons"       => pub fn head_cons_cov;
        "tail_cons"       => pub fn tail_cons_cov;
        "nil_ne_cons"     => pub fn nil_ne_cons_cov;
        "cons_inj"        => pub fn cons_inj_cov;
        "length_nil"      => pub fn length_nil_cov;
        "length_cons"     => pub fn length_cons_cov;
        "cat_nil"         => pub fn cat_nil_cov;
        "cat_cons"        => pub fn cat_cons_cov;
        "cat_nil_r"       => pub fn cat_nil_r_cov;
        "cat_assoc"       => pub fn cat_assoc_cov;
        "length_cat"      => pub fn length_cat_cov;
        "cat_cons_singleton" => pub fn cat_cons_singleton_cov;
    }
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
        let expected = Term::app(finite(alpha()), const_none(&alpha()));
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn finite_rep_is_genuine() {
        let xs = Term::free("xs", list(alpha()));
        let thm = finite_rep(&alpha(), &xs).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "finite_rep is proved, not postulated"
        );
        let expected = Term::app(finite(alpha()), rep_of(&alpha(), &xs));
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn cons_stream_computations() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let z = cons_stream_zero(&alpha(), &x, &xs).unwrap();
        assert!(z.hyps().is_empty());
        let k = Term::free("k", nat());
        let s = cons_stream_succ(&alpha(), &x, &xs, &k).unwrap();
        assert!(s.hyps().is_empty());
    }

    #[test]
    fn finite_cons_is_genuine() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let thm = finite_cons(&alpha(), &x, &xs).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "finite_cons is proved, not postulated"
        );
        // ⊢ finite (streamMk (consStream x xs))
        let g = cons_stream(&alpha(), &x, &xs);
        let expected = Term::app(finite(alpha()), mk_stream(&alpha(), &g));
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn pred_nonempty_is_genuine() {
        let thm = pred_nonempty(&alpha()).unwrap();
        assert!(thm.hyps().is_empty());
        // ⊢ ∃s. list_predicate s
        let expected = Term::app(
            covalence_hol_eval::defs::exists(crate::init::stream::stream(option(alpha()))),
            list_pred_op(&alpha()),
        );
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn pred_const_none_and_cons_are_genuine() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let pc = pred_const_none(&alpha()).unwrap();
        assert!(pc.hyps().is_empty());
        assert_eq!(pc.concl(), &list_pred(&alpha(), &const_none(&alpha())));
        let pk = pred_cons(&alpha(), &x, &xs).unwrap();
        assert!(pk.hyps().is_empty());
        let g = cons_stream(&alpha(), &x, &xs);
        assert_eq!(pk.concl(), &list_pred(&alpha(), &mk_stream(&alpha(), &g)));
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
    fn index_cons_zero_is_head() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let thm = index_cons_zero(&alpha(), &x, &xs).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let consed = cons(alpha())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        assert_eq!(lhs, &index(&alpha(), &zero(), &consed));
        assert_eq!(rhs, &Term::app(some(alpha()), x));
    }

    #[test]
    fn index_cons_succ_recurses() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let k = Term::free("k", nat());
        let thm = index_cons_succ(&alpha(), &x, &xs, &k).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let consed = cons(alpha())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        assert_eq!(lhs, &index(&alpha(), &succ(k.clone()), &consed));
        assert_eq!(rhs, &index(&alpha(), &k, &xs));
    }

    #[test]
    fn head_cons_is_some() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let thm = head_cons(&alpha(), &x, &xs).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let consed = cons(alpha())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        assert_eq!(lhs, &Term::app(head(alpha()), consed));
        assert_eq!(rhs, &Term::app(some(alpha()), x));
    }

    #[test]
    fn tail_cons_drops_head() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let thm = tail_cons(&alpha(), &x, &xs).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let consed = cons(alpha())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        assert_eq!(lhs, &Term::app(tail(alpha()), consed));
        assert_eq!(rhs, &xs);
    }

    #[test]
    fn head_nil_is_none() {
        let thm = head_nil(&alpha()).unwrap();
        assert!(thm.hyps().is_empty(), "head_nil is proved, not postulated");
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &Term::app(head(alpha()), nil(alpha())));
        assert_eq!(rhs, &none(alpha()));
    }

    #[test]
    fn cons_head_tail_reconstructs() {
        let a = Term::free("a", alpha());
        let l = Term::free("l", list(alpha()));
        let thm = cons_head_tail(&alpha(), &a, &l).unwrap();
        assert!(thm.hyps().is_empty());
        // ⊢ (head l = some a) ⟹ (cons a (tail l) = l)
        let some_a = Term::app(some(alpha()), a.clone());
        let prem = Term::app(head(alpha()), l.clone()).equals(some_a).unwrap();
        let tl = Term::app(tail(alpha()), l.clone());
        let consed = cons(alpha()).apply(a.clone()).unwrap().apply(tl).unwrap();
        let concl = prem.imp(consed.equals(l.clone()).unwrap()).unwrap();
        assert_eq!(thm.concl(), &concl);
    }

    #[test]
    fn list_induct_trivial_motive() {
        // P = λl. T. nil_case ⊢ T; cons_case ⊢ ∀x xs. T ⟹ T. Conclude ∀l. T.
        use crate::init::logic::truth;
        let a = alpha();
        let p = Term::abs(list(a.clone()), Term::bool_lit(true)); // λl. T
        // P nil = T (β), so pl_nil ⊢ P nil from ⊢ T.
        let pl_nil = {
            let t = truth(); // ⊢ T
            beta_expand(&p, nil(a.clone()), t).unwrap() // ⊢ P nil
        };
        // cons_case ⊢ ∀x xs. P xs ⟹ P (cons x xs).
        let cons_case = {
            let x = Term::free("x", a.clone());
            let xs = Term::free("xs", list(a.clone()));
            let p_xs = Term::app(p.clone(), xs.clone());
            let consed = cons(a.clone())
                .apply(x.clone())
                .unwrap()
                .apply(xs.clone())
                .unwrap();
            let p_cons = Term::app(p.clone(), consed);
            // P (cons x xs) = T, so assume P xs, prove P (cons x xs) from ⊢ T.
            let body = beta_expand(
                &p,
                cons(a.clone())
                    .apply(x.clone())
                    .unwrap()
                    .apply(xs.clone())
                    .unwrap(),
                truth(),
            )
            .unwrap() // ⊢ P (cons x xs)
            .imp_intro(&p_xs)
            .unwrap(); // P xs ⟹ P (cons x xs)
            let _ = p_cons;
            body.all_intro("xs", list(a.clone()))
                .unwrap()
                .all_intro("x", a.clone())
                .unwrap()
        };
        let thm = list_induct(&a, &p, pl_nil, cons_case).unwrap();
        assert!(thm.hyps().is_empty());
        // ⊢ ∀l. P l
        let l = Term::free("l", list(a.clone()));
        let expected = Term::app(p.clone(), l).forall("l", list(a)).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn allnone_from_head_none_is_genuine() {
        let l = Term::free("l", list(alpha()));
        let thm = allnone_from_head_none(&alpha(), &l).unwrap();
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn nil_from_allnone_is_genuine() {
        let l = Term::free("l", list(alpha()));
        let thm = nil_from_allnone(&alpha(), &l).unwrap();
        assert!(thm.hyps().is_empty());
        let i = Term::free("i", nat());
        let allnone = index(&alpha(), &i, &l)
            .equals(none(alpha()))
            .unwrap()
            .forall("i", nat())
            .unwrap();
        let concl = allnone.imp(l.equals(nil(alpha())).unwrap()).unwrap();
        assert_eq!(thm.concl(), &concl);
    }

    #[test]
    fn index_tail_shifts_up() {
        let i = Term::free("i", nat());
        let l = Term::free("l", list(alpha()));
        let thm = index_tail(&alpha(), &i, &l).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let tailed = Term::app(tail(alpha()), l.clone());
        assert_eq!(lhs, &index(&alpha(), &i, &tailed));
        assert_eq!(rhs, &index(&alpha(), &succ(i.clone()), &l));
    }

    #[test]
    fn nil_ne_cons_is_genuine() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let thm = nil_ne_cons(&alpha(), &x, &xs).unwrap();
        assert!(thm.hyps().is_empty());
        let consed = cons(alpha())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        let expected = nil(alpha()).equals(consed).unwrap().not().unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn cons_inj_is_genuine() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let y = Term::free("y", alpha());
        let ys = Term::free("ys", list(alpha()));
        let thm = cons_inj(&alpha(), &x, &xs, &y, &ys).unwrap();
        assert!(thm.hyps().is_empty());
        let cxs = cons(alpha())
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap();
        let cys = cons(alpha())
            .apply(y.clone())
            .unwrap()
            .apply(ys.clone())
            .unwrap();
        let concl = cxs
            .equals(cys)
            .unwrap()
            .imp(
                x.equals(y.clone())
                    .unwrap()
                    .and(xs.equals(ys.clone()).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(thm.concl(), &concl);
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

    // ========================================================================
    // `list.cov` port — the ported theorems match their Rust originals, the
    // new theorems are genuine.
    // ========================================================================

    fn ev(name: &str) -> Term {
        Term::free(name, alpha())
    }
    fn lv(name: &str) -> Term {
        Term::free(name, list(alpha()))
    }

    /// Every `list.cov` theorem is genuine (hypothesis- and oracle-free).
    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "expected a hypothesis-free theorem");
    }

    #[test]
    fn cov_index_cons_zero_matches_rust() {
        let (x, xs) = (ev("x"), lv("xs"));
        let want = index_cons_zero(&alpha(), &x, &xs)
            .unwrap()
            .all_intro("xs", list(alpha()))
            .unwrap()
            .all_intro("x", alpha())
            .unwrap();
        let got = cov::index_cons_zero_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    #[test]
    fn cov_head_cons_matches_rust() {
        let (x, xs) = (ev("x"), lv("xs"));
        let want = head_cons(&alpha(), &x, &xs)
            .unwrap()
            .all_intro("xs", list(alpha()))
            .unwrap()
            .all_intro("x", alpha())
            .unwrap();
        let got = cov::head_cons_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    #[test]
    fn cov_tail_cons_matches_rust() {
        let (x, xs) = (ev("x"), lv("xs"));
        let want = tail_cons(&alpha(), &x, &xs)
            .unwrap()
            .all_intro("xs", list(alpha()))
            .unwrap()
            .all_intro("x", alpha())
            .unwrap();
        let got = cov::tail_cons_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    #[test]
    fn cov_nil_ne_cons_matches_rust() {
        let (x, xs) = (ev("x"), lv("xs"));
        let want = nil_ne_cons(&alpha(), &x, &xs)
            .unwrap()
            .all_intro("xs", list(alpha()))
            .unwrap()
            .all_intro("x", alpha())
            .unwrap();
        let got = cov::nil_ne_cons_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    #[test]
    fn cov_cons_inj_matches_rust() {
        let (x, xs, y, ys) = (ev("x"), lv("xs"), ev("y"), lv("ys"));
        let want = cons_inj(&alpha(), &x, &xs, &y, &ys)
            .unwrap()
            .all_intro("ys", list(alpha()))
            .unwrap()
            .all_intro("y", alpha())
            .unwrap()
            .all_intro("xs", list(alpha()))
            .unwrap()
            .all_intro("x", alpha())
            .unwrap();
        let got = cov::cons_inj_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    #[test]
    fn cov_length_nil_matches_rust() {
        let want = crate::init::list_recursion::length_nil(&alpha()).unwrap();
        let got = cov::length_nil_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    #[test]
    fn cov_length_cons_matches_rust() {
        let (x, xs) = (ev("x"), lv("xs"));
        let want = crate::init::list_recursion::length_cons(&alpha(), &x, &xs)
            .unwrap()
            .all_intro("xs", list(alpha()))
            .unwrap()
            .all_intro("x", alpha())
            .unwrap();
        let got = cov::length_cons_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    #[test]
    fn cov_cat_nil_matches_rust() {
        let ys = lv("ys");
        let want = crate::init::list_recursion::cat_nil(&alpha(), &ys)
            .unwrap()
            .all_intro("ys", list(alpha()))
            .unwrap();
        let got = cov::cat_nil_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    #[test]
    fn cov_cat_cons_matches_rust() {
        let (x, xs, ys) = (ev("x"), lv("xs"), lv("ys"));
        let want = crate::init::list_recursion::cat_cons(&alpha(), &x, &xs, &ys)
            .unwrap()
            .all_intro("ys", list(alpha()))
            .unwrap()
            .all_intro("xs", list(alpha()))
            .unwrap()
            .all_intro("x", alpha())
            .unwrap();
        let got = cov::cat_cons_cov();
        assert_genuine(&got);
        assert_eq!(got.concl(), want.concl());
    }

    // -- the NEW theorems: genuine, with the expected conclusions ------------

    #[test]
    fn cov_cat_nil_r_is_genuine() {
        // ⊢ ∀xs. cat xs nil = xs  (append's right unit — needs induction).
        let got = cov::cat_nil_r_cov();
        assert_genuine(&got);
        let xs = lv("xs");
        let expected = cat_app(&alpha(), &xs, &nil(alpha()))
            .equals(xs.clone())
            .unwrap()
            .forall("xs", list(alpha()))
            .unwrap();
        assert_eq!(got.concl(), &expected);
    }

    #[test]
    fn cov_cat_assoc_is_genuine() {
        // ⊢ ∀xs ys zs. cat (cat xs ys) zs = cat xs (cat ys zs).
        let got = cov::cat_assoc_cov();
        assert_genuine(&got);
        let (xs, ys, zs) = (lv("xs"), lv("ys"), lv("zs"));
        let lhs = cat_app(&alpha(), &cat_app(&alpha(), &xs, &ys), &zs);
        let rhs = cat_app(&alpha(), &xs, &cat_app(&alpha(), &ys, &zs));
        let expected = lhs
            .equals(rhs)
            .unwrap()
            .forall("zs", list(alpha()))
            .unwrap()
            .forall("ys", list(alpha()))
            .unwrap()
            .forall("xs", list(alpha()))
            .unwrap();
        assert_eq!(got.concl(), &expected);
    }

    #[test]
    fn cov_length_cat_is_genuine() {
        // ⊢ ∀xs ys. length (cat xs ys) = length xs + length ys.
        let got = cov::length_cat_cov();
        assert_genuine(&got);
    }

    #[test]
    fn cov_cat_cons_singleton_is_genuine() {
        // ⊢ ∀x xs. cons x xs = cat (cons x nil) xs.
        let got = cov::cat_cons_singleton_cov();
        assert_genuine(&got);
    }

    /// `list_cat[α] xs ys` applied (test helper mirroring the Rust builder).
    fn cat_app(alpha: &Type, xs: &Term, ys: &Term) -> Term {
        Term::app(Term::app(list_cat(alpha.clone()), xs.clone()), ys.clone())
    }
}
