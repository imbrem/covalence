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

use crate::init::eq::{beta_expand, trans_chain};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{exists_elim, exists_intro};
use crate::init::stream::{const_at, head_const, stream_at, stream_head, stream_mk};

// Re-export the `defs/list.rs` term catalogue (the `*_spec` handles stay
// in `covalence_core::defs`, reached via the blanket re-export there).
pub use covalence_core::defs::{
    cons, head, list, list_cat, list_filter, list_flatten, list_foldl, list_foldr, list_index,
    list_length, list_map, list_repeat, list_skip, list_take, nil, tail,
};

use covalence_core::defs::{
    finite, finite_spec, head_spec, list_index_spec, list_spec, nat_le, nat_rec, nat_succ, none,
    option, some, stream_const,
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
    Term::app(Term::app(stream_at(option(alpha.clone())), mk_stream(alpha, g)), n.clone())
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

    let all = Thm::nat_induct(base, step)?; // {body[N]} ⊢ ∀m. motive m
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

/// `⊢ finite (rep xs)` for any `xs : list α` — the carrier stream behind
/// a list really is finite. Derived without a hypothesis: instantiate the
/// witness-free back-law [`Thm::spec_rep_abs_back`] at `a := rep xs`,
/// discharge its premise `rep (abs (rep xs)) = rep xs` via the
/// unconditional `abs (rep xs) = xs` ([`Thm::spec_abs_rep`]), then kill
/// the spurious `¬∃s. finite s` disjunct with [`finite_nonempty`].
pub fn finite_rep(alpha: &Type, xs: &Term) -> Result<Thm> {
    let rep = Term::spec_rep(list_spec(), vec![alpha.clone()]);
    let rep_xs = Term::app(rep.clone(), xs.clone());

    // back: ⊢ rep (abs (rep xs)) = rep xs ⟹ (finite (rep xs) ∨ ¬∃s. finite s)
    let back = Thm::spec_rep_abs_back(list_spec(), vec![alpha.clone()], rep_xs.clone())?;

    // Premise: rep (abs (rep xs)) = rep xs, from abs (rep xs) = xs by cong.
    let abs_rep = Thm::spec_abs_rep(list_spec(), vec![alpha.clone()], xs.clone())?; // abs (rep xs) = xs
    let prem = abs_rep.cong_arg(rep)?; // rep (abs (rep xs)) = rep xs
    let disj = back.imp_elim(prem)?; // finite (rep xs) ∨ ¬∃x. (finite α) x

    // Eliminate the disjunction `P ∨ ¬∃x. (finite α) x`. Left: the goal
    // `finite (rep xs)` directly. Right: the negated existential
    // contradicts a freshly-built witness (`finite (streamConst none)`).
    let goal = Term::app(finite(alpha.clone()), rep_xs.clone()); // finite (rep xs)

    // Peel the right disjunct `¬(∃x. P x)` from `disj`, exactly as the
    // kernel built it (η-expanded predicate), and re-prove that `∃` with a
    // matching witness so `not_elim` sees identical terms.
    let not_some = disj
        .concl()
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone(); // ¬∃x. P x
    let some_x = not_some.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // ∃x. P x
    let pred_eta = some_x.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λx. (finite α) x

    // ⊢ ∃x. P x via witness `streamConst none` (β-reduce `P w` to `finite w`).
    let cst = const_none(alpha);
    let at_w = beta_expand(&pred_eta, cst.clone(), finite_const_none(alpha)?)?; // ⊢ P (streamConst none)
    let some_proof = exists_intro(pred_eta, cst, at_w)?; // ⊢ ∃x. P x

    let left = Thm::assume(goal.clone())?.imp_intro(&goal)?; // ⊢ finite (rep xs) ⟹ goal
    let contra = Thm::assume(not_some.clone())?.not_elim(some_proof)?; // {¬∃x} ⊢ F
    let right = contra.false_elim(goal.clone())?.imp_intro(&not_some)?; // ⊢ ¬∃x ⟹ goal
    disj.or_elim(left, right)
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
// `cons`-side element access.
// ============================================================================

/// `⊢ rep (cons x xs) = streamMk (consStream x xs)` — the carrier stream
/// behind `cons x xs`, with finiteness discharged by [`finite_cons`].
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
    let ra = rep_abs_finite(alpha, &made, finite_cons(alpha, x, xs)?)?;
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
    let idx = index_unfold(alpha, &zero(), &cons(alpha.clone()).apply(x.clone())?.apply(xs.clone())?)?;
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
    let head_eq = crate::init::eq::delta_head(&Term::app(stream_head(opt.clone()), mk_stream(alpha, &g)))?
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
    fn finite_rep_is_genuine() {
        let xs = Term::free("xs", list(alpha()));
        let thm = finite_rep(&alpha(), &xs).unwrap();
        assert!(thm.hyps().is_empty(), "finite_rep is proved, not postulated");
        assert!(thm.has_no_obs(), "finite_rep is oracle-free");
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
        assert!(thm.hyps().is_empty(), "finite_cons is proved, not postulated");
        assert!(thm.has_no_obs(), "finite_cons is oracle-free");
        // ⊢ finite (streamMk (consStream x xs))
        let g = cons_stream(&alpha(), &x, &xs);
        let expected = Term::app(finite(alpha()), mk_stream(&alpha(), &g));
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
    fn index_cons_zero_is_head() {
        let x = Term::free("x", alpha());
        let xs = Term::free("xs", list(alpha()));
        let thm = index_cons_zero(&alpha(), &x, &xs).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
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
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
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
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
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
