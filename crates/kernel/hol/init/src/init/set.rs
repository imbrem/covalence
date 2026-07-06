//! `set` theorems: the `defs/set.rs` catalogue re-exported, plus a
//! **high-level, implementation-hiding** proof API for sets — mirroring
//! how [`init::logic`] pairs the connective definitions with their
//! proved facts.
//!
//! [`init::logic`]: crate::init::logic
//!
//! ## The abstraction barrier
//!
//! `defs/set.rs` implements `set α` as a `newtype` over the membership
//! predicate `α → bool`, with every operation funnelling through the
//! `abs`/`rep` coercions (named [`set_mk`] / [`set_mem`]). **Downstream
//! set proofs must not see that.** They should reason entirely through
//! two primitives exposed here —
//!
//! - **membership computation** ([`mem_mk`] and the per-operation
//!   [`mem_empty`] / [`mem_singleton`] / [`mem_insert`] / [`mem_union`]
//!   / [`mem_intersect`] / [`mem_diff`] lemmas): `⊢ set.mem x (op …) =
//!   <bool formula>`; and
//! - **extensionality** ([`ext`]): from `⊢ ∀x. mem x s = mem x t`
//!   conclude `⊢ s = t`.
//!
//! On top of those sits the one-shot prover [`set_eq`]: it normalises
//! both sides' membership with [`mem_norm`] (recursively expanding
//! nested `∪ ∩ \ …`) and decides the resulting boolean equality with
//! [`prop_eq`] — so a whole set identity
//! (`union_comm`, `union_assoc`, `inter_union_distrib`, …) is stated and
//! discharged in one line. The [`subset_unfold`] / [`subset_refl`] /
//! [`subset_antisym`] family connects `⊆` to equality on the same
//! footing.
//!
//! Everything else (`union_comm`, …) is derived from those, and a
//! consumer that stays above this line never mentions `abs`/`rep`. The
//! `newtype` representation could be swapped for a literal-backed
//! builtin without touching a single downstream proof.
//!
//! ## `∪` / `∩` are AC
//!
//! [`union_comm`] / [`union_assoc`] (and [`inter_comm`] / [`inter_assoc`])
//! state union and intersection as commutative-associative **equations** — the
//! exact shape the model-generic AC rewriter [`crate::algebra::ac`] consumes. Build a
//! [`HolAc::from_free`](crate::algebra::ac::HolAc::from_free) over `set.union` /
//! `set.intersect` (free vars `s, t, u`) and the normalizer decides `∪`/`∩`
//! rearrangements the same way it does `+`/`∧` (see `ac::tests`).
//!
//! ## No postulates
//!
//! Unlike [`init::nat`] (whose recursion equations are still postulated
//! pending the recursion theorem), **`init::set` postulates nothing**.
//! The whole API bottoms out in the kernel's witness-free subtype laws
//! [`Thm::spec_abs_rep`] / [`Thm::spec_rep_abs_fwd`] — the round-trip
//! equations for a derived type — so every theorem here is genuine
//! (hypothesis- and oracle-free).
//!
//! [`init::nat`]: crate::init::nat

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::eq::{delta_head, spine, trans_chain};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{prop_eq, truth};

// Re-export the `defs/set.rs` term catalogue (the `*_spec` handles stay
// in `covalence_hol_eval::defs`, reached via the blanket re-export there).
pub use covalence_hol_eval::defs::{
    list_elems, set, set_all, set_any, set_card, set_card_opt, set_diff, set_empty, set_finite,
    set_flatten, set_image, set_insert, set_intersect, set_is_empty, set_mem, set_min, set_mk,
    set_preimage, set_singleton, set_subset, set_union,
};

use covalence_hol_eval::defs::{
    set_diff_spec, set_empty_spec, set_insert_spec, set_intersect_spec, set_mem_spec, set_mk_spec,
    set_singleton_spec, set_spec, set_subset_spec, set_union_spec,
};

// ============================================================================
// Term helpers (private — the public surface is membership lemmas + theorems)
// ============================================================================

/// `set.mem[α] x s : bool` — membership as a builder.
fn mem(alpha: &Type, x: &Term, s: &Term) -> Term {
    Term::app(Term::app(set_mem(alpha.clone()), x.clone()), s.clone())
}

/// `set.union[α] s t : set α`.
fn union(alpha: &Type, s: &Term, t: &Term) -> Term {
    Term::app(Term::app(set_union(alpha.clone()), s.clone()), t.clone())
}

// ============================================================================
// THE SEAM — the only code aware that `set` is a newtype over `α → bool`.
//
// `set.mk = λp. abs p` and `set.mem = λx s. (rep s) x`, so the two
// round-trip equations of the `set` newtype —
//   rep (abs p) = p   (carrier side, used by `mem_mk`)
//   abs (rep s) = s   (wrapper side, used by `ext`)
// — are exactly what membership computation and extensionality need.
// Both come straight from the kernel's subtype laws; `set`'s predicate
// is `λ_. T`, so the conditional `rep`-side law's premise is discharged
// by `truth`.
// ============================================================================

/// Raw `abs : (α → bool) → set α` coercion of the `set` newtype.
fn set_abs(alpha: &Type) -> Term {
    Term::spec_abs(set_spec(), vec![alpha.clone()])
}

/// `⊢ rep (abs p) = p` — the carrier-side round-trip. From the kernel's
/// [`Thm::spec_rep_abs_fwd`] (`⊢ (λ_. T) p ⟹ rep (abs p) = p` for the
/// `set` newtype), discharging the always-true premise via β + [`truth`].
fn rep_abs(alpha: &Type, p: &Term) -> Result<Thm> {
    let fwd = Thm::spec_rep_abs_fwd(set_spec(), vec![alpha.clone()], p.clone())?;
    // `fwd : ⊢ prem ⟹ (rep (abs p) = p)`; peel the antecedent `prem`.
    let (imp_p, _eq) = fwd.concl().as_app().ok_or(Error::NotAnEquation)?;
    let (_imp, prem) = imp_p.as_app().ok_or(Error::NotAnEquation)?;
    // `prem = (λ_. T) p`  →β  `T`; transport `⊢ T` back across it.
    let prem_thm = Thm::beta_conv(prem.clone())?.sym()?.eq_mp(truth())?;
    fwd.imp_elim(prem_thm)
}

/// `⊢ abs (rep s) = s` — the wrapper-side round-trip, straight from the
/// kernel's unconditional [`Thm::spec_abs_rep`].
fn abs_rep(alpha: &Type, s: &Term) -> Result<Thm> {
    Thm::spec_abs_rep(set_spec(), vec![alpha.clone()], s.clone())
}

// ============================================================================
// Foundation: membership computation + extensionality.
// ============================================================================

/// `⊢ set.mem x (set.mk p) = p x` — the defining computation of
/// membership against a predicate-built set. The bridge from the
/// `set.mk` constructor to its membership predicate; every per-operation
/// `mem_*` lemma is this plus a δ/β unfolding of the operation.
pub fn mem_mk(alpha: &Type, x: &Term, p: &Term) -> Result<Thm> {
    // set.mem x (set.mk p):  δ-unfold `set.mem` then `set.mk`, βι-reduce
    // to `(rep (abs p)) x`, then collapse `rep (abs p)` to `p`.
    let mk_p = Term::app(set_mk(alpha.clone()), p.clone());
    let lhs = mem(alpha, x, &mk_p);
    let d_mem = lhs.delta_all(set_mem_spec().symbol())?; // = (λx s. rep s x) x (set.mk p)
    let after_mem = rhs_of(&d_mem)?;
    let d_mk = after_mem.delta_all(set_mk_spec().symbol())?; // unfold the inner set.mk
    let reduced = rhs_of(&d_mk)?.reduce()?; // βι → (rep (abs p)) x
    // `rep (abs p) = p`, lifted to `(rep (abs p)) x = p x` by congruence.
    let cong = rep_abs(alpha, p)?.cong_fn(x.clone())?;
    trans_chain([d_mem, d_mk, reduced, cong])
}

/// **Set extensionality.** From `mem_eq : Γ ⊢ ∀x. set.mem x s = set.mem
/// x t`, conclude `Γ ⊢ s = t`. The companion to [`mem_mk`]: together
/// they are the complete interface to `set`, hiding `abs`/`rep`.
///
/// Derivation (HOL Light's `EQ_EXT` over the newtype): each side's
/// membership is `(rep ·) x`, so `∀x. (rep s) x = (rep t) x`; `abs` +
/// η-contraction give `rep s = rep t`, congruence under `abs` gives
/// `abs (rep s) = abs (rep t)`, and the wrapper round-trip `abs_rep`
/// rewrites both sides to `s` and `t`.
pub fn ext(alpha: &Type, s: &Term, t: &Term, mem_eq: Thm) -> Result<Thm> {
    const PT: &str = "_ext_x";
    let v = Term::free(PT, alpha.clone());
    let pointwise = mem_eq.all_elim(v.clone())?; // Γ ⊢ mem v s = mem v t
    // Rewrite each membership to the raw `(rep ·) v`.
    let rep_s = mem_rep(alpha, &v, s)?; // ⊢ mem v s = (rep s) v
    let rep_t = mem_rep(alpha, &v, t)?; // ⊢ mem v t = (rep t) v
    let rep_pointwise = rep_s.sym()?.trans(pointwise)?.trans(rep_t)?; // Γ ⊢ (rep s) v = (rep t) v
    // ABS then η on both sides: rep s = rep t.
    let abstracted = rep_pointwise.abs(PT, alpha.clone())?; // Γ ⊢ (λv. (rep s) v) = (λv. (rep t) v)
    let reps_eq = abstracted
        .lhs_conv(|tm| Thm::eta_conv(tm.clone()))?
        .rhs_conv(|tm| Thm::eta_conv(tm.clone()))?; // Γ ⊢ rep s = rep t
    // Congruence under `abs`, then collapse `abs (rep ·)` on each side.
    let abs_cong = reps_eq.cong_arg(set_abs(alpha))?; // Γ ⊢ abs (rep s) = abs (rep t)
    let s_eq = abs_rep(alpha, s)?; // ⊢ abs (rep s) = s
    let t_eq = abs_rep(alpha, t)?; // ⊢ abs (rep t) = t
    s_eq.sym()?.trans(abs_cong)?.trans(t_eq) // Γ ⊢ s = t
}

/// `⊢ set.mem x s = (rep s) x` — unfold membership to the raw `rep`
/// coercion (no `set.mk` involved, so `s` stays opaque). Internal to the
/// seam.
fn mem_rep(alpha: &Type, x: &Term, s: &Term) -> Result<Thm> {
    let lhs = mem(alpha, x, s);
    let d = lhs.delta_all(set_mem_spec().symbol())?; // = (λx s. rep s x) x s
    d.rhs_conv(|tm| tm.reduce()) // βι → (rep s) x
}

// ============================================================================
// Membership lemmas — the high-level computational surface.
//
// Each says `mem x (op args) = <bool formula>` and is proved uniformly:
// δ-unfold the *head* operation only (leaving its set arguments opaque)
// to expose `set.mk pred`, push membership through with `mem_mk`, then
// β-reduce `pred x` to the formula.
// ============================================================================

/// `⊢ set.mem x set.empty = F`.
pub fn mem_empty(alpha: &Type, x: &Term) -> Result<Thm> {
    mem_of(alpha, x, &set_empty(alpha.clone()))
}

/// `⊢ set.mem x (set.singleton a) = (x = a)`.
pub fn mem_singleton(alpha: &Type, x: &Term, a: &Term) -> Result<Thm> {
    mem_of(
        alpha,
        x,
        &Term::app(set_singleton(alpha.clone()), a.clone()),
    )
}

/// `⊢ set.mem x (set.insert a s) = (x = a ∨ set.mem x s)`.
pub fn mem_insert(alpha: &Type, x: &Term, a: &Term, s: &Term) -> Result<Thm> {
    mem_of(
        alpha,
        x,
        &Term::app(Term::app(set_insert(alpha.clone()), a.clone()), s.clone()),
    )
}

/// `⊢ set.mem x (set.union s t) = (set.mem x s ∨ set.mem x t)`.
pub fn mem_union(alpha: &Type, x: &Term, s: &Term, t: &Term) -> Result<Thm> {
    mem_of(alpha, x, &union(alpha, s, t))
}

/// `⊢ set.mem x (set.intersect s t) = (set.mem x s ∧ set.mem x t)`.
pub fn mem_intersect(alpha: &Type, x: &Term, s: &Term, t: &Term) -> Result<Thm> {
    mem_of(alpha, x, &inter(alpha, s, t))
}

/// `⊢ set.mem x (set.diff s t) = (set.mem x s ∧ ¬ set.mem x t)`.
pub fn mem_diff(alpha: &Type, x: &Term, s: &Term, t: &Term) -> Result<Thm> {
    mem_of(
        alpha,
        x,
        &Term::app(Term::app(set_diff(alpha.clone()), s.clone()), t.clone()),
    )
}

/// `⊢ set.mem x st = body[x]`, where `st = op a₁ … aₙ` and the **head**
/// operation `op` δ-unfolds (its arguments staying opaque) so the body
/// β-reduces to `set.mk (λ. body)`. The shared engine of the `mem_*`
/// lemmas.
fn mem_of(alpha: &Type, x: &Term, st: &Term) -> Result<Thm> {
    // st = set.mk pred  (δ-unfold ONLY the head op, β-reduce the spine).
    let as_mk = delta_head(st)?.rhs_conv(|t| t.reduce())?;
    let mk_pred = rhs_of(&as_mk)?;
    let pred = mk_pred.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    // mem x st = mem x (set.mk pred):
    let mem_head = Term::app(set_mem(alpha.clone()), x.clone());
    let step1 = as_mk.cong_arg(mem_head)?;
    // mem x (set.mk pred) = pred x:
    let step2 = mem_mk(alpha, x, &pred)?;
    // pred x = body[x] by β.
    let step3 = rhs_of(&step2)?.reduce()?;
    trans_chain([step1, step2, step3])
}

// ============================================================================
// Membership normalisation — recursively compute `mem x st` to a boolean
// formula over the *atomic* memberships `mem x <var>`.
// ============================================================================

/// `⊢ set.mem x st = <bool formula>`, fully expanding a nested set
/// expression `st` (built from `∪ ∩ \ insert singleton ∅`) down to a
/// propositional combination of atomic memberships `set.mem x <leaf>`.
/// The recursive engine behind [`set_eq`]: each node fires its `mem_*`
/// lemma, then its set-valued children are normalised and rewritten in.
/// Opaque leaves (a free `set` variable, an operation not handled here)
/// are left as `set.mem x <leaf>` atoms.
pub fn mem_norm(alpha: &Type, x: &Term, st: &Term) -> Result<Thm> {
    let (head, args) = spine(st);
    let label = head.as_spec().map(|(s, _)| s.symbol().label());
    let label = match label {
        Some(l) => l,
        None => return Thm::refl(mem(alpha, x, st)), // free var / non-spec head
    };
    if label == set_union_spec().symbol().label() && args.len() == 2 {
        let base = mem_union(alpha, x, args[0], args[1])?;
        expand_children(alpha, x, base, &[args[0], args[1]])
    } else if label == set_intersect_spec().symbol().label() && args.len() == 2 {
        let base = mem_intersect(alpha, x, args[0], args[1])?;
        expand_children(alpha, x, base, &[args[0], args[1]])
    } else if label == set_diff_spec().symbol().label() && args.len() == 2 {
        let base = mem_diff(alpha, x, args[0], args[1])?;
        expand_children(alpha, x, base, &[args[0], args[1]])
    } else if label == set_insert_spec().symbol().label() && args.len() == 2 {
        // insert a s: only `s` (the second arg) is a set to recurse into.
        let base = mem_insert(alpha, x, args[0], args[1])?;
        expand_children(alpha, x, base, &[args[1]])
    } else if label == set_singleton_spec().symbol().label() && args.len() == 1 {
        mem_singleton(alpha, x, args[0])
    } else if label == set_empty_spec().symbol().label() && args.is_empty() {
        mem_empty(alpha, x)
    } else {
        Thm::refl(mem(alpha, x, st)) // an operation we don't normalise
    }
}

/// Rewrite each `set.mem x child` atom in `base`'s right-hand side by
/// the child's own [`mem_norm`], expanding the formula bottom-up.
fn expand_children(alpha: &Type, x: &Term, base: Thm, children: &[&Term]) -> Result<Thm> {
    let mut acc = base;
    for child in children {
        let child_norm = mem_norm(alpha, x, child)?; // ⊢ mem x child = formula
        acc = acc.rhs_conv(|t| t.rw_all(&child_norm))?;
    }
    Ok(acc)
}

// ============================================================================
// `set_eq` — decide a set equality by membership + propositional reasoning.
// ============================================================================

/// `⊢ s = t` for set expressions `s`, `t` whose memberships are
/// propositionally equal. Normalises `set.mem x s` and `set.mem x t`
/// with [`mem_norm`], bridges the two boolean formulas with
/// [`prop_eq`] (which handles commutativity,
/// associativity, distribution, …), and closes by [`ext`]. This is the
/// one-shot prover the set-algebra theorems below are built on — a
/// consumer states the equation and `set_eq` discharges it, never
/// touching `abs`/`rep`. Errors if the memberships are not propositionally
/// equal.
pub fn set_eq(alpha: &Type, s: &Term, t: &Term) -> Result<Thm> {
    const PT: &str = "_set_x";
    let x = Term::free(PT, alpha.clone());
    let ns = mem_norm(alpha, &x, s)?; // ⊢ mem x s = Bs
    let nt = mem_norm(alpha, &x, t)?; // ⊢ mem x t = Bt
    let bridge = prop_eq(&rhs_of(&ns)?, &rhs_of(&nt)?)?; // ⊢ Bs = Bt
    let mem_eq = ns.trans(bridge)?.trans(nt.sym()?)?; // ⊢ mem x s = mem x t
    let all = mem_eq.all_intro(PT, alpha.clone())?;
    ext(alpha, s, t, all)
}

// ============================================================================
// Set-algebra theorems — each a one-liner over `set_eq`.
// ============================================================================

/// `⊢ set.union s t = set.union t s` — union is commutative.
pub fn union_comm() -> Thm {
    let (a, s, t, _u) = vars();
    set_eq(&a, &union(&a, &s, &t), &union(&a, &t, &s)).expect("union.comm")
}

/// `⊢ set.intersect s t = set.intersect t s` — intersection is commutative.
pub fn inter_comm() -> Thm {
    let (a, s, t, _u) = vars();
    set_eq(&a, &inter(&a, &s, &t), &inter(&a, &t, &s)).expect("inter.comm")
}

/// `⊢ set.union (set.union s t) u = set.union s (set.union t u)` —
/// union is associative.
pub fn union_assoc() -> Thm {
    let (a, s, t, u) = vars();
    let lhs = union(&a, &union(&a, &s, &t), &u);
    let rhs = union(&a, &s, &union(&a, &t, &u));
    set_eq(&a, &lhs, &rhs).expect("union.assoc")
}

/// `⊢ set.intersect (set.intersect s t) u = set.intersect s
/// (set.intersect t u)` — intersection is associative.
pub fn inter_assoc() -> Thm {
    let (a, s, t, u) = vars();
    let lhs = inter(&a, &inter(&a, &s, &t), &u);
    let rhs = inter(&a, &s, &inter(&a, &t, &u));
    set_eq(&a, &lhs, &rhs).expect("inter.assoc")
}

/// `⊢ set.union s s = s` — union is idempotent.
pub fn union_idem() -> Thm {
    let (a, s, _t, _u) = vars();
    set_eq(&a, &union(&a, &s, &s), &s).expect("union.idem")
}

/// `⊢ set.intersect s s = s` — intersection is idempotent.
pub fn inter_idem() -> Thm {
    let (a, s, _t, _u) = vars();
    set_eq(&a, &inter(&a, &s, &s), &s).expect("inter.idem")
}

/// `⊢ set.union s set.empty = s` — `∅` is a (right) identity for union.
pub fn union_empty() -> Thm {
    let (a, s, _t, _u) = vars();
    set_eq(&a, &union(&a, &s, &set_empty(a.clone())), &s).expect("union.empty")
}

/// `⊢ set.intersect s set.empty = set.empty` — `∅` absorbs intersection.
pub fn inter_empty() -> Thm {
    let (a, s, _t, _u) = vars();
    let empty = set_empty(a.clone());
    set_eq(&a, &inter(&a, &s, &empty), &empty).expect("inter.empty")
}

/// `⊢ set.intersect s (set.union t u) = set.union (set.intersect s t)
/// (set.intersect s u)` — intersection distributes over union.
pub fn inter_union_distrib() -> Thm {
    let (a, s, t, u) = vars();
    let lhs = inter(&a, &s, &union(&a, &t, &u));
    let rhs = union(&a, &inter(&a, &s, &t), &inter(&a, &s, &u));
    set_eq(&a, &lhs, &rhs).expect("inter.union_distrib")
}

// ============================================================================
// Subset — the high-level interface is `subset_intro` / `subset_elim`
// (the membership characterisation), out of which the order laws follow.
// ============================================================================

/// `⊢ set.subset s t = (∀x. set.mem x s ⟹ set.mem x t)` — the defining
/// unfolding of `⊆`.
pub fn subset_unfold(alpha: &Type, s: &Term, t: &Term) -> Result<Thm> {
    let st = subset_tm(alpha, s, t);
    st.delta_all(set_subset_spec().symbol())?
        .rhs_conv(|x| x.reduce())
}

/// **Subset introduction.** From `all_imp : Γ ⊢ ∀x. set.mem x s ⟹
/// set.mem x t`, conclude `Γ ⊢ set.subset s t`. The `⊆` companion to
/// [`ext`] — proofs build `⊆` facts through this, never by unfolding the
/// definition.
pub fn subset_intro(alpha: &Type, s: &Term, t: &Term, all_imp: Thm) -> Result<Thm> {
    subset_unfold(alpha, s, t)?.sym()?.eq_mp(all_imp)
}

/// **Subset elimination.** From `sub : Γ ⊢ set.subset s t`, recover
/// `Γ ⊢ ∀x. set.mem x s ⟹ set.mem x t`.
pub fn subset_elim(alpha: &Type, s: &Term, t: &Term, sub: Thm) -> Result<Thm> {
    subset_unfold(alpha, s, t)?.eq_mp(sub)
}

/// `⊢ set.subset s s` — `⊆` is reflexive.
pub fn subset_refl() -> Thm {
    let (a, s, _t, _u) = vars();
    pointwise_subset(&a, &s, &s, |v| {
        let ms = mem(&a, v, &s);
        Thm::assume(ms.clone())?.imp_intro(&ms) // ⊢ mem v s ⟹ mem v s
    })
    .expect("subset.refl")
}

/// `⊢ set.subset s t ⟹ set.subset t u ⟹ set.subset s u` — transitivity
/// of `⊆`.
pub fn subset_trans() -> Thm {
    let (a, s, t, u) = vars();
    let v = Term::free("x", a.clone());
    let sub_st = subset_tm(&a, &s, &t);
    let sub_tu = subset_tm(&a, &t, &u);

    let build = || -> Result<Thm> {
        let imp_st = subset_elim(&a, &s, &t, Thm::assume(sub_st.clone())?)?.all_elim(v.clone())?;
        let imp_tu = subset_elim(&a, &t, &u, Thm::assume(sub_tu.clone())?)?.all_elim(v.clone())?;
        // mem v s ⟹ mem v u: chain the two implications through mem v t.
        let mem_s = Thm::assume(mem(&a, &v, &s))?;
        let mem_u = imp_tu.imp_elim(imp_st.imp_elim(mem_s)?)?; // {s⊆t, t⊆u, mem v s} ⊢ mem v u
        let all = mem_u
            .imp_intro(&mem(&a, &v, &s))?
            .all_intro("x", a.clone())?;
        let sub_su = subset_intro(&a, &s, &u, all)?; // {s⊆t, t⊆u} ⊢ s ⊆ u
        sub_su.imp_intro(&sub_tu)?.imp_intro(&sub_st)
    };
    build().expect("subset.trans")
}

/// `⊢ set.subset s t ⟹ set.subset t s ⟹ s = t` — antisymmetry of `⊆`,
/// the subset route to set equality. Each direction supplies one half of
/// the membership equivalence at every point; [`ext`] then concludes.
pub fn subset_antisym() -> Thm {
    let (a, s, t, _u) = vars();
    let v = Term::free("x", a.clone());
    let sub_st = subset_tm(&a, &s, &t);
    let sub_ts = subset_tm(&a, &t, &s);

    let build = || -> Result<Thm> {
        let imp_st = subset_elim(&a, &s, &t, Thm::assume(sub_st.clone())?)?.all_elim(v.clone())?;
        let imp_ts = subset_elim(&a, &t, &s, Thm::assume(sub_ts.clone())?)?.all_elim(v.clone())?;
        let s_to_t = imp_st.imp_elim(Thm::assume(mem(&a, &v, &s))?)?; // {…, mem v s} ⊢ mem v t
        let t_to_s = imp_ts.imp_elim(Thm::assume(mem(&a, &v, &t))?)?; // {…, mem v t} ⊢ mem v s
        let mem_eq = t_to_s.deduct_antisym(s_to_t)?; // {s⊆t, t⊆s} ⊢ mem v s = mem v t
        let all_eq = mem_eq.all_intro("x", a.clone())?;
        let s_eq_t = ext(&a, &s, &t, all_eq)?; // {s⊆t, t⊆s} ⊢ s = t
        s_eq_t.imp_intro(&sub_ts)?.imp_intro(&sub_st)
    };
    build().expect("subset.antisym")
}

/// `⊢ set.subset set.empty s` — `∅` is the least set.
pub fn empty_subset() -> Thm {
    let (a, s, _t, _u) = vars();
    let empty = set_empty(a.clone());
    pointwise_subset(&a, &empty, &s, |v| {
        // mem v ∅ ⟹ mem v s : the antecedent is `F`, so ex falso.
        let mem_empty_v = mem(&a, v, &empty);
        let f = mem_empty(&a, v)?.eq_mp(Thm::assume(mem_empty_v.clone())?)?; // {mem v ∅} ⊢ F
        f.false_elim(mem(&a, v, &s))?.imp_intro(&mem_empty_v)
    })
    .expect("empty.subset")
}

/// `⊢ set.subset s (set.union s t)` — a set is contained in its unions.
pub fn subset_union_l() -> Thm {
    let (a, s, t, _u) = vars();
    let st = union(&a, &s, &t);
    pointwise_subset(&a, &s, &st, |v| {
        // mem v s ⟹ mem v (s∪t) : inject on the left, refold via mem_union.
        let disj = Thm::assume(mem(&a, v, &s))?.or_intro_l(mem(&a, v, &t))?; // {mem v s} ⊢ mem v s ∨ mem v t
        mem_union(&a, v, &s, &t)?
            .sym()?
            .eq_mp(disj)? // {mem v s} ⊢ mem v (s∪t)
            .imp_intro(&mem(&a, v, &s))
    })
    .expect("subset.union_l")
}

/// `⊢ set.subset (set.intersect s t) s` — an intersection is contained in
/// its factors.
pub fn inter_subset_l() -> Thm {
    let (a, s, t, _u) = vars();
    let st = inter(&a, &s, &t);
    pointwise_subset(&a, &st, &s, |v| {
        // mem v (s∩t) ⟹ mem v s : unfold to the conjunction, take the left.
        let conj = mem_intersect(&a, v, &s, &t)?.eq_mp(Thm::assume(mem(&a, v, &st))?)?;
        conj.and_elim_l()?.imp_intro(&mem(&a, v, &st))
    })
    .expect("inter.subset_l")
}

/// `⊢ set.subset s t` from a per-point `branch` proving
/// `⊢ set.mem v s ⟹ set.mem v t` (for the canonical witness `v = "x"`),
/// closed with [`subset_intro`]. The shared shape of the `⊆` lemmas.
fn pointwise_subset(
    alpha: &Type,
    s: &Term,
    t: &Term,
    branch: impl FnOnce(&Term) -> Result<Thm>,
) -> Result<Thm> {
    let v = Term::free("x", alpha.clone());
    let all = branch(&v)?.all_intro("x", alpha.clone())?;
    subset_intro(alpha, s, t, all)
}

/// `set.subset[α] s t : bool` — builder.
fn subset_tm(alpha: &Type, s: &Term, t: &Term) -> Term {
    Term::app(Term::app(set_subset(alpha.clone()), s.clone()), t.clone())
}

/// `set.intersect[α] s t : set α`.
fn inter(alpha: &Type, s: &Term, t: &Term) -> Term {
    Term::app(
        Term::app(set_intersect(alpha.clone()), s.clone()),
        t.clone(),
    )
}

/// Canonical free `(α, s, t, u)` for the closed algebra theorems.
fn vars() -> (Type, Term, Term, Term) {
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    (
        alpha.clone(),
        Term::free("s", sa.clone()),
        Term::free("t", sa.clone()),
        Term::free("u", sa),
    )
}

// ============================================================================
// Small accessors.
// ============================================================================

/// The right-hand side of an equational theorem.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

// ============================================================================
// `setprim` env + the `set.cov` port.
// ============================================================================

/// The `setprim` environment imported by `set.cov`: the `set` operators
/// (monomorphic at the type variable `'a` — the algebra theorems are all
/// schematic in one element type) plus the **seam** lemmas (membership
/// computation `mem_*`, extensionality `ext`, and the `⊆` unfolding) in
/// universally-quantified form. These cross the abs/rep boundary via the
/// kernel's subtype laws, so they stay Rust-proved givens (the `nat.cov`
/// `rec_holds` pattern); `set.cov` proves the algebra/order theorems over them
/// and never mentions abs/rep.
pub fn set_env() -> crate::script::Env {
    use crate::script::{ConstDef, Env};
    let a = Type::tfree("a");
    let sa = set(a.clone());
    let mut e = Env::empty();

    // operators (monomorphic at `'a`)
    e.define_const("set.mem", ConstDef::Op(set_mem(a.clone())));
    e.define_const("set.union", ConstDef::Op(set_union(a.clone())));
    e.define_const("set.intersect", ConstDef::Op(set_intersect(a.clone())));
    e.define_const("set.empty", ConstDef::Op(set_empty(a.clone())));
    e.define_const("set.subset", ConstDef::Op(set_subset(a.clone())));

    let x = Term::free("x", a.clone());
    let s = Term::free("s", sa.clone());
    let t = Term::free("t", sa.clone());

    // mem_empty : ⊢ ∀x. mem x ∅ = F
    e.define_lemma(
        "mem.empty",
        mem_empty(&a, &x)
            .unwrap()
            .all_intro("x", a.clone())
            .unwrap(),
    );
    // mem_union : ⊢ ∀x s t. mem x (s ∪ t) = (mem x s ∨ mem x t)
    e.define_lemma(
        "mem.union",
        mem_union(&a, &x, &s, &t)
            .unwrap()
            .all_intro("t", sa.clone())
            .unwrap()
            .all_intro("s", sa.clone())
            .unwrap()
            .all_intro("x", a.clone())
            .unwrap(),
    );
    // mem_intersect : ⊢ ∀x s t. mem x (s ∩ t) = (mem x s ∧ mem x t)
    e.define_lemma(
        "mem.intersect",
        mem_intersect(&a, &x, &s, &t)
            .unwrap()
            .all_intro("t", sa.clone())
            .unwrap()
            .all_intro("s", sa.clone())
            .unwrap()
            .all_intro("x", a.clone())
            .unwrap(),
    );
    // ext : ⊢ ∀s t. (∀x. mem x s = mem x t) ⟹ s = t
    let h = mem(&a, &x, &s)
        .equals(mem(&a, &x, &t))
        .unwrap()
        .forall("x", a.clone())
        .unwrap();
    e.define_lemma(
        "ext",
        ext(&a, &s, &t, Thm::assume(h.clone()).unwrap())
            .unwrap()
            .imp_intro(&h)
            .unwrap()
            .all_intro("t", sa.clone())
            .unwrap()
            .all_intro("s", sa.clone())
            .unwrap(),
    );
    // subset_unfold : ⊢ ∀s t. subset s t = (∀x. mem x s ⟹ mem x t)
    e.define_lemma(
        "subset.unfold",
        subset_unfold(&a, &s, &t)
            .unwrap()
            .all_intro("t", sa.clone())
            .unwrap()
            .all_intro("s", sa.clone())
            .unwrap(),
    );
    e
}

crate::cov_theory! {
    /// `set` algebra/order theorems ported to `set.cov`, over `core` + `logic`
    /// + the `setprim` seam env.
    pub mod cov from "set.cov" {
        import "core" = crate::script::Env::core();
        import "logic" = crate::init::logic::cov::env();
        import "setprim" = crate::init::set::set_env();
        "union.comm"          => pub fn union_comm_cov;
        "inter.comm"          => pub fn inter_comm_cov;
        "union.assoc"         => pub fn union_assoc_cov;
        "inter.assoc"         => pub fn inter_assoc_cov;
        "union.idem"          => pub fn union_idem_cov;
        "inter.idem"          => pub fn inter_idem_cov;
        "union.empty"         => pub fn union_empty_cov;
        "inter.empty"         => pub fn inter_empty_cov;
        "inter.union_distrib" => pub fn inter_union_distrib_cov;
        "subset.refl"         => pub fn subset_refl_cov;
        "subset.trans"        => pub fn subset_trans_cov;
        "subset.antisym"      => pub fn subset_antisym_cov;
        "empty.subset"        => pub fn empty_subset_cov;
        "subset.union_l"      => pub fn subset_union_l_cov;
        "inter.subset_l"      => pub fn inter_subset_l_cov;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> Type {
        Type::tfree("a")
    }

    fn setvar(name: &str) -> Term {
        Term::free(name, set(alpha()))
    }

    fn elem(name: &str) -> Term {
        Term::free(name, alpha())
    }

    #[test]
    fn mem_mk_computes() {
        // mem x (mk (λy. y = a)) = (x = a).
        let x = elem("x");
        let a = elem("a");
        let pred = Term::abs(alpha(), {
            // λy. y = a  (closed in `y`)
            let y = Term::free("y", alpha());
            covalence_core::subst::close(&y.equals(a.clone()).unwrap(), "y")
        });
        let thm = mem_mk(&alpha(), &x, &pred).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let mk_p = Term::app(set_mk(alpha()), pred.clone());
        assert_eq!(lhs, &mem(&alpha(), &x, &mk_p));
        // `mem_mk` lands on the raw application `p x` (β is the caller's
        // job — `mem_of` follows up with a reduce); here `p x = (λy. y=a) x`,
        // which β-reduces to `x = a`.
        assert_eq!(
            rhs,
            &Term::app(pred, x.clone()),
            "membership reduces to `p x`"
        );
        assert_eq!(
            rhs.reduce().unwrap().concl().as_eq().unwrap().1,
            &x.equals(a).unwrap(),
            "`p x` β-reduces to `x = a`"
        );
    }

    #[test]
    fn mem_empty_is_false() {
        let thm = mem_empty(&alpha(), &elem("x")).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(rhs_of(&thm).unwrap(), Term::bool_lit(false));
    }

    #[test]
    fn mem_union_is_disjunction() {
        let (x, s, t) = (elem("x"), setvar("s"), setvar("t"));
        let thm = mem_union(&alpha(), &x, &s, &t).unwrap();
        assert!(thm.hyps().is_empty());
        let expected = mem(&alpha(), &x, &s).or(mem(&alpha(), &x, &t)).unwrap();
        assert_eq!(rhs_of(&thm).unwrap(), expected);
    }

    #[test]
    fn mem_intersect_is_conjunction() {
        let (x, s, t) = (elem("x"), setvar("s"), setvar("t"));
        let thm = mem_intersect(&alpha(), &x, &s, &t).unwrap();
        let expected = mem(&alpha(), &x, &s).and(mem(&alpha(), &x, &t)).unwrap();
        assert_eq!(rhs_of(&thm).unwrap(), expected);
    }

    #[test]
    fn mem_singleton_is_equality() {
        let (x, a) = (elem("x"), elem("a"));
        let thm = mem_singleton(&alpha(), &x, &a).unwrap();
        assert_eq!(rhs_of(&thm).unwrap(), x.equals(a).unwrap());
    }

    #[test]
    fn ext_from_pointwise_membership() {
        // A trivial use of ext: reflexive membership ⟹ s = s.
        let s = setvar("s");
        let v = Term::free("_ext_x", alpha());
        let refl = Thm::refl(mem(&alpha(), &v, &s)).unwrap();
        let all = refl.all_intro("_ext_x", alpha()).unwrap();
        let eq = ext(&alpha(), &s, &s, all).unwrap();
        assert_eq!(eq.concl(), &s.clone().equals(s).unwrap());
    }

    #[test]
    fn union_comm_is_genuine() {
        let thm = union_comm();
        assert!(
            thm.hyps().is_empty(),
            "union.comm is proved, not postulated"
        );
        let alpha = alpha();
        let s = setvar("s");
        let t = setvar("t");
        let expected = union(&alpha, &s, &t).equals(union(&alpha, &t, &s)).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn inter_comm_is_genuine() {
        let thm = inter_comm();
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn union_empty_right_identity() {
        let thm = union_empty();
        assert!(thm.hyps().is_empty(), "union.empty is proved");
        let alpha = alpha();
        let s = setvar("s");
        let expected = union(&alpha, &s, &set_empty(alpha.clone()))
            .equals(s)
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    /// Every algebra theorem must be a genuine, oracle-free equation.
    fn assert_genuine_eq(thm: &Thm) {
        assert!(
            thm.hyps().is_empty(),
            "theorem must be proved, not postulated"
        );
    }

    #[test]
    fn algebra_laws_are_genuine() {
        for thm in [
            union_assoc(),
            inter_assoc(),
            union_idem(),
            inter_idem(),
            inter_empty(),
            inter_union_distrib(),
        ] {
            assert_genuine_eq(&thm);
            assert!(thm.concl().as_eq().is_some(), "conclusion is an equation");
        }
    }

    #[test]
    fn union_idem_collapses() {
        let thm = union_idem();
        let s = setvar("s");
        assert_eq!(thm.concl(), &union(&alpha(), &s, &s).equals(s).unwrap());
    }

    #[test]
    fn inter_union_distrib_shape() {
        // s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u).
        let thm = inter_union_distrib();
        let (a, s, t, u) = vars();
        let lhs = inter(&a, &s, &union(&a, &t, &u));
        let rhs = union(&a, &inter(&a, &s, &t), &inter(&a, &s, &u));
        assert_eq!(thm.concl(), &lhs.equals(rhs).unwrap());
    }

    #[test]
    fn subset_refl_is_genuine() {
        let thm = subset_refl();
        assert!(thm.hyps().is_empty());
        let s = setvar("s");
        assert_eq!(thm.concl(), &subset_tm(&alpha(), &s, &s));
    }

    #[test]
    fn subset_order_laws_are_genuine() {
        for thm in [
            subset_refl(),
            subset_trans(),
            empty_subset(),
            subset_union_l(),
            inter_subset_l(),
        ] {
            assert!(thm.hyps().is_empty(), "subset law must be proved");
        }
    }

    #[test]
    fn subset_trans_shape() {
        let thm = subset_trans();
        let (a, s, t, u) = vars();
        let expected = subset_tm(&a, &s, &t)
            .imp(subset_tm(&a, &t, &u).imp(subset_tm(&a, &s, &u)).unwrap())
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn empty_subset_shape() {
        let (a, s, _t, _u) = vars();
        let thm = empty_subset();
        assert_eq!(thm.concl(), &subset_tm(&a, &set_empty(a.clone()), &s));
    }

    #[test]
    fn subset_union_and_inter_bounds() {
        let (a, s, t, _u) = vars();
        assert_eq!(
            subset_union_l().concl(),
            &subset_tm(&a, &s, &union(&a, &s, &t))
        );
        assert_eq!(
            inter_subset_l().concl(),
            &subset_tm(&a, &inter(&a, &s, &t), &s)
        );
    }

    #[test]
    fn subset_antisym_shape() {
        // ⊢ s ⊆ t ⟹ t ⊆ s ⟹ s = t.
        let thm = subset_antisym();
        assert!(thm.hyps().is_empty(), "subset.antisym is proved");
        let (a, s, t, _u) = vars();
        let expected = subset_tm(&a, &s, &t)
            .imp(subset_tm(&a, &t, &s).imp(s.equals(t).unwrap()).unwrap())
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn set_cov_matches_rust() {
        // The ported `set.cov` theorems must state exactly what the Rust
        // proofs state (same checked theorem, two proofs — over the seam env).
        assert_eq!(cov::union_comm_cov().concl(), super::union_comm().concl());
        assert_eq!(cov::inter_comm_cov().concl(), super::inter_comm().concl());
        assert_eq!(cov::union_assoc_cov().concl(), super::union_assoc().concl());
        assert_eq!(cov::inter_assoc_cov().concl(), super::inter_assoc().concl());
        assert_eq!(cov::union_idem_cov().concl(), super::union_idem().concl());
        assert_eq!(cov::inter_idem_cov().concl(), super::inter_idem().concl());
        assert_eq!(cov::union_empty_cov().concl(), super::union_empty().concl());
        assert_eq!(cov::inter_empty_cov().concl(), super::inter_empty().concl());
        assert_eq!(
            cov::inter_union_distrib_cov().concl(),
            super::inter_union_distrib().concl()
        );
        assert_eq!(cov::subset_refl_cov().concl(), super::subset_refl().concl());
        assert_eq!(
            cov::subset_trans_cov().concl(),
            super::subset_trans().concl()
        );
        assert_eq!(
            cov::subset_antisym_cov().concl(),
            super::subset_antisym().concl()
        );
        assert_eq!(
            cov::empty_subset_cov().concl(),
            super::empty_subset().concl()
        );
        assert_eq!(
            cov::subset_union_l_cov().concl(),
            super::subset_union_l().concl()
        );
        assert_eq!(
            cov::inter_subset_l_cov().concl(),
            super::inter_subset_l().concl()
        );
    }

    #[test]
    fn subset_unfold_exposes_forall_imp() {
        let (a, s, t, _u) = vars();
        let thm = subset_unfold(&a, &s, &t).unwrap();
        // lhs is `set.subset s t`; rhs is a `∀`-headed term.
        let (lhs, _rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &subset_tm(&a, &s, &t));
    }
}
