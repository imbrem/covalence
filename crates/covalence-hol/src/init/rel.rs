//! `rel` theorems: the `defs/rel.rs` catalogue re-exported, plus a
//! **high-level, implementation-hiding** proof API for relations —
//! mirroring how [`init::set`] pairs the `set` definitions with their
//! proved facts.
//!
//! [`init::set`]: crate::init::set
//!
//! ## The abstraction barrier
//!
//! `defs/rel.rs` implements `rel α β` as a `newtype` over the two-place
//! predicate `α → β → bool`, with every operation funnelling through the
//! `abs`/`rep` coercions (named [`rel_mk`] / [`rel_holds`]). **Downstream
//! relation proofs must not see that.** They should reason entirely
//! through two primitives exposed here —
//!
//! - **holds computation** ([`holds_mk`] and the per-operation
//!   [`holds_id`] / [`holds_compose`] / [`holds_converse`] /
//!   [`holds_graph`] lemmas): `⊢ rel.holds (op …) x y = <bool
//!   formula>`; and
//! - **extensionality** ([`ext`]): from `⊢ ∀x y. holds r x y = holds s
//!   x y` conclude `⊢ r = s`.
//!
//! Everything else ([`converse_converse`], …) is derived from those
//! two, and a consumer that stays above this line never mentions
//! `abs`/`rep`. The `newtype` representation could be swapped for a
//! literal-backed builtin without touching a single downstream proof.
//!
//! ## No postulates
//!
//! Exactly as in [`init::set`], **`init::rel` postulates nothing**. The
//! whole API bottoms out in the kernel's witness-free subtype laws
//! [`Thm::spec_abs_rep`] / [`Thm::spec_rep_abs_fwd`] — the round-trip
//! equations for a derived type — so every theorem here is genuine
//! (hypothesis- and oracle-free).
//!
//! The derived theorems provided so far are the ones expressible purely
//! by pointwise rewriting + [`ext`] (the `converse` laws). The identity
//! and associativity laws for [`rel_compose`] need the existential
//! one-point rule (`(∃y. x = y ∧ P y) = P x`); they will land here once
//! the existential toolkit grows the matching tactic, with no change to
//! the seam below.

use covalence_core::defs::Symbol;
use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::eq::trans_chain;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::truth;

// Re-export the `defs/rel.rs` term catalogue (the `*_spec` handles stay
// in `covalence_core::defs`, reached via the blanket re-export there).
pub use covalence_core::defs::{
    part, per, pord, preord, rel, rel_compose, rel_converse, rel_deterministic, rel_graph,
    rel_holds, rel_id, rel_is_function, rel_mk, rel_to_fun, rel_total,
};

use covalence_core::defs::{
    rel_compose_spec, rel_converse_spec, rel_graph_spec, rel_holds_spec, rel_id_spec, rel_mk_spec,
    rel_spec,
};

// ============================================================================
// Term helpers (private — the public surface is holds lemmas + theorems)
// ============================================================================

/// `rel.holds[α,β] r x y : bool` — "does `r` relate `x` to `y`", as a
/// builder.
fn holds(alpha: &Type, beta: &Type, r: &Term, x: &Term, y: &Term) -> Term {
    let h = rel_holds(alpha.clone(), beta.clone());
    Term::app(Term::app(Term::app(h, r.clone()), x.clone()), y.clone())
}

/// `rel.converse[α,β] r : rel β α`.
fn converse(alpha: &Type, beta: &Type, r: &Term) -> Term {
    Term::app(rel_converse(alpha.clone(), beta.clone()), r.clone())
}

// ============================================================================
// THE SEAM — the only code aware that `rel` is a newtype over `α → β → bool`.
//
// `rel.mk = λp. abs p` and `rel.holds = λr x y. (rep r) x y`, so the
// two round-trip equations of the `rel` newtype —
//   rep (abs p) = p   (carrier side, used by `holds_mk`)
//   abs (rep r) = r   (wrapper side, used by `ext`)
// — are exactly what holds-computation and extensionality need. Both
// come straight from the kernel's subtype laws; `rel`'s predicate is
// `λ_. T`, so the conditional `rep`-side law's premise is discharged by
// `truth`. This mirrors `init::set` one type parameter wider.
// ============================================================================

/// Raw `abs : (α → β → bool) → rel α β` coercion of the `rel` newtype.
fn rel_abs(alpha: &Type, beta: &Type) -> Term {
    Term::spec_abs(rel_spec(), vec![alpha.clone(), beta.clone()])
}

/// `⊢ rep (abs p) = p` — the carrier-side round-trip. From the kernel's
/// [`Thm::spec_rep_abs_fwd`] (`⊢ (λ_. T) p ⟹ rep (abs p) = p` for the
/// `rel` newtype), discharging the always-true premise via β + [`truth`].
fn rep_abs(alpha: &Type, beta: &Type, p: &Term) -> Result<Thm> {
    let fwd = Thm::spec_rep_abs_fwd(rel_spec(), vec![alpha.clone(), beta.clone()], p.clone())?;
    // `fwd : ⊢ prem ⟹ (rep (abs p) = p)`; peel the antecedent `prem`.
    let (imp_p, _eq) = fwd.concl().as_app().ok_or(Error::NotAnEquation)?;
    let (_imp, prem) = imp_p.as_app().ok_or(Error::NotAnEquation)?;
    // `prem = (λ_. T) p`  →β  `T`; transport `⊢ T` back across it.
    let prem_thm = Thm::beta_conv(prem.clone())?.sym()?.eq_mp(truth())?;
    fwd.imp_elim(prem_thm)
}

/// `⊢ abs (rep r) = r` — the wrapper-side round-trip, straight from the
/// kernel's unconditional [`Thm::spec_abs_rep`].
fn abs_rep(alpha: &Type, beta: &Type, r: &Term) -> Result<Thm> {
    Thm::spec_abs_rep(rel_spec(), vec![alpha.clone(), beta.clone()], r.clone())
}

// ============================================================================
// Foundation: holds computation + extensionality.
// ============================================================================

/// `⊢ rel.holds (rel.mk p) x y = p x y` — the defining computation of
/// holds against a predicate-built relation. The bridge from the
/// `rel.mk` constructor to its predicate; every per-operation `holds_*`
/// lemma is this plus a δ/β unfolding of the operation.
pub fn holds_mk(alpha: &Type, beta: &Type, x: &Term, y: &Term, p: &Term) -> Result<Thm> {
    // rel.holds (rel.mk p) x y:  δ-unfold `rel.holds` then `rel.mk`,
    // βι-reduce to `(rep (abs p)) x y`, then collapse `rep (abs p)` to `p`.
    let mk_p = Term::app(rel_mk(alpha.clone(), beta.clone()), p.clone());
    let lhs = holds(alpha, beta, &mk_p, x, y);
    let d_holds = lhs.delta_all(rel_holds_spec().symbol())?; // = (λr x y. rep r x y) (mk p) x y
    let after = rhs_of(&d_holds)?;
    let d_mk = after.delta_all(rel_mk_spec().symbol())?; // unfold the inner rel.mk
    let reduced = rhs_of(&d_mk)?.reduce()?; // βι → (rep (abs p)) x y
    // `rep (abs p) = p`, lifted to `(rep (abs p)) x y = p x y` by congruence.
    let cong = rep_abs(alpha, beta, p)?
        .cong_fn(x.clone())?
        .cong_fn(y.clone())?;
    trans_chain([d_holds, d_mk, reduced, cong])
}

/// **Relation extensionality.** From `holds_eq : Γ ⊢ ∀x y. rel.holds r
/// x y = rel.holds s x y`, conclude `Γ ⊢ r = s`. The companion to
/// [`holds_mk`]: together they are the complete interface to `rel`,
/// hiding `abs`/`rep`.
///
/// Derivation (HOL Light's `EQ_EXT`, twice over the newtype): each
/// side's holds is `(rep ·) x y`, so `∀x y. (rep r) x y = (rep s) x y`;
/// `abs` + η-contraction on each argument give `rep r = rep s`,
/// congruence under `abs` gives `abs (rep r) = abs (rep s)`, and the
/// wrapper round-trip [`abs_rep`] rewrites both sides to `r` and `s`.
pub fn ext(alpha: &Type, beta: &Type, r: &Term, s: &Term, holds_eq: Thm) -> Result<Thm> {
    const PX: &str = "_ext_x";
    const PY: &str = "_ext_y";
    let u = Term::free(PX, alpha.clone());
    let v = Term::free(PY, beta.clone());
    let pointwise = holds_eq.all_elim(u.clone())?.all_elim(v.clone())?; // Γ ⊢ holds r u v = holds s u v
    // Rewrite each holds to the raw `(rep ·) u v`.
    let rep_r = holds_rep(alpha, beta, r, &u, &v)?; // ⊢ holds r u v = (rep r) u v
    let rep_s = holds_rep(alpha, beta, s, &u, &v)?; // ⊢ holds s u v = (rep s) u v
    let rep_pointwise = rep_r.sym()?.trans(pointwise)?.trans(rep_s)?; // Γ ⊢ (rep r) u v = (rep s) u v
    // ABS then η on the second argument: (rep r) u = (rep s) u.
    let reps_u = rep_pointwise
        .abs(PY, beta.clone())? // Γ ⊢ (λv. (rep r) u v) = (λv. (rep s) u v)
        .lhs_conv(|tm| Thm::eta_conv(tm.clone()))?
        .rhs_conv(|tm| Thm::eta_conv(tm.clone()))?; // Γ ⊢ (rep r) u = (rep s) u
    // ABS then η on the first argument: rep r = rep s.
    let reps_eq = reps_u
        .abs(PX, alpha.clone())? // Γ ⊢ (λu. (rep r) u) = (λu. (rep s) u)
        .lhs_conv(|tm| Thm::eta_conv(tm.clone()))?
        .rhs_conv(|tm| Thm::eta_conv(tm.clone()))?; // Γ ⊢ rep r = rep s
    // Congruence under `abs`, then collapse `abs (rep ·)` on each side.
    let abs_cong = reps_eq.cong_arg(rel_abs(alpha, beta))?; // Γ ⊢ abs (rep r) = abs (rep s)
    let r_eq = abs_rep(alpha, beta, r)?; // ⊢ abs (rep r) = r
    let s_eq = abs_rep(alpha, beta, s)?; // ⊢ abs (rep s) = s
    r_eq.sym()?.trans(abs_cong)?.trans(s_eq) // Γ ⊢ r = s
}

/// `⊢ rel.holds r x y = (rep r) x y` — unfold holds to the raw `rep`
/// coercion (no `rel.mk` involved, so `r` stays opaque). Internal to the
/// seam.
fn holds_rep(alpha: &Type, beta: &Type, r: &Term, x: &Term, y: &Term) -> Result<Thm> {
    let lhs = holds(alpha, beta, r, x, y);
    let d = lhs.delta_all(rel_holds_spec().symbol())?; // = (λr x y. rep r x y) r x y
    d.rhs_conv(|tm| tm.reduce()) // βι → (rep r) x y
}

// ============================================================================
// Holds lemmas — the high-level computational surface.
//
// Each says `holds (op args) x y = <bool formula>` and is proved
// uniformly: δ-unfold `op` to expose `rel.mk pred`, push holds through
// with `holds_mk`, then β-reduce `pred x y` to the formula.
// ============================================================================

/// `⊢ rel.holds rel.id x y = (x = y)` — the identity relation is
/// equality.
pub fn holds_id(alpha: &Type, x: &Term, y: &Term) -> Result<Thm> {
    let r = rel_id(alpha.clone());
    holds_of(alpha, alpha, x, y, &r, rel_id_spec().symbol())
}

/// `⊢ rel.holds (rel.compose s r) x z = (∃y. rel.holds r x y ∧
/// rel.holds s y z)` — composition `s ∘ r` relates `x` to `z` via some
/// intermediate `y`. (`r : rel α β`, `s : rel β γ`.)
pub fn holds_compose(
    alpha: &Type,
    beta: &Type,
    gamma: &Type,
    s: &Term,
    r: &Term,
    x: &Term,
    z: &Term,
) -> Result<Thm> {
    let comp = Term::app(
        Term::app(
            rel_compose(alpha.clone(), beta.clone(), gamma.clone()),
            s.clone(),
        ),
        r.clone(),
    );
    holds_of(alpha, gamma, x, z, &comp, rel_compose_spec().symbol())
}

/// `⊢ rel.holds (rel.converse r) y x = rel.holds r x y` — the converse
/// swaps the two arguments. (`r : rel α β`, so `y : β`, `x : α`.)
pub fn holds_converse(alpha: &Type, beta: &Type, r: &Term, y: &Term, x: &Term) -> Result<Thm> {
    let conv = converse(alpha, beta, r); // rel β α
    holds_of(beta, alpha, y, x, &conv, rel_converse_spec().symbol())
}

/// `⊢ rel.holds (rel.graph f) x y = (f x = y)` — the graph of a function
/// relates `x` to `f x`. (`f : α → β`.)
pub fn holds_graph(alpha: &Type, beta: &Type, f: &Term, x: &Term, y: &Term) -> Result<Thm> {
    let g = Term::app(rel_graph(alpha.clone(), beta.clone()), f.clone());
    holds_of(alpha, beta, x, y, &g, rel_graph_spec().symbol())
}

/// `⊢ rel.holds rel_tm x y = body[x,y]`, where `rel_tm` δ-unfolds (`op`)
/// and β-reduces to `rel.mk (λ.. body)`. The shared engine of the
/// `holds_*` lemmas. The point types `α`/`β` are those of `rel_tm`
/// itself (e.g. for `converse` they are swapped relative to the source
/// relation).
fn holds_of(
    alpha: &Type,
    beta: &Type,
    x: &Term,
    y: &Term,
    rel_tm: &Term,
    op: &dyn Symbol,
) -> Result<Thm> {
    // rel_tm = rel.mk pred  (δ-unfold the operation, β-reduce the spine).
    // `delta_head` (not `delta_all`) so that a nested occurrence of the
    // same op in an *argument* — e.g. the inner `converse` of `converse
    // (converse r)` — stays folded; `delta_all` would expand it too and
    // desync this from the lemmas that keep it folded.
    let as_mk = delta_head(rel_tm, op)?.rhs_conv(|t| t.reduce())?;
    let mk_pred = rhs_of(&as_mk)?;
    let pred = mk_pred.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    // holds rel_tm x y = holds (rel.mk pred) x y  (congruence in the
    // relation slot, then re-apply the two points).
    let step1 = as_mk
        .cong_arg(rel_holds(alpha.clone(), beta.clone()))?
        .cong_fn(x.clone())?
        .cong_fn(y.clone())?;
    // holds (rel.mk pred) x y = pred x y:
    let step2 = holds_mk(alpha, beta, x, y, &pred)?;
    // pred x y = body[x,y] by β.
    let step3 = rhs_of(&step2)?.reduce()?;
    trans_chain([step1, step2, step3])
}

/// `⊢ t = t'` δ-unfolding only the *head* `op` of `t = op[..] a1 … an`,
/// leaving the arguments untouched. Unlike [`TermExt::delta_all`] (which
/// also rewrites `op` occurrences inside the arguments), this descends
/// only the function spine — the right behaviour when an argument is
/// itself built from `op` (e.g. `rel.converse (rel.converse r)`).
fn delta_head(t: &Term, op: &dyn Symbol) -> Result<Thm> {
    if let Some((spec, _args)) = t.as_spec() {
        if spec.symbol().label() == op.label() {
            return Thm::unfold_term_spec(t.clone());
        }
        return Thm::refl(t.clone());
    }
    if let Some((f, x)) = t.as_app() {
        return delta_head(f, op)?.cong_fn(x.clone()); // function position only
    }
    Thm::refl(t.clone())
}

// ============================================================================
// Theorems — derived purely through `holds_*` + `ext` (no `abs`/`rep`).
// ============================================================================

/// `⊢ rel.converse (rel.converse r) = r` — `converse` is an involution
/// (free `r : rel 'a 'b`). Pointwise both sides hold exactly when `r`
/// relates the corresponding pair, so the relations agree by [`ext`].
pub fn converse_converse() -> Thm {
    converse_involution().expect("converse.converse")
}

fn converse_involution() -> Result<Thm> {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let r = Term::free("r", rel(alpha.clone(), beta.clone()));
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let cr = converse(&alpha, &beta, &r); // converse r        : rel β α
    let cc = converse(&beta, &alpha, &cr); // converse (conv r) : rel α β

    // holds (converse (converse r)) x y = holds (converse r) y x
    let step_outer = holds_converse(&beta, &alpha, &cr, &x, &y)?;
    // holds (converse r) y x = holds r x y
    let step_inner = holds_converse(&alpha, &beta, &r, &y, &x)?;
    let pointwise = step_outer.trans(step_inner)?; // holds (cc r) x y = holds r x y

    let all = pointwise
        .all_intro("y", beta.clone())?
        .all_intro("x", alpha.clone())?;
    ext(&alpha, &beta, &cc, &r, all)
}

/// `⊢ rel.converse rel.id = rel.id` — the identity relation is its own
/// converse. Pointwise `holds (converse id) x y = (y = x) = (x = y) =
/// holds id x y` via [`holds_converse`], [`holds_id`], and symmetry of
/// equality as an equation.
pub fn converse_id() -> Thm {
    converse_id_inner().expect("converse.id")
}

fn converse_id_inner() -> Result<Thm> {
    let alpha = Type::tfree("a");
    let id = rel_id(alpha.clone()); // rel α α
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let conv_id = converse(&alpha, &alpha, &id); // converse id : rel α α

    let step1 = holds_converse(&alpha, &alpha, &id, &x, &y)?; // holds (conv id) x y = holds id y x
    let step2 = holds_id(&alpha, &y, &x)?; // holds id y x = (y = x)
    let step3 = eq_comm_eq(y.clone(), x.clone())?; // (y = x) = (x = y)
    let step4 = holds_id(&alpha, &x, &y)?; // holds id x y = (x = y)
    // chain to: holds (conv id) x y = holds id x y
    let pointwise = trans_chain([step1, step2, step3, step4.sym()?])?;

    let all = pointwise
        .all_intro("y", alpha.clone())?
        .all_intro("x", alpha.clone())?;
    ext(&alpha, &alpha, &conv_id, &id, all)
}

// ============================================================================
// Equality symmetry as an equation (helper shared by the theorems).
// ============================================================================

/// `⊢ (a = b) = (b = a)` — symmetry of equality as a `bool` equation,
/// from the two directions of [`Thm::sym`] via `deduct_antisym` (the
/// same shape as `set`'s connective-commutativity helpers).
fn eq_comm_eq(a: Term, b: Term) -> Result<Thm> {
    let ab = a.clone().equals(b.clone())?;
    let ba = b.equals(a)?;
    let fwd = Thm::assume(ab.clone())?.sym()?; // {a=b} ⊢ b=a
    let bwd = Thm::assume(ba.clone())?.sym()?; // {b=a} ⊢ a=b
    bwd.deduct_antisym(fwd) // ⊢ (a=b) = (b=a)
}

// ============================================================================
// Small accessors.
// ============================================================================

/// The right-hand side of an equational theorem.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

// ============================================================================
// The `relrec` environment — seam givens + operators for `rel.cov`.
// ============================================================================

/// Build `∀x y. holds r x y = holds s x y` (where `r` and `s` are already
/// free variables), as a fully-closed term for use in the `ext` axiom.
fn build_all_holds_eq(alpha: &Type, beta: &Type, r: &Term, s: &Term) -> Result<Term> {
    let x = Term::free("_ext_x", alpha.clone());
    let y = Term::free("_ext_y", beta.clone());
    let inner = holds(alpha, beta, r, &x, &y)
        .equals(holds(alpha, beta, s, &x, &y))?
        .forall("_ext_y", beta.clone())?
        .forall("_ext_x", alpha.clone())?;
    Ok(inner)
}

/// The `rel` environment imported by `rel.cov`: the seam lemmas as
/// universally-quantified **given** theorems, plus the operators
/// (`rel.holds`, `rel.converse`, `rel.id`, `rel.mk`) as `ConstDef::Poly`
/// schemes (instantiated per use site, so `rel.converse` can appear at two
/// type orderings in one term — no `.ba`/`.aa` aliases needed).
pub fn rel_env() -> crate::script::Env {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");

    let mut e = crate::script::Env::empty();

    // ---- operators -----------------------------------------------------------
    // All registered as `ConstDef::Poly`: each carries a scheme term whose free
    // type variables (`'a`/`'b`) are instantiated with fresh metavariables PER
    // USE SITE, so e.g. `rel.converse` can appear at both `('a,'b)` and `('b,'a)`
    // within one term (the double-converse). This is what replaced the old
    // type-specialised `rel.converse.ba`/`rel.converse.aa` aliases.
    e.define_const(
        "rel.holds",
        crate::script::ConstDef::Poly(rel_holds(alpha.clone(), beta.clone())),
    );
    // `rel.converse` : `rel 'a 'b → rel 'b 'a` (polymorphic in both `'a`/`'b`).
    e.define_const(
        "rel.converse",
        crate::script::ConstDef::Poly(rel_converse(alpha.clone(), beta.clone())),
    );
    e.define_const(
        "rel.id",
        crate::script::ConstDef::Poly(rel_id(alpha.clone())),
    );
    e.define_const(
        "rel.mk",
        crate::script::ConstDef::Poly(rel_mk(alpha.clone(), beta.clone())),
    );

    // ---- seam givens --------------------------------------------------------
    // `holds_mk_ax`: ∀p x y. rel.holds (rel.mk p) x y = p x y
    let holds_mk_ax = (|| -> Result<Thm> {
        let p_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));
        let p = Term::free("p", p_ty.clone());
        let x = Term::free("x", alpha.clone());
        let y = Term::free("y", beta.clone());
        holds_mk(&alpha, &beta, &x, &y, &p)?
            .all_intro("y", beta.clone())?
            .all_intro("x", alpha.clone())?
            .all_intro("p", p_ty)
    })()
    .expect("rel_env: holds.mk_ax");
    e.define_lemma("holds.mk_ax", holds_mk_ax);

    // `ext_ax`: ∀r s. (∀x y. holds r x y = holds s x y) ⟹ r = s
    // (r, s : rel 'a 'b — two distinct type parameters)
    let ext_ax = (|| -> Result<Thm> {
        let r = Term::free("r", rel(alpha.clone(), beta.clone()));
        let s = Term::free("s", rel(alpha.clone(), beta.clone()));
        let all_holds_eq_term = build_all_holds_eq(&alpha, &beta, &r, &s)?;
        let holds_eq = Thm::assume(all_holds_eq_term.clone())?;
        let r_eq_s = ext(&alpha, &beta, &r, &s, holds_eq)?;
        r_eq_s
            .imp_intro(&all_holds_eq_term)?
            .all_intro("s", rel(alpha.clone(), beta.clone()))?
            .all_intro("r", rel(alpha.clone(), beta.clone()))
    })()
    .expect("rel_env: ext.ax");
    e.define_lemma("ext.ax", ext_ax);

    // `holds_id_ax`: ∀x y. rel.holds rel.id x y = (x = y)
    let holds_id_ax = (|| -> Result<Thm> {
        let x = Term::free("x", alpha.clone());
        let y = Term::free("y", alpha.clone());
        holds_id(&alpha, &x, &y)?
            .all_intro("y", alpha.clone())?
            .all_intro("x", alpha.clone())
    })()
    .expect("rel_env: holds.id_ax");
    e.define_lemma("holds.id_ax", holds_id_ax);

    // `holds_converse_ax`: ∀r y x. rel.holds (rel.converse r) y x = rel.holds r x y
    // (r : rel 'a 'b, y : 'b, x : 'a)
    let holds_converse_ax = (|| -> Result<Thm> {
        let r = Term::free("r", rel(alpha.clone(), beta.clone()));
        let y = Term::free("y", beta.clone());
        let x = Term::free("x", alpha.clone());
        holds_converse(&alpha, &beta, &r, &y, &x)?
            .all_intro("x", alpha.clone())?
            .all_intro("y", beta.clone())?
            .all_intro("r", rel(alpha.clone(), beta.clone()))
    })()
    .expect("rel_env: holds.converse_ax");
    e.define_lemma("holds.converse_ax", holds_converse_ax);

    e
}

crate::cov_theory! {
    /// rel lemmas ported to `rel.cov`, over `core` + the `rel` env.
    pub mod cov from "rel.cov" {
        import "core" = crate::script::Env::core();
        import "logic" = crate::init::logic::cov::env();
        import "relprim" = crate::init::rel::rel_env();
        "converse.converse" => pub fn converse_converse_cov;
        "converse.id"       => pub fn converse_id_cov;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> Type {
        Type::tfree("a")
    }

    fn beta() -> Type {
        Type::tfree("b")
    }

    fn relvar(name: &str) -> Term {
        Term::free(name, rel(alpha(), beta()))
    }

    fn a_elem(name: &str) -> Term {
        Term::free(name, alpha())
    }

    fn b_elem(name: &str) -> Term {
        Term::free(name, beta())
    }

    #[test]
    fn holds_mk_computes() {
        // holds (mk (λu v. u = w)) x y = (x = w), via `p x y` then β.
        let x = a_elem("x");
        let y = b_elem("y");
        let w = a_elem("w");
        // p : α → β → bool  =  λu:α. λv:β. u = w
        let u = Term::free("u", alpha());
        let inner = {
            let body = u.equals(w.clone()).unwrap(); // u = w (open in `u`)
            let lam_v = Term::abs(beta(), covalence_core::subst::close(&body, "v"));
            Term::abs(alpha(), covalence_core::subst::close(&lam_v, "u"))
        };
        let thm = holds_mk(&alpha(), &beta(), &x, &y, &inner).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let mk_p = Term::app(rel_mk(alpha(), beta()), inner.clone());
        assert_eq!(lhs, &holds(&alpha(), &beta(), &mk_p, &x, &y));
        // lands on the raw application `p x y`; β-reduces to `x = w`.
        let p_xy = Term::app(Term::app(inner, x.clone()), y.clone());
        assert_eq!(rhs, &p_xy, "holds reduces to `p x y`");
    }

    #[test]
    fn holds_id_is_equality() {
        let (x, y) = (a_elem("x"), a_elem("y"));
        let thm = holds_id(&alpha(), &x, &y).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(rhs_of(&thm).unwrap(), x.equals(y).unwrap());
    }

    #[test]
    fn holds_converse_swaps() {
        let r = relvar("r");
        let (x, y) = (a_elem("x"), b_elem("y"));
        // holds (converse r) y x = holds r x y
        let thm = holds_converse(&alpha(), &beta(), &r, &y, &x).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(rhs_of(&thm).unwrap(), holds(&alpha(), &beta(), &r, &x, &y));
    }

    #[test]
    fn holds_graph_is_application_eq() {
        let f = Term::free("f", Type::fun(alpha(), beta()));
        let (x, y) = (a_elem("x"), b_elem("y"));
        let thm = holds_graph(&alpha(), &beta(), &f, &x, &y).unwrap();
        assert!(thm.hyps().is_empty());
        let fx = Term::app(f, x);
        assert_eq!(rhs_of(&thm).unwrap(), fx.equals(y).unwrap());
    }

    #[test]
    fn holds_compose_is_witnessed() {
        // r : rel a b, s : rel b c.
        let gamma = Type::tfree("c");
        let r = Term::free("r", rel(alpha(), beta()));
        let s = Term::free("s", rel(beta(), gamma.clone()));
        let x = a_elem("x");
        let z = Term::free("z", gamma.clone());
        let thm = holds_compose(&alpha(), &beta(), &gamma, &s, &r, &x, &z).unwrap();
        assert!(thm.hyps().is_empty());
        // RHS is an existential `∃y. holds r x y ∧ holds s y z`.
        let comp = Term::app(
            Term::app(rel_compose(alpha(), beta(), gamma.clone()), s.clone()),
            r.clone(),
        );
        let (lhs, _rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &holds(&alpha(), &gamma, &comp, &x, &z));
    }

    #[test]
    fn ext_from_pointwise_holds() {
        // A trivial use of ext: reflexive holds ⟹ r = r.
        let r = relvar("r");
        let u = Term::free("_ext_x", alpha());
        let v = Term::free("_ext_y", beta());
        let refl = Thm::refl(holds(&alpha(), &beta(), &r, &u, &v)).unwrap();
        let all = refl
            .all_intro("_ext_y", beta())
            .unwrap()
            .all_intro("_ext_x", alpha())
            .unwrap();
        let eq = ext(&alpha(), &beta(), &r, &r, all).unwrap();
        assert_eq!(eq.concl(), &r.clone().equals(r).unwrap());
    }

    #[test]
    fn converse_converse_is_genuine() {
        let thm = converse_converse();
        assert!(
            thm.hyps().is_empty(),
            "converse.converse is proved, not postulated"
        );
        assert!(thm.has_no_obs(), "converse.converse is oracle-free");
        let r = relvar("r");
        let cr = converse(&alpha(), &beta(), &r);
        let cc = converse(&beta(), &alpha(), &cr);
        assert_eq!(thm.concl(), &cc.equals(r).unwrap());
    }

    #[test]
    fn converse_id_is_genuine() {
        let thm = converse_id();
        assert!(thm.hyps().is_empty(), "converse.id is proved");
        assert!(thm.has_no_obs());
        let id = rel_id(alpha());
        let conv_id = converse(&alpha(), &alpha(), &id);
        assert_eq!(thm.concl(), &conv_id.equals(id).unwrap());
    }
}

#[cfg(test)]
mod cov_tests {
    use super::cov;

    #[test]
    fn rel_cov_matches_rust() {
        assert_eq!(
            cov::converse_converse_cov().concl(),
            super::converse_converse().concl()
        );
        assert_eq!(
            cov::converse_id_cov().concl(),
            super::converse_id().concl()
        );
    }
}
