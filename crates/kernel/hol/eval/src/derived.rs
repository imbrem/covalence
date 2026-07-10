//! **Derived** connective / quantifier rules — the stage-L2 replacements
//! for the deleted kernel fast rules, as executable derivations over the
//! remaining equality-core rules. Zero TCB: every method here composes
//! admitted kernel mints (`refl` / `sym` / `trans` / `mk_comb` / `abs` /
//! `beta_conv` / `assume` / `eq_mp` / `deduct_antisym` / `inst` /
//! definitional unfolding ([`crate::delta`]) / `select_ax`), so nothing in
//! this module can forge
//! a theorem — it can only fail.
//!
//! The definitions being folded/unfolded are the ordinary catalogue
//! specs in [`crate::defs`] (`∧ ≡ λp q. (λf. f p q) = (λf. f T T)`,
//! `⟹ ≡ λp q. (p ∧ q) = p`, `¬ ≡ λp. p ⟹ F`,
//! `∨ ≡ λp q. ∀r. (p⟹r) ⟹ (q⟹r) ⟹ r`, `∀ ≡ λP. P = (λx. T)`); the
//! derivations are the standard HOL Light `bool.ml` bootstrap
//! (`CONJ` / `CONJUNCT1/2` / `DISCH` / `MP` / `GEN` / `SPEC` /
//! `DISJ1/2` / `DISJ_CASES` / `NOT_INTRO/ELIM`) plus the classical
//! `EXCLUDED_MIDDLE` derivation from Hilbert choice (`select_ax`).
//!
//! ## Tier
//!
//! Since stage EG3b, `T` and `F` are the **defined constants**
//! [`defs::tru`] / [`defs::fal`] and the connective bodies reference
//! them, so the whole bootstrap bottoms out in [`truth`] — `⊢ T` derived
//! from `tru`'s defining equation by `refl` + `eq_mp` — at the **pure
//! `CoreLang` tier**. Every cached ingredient (the connective defining
//! equations, the rule schemas, the LEM schema) is therefore derived
//! once as a `Thm<CoreLang>`, and the whole module is generic over the
//! [`HolTier`]: the rules serve `Thm<CoreLang>` and [`crate::EvalThm`]
//! alike (cached pure-tier ingredients enter a higher tier via the
//! sound low→high [`Thm::lift`]).
//!
//! The transitional `Bool` literals `⌜T⌝` / `⌜F⌝` are NOT this module's
//! business: they remain eval-tier citizens of the certificate path,
//! bridged to the defined constants by the derived equations in
//! [`crate::boolean`] (`⊢ T = ⌜T⌝`, `⊢ F = ⌜F⌝`).
//!
//! ## Drop-in surface
//!
//! [`DerivedRules`] mirrors the deleted kernel methods signature-for-
//! signature (including the `_with` [`TrustedCons`] variants and the
//! associated `lem`), so downstream call sites change **imports only**:
//! `use covalence_hol_eval::derived::DerivedRules;` (re-exported as
//! `covalence_init::init::derived_rules`). [`TypeDefExt`] splits the
//! [`covalence_core::TypeDef`] bijection conjunction — the kernel's
//! `new_type_definition` no longer splits it itself (that needed the
//! deleted `and_elim` rules).
//!
//! ## Performance
//!
//! A derived step costs several kernel mints where the deleted rule cost
//! one. Two mitigations keep the hot paths flat:
//! - the closed ingredients (`⊢ T`, each connective's defining equation,
//!   the `⊢ p ∨ ¬p` LEM schema) are derived once and cached;
//! - [`lem`](DerivedRules::lem) instantiates its cached schema with one
//!   kernel `inst` per call.
//!
//! The remaining per-call β/congruence work is measured by
//! `scripts/bench-proving.mjs` against `docs/deps/proving-baseline.json`.

use std::any::{Any, TypeId};
use std::sync::LazyLock;

use covalence_core::seam::{CoreLang, HolTier};
use covalence_core::term::TrustedCons;
use covalence_core::{Error, Result, Term, TermKind, Thm, Type, TypeDef, subst};

use crate::defs;

/// The pure-HOL tier theorem — the tier every cached ingredient is
/// derived at (`covalence_core::Thm`'s default tier parameter).
type CoreThm = Thm<CoreLang>;

/// Re-home a cached pure-tier ingredient at the working tier `L`:
/// the identity when `L` **is** `CoreLang`, else the sound low→high
/// [`Thm::lift`] (which mints nothing; it re-checks `extends` and
/// re-wraps). Errors only for an exotic tier that does not extend
/// `CoreLang` — such a tier cannot consume `CoreLang`-derived
/// ingredients, so the derivations correctly fail there.
fn at_tier<L: HolTier>(t: &CoreThm) -> Result<Thm<L>> {
    if TypeId::of::<L>() == TypeId::of::<CoreLang>() {
        let boxed: Box<dyn Any> = Box::new(t.clone());
        return Ok(*boxed.downcast::<Thm<L>>().expect("same tier"));
    }
    t.clone().lift::<L>()
}

/// Statically-checked identity coercion between `Thm<L>` and `Thm<L2>`
/// when `L` **is** `L2` (`TypeId` equality) — no mint, no lift, a pure
/// move through `Any`. `None` when the tiers differ. Used to dispatch a
/// tier-specific fallback (the eval-tier literal bridge) from generic
/// code without weakening any other tier.
fn same_tier<L: HolTier, L2: HolTier>(t: Thm<L>) -> Option<Thm<L2>> {
    if TypeId::of::<L>() != TypeId::of::<L2>() {
        return None;
    }
    let boxed: Box<dyn Any> = Box::new(t);
    Some(*boxed.downcast::<Thm<L2>>().expect("same tier"))
}

// ============================================================================
// Cached closed ingredients (all derived ONCE at the pure CoreLang tier)
// ============================================================================

/// `⊢ T` for the **defined** `T` ([`defs::tru`]), derived at the pure
/// `CoreLang` tier from the defining equation: δ-unfold gives
/// `⊢ T = ((λp.p) = (λp.p))`, `refl` proves the right-hand side, and
/// `eq_mp` (through `sym`) concludes. No certificate, no computation
/// TCB. The root of the `EQT_INTRO` / `EQT_ELIM` bridge every
/// connective derivation bottoms out in.
pub fn truth<L: HolTier>() -> Result<Thm<L>> {
    static TRUTH: LazyLock<CoreThm> = LazyLock::new(|| {
        (|| -> Result<CoreThm> {
            let def = crate::delta_at::<CoreLang>(&defs::tru())?; // ⊢ T = ((λp.p) = (λp.p))
            let rhs = def.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
            let id = rhs.as_eq().ok_or(Error::NotAnEquation)?.0.clone();
            def.sym()?.eq_mp(Thm::refl(id)?) // ⊢ T
        })()
        .expect("derived: ⊢ T")
    });
    at_tier(&TRUTH)
}

/// `⊢ ∧ = λp q. (λf. f p q) = (λf. f T T)` (cached).
fn and_def<L: HolTier>() -> Result<Thm<L>> {
    static D: LazyLock<CoreThm> =
        LazyLock::new(|| crate::delta_at(&defs::and()).expect("derived: unfold ∧"));
    at_tier(&D)
}

/// `⊢ ⟹ = λp q. (p ∧ q) = p` (cached).
fn imp_def<L: HolTier>() -> Result<Thm<L>> {
    static D: LazyLock<CoreThm> =
        LazyLock::new(|| crate::delta_at(&defs::imp()).expect("derived: unfold ⟹"));
    at_tier(&D)
}

/// `⊢ ¬ = λp. p ⟹ F` (cached).
fn not_def<L: HolTier>() -> Result<Thm<L>> {
    static D: LazyLock<CoreThm> =
        LazyLock::new(|| crate::delta_at(&defs::not()).expect("derived: unfold ¬"));
    at_tier(&D)
}

/// `⊢ ∨ = λp q. ∀r. (p⟹r) ⟹ (q⟹r) ⟹ r` (cached).
fn or_def<L: HolTier>() -> Result<Thm<L>> {
    static D: LazyLock<CoreThm> =
        LazyLock::new(|| crate::delta_at(&defs::or()).expect("derived: unfold ∨"));
    at_tier(&D)
}

// ============================================================================
// Small equational helpers
// ============================================================================

fn b() -> Type {
    Type::bool()
}

fn rhs_of<L: HolTier>(thm: &Thm<L>) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// From `⊢ f = (λx. body)` and `a`, build `⊢ f a = body[a]` (congruence
/// with `refl a`, then one β-step on the right).
fn unfold_at<L: HolTier>(op_eq: Thm<L>, a: Term) -> Result<Thm<L>> {
    let applied = op_eq.mk_comb(Thm::refl(a)?)?; // ⊢ f a = (λx. body) a
    let beta = Thm::beta_conv(rhs_of(&applied)?)?; // ⊢ (λx. body) a = body[a]
    applied.trans(beta)
}

/// `⊢ op a b = body[a, b]` for a binary connective's cached defining
/// equation `op_eq : ⊢ op = λp q. body`.
fn unfold_at_2<L: HolTier>(op_eq: Thm<L>, a: Term, b: Term) -> Result<Thm<L>> {
    unfold_at(unfold_at(op_eq, a)?, b)
}

/// `⊢ t = t'` — fire **exactly `n`** head-spine β-steps (leftmost
/// redex on the application spine, never under a binder, never inside
/// the residue). The connective-selector collapses below take a fixed
/// number of steps (`(λf. f p q) (λa b. a) →β (λa b. a) p q →β
/// (λb. p) q →β p` — three), and stopping at that count is what keeps
/// a component that is *itself* a β-redex intact (normalising to a
/// fixpoint would reduce into it and change the conclusion).
fn beta_head_steps<L: HolTier>(t: Term, n: usize) -> Result<Thm<L>> {
    let mut acc = Thm::refl(t)?;
    for _ in 0..n {
        let cur = rhs_of(&acc)?;
        // Unwind the spine: cur = head a₁ … aₖ.
        let mut args = Vec::new();
        let mut head = cur;
        while let TermKind::App(f, x) = head.kind() {
            args.push(x.clone());
            let f = f.clone();
            head = f;
        }
        if args.is_empty() || !matches!(head.kind(), TermKind::Abs(..)) {
            return Err(Error::ConnectiveRule(format!(
                "beta_head_steps: no head redex in {head}"
            )));
        }
        args.reverse();
        // Fire the innermost redex `head a₁`, then carry the equation out
        // through the remaining arguments by congruence.
        let mut step = Thm::beta_conv(Term::app(head, args[0].clone()))?;
        for a in &args[1..] {
            step = step.mk_comb(Thm::refl(a.clone())?)?;
        }
        acc = acc.trans(step)?;
    }
    Ok(acc)
}

/// A variable name (from `hint`) not free — at any type — in any of
/// `terms` nor in any hypothesis of `thms`.
fn fresh_name<L: HolTier>(hint: &str, terms: &[&Term], thms: &[&Thm<L>]) -> String {
    let clashes = |name: &str| {
        terms.iter().any(|t| subst::has_free_var(t, name))
            || thms
                .iter()
                .any(|t| t.hyps().iter().any(|h| subst::has_free_var(h, name)))
    };
    (0u32..)
        .map(|i| format!("{hint}{i}"))
        .find(|c| !clashes(c))
        .expect("unbounded candidate stream")
}

// ============================================================================
// Term-shape parsing (read-only; parsing mints nothing)
// ============================================================================

fn is_spec(t: &Term, want: &covalence_core::TermSpec) -> bool {
    matches!(t.kind(), TermKind::Spec(h, _) if h.ptr_eq(want))
}

/// The defined falsity constant `F` (`defs::fal`) as a shape test.
fn is_fal(t: &Term) -> bool {
    is_spec(t, &defs::fal_spec())
}

fn parse_binop<'a>(
    t: &'a Term,
    op: &covalence_core::TermSpec,
    what: &str,
) -> Result<(&'a Term, &'a Term)> {
    let err = || Error::ConnectiveRule(format!("expected {what}, got {t}"));
    let TermKind::App(f, q) = t.kind() else {
        return Err(err());
    };
    let TermKind::App(head, p) = f.kind() else {
        return Err(err());
    };
    if !is_spec(head, op) {
        return Err(err());
    }
    Ok((p, q))
}

fn parse_and(t: &Term) -> Result<(&Term, &Term)> {
    parse_binop(t, &defs::and_spec(), "p /\\ q")
}

fn parse_or(t: &Term) -> Result<(&Term, &Term)> {
    parse_binop(t, &defs::or_spec(), "p \\/ q")
}

fn parse_imp(t: &Term) -> Result<(&Term, &Term)> {
    parse_binop(t, &defs::imp_spec(), "p ==> q").map_err(|_| Error::NotHolImp(format!("{t}")))
}

fn parse_not(t: &Term) -> Result<&Term> {
    let err = || Error::ConnectiveRule(format!("expected ~p, got {t}"));
    let TermKind::App(head, p) = t.kind() else {
        return Err(err());
    };
    if !is_spec(head, &defs::not_spec()) {
        return Err(err());
    }
    Ok(p)
}

/// Parse `App(∀[τ], λ)` → `(τ, lambda)`.
fn parse_forall(t: &Term) -> Result<(Type, Term)> {
    let err = || Error::NotHolForall(format!("{t}"));
    let TermKind::App(head, lambda) = t.kind() else {
        return Err(err());
    };
    let TermKind::Spec(h, args) = head.kind() else {
        return Err(err());
    };
    if !h.ptr_eq(&defs::forall_spec()) || args.len() != 1 {
        return Err(err());
    }
    if !matches!(lambda.kind(), TermKind::Abs(..)) {
        return Err(err());
    }
    Ok((args[0].clone(), lambda.clone()))
}

fn check_bool(t: &Term) -> Result<()> {
    let ty = t.type_of()?;
    if !ty.is_bool() {
        return Err(Error::NotBool(ty));
    }
    Ok(())
}

// ============================================================================
// The EQT bridge
// ============================================================================

/// `Γ ⊢ p` → `Γ ⊢ p = T` (HOL Light `EQT_INTRO`), via `deduct_antisym`
/// against the cached [`truth`].
fn eqt_intro<L: HolTier>(th: Thm<L>) -> Result<Thm<L>> {
    th.deduct_antisym(truth()?)
}

/// `Γ ⊢ p = T` → `Γ ⊢ p` (HOL Light `EQT_ELIM`), via `sym` + `eq_mp`
/// against the cached [`truth`].
fn eqt_elim<L: HolTier>(th: Thm<L>) -> Result<Thm<L>> {
    th.sym()?.eq_mp(truth()?)
}

// ============================================================================
// Conjunction — `p ∧ q ≡ (λf. f p q) = (λf. f T T)`
// ============================================================================

fn and_intro_slow<L: HolTier>(a: Thm<L>, other: Thm<L>) -> Result<Thm<L>> {
    let p = a.concl().clone();
    let q = other.concl().clone();
    check_bool(&p)?;
    check_bool(&q)?;

    let p_eq_t = eqt_intro(a)?; // Γ ⊢ p = T
    let q_eq_t = eqt_intro(other)?; // Δ ⊢ q = T

    // Γ ∪ Δ ⊢ (λf. f p q) = (λf. f T T), with `f` fresh for p, q and the
    // hypotheses (the kernel `abs` side condition).
    let bbb = Type::fun(b(), Type::fun(b(), b()));
    let f_name = fresh_name("f", &[&p, &q], &[&p_eq_t, &q_eq_t]);
    let f = Term::free(f_name.as_str(), bbb.clone());
    let fpq_eq = Thm::refl(f)?.mk_comb(p_eq_t)?.mk_comb(q_eq_t)?; // ⊢ f p q = f T T
    let lam_eq = fpq_eq.abs(&f_name, bbb)?;

    // Fold: ⊢ (p ∧ q) = <that body>, then eq_mp backwards.
    unfold_at_2(and_def()?, p, q)?.sym()?.eq_mp(lam_eq)
}

/// Shared `CONJUNCT1` / `CONJUNCT2`: apply the unfolded conjunction to a
/// selector `λa b. a` / `λa b. b` and β-collapse both sides.
fn and_elim_slow<L: HolTier>(conj: Thm<L>, first: bool) -> Result<Thm<L>> {
    let (p, q) = {
        let (p, q) = parse_and(conj.concl())?;
        (p.clone(), q.clone())
    };
    // Γ ⊢ (λf. f p q) = (λf. f T T)
    let body = unfold_at_2(and_def()?, p, q)?.eq_mp(conj)?;
    // Selector: λa b:bool. a  /  λa b:bool. b.
    let sel = Term::abs(b(), Term::abs(b(), Term::bound(if first { 1 } else { 0 })));
    let applied = body.mk_comb(Thm::refl(sel)?)?; // Γ ⊢ (λf. f p q) sel = (λf. f T T) sel
    let (lhs, rhs) = applied.concl().as_eq().ok_or(Error::NotAnEquation)?;
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let lhs_nf = beta_head_steps(lhs, 3)?; // ⊢ … = component
    let rhs_nf = beta_head_steps(rhs, 3)?; // ⊢ … = T
    eqt_elim(lhs_nf.sym()?.trans(applied)?.trans(rhs_nf)?)
}

// ============================================================================
// Implication — `p ⟹ q ≡ (p ∧ q) = p`
// ============================================================================

fn imp_intro_slow<L: HolTier>(th: Thm<L>, phi: &Term) -> Result<Thm<L>> {
    check_bool(phi)?;
    let psi = th.concl().clone();
    // Γ ∪ {φ} ⊢ φ ∧ ψ.
    let conj = and_intro_drv(Thm::assume(phi.clone())?, th)?;
    // {φ ∧ ψ} ⊢ φ.
    let elim = and_elim_drv(Thm::assume(conj.concl().clone())?, true)?;
    // deduct_antisym: (Γ ∪ {φ}) \ {φ}  ∪  {φ∧ψ} \ {φ∧ψ}  ⊢ (φ ∧ ψ) = φ.
    let eq = conj.deduct_antisym(elim)?;
    // Fold the definition backwards.
    unfold_at_2(imp_def()?, phi.clone(), psi)?.sym()?.eq_mp(eq)
}

fn imp_elim_slow<L: HolTier>(imp: Thm<L>, hyp: Thm<L>) -> Result<Thm<L>> {
    let (phi, psi) = {
        let (p, q) = parse_imp(imp.concl())?;
        (p.clone(), q.clone())
    };
    if *hyp.concl() != phi {
        return Err(Error::ImpAntecedentMismatch {
            expected: format!("{phi}"),
            got: format!("{}", hyp.concl()),
        });
    }
    // Γ ⊢ (φ ∧ ψ) = φ, then transport ⊢ φ across it and project.
    let conj_eq = unfold_at_2(imp_def()?, phi, psi)?.eq_mp(imp)?;
    let conj = conj_eq.sym()?.eq_mp(hyp)?; // Γ ∪ Δ ⊢ φ ∧ ψ
    and_elim_drv(conj, false)
}

// ============================================================================
// Universal quantification — `∀ ≡ λP. P = (λx. T)`
// ============================================================================

fn all_intro_drv<L: HolTier>(th: Thm<L>, name: &str, ty: Type) -> Result<Thm<L>> {
    // Γ ⊢ (λx. φ') = (λx. T); the kernel `abs` enforces x ∉ FV(Γ).
    let lam_eq = eqt_intro(th)?.abs(name, ty.clone())?;
    let lam = lam_eq
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .0
        .clone();
    // ⊢ (∀ (λx. φ')) = ((λx. φ') = (λx. T)), folded backwards.
    forall_at_eq(ty, lam)?.sym()?.eq_mp(lam_eq)
}

fn all_elim_slow<L: HolTier>(th: Thm<L>, witness: Term) -> Result<Thm<L>> {
    let (ty, lam) = parse_forall(th.concl())?;
    let wit_ty = witness.type_of()?;
    if wit_ty != ty {
        return Err(Error::TypeMismatch {
            expected: ty,
            got: wit_ty,
        });
    }
    // Γ ⊢ (λx. φ') = (λx. T).
    let inner = forall_at_eq(ty, lam.clone())?.eq_mp(th)?;
    // Γ ⊢ (λx. φ') w = (λx. T) w, then β both sides.
    let applied = inner.mk_comb(Thm::refl(witness.clone())?)?;
    let lhs_beta = Thm::beta_conv(Term::app(lam, witness))?; // ⊢ (λx. φ') w = φ[w]
    let rhs_beta = Thm::beta_conv(rhs_of(&applied)?)?; // ⊢ (λx. T) w = T
    eqt_elim(lhs_beta.sym()?.trans(applied)?.trans(rhs_beta)?)
}

// ============================================================================
// Disjunction — `p ∨ q ≡ ∀r. (p⟹r) ⟹ (q⟹r) ⟹ r`
// ============================================================================

/// Build `p ⟹ q` as a term (over the catalogue `imp` spec).
fn imp_term(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::imp(), p), q)
}

/// Shared `DISJ1` / `DISJ2`: `Γ ⊢ p` (resp. `q`) into `Γ ⊢ p ∨ q`.
fn or_intro_slow<L: HolTier>(th: Thm<L>, p: Term, q: Term, left: bool) -> Result<Thm<L>> {
    check_bool(&p)?;
    check_bool(&q)?;
    // Fresh r for the ∀-generalisation.
    let r_name = fresh_name("r", &[&p, &q], &[&th]);
    let r = Term::free(r_name.as_str(), b());
    let p_r = imp_term(p.clone(), r.clone());
    let q_r = imp_term(q.clone(), r.clone());
    // Γ ∪ {side ⟹ r} ⊢ r.
    let picked = if left { &p_r } else { &q_r };
    let fired = imp_elim_drv(Thm::assume(picked.clone())?, th)?;
    // Discharge in order: (q ⟹ r) then (p ⟹ r).
    let d1 = imp_intro_drv(fired, &q_r)?;
    let d2 = imp_intro_drv(d1, &p_r)?;
    let closed = all_intro_drv(d2, &r_name, b())?; // Γ ⊢ ∀r. (p⟹r) ⟹ (q⟹r) ⟹ r
    unfold_at_2(or_def()?, p, q)?.sym()?.eq_mp(closed)
}

fn or_elim_slow<L: HolTier>(disj: Thm<L>, left: Thm<L>, right: Thm<L>) -> Result<Thm<L>> {
    let (p, q) = {
        let (p, q) = parse_or(disj.concl())?;
        (p.clone(), q.clone())
    };
    let (lp, lr) = {
        let (a, c) = parse_imp(left.concl())?;
        (a.clone(), c.clone())
    };
    let (rq, rr) = {
        let (a, c) = parse_imp(right.concl())?;
        (a.clone(), c.clone())
    };
    if lp != p {
        return Err(Error::ConnectiveRule(format!(
            "or_elim: left branch antecedent {lp} ≠ left disjunct {p}"
        )));
    }
    if rq != q {
        return Err(Error::ConnectiveRule(format!(
            "or_elim: right branch antecedent {rq} ≠ right disjunct {q}"
        )));
    }
    if lr != rr {
        return Err(Error::ConnectiveRule(format!(
            "or_elim: branch consequents differ ({lr} vs {rr})"
        )));
    }
    // Γ ⊢ (p⟹r) ⟹ (q⟹r) ⟹ r at r := the branches' consequent.
    let spec = all_elim_drv(unfold_at_2(or_def()?, p, q)?.eq_mp(disj)?, lr)?;
    imp_elim_drv(imp_elim_drv(spec, left)?, right)
}

// ============================================================================
// Negation — `¬p ≡ p ⟹ F`  (`F` = the defined `defs::fal`)
// ============================================================================

fn not_intro_slow<L: HolTier>(th: Thm<L>) -> Result<Thm<L>> {
    let (p, f) = parse_imp(th.concl())?;
    if !is_fal(f) {
        return Err(Error::ConnectiveRule(format!(
            "not_intro: consequent {f} is not F"
        )));
    }
    let p = p.clone();
    unfold_at(not_def()?, p)?.sym()?.eq_mp(th)
}

fn not_elim_slow<L: HolTier>(neg: Thm<L>, other: Thm<L>) -> Result<Thm<L>> {
    let p = parse_not(neg.concl())?.clone();
    if p != *other.concl() {
        return Err(Error::ConnectiveRule(format!(
            "not_elim: negated {p} ≠ hypothesis {}",
            other.concl()
        )));
    }
    let unfolded = unfold_at(not_def()?, p)?.eq_mp(neg)?; // Γ ⊢ p ⟹ F
    imp_elim_drv(unfolded, other)
}

// ============================================================================
// Ex falso — `F ≡ ∀p:bool. p`
// ============================================================================

fn false_elim_drv<L: HolTier>(th: Thm<L>, p: Term) -> Result<Thm<L>> {
    if !is_fal(th.concl()) {
        return Err(Error::ConnectiveRule(format!(
            "false_elim: conclusion {} is not F",
            th.concl()
        )));
    }
    check_bool(&p)?;
    // Γ ⊢ ∀q:bool. q, then ∀-elim at the target.
    let unfolded = fal_def()?.eq_mp(th)?;
    all_elim_drv(unfolded, p)
}

/// `⊢ F = (∀p:bool. p)` (cached) — `fal`'s defining equation.
fn fal_def<L: HolTier>() -> Result<Thm<L>> {
    static D: LazyLock<CoreThm> =
        LazyLock::new(|| crate::delta_at(&defs::fal()).expect("derived: unfold F"));
    at_tier(&D)
}

// ============================================================================
// Schema fast paths
// ============================================================================
//
// Each hot rule keeps a **schema** — the rule derived ONCE (via its slow
// derivation above) at fresh `bool` variables, at the pure `CoreLang`
// tier — and per call instantiates it with one kernel `inst` per
// variable, then cuts the premises in with `PROVE_HYP` (`deduct_antisym`
// + `eq_mp`, 2 mints). That turns a 15–100-mint derivation into 3–8
// mints on the hot path.
//
// **Verified, not trusted:** a fast path's result is checked against the
// exact rule contract — conclusion term AND hypothesis set — and any
// mismatch (schema-variable capture, an `inst` no-op on a non-bool
// argument, a hypothesis-bookkeeping edge case) falls back to the slow
// derivation, which reproduces the old kernel rule's behaviour and typed
// errors bit-for-bit. Soundness never rests on the fast path (every mint
// is still a gated kernel rule); the verification only pins the API
// contract.
//
// Schema variable names are `∂`-prefixed to keep accidental capture (and
// so slow-path fallbacks) out of real proof traffic.

const SP: &str = "\u{2202}p#l2";
const SQ: &str = "\u{2202}q#l2";
const SR: &str = "\u{2202}r#l2";
const SPRED: &str = "\u{2202}P#l2";
const SW: &str = "\u{2202}w#l2";

fn svar(name: &str) -> Term {
    Term::free(name, b())
}

/// `PROVE_HYP`: from `a : A ⊢ x` and `b : B ⊢ y` with `x ∈ B`, derive
/// `A ∪ (B \ {x}) ⊢ y` (via `deduct_antisym` + `eq_mp`). Strict: `None`
/// unless `x` really is a hypothesis of `b` (so a cut can never silently
/// leave a schema hypothesis behind).
fn prove_hyp<L: HolTier>(a: &Thm<L>, b: Thm<L>) -> Option<Thm<L>> {
    if !b.hyps().contains(a.concl()) {
        return None;
    }
    let eq = a.clone().deduct_antisym(b).ok()?;
    eq.eq_mp(a.clone()).ok()
}

/// Instantiate a cached pure-tier `schema` at `subs` in order (each at
/// the replacement's own type), landing at the working tier `L`. Purely
/// mechanical; the callers verify the result shape.
fn inst_schema<L: HolTier>(schema: &CoreThm, subs: &[(&str, &Term)]) -> Option<Thm<L>> {
    let mut out = at_tier::<L>(schema).ok()?;
    for (n, t) in subs {
        out = out.inst(n, (*t).clone()).ok()?;
    }
    Some(out)
}

fn and_term(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::and(), p), q)
}

fn or_term(p: Term, q: Term) -> Term {
    Term::app(Term::app(defs::or(), p), q)
}

fn not_term(p: Term) -> Term {
    Term::app(defs::not(), p)
}

/// The final fast-path gate: conclusion and hypothesis set must match the
/// rule contract exactly.
fn verified<L: HolTier>(out: Thm<L>, concl: &Term, hyps: &covalence_core::Ctx) -> Option<Thm<L>> {
    (out.concl() == concl && out.hyps() == hyps).then_some(out)
}

fn schema_and_intro() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        // {∂p, ∂q} ⊢ ∂p ∧ ∂q
        and_intro_slow(
            Thm::assume(svar(SP)).unwrap(),
            Thm::assume(svar(SQ)).unwrap(),
        )
        .expect("derived: ∧-intro schema")
    });
    &S
}

fn schema_and_elim(first: bool) -> &'static CoreThm {
    // {∂p ∧ ∂q} ⊢ ∂p   /   {∂p ∧ ∂q} ⊢ ∂q
    static L: LazyLock<CoreThm> = LazyLock::new(|| {
        and_elim_slow(Thm::assume(and_term(svar(SP), svar(SQ))).unwrap(), true)
            .expect("derived: ∧-elim-l schema")
    });
    static R: LazyLock<CoreThm> = LazyLock::new(|| {
        and_elim_slow(Thm::assume(and_term(svar(SP), svar(SQ))).unwrap(), false)
            .expect("derived: ∧-elim-r schema")
    });
    if first { &L } else { &R }
}

fn schema_imp_def() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        // ⊢ (∂p ⟹ ∂q) = ((∂p ∧ ∂q) = ∂p)
        unfold_at_2(imp_def().expect("derived: ⟹-def"), svar(SP), svar(SQ))
            .expect("derived: ⟹-def schema")
    });
    &S
}

fn schema_imp_elim() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        // {∂p ⟹ ∂q, ∂p} ⊢ ∂q
        imp_elim_slow(
            Thm::assume(imp_term(svar(SP), svar(SQ))).unwrap(),
            Thm::assume(svar(SP)).unwrap(),
        )
        .expect("derived: ⟹-elim schema")
    });
    &S
}

fn schema_or_intro(left: bool) -> &'static CoreThm {
    // {∂p} ⊢ ∂p ∨ ∂q   /   {∂q} ⊢ ∂p ∨ ∂q
    static L: LazyLock<CoreThm> = LazyLock::new(|| {
        or_intro_slow(Thm::assume(svar(SP)).unwrap(), svar(SP), svar(SQ), true)
            .expect("derived: ∨-intro-l schema")
    });
    static R: LazyLock<CoreThm> = LazyLock::new(|| {
        or_intro_slow(Thm::assume(svar(SQ)).unwrap(), svar(SP), svar(SQ), false)
            .expect("derived: ∨-intro-r schema")
    });
    if left { &L } else { &R }
}

fn schema_or_elim() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        // {∂p ∨ ∂q, ∂p ⟹ ∂r, ∂q ⟹ ∂r} ⊢ ∂r
        or_elim_slow(
            Thm::assume(or_term(svar(SP), svar(SQ))).unwrap(),
            Thm::assume(imp_term(svar(SP), svar(SR))).unwrap(),
            Thm::assume(imp_term(svar(SQ), svar(SR))).unwrap(),
        )
        .expect("derived: ∨-elim schema")
    });
    &S
}

fn schema_not_intro() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        // {∂p ⟹ F} ⊢ ¬∂p
        not_intro_slow(Thm::assume(imp_term(svar(SP), defs::fal())).unwrap())
            .expect("derived: ¬-intro schema")
    });
    &S
}

fn schema_not_elim() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        // {¬∂p, ∂p} ⊢ F
        not_elim_slow(
            Thm::assume(not_term(svar(SP))).unwrap(),
            Thm::assume(svar(SP)).unwrap(),
        )
        .expect("derived: ¬-elim schema")
    });
    &S
}

fn schema_false_elim() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        // {F} ⊢ ∂p
        false_elim_drv(Thm::assume(defs::fal()).unwrap(), svar(SP))
            .expect("derived: ex-falso schema")
    });
    &S
}

/// `⊢ (∀[a] ∂P) = (∂P = (λx:a. T))` — the `∀`-unfold at a free predicate
/// variable; per call two kernel `inst`s (`a := τ`, `∂P := λ`) rebuild the
/// definitional equation with no congruence/β work.
fn schema_forall_at() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let pred = Term::free(SPRED, Type::fun(alpha.clone(), b()));
        let fa_def = crate::delta_at(&defs::forall(alpha)).expect("derived: unfold ∀");
        unfold_at(fa_def, pred).expect("derived: ∀-at schema")
    });
    &S
}

/// `⊢ (∀[ty] lam) = (lam = (λx:ty. T))` via [`schema_forall_at`]. Exact:
/// the replacements are inserted wholesale (never re-scanned), so no
/// capture is possible.
fn forall_at_eq<L: HolTier>(ty: Type, lam: Term) -> Result<Thm<L>> {
    at_tier::<L>(schema_forall_at())?
        .inst_tfree("a", ty)?
        .inst(SPRED, lam)
}

/// `{∀[a] ∂P} ⊢ ∂P ∂w` — `SPEC` at a free witness variable, with the
/// conclusion left as an **unreduced application** (the per-call β-step
/// happens at the real witness).
fn schema_all_elim() -> &'static CoreThm {
    static S: LazyLock<CoreThm> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let pred = Term::free(SPRED, Type::fun(alpha.clone(), b()));
        let w = Term::free(SW, alpha.clone());
        let fa = Term::app(defs::forall(alpha), pred.clone());
        let th = Thm::assume(fa).expect("derived: ∀-elim schema assume");
        // {∀ ∂P} ⊢ ∂P = (λx:a. T)
        let inner = forall_at_eq(Type::tfree("a"), pred)
            .and_then(|eq| eq.eq_mp(th))
            .expect("derived: ∀-elim schema unfold");
        // {∀ ∂P} ⊢ ∂P ∂w = (λx:a. T) ∂w  →  … = T  →  ∂P ∂w.
        let applied = Thm::refl(w)
            .and_then(|r| inner.mk_comb(r))
            .expect("derived: ∀-elim schema cong");
        let rhs_beta = rhs_of(&applied)
            .and_then(Thm::beta_conv)
            .expect("derived: ∀-elim schema β");
        applied
            .trans(rhs_beta)
            .and_then(eqt_elim)
            .expect("derived: ∀-elim schema")
    });
    &S
}

fn all_elim_fast<L: HolTier>(x: &Thm<L>, w: &Term) -> Option<Thm<L>> {
    let (ty, lam) = parse_forall(x.concl()).ok()?;
    if w.type_of().ok()? != ty {
        return None; // slow path raises TypeMismatch
    }
    // {∀[ty] lam} ⊢ lam w  (three kernel `inst`s of the schema).
    let s = at_tier::<L>(schema_all_elim())
        .ok()?
        .inst_tfree("a", ty)
        .ok()?
        .inst(SPRED, lam.clone())
        .ok()?
        .inst(SW, w.clone())
        .ok()?;
    let t = prove_hyp(x, s)?; // Γ ⊢ lam w
    let beta = Thm::beta_conv(Term::app(lam.clone(), w.clone())).ok()?; // ⊢ lam w = φ[w]
    let out = beta.eq_mp(t).ok()?;
    let TermKind::Abs(_, body) = lam.kind() else {
        return None;
    };
    verified(out, &subst::open(body, w), x.hyps())
}

fn and_intro_fast<L: HolTier>(x: &Thm<L>, y: &Thm<L>) -> Option<Thm<L>> {
    let (p, q) = (x.concl().clone(), y.concl().clone());
    let s = inst_schema(schema_and_intro(), &[(SP, &p), (SQ, &q)])?;
    let t = prove_hyp(x, s)?;
    let out = prove_hyp(y, t)?;
    verified(out, &and_term(p, q), &x.hyps().union(y.hyps()))
}

fn and_elim_fast<L: HolTier>(x: &Thm<L>, first: bool) -> Option<Thm<L>> {
    let (p, q) = parse_and(x.concl()).ok()?;
    let (p, q) = (p.clone(), q.clone());
    let s = inst_schema(schema_and_elim(first), &[(SP, &p), (SQ, &q)])?;
    let out = prove_hyp(x, s)?;
    verified(out, if first { &p } else { &q }, x.hyps())
}

fn imp_elim_fast<L: HolTier>(x: &Thm<L>, y: &Thm<L>) -> Option<Thm<L>> {
    let (phi, psi) = parse_imp(x.concl()).ok()?;
    let (phi, psi) = (phi.clone(), psi.clone());
    if y.concl() != &phi {
        return None; // slow path raises ImpAntecedentMismatch
    }
    let s = inst_schema(schema_imp_elim(), &[(SP, &phi), (SQ, &psi)])?;
    let t = prove_hyp(x, s)?;
    let out = prove_hyp(y, t)?;
    verified(out, &psi, &x.hyps().union(y.hyps()))
}

fn imp_intro_fast<L: HolTier>(x: &Thm<L>, phi: &Term) -> Option<Thm<L>> {
    if !phi.type_of().ok()?.is_bool() {
        return None; // slow path raises NotBool
    }
    let psi = x.concl().clone();
    // Γ ∪ {φ} ⊢ φ ∧ ψ  (fast ∧-intro, itself verified).
    let conj = and_intro_fast(&Thm::assume(phi.clone()).ok()?, x)?;
    // {φ ∧ ψ} ⊢ φ.
    let elim = inst_schema(schema_and_elim(true), &[(SP, phi), (SQ, &psi)])?;
    // Γ \ {φ} ⊢ (φ ∧ ψ) = φ (deduct_antisym discharges φ), then fold.
    let eq = conj.deduct_antisym(elim).ok()?;
    let fold = inst_schema(schema_imp_def(), &[(SP, phi), (SQ, &psi)])?;
    let out = fold.sym().ok()?.eq_mp(eq).ok()?;
    verified(out, &imp_term(phi.clone(), psi), &x.hyps().remove(phi))
}

fn or_intro_fast<L: HolTier>(x: &Thm<L>, p: &Term, q: &Term, left: bool) -> Option<Thm<L>> {
    let s = inst_schema(schema_or_intro(left), &[(SP, p), (SQ, q)])?;
    let out = prove_hyp(x, s)?;
    verified(out, &or_term(p.clone(), q.clone()), x.hyps())
}

fn or_elim_fast<L: HolTier>(d: &Thm<L>, l: &Thm<L>, r: &Thm<L>) -> Option<Thm<L>> {
    let (p, q) = parse_or(d.concl()).ok()?;
    let (p, q) = (p.clone(), q.clone());
    let (lp, lr) = parse_imp(l.concl()).ok()?;
    let (rq, rr) = parse_imp(r.concl()).ok()?;
    if lp != &p || rq != &q || lr != rr {
        return None; // slow path raises the shape errors
    }
    let goal = lr.clone();
    let s = inst_schema(schema_or_elim(), &[(SP, &p), (SQ, &q), (SR, &goal)])?;
    let t1 = prove_hyp(d, s)?;
    let t2 = prove_hyp(l, t1)?;
    let out = prove_hyp(r, t2)?;
    verified(out, &goal, &d.hyps().union(l.hyps()).union(r.hyps()))
}

fn not_intro_fast<L: HolTier>(x: &Thm<L>) -> Option<Thm<L>> {
    let (p, f) = parse_imp(x.concl()).ok()?;
    if !is_fal(f) {
        return None; // slow path raises ConnectiveRule
    }
    let p = p.clone();
    let s = inst_schema(schema_not_intro(), &[(SP, &p)])?;
    let out = prove_hyp(x, s)?;
    verified(out, &not_term(p), x.hyps())
}

fn not_elim_fast<L: HolTier>(neg: &Thm<L>, other: &Thm<L>) -> Option<Thm<L>> {
    let p = parse_not(neg.concl()).ok()?.clone();
    if other.concl() != &p {
        return None; // slow path raises ConnectiveRule
    }
    let s = inst_schema(schema_not_elim(), &[(SP, &p)])?;
    let t = prove_hyp(neg, s)?;
    let out = prove_hyp(other, t)?;
    verified(out, &defs::fal(), &neg.hyps().union(other.hyps()))
}

fn false_elim_fast<L: HolTier>(x: &Thm<L>, p: &Term) -> Option<Thm<L>> {
    if !is_fal(x.concl()) || !p.type_of().ok()?.is_bool() {
        return None; // slow path raises the shape/type errors
    }
    let s = inst_schema(schema_false_elim(), &[(SP, p)])?;
    let out = prove_hyp(x, s)?;
    verified(out, p, x.hyps())
}

// ============================================================================
// Dispatchers: fast path, verified; else the slow derivation
// ============================================================================

fn and_intro_drv<L: HolTier>(a: Thm<L>, other: Thm<L>) -> Result<Thm<L>> {
    if let Some(t) = and_intro_fast(&a, &other) {
        return Ok(t);
    }
    and_intro_slow(a, other)
}

fn and_elim_drv<L: HolTier>(conj: Thm<L>, first: bool) -> Result<Thm<L>> {
    if let Some(t) = and_elim_fast(&conj, first) {
        return Ok(t);
    }
    and_elim_slow(conj, first)
}

fn imp_intro_drv<L: HolTier>(th: Thm<L>, phi: &Term) -> Result<Thm<L>> {
    if let Some(t) = imp_intro_fast(&th, phi) {
        return Ok(t);
    }
    imp_intro_slow(th, phi)
}

fn imp_elim_drv<L: HolTier>(imp: Thm<L>, hyp: Thm<L>) -> Result<Thm<L>> {
    if let Some(t) = imp_elim_fast(&imp, &hyp) {
        return Ok(t);
    }
    imp_elim_slow(imp, hyp)
}

fn all_elim_drv<L: HolTier>(th: Thm<L>, witness: Term) -> Result<Thm<L>> {
    if let Some(t) = all_elim_fast(&th, &witness) {
        return Ok(t);
    }
    all_elim_slow(th, witness)
}

fn or_intro_drv<L: HolTier>(th: Thm<L>, p: Term, q: Term, left: bool) -> Result<Thm<L>> {
    if let Some(t) = or_intro_fast(&th, &p, &q, left) {
        return Ok(t);
    }
    or_intro_slow(th, p, q, left)
}

fn or_elim_drv<L: HolTier>(disj: Thm<L>, left: Thm<L>, right: Thm<L>) -> Result<Thm<L>> {
    if let Some(t) = or_elim_fast(&disj, &left, &right) {
        return Ok(t);
    }
    or_elim_slow(disj, left, right)
}

fn not_intro_drv<L: HolTier>(th: Thm<L>) -> Result<Thm<L>> {
    // Transitional drop-in tolerance (dies with EG5): a premise stated
    // over the literal — `Γ ⊢ p ⟹ ⌜F⌝`, the shape the deleted kernel
    // rule accepted — crosses the EG3b bridge at the eval tier first
    // (re-point the consequent at the defined `F`, then fold).
    if let Ok((p, f)) = parse_imp(th.concl())
        && matches!(f.kind(), TermKind::Bool(false))
        && let Some(eval_th) = same_tier::<L, crate::CoreEval>(th.clone())
    {
        let p = p.clone();
        let bridged = (|| -> Result<crate::EvalThm> {
            let fired = imp_elim_drv(eval_th, Thm::assume(p.clone())?)?; // Γ ∪ {p} ⊢ ⌜F⌝
            imp_intro_drv(crate::boolean::fal_from_lit(fired)?, &p) // Γ ⊢ p ⟹ F
        })()?;
        let back = same_tier::<crate::CoreEval, L>(bridged).expect("same tier");
        return not_intro_drv(back);
    }
    if let Some(t) = not_intro_fast(&th) {
        return Ok(t);
    }
    not_intro_slow(th)
}

fn not_elim_drv<L: HolTier>(neg: Thm<L>, other: Thm<L>) -> Result<Thm<L>> {
    if let Some(t) = not_elim_fast(&neg, &other) {
        return Ok(t);
    }
    not_elim_slow(neg, other)
}

fn false_elim_disp<L: HolTier>(th: Thm<L>, p: Term) -> Result<Thm<L>> {
    // Transitional drop-in tolerance (dies with EG5): a literal-`⌜F⌝`
    // premise — the shape the deleted kernel rule required — crosses the
    // EG3b bridge at the eval tier (`fal_from_lit`, the derived literal
    // ex falso) before the defined-`F` derivation runs. At any other
    // tier the literal carries no commitments and is correctly rejected.
    if matches!(th.concl().kind(), TermKind::Bool(false))
        && let Some(eval_th) = same_tier::<L, crate::CoreEval>(th.clone())
    {
        let bridged = crate::boolean::fal_from_lit(eval_th)?; // Γ ⊢ F
        let back = same_tier::<crate::CoreEval, L>(bridged).expect("same tier");
        return false_elim_disp(back, p);
    }
    if let Some(t) = false_elim_fast(&th, &p) {
        return Ok(t);
    }
    false_elim_drv(th, p)
}

// ============================================================================
// Excluded middle — the classical ε-derivation, cached as a schema
// ============================================================================

/// The classical `EXCLUDED_MIDDLE` derivation: `⊢ p ∨ ¬p` for the free
/// variable `p : bool`, from Hilbert choice
/// ([`covalence_core::Thm::select_ax`]) plus funext-via-`abs`, following
/// HOL Light `class.ml` — derived at the pure `CoreLang` tier over the
/// defined `T` / `F`.
///
/// With `Pt := λx. (x = T) ∨ p` and `Pf := λx. (x = F) ∨ p`,
/// `U := ε Pt`, `V := ε Pf`:
/// 1. `⊢ (U = T) ∨ p` and `⊢ (V = F) ∨ p` — `select_ax` on the witnesses
///    `T` / `F` (each satisfies its predicate by `DISJ1` on `refl`).
/// 2. Under `{p}`: both predicate bodies are `= T` (`DISJ2` + `EQT_INTRO`),
///    so `Pt = Pf` by `abs`, so `U = V` by congruence — hence under
///    `{p, U = T, V = F}`: `T = U = V = F`, so `⊢ F` via [`truth`] +
///    `eq_mp`, so `{U = T, V = F} ⊢ ¬p`, so `p ∨ ¬p` by `DISJ2`.
/// 3. `DISJ_CASES` over (1)'s two disjunctions: every branch ends in
///    `p ∨ ¬p` (`{p}` branches by `DISJ1`). ∎
fn lem_schema() -> Result<CoreThm> {
    let p = svar(SP);
    let not_p = Term::app(defs::not(), p.clone());
    let goal = Term::app(Term::app(defs::or(), p.clone()), not_p.clone());
    let t_def = defs::tru();
    let f_def = defs::fal();

    // The two selector predicates and their ε-choices.
    let x = Term::free("x", b());
    let pred_at = |c: &Term| -> Result<Term> {
        // λx:bool. (x = c) ∨ p
        let body = Term::app(
            Term::app(
                defs::or(),
                covalence_core::hol::hol_eq(x.clone(), c.clone()),
            ),
            p.clone(),
        );
        Ok(Term::abs(b(), subst::close(&body, "x")))
    };
    let pt = pred_at(&t_def)?;
    let pf = pred_at(&f_def)?;
    let u = Term::app(Term::select_op(b()), pt.clone());
    let v = Term::app(Term::select_op(b()), pf.clone());

    // 1. ⊢ (U = T) ∨ p  and  ⊢ (V = F) ∨ p.
    let choose = |pred: &Term, c: &Term, chosen: &Term| -> Result<CoreThm> {
        // ⊢ (c = c) ∨ p, β-folded into `pred c`.
        let refl_c = Thm::refl(c.clone())?;
        let c_case = or_intro_drv(refl_c.clone(), refl_c.concl().clone(), p.clone(), true)?;
        let beta_w = Thm::beta_conv(Term::app(pred.clone(), c.clone()))?; // ⊢ pred c = ((c=c) ∨ p)
        let pred_holds = beta_w.sym()?.eq_mp(c_case)?; // ⊢ pred c
        // select_intro (sequent choice): ⊢ pred c gives ⊢ pred (ε pred),
        // then β the conclusion.
        let at_choice = Thm::select_intro(pred_holds)?; // ⊢ pred (ε pred)
        let beta_c = Thm::beta_conv(Term::app(pred.clone(), chosen.clone()))?;
        beta_c.eq_mp(at_choice) // ⊢ (chosen = c) ∨ p
    };
    let u_case = choose(&pt, &t_def, &u)?; // ⊢ (U = T) ∨ p
    let v_case = choose(&pf, &f_def, &v)?; // ⊢ (V = F) ∨ p

    // Branch A: ⊢ p ⟹ (p ∨ ¬p).
    let branch_p = {
        let by_p = or_intro_drv(Thm::assume(p.clone())?, p.clone(), not_p.clone(), true)?;
        imp_intro_drv(by_p, &p)?
    };

    // Branch B: {U = T, V = F} ⊢ p ∨ ¬p (via ¬p).
    let u_eq_t = covalence_core::hol::hol_eq(u.clone(), t_def.clone());
    let v_eq_f = covalence_core::hol::hol_eq(v.clone(), f_def.clone());
    let branch_uv = {
        // Under {p}: Pt = Pf pointwise at the free x, then abs + congruence.
        let assume_p = Thm::assume(p.clone())?;
        let xt = covalence_core::hol::hol_eq(x.clone(), t_def.clone());
        let xf = covalence_core::hol::hol_eq(x.clone(), f_def.clone());
        let bt = eqt_intro(or_intro_drv(
            assume_p.clone(),
            xt.clone(),
            p.clone(),
            false,
        )?)?; // {p} ⊢ ((x=T) ∨ p) = T
        let bf = eqt_intro(or_intro_drv(assume_p, xf.clone(), p.clone(), false)?)?; // {p} ⊢ ((x=F) ∨ p) = T
        let pointwise = bt.trans(bf.sym()?)?; // {p} ⊢ ((x=T)∨p) = ((x=F)∨p)
        let lam_eq = pointwise.abs("x", b())?; // {p} ⊢ Pt = Pf
        let u_eq_v = Thm::refl(Term::select_op(b()))?.mk_comb(lam_eq)?; // {p} ⊢ U = V
        // {p, U=T, V=F} ⊢ T = F.
        let t_eq_f = Thm::assume(u_eq_t.clone())?
            .sym()? // T = U
            .trans(u_eq_v)? // T = V
            .trans(Thm::assume(v_eq_f.clone())?)?; // T = F
        let falsity = t_eq_f.eq_mp(truth()?)?; // {p, U=T, V=F} ⊢ F
        let neg = not_intro_drv(imp_intro_drv(falsity, &p)?)?; // {U=T, V=F} ⊢ ¬p
        or_intro_drv(neg, p.clone(), not_p.clone(), false)? // {U=T, V=F} ⊢ p ∨ ¬p
    };

    // Stitch: inner DISJ_CASES over (V = F) ∨ p under {U = T}, then the
    // outer one over (U = T) ∨ p.
    let inner_left = imp_intro_drv(branch_uv, &v_eq_f)?; // {U=T} ⊢ (V=F) ⟹ (p∨¬p)
    let inner = or_elim_drv(v_case, inner_left, branch_p.clone())?; // {U=T} ⊢ p∨¬p
    let outer_left = imp_intro_drv(inner, &u_eq_t)?; // ⊢ (U=T) ⟹ (p∨¬p)
    let out = or_elim_drv(u_case, outer_left, branch_p)?;
    debug_assert_eq!(out.concl(), &goal);
    debug_assert!(out.hyps().is_empty());
    Ok(out)
}

fn lem_drv<L: HolTier>(p: Term) -> Result<Thm<L>> {
    static SCHEMA: LazyLock<CoreThm> = LazyLock::new(|| lem_schema().expect("derived: LEM schema"));
    check_bool(&p)?;
    // One kernel `inst`: the schema's sole free variable is `∂p : bool`,
    // so the instance is exactly `⊢ p ∨ ¬p` at the given `p` (verified).
    let out = at_tier::<L>(&SCHEMA)?.inst(SP, p.clone())?;
    debug_assert_eq!(out.concl(), &or_term(p.clone(), not_term(p.clone())));
    debug_assert!(out.hyps().is_empty());
    Ok(out)
}

// ============================================================================
// Derived axiom forms of the sequent-reshaped kernel rules (stage A3)
// ============================================================================
//
// The kernel's choice / def-spec / subtype / nat-freeness rules are
// connective-free **sequent** rules (`Thm::select_intro`, `Thm::spec_intro`,
// `Thm::spec_rep_abs_intro`, `Thm::succ_eq_elim`, `Thm::zero_eq_succ_elim`);
// the classic implication / negation axiom forms below are zero-TCB
// derivations over them (`assume` + rule + `imp_intro` / `not_intro`),
// provided as drop-ins with the pre-sequent kernel signatures.

/// `⊢ p x ⟹ p (ε p)` — the classic Hilbert-choice axiom form
/// (`assume` + [`Thm::select_intro`] + `imp_intro`).
fn select_ax_drv<L: HolTier>(p: Term, x: Term) -> Result<Thm<L>> {
    let px = Term::app(p, x);
    let holds = Thm::assume(px.clone())?; // {p x} ⊢ p x (validates typing)
    let chosen = Thm::select_intro(holds)?; // {p x} ⊢ p (ε p)
    imp_intro_drv(chosen, &px) // ⊢ p x ⟹ p (ε p)
}

/// Rebuild a spec's instantiated selector predicate — the same positional
/// simultaneous tvar substitution the kernel's `spec_intro` /
/// `spec_rep_abs_intro` apply (their structural-equality premise check
/// makes any divergence here fail closed, never mis-mint).
fn spec_pred(
    ty: Option<&Type>,
    tm: Option<&Term>,
    args: &covalence_core::TypeList,
) -> Result<Term> {
    let declared_ty = ty.ok_or(Error::SpecHasNoBody)?;
    let body = tm.ok_or(Error::SpecHasNoBody)?;
    let tvars = declared_ty.free_tvars();
    let sub: std::collections::BTreeMap<_, _> =
        tvars.iter().cloned().zip(args.iter().cloned()).collect();
    Ok(subst::subst_tfrees_in_term(body, &sub))
}

/// `⊢ p w ⟹ p t` for a def-style `TermSpec` leaf `t` with selector
/// predicate `p` and witness `w` (`assume` + [`Thm::spec_intro`] +
/// `imp_intro`).
fn spec_ax_drv<L: HolTier>(t: Term, w: Term) -> Result<Thm<L>> {
    let (spec, args) = match t.kind() {
        TermKind::Spec(spec, args) => (spec.clone(), args.clone()),
        _ => return Err(Error::NotASpec),
    };
    let pred = spec_pred(spec.ty(), spec.tm(), &args)?;
    let pw = Term::app(pred, w);
    let holds = Thm::assume(pw.clone())?; // {p w} ⊢ p w (validates typing)
    let concl = Thm::spec_intro(holds, t)?; // {p w} ⊢ p t
    imp_intro_drv(concl, &pw)
}

/// `⊢ P a ⟹ rep (abs a) = a` for a subtype `TypeSpec` (`assume` +
/// [`Thm::spec_rep_abs_intro`] + `imp_intro`).
fn spec_rep_abs_fwd_drv<L: HolTier>(
    spec: covalence_core::TypeSpec,
    args: covalence_core::TypeList,
    a: Term,
) -> Result<Thm<L>> {
    let pred = spec_pred(spec.ty(), spec.tm(), &args).map_err(|_| Error::NotASubtype)?;
    let pa = Term::app(pred, a);
    let holds = Thm::assume(pa.clone())?; // {P a} ⊢ P a (validates typing)
    let eq = Thm::spec_rep_abs_intro(spec, args, holds)?; // {P a} ⊢ rep (abs a) = a
    imp_intro_drv(eq, &pa)
}

/// `⊢ succ m = succ n ⟹ m = n` (`assume` + [`Thm::succ_eq_elim`] +
/// `imp_intro`).
fn succ_inj_drv<L: HolTier>(m: Term, n: Term) -> Result<Thm<L>> {
    let eq = covalence_core::hol::hol_eq_at(
        Type::nat(),
        Term::app(Term::succ(), m),
        Term::app(Term::succ(), n),
    );
    let holds = Thm::assume(eq.clone())?; // validates m, n : nat
    let stripped = Thm::succ_eq_elim(holds)?; // {succ m = succ n} ⊢ m = n
    imp_intro_drv(stripped, &eq)
}

/// `⊢ ¬(⌜0⌝ = succ n)` — `assume`, then [`Thm::zero_eq_succ_elim`] at
/// `q := F`, then `imp_intro` and `not_intro`. The zero side is the
/// `Nat` literal `⌜0⌝`, exactly as the pre-sequent kernel rule minted it.
fn zero_ne_succ_drv<L: HolTier>(n: Term) -> Result<Thm<L>> {
    let eq = covalence_core::hol::hol_eq_at(
        Type::nat(),
        covalence_core::hol::zero(),
        Term::app(Term::succ(), n),
    );
    let holds = Thm::assume(eq.clone())?; // validates n : nat
    let falsum = Thm::zero_eq_succ_elim(holds, defs::fal())?; // {0 = succ n} ⊢ F
    not_intro_drv(imp_intro_drv(falsum, &eq)?) // ⊢ ¬(0 = succ n)
}

// ============================================================================
// The drop-in trait
// ============================================================================

/// The deleted kernel connective / quantifier rules, re-provided as
/// **derivations** with identical signatures (see the [module docs](self)),
/// implemented for `Thm<L>` at **every** [`HolTier`] `L` (the cached
/// ingredients are pure-tier; higher tiers consume them via the sound
/// low→high lift). Import this trait and the old call sites compile
/// unchanged.
pub trait DerivedRules: Sized {
    /// `Γ \ {φ} ⊢ φ ⟹ ψ`, given `Γ ⊢ ψ` (HOL Light `DISCH`).
    fn imp_intro(self, phi: &Term) -> Result<Self>;
    /// [`imp_intro`](Self::imp_intro) interning its conclusion into `cons`.
    fn imp_intro_with<C: TrustedCons + ?Sized>(self, phi: &Term, cons: &mut C) -> Result<Self>;
    /// `Γ ∪ Δ ⊢ ψ`, given `Γ ⊢ φ ⟹ ψ` and `Δ ⊢ φ` (HOL Light `MP`).
    fn imp_elim(self, hyp: Self) -> Result<Self>;
    /// `Γ ⊢ ∀x:τ. φ`, given `Γ ⊢ φ` with `(name:τ)` not free in `Γ`
    /// (HOL Light `GEN`).
    fn all_intro(self, name: &str, ty: Type) -> Result<Self>;
    /// [`all_intro`](Self::all_intro) interning its conclusion into `cons`.
    fn all_intro_with<C: TrustedCons + ?Sized>(
        self,
        name: &str,
        ty: Type,
        cons: &mut C,
    ) -> Result<Self>;
    /// `Γ ⊢ φ[t/x]`, given `Γ ⊢ ∀x:τ. φ` and `t : τ` (HOL Light `SPEC`).
    fn all_elim(self, witness: Term) -> Result<Self>;
    /// [`all_elim`](Self::all_elim) interning its conclusion into `cons`.
    fn all_elim_with<C: TrustedCons + ?Sized>(self, witness: Term, cons: &mut C) -> Result<Self>;
    /// `Γ ∪ Δ ⊢ p ∧ q`, given `Γ ⊢ p` and `Δ ⊢ q` (HOL Light `CONJ`).
    fn and_intro(self, other: Self) -> Result<Self>;
    /// [`and_intro`](Self::and_intro) interning its conclusion into `cons`.
    fn and_intro_with<C: TrustedCons + ?Sized>(self, other: Self, cons: &mut C) -> Result<Self>;
    /// `Γ ⊢ p`, given `Γ ⊢ p ∧ q` (HOL Light `CONJUNCT1`).
    fn and_elim_l(self) -> Result<Self>;
    /// `Γ ⊢ q`, given `Γ ⊢ p ∧ q` (HOL Light `CONJUNCT2`).
    fn and_elim_r(self) -> Result<Self>;
    /// `Γ ⊢ p ∨ q`, given `Γ ⊢ p` and `q : bool` (HOL Light `DISJ1`).
    fn or_intro_l(self, q: Term) -> Result<Self>;
    /// [`or_intro_l`](Self::or_intro_l) interning its conclusion into `cons`.
    fn or_intro_l_with<C: TrustedCons + ?Sized>(self, q: Term, cons: &mut C) -> Result<Self>;
    /// `Γ ⊢ p ∨ q`, given `Γ ⊢ q` and `p : bool` (HOL Light `DISJ2`).
    fn or_intro_r(self, p: Term) -> Result<Self>;
    /// [`or_intro_r`](Self::or_intro_r) interning its conclusion into `cons`.
    fn or_intro_r_with<C: TrustedCons + ?Sized>(self, p: Term, cons: &mut C) -> Result<Self>;
    /// `Γ ∪ Δ₁ ∪ Δ₂ ⊢ r`, given `Γ ⊢ p ∨ q`, `Δ₁ ⊢ p ⟹ r`, `Δ₂ ⊢ q ⟹ r`
    /// (HOL Light `DISJ_CASES`).
    fn or_elim(self, left: Self, right: Self) -> Result<Self>;
    /// `Γ ⊢ ¬p`, given `Γ ⊢ p ⟹ F` (HOL Light `NOT_INTRO`).
    fn not_intro(self) -> Result<Self>;
    /// [`not_intro`](Self::not_intro) interning its conclusion into `cons`.
    fn not_intro_with<C: TrustedCons + ?Sized>(self, cons: &mut C) -> Result<Self>;
    /// `Γ ∪ Δ ⊢ F`, given `Γ ⊢ ¬p` and `Δ ⊢ p` (HOL Light `NOT_ELIM`).
    fn not_elim(self, other: Self) -> Result<Self>;
    /// [`not_elim`](Self::not_elim) interning its conclusion into `cons`.
    fn not_elim_with<C: TrustedCons + ?Sized>(self, other: Self, cons: &mut C) -> Result<Self>;
    /// `Γ ⊢ p`, given `Γ ⊢ F` and `p : bool` — ex falso quodlibet,
    /// **derived** (`F ≡ ∀p:bool. p`, unfold + `∀`-elim at the target;
    /// the deleted kernel `FalseElim` primitive's drop-in). `F` here is
    /// the *defined* [`defs::fal`]; at the **eval tier** a transitional
    /// literal-`⌜F⌝` premise is also accepted, crossing the bridge
    /// automatically ([`crate::boolean::fal_from_lit`] — a cert-backed
    /// derivation, so other tiers correctly reject the literal form).
    fn false_elim(self, p: Term) -> Result<Self>;
    /// `⊢ p ∨ ¬p` — excluded middle, derived from `ε` (one cached schema +
    /// one `inst` per call).
    fn lem(p: Term) -> Result<Self>;
    /// `⊢ p x ⟹ p (ε p)` — Hilbert's choice axiom, the pre-sequent
    /// kernel `select_ax` signature (derived over [`covalence_core::Thm::select_intro`]).
    fn select_ax(p: Term, x: Term) -> Result<Self>;
    /// `⊢ p w ⟹ p t` for a def-style `TermSpec` leaf `t` — the
    /// pre-sequent kernel `spec_ax` signature (derived over
    /// [`covalence_core::Thm::spec_intro`]).
    fn spec_ax(t: Term, w: Term) -> Result<Self>;
    /// `⊢ P a ⟹ rep (abs a) = a` for a subtype `TypeSpec` — the
    /// pre-sequent kernel `spec_rep_abs_fwd` signature (derived over
    /// [`covalence_core::Thm::spec_rep_abs_intro`]).
    fn spec_rep_abs_fwd(
        spec: covalence_core::TypeSpec,
        args: impl Into<covalence_core::TypeList>,
        a: Term,
    ) -> Result<Self>;
    /// `⊢ succ m = succ n ⟹ m = n` — the pre-sequent kernel `succ_inj`
    /// signature (derived over [`covalence_core::Thm::succ_eq_elim`]).
    fn succ_inj(m: Term, n: Term) -> Result<Self>;
    /// `⊢ ¬(⌜0⌝ = succ n)` — the pre-sequent kernel `zero_ne_succ`
    /// signature (derived over [`covalence_core::Thm::zero_eq_succ_elim`]).
    fn zero_ne_succ(n: Term) -> Result<Self>;
}

/// Deep-intern a theorem's conclusion into `cons` — the `_with` sharing
/// contract of the old kernel glue. Pure sharing, no soundness role.
fn intern_concl<L: HolTier, C: TrustedCons + ?Sized>(thm: &Thm<L>, cons: &mut C) {
    let _ = thm.concl().cons_with(cons);
}

impl<L: HolTier> DerivedRules for Thm<L> {
    fn imp_intro(self, phi: &Term) -> Result<Self> {
        imp_intro_drv(self, phi)
    }
    fn imp_intro_with<C: TrustedCons + ?Sized>(self, phi: &Term, cons: &mut C) -> Result<Self> {
        let thm = imp_intro_drv(self, phi)?;
        intern_concl(&thm, cons);
        Ok(thm)
    }
    fn imp_elim(self, hyp: Self) -> Result<Self> {
        imp_elim_drv(self, hyp)
    }
    fn all_intro(self, name: &str, ty: Type) -> Result<Self> {
        all_intro_drv(self, name, ty)
    }
    fn all_intro_with<C: TrustedCons + ?Sized>(
        self,
        name: &str,
        ty: Type,
        cons: &mut C,
    ) -> Result<Self> {
        let thm = all_intro_drv(self, name, ty)?;
        intern_concl(&thm, cons);
        Ok(thm)
    }
    fn all_elim(self, witness: Term) -> Result<Self> {
        all_elim_drv(self, witness)
    }
    fn all_elim_with<C: TrustedCons + ?Sized>(self, witness: Term, cons: &mut C) -> Result<Self> {
        let thm = all_elim_drv(self, witness)?;
        intern_concl(&thm, cons);
        Ok(thm)
    }
    fn and_intro(self, other: Self) -> Result<Self> {
        and_intro_drv(self, other)
    }
    fn and_intro_with<C: TrustedCons + ?Sized>(self, other: Self, cons: &mut C) -> Result<Self> {
        let thm = and_intro_drv(self, other)?;
        intern_concl(&thm, cons);
        Ok(thm)
    }
    fn and_elim_l(self) -> Result<Self> {
        and_elim_drv(self, true)
    }
    fn and_elim_r(self) -> Result<Self> {
        and_elim_drv(self, false)
    }
    fn or_intro_l(self, q: Term) -> Result<Self> {
        let p = self.concl().clone();
        or_intro_drv(self, p, q, true)
    }
    fn or_intro_l_with<C: TrustedCons + ?Sized>(self, q: Term, cons: &mut C) -> Result<Self> {
        let p = self.concl().clone();
        let thm = or_intro_drv(self, p, q, true)?;
        intern_concl(&thm, cons);
        Ok(thm)
    }
    fn or_intro_r(self, p: Term) -> Result<Self> {
        let q = self.concl().clone();
        or_intro_drv(self, p, q, false)
    }
    fn or_intro_r_with<C: TrustedCons + ?Sized>(self, p: Term, cons: &mut C) -> Result<Self> {
        let q = self.concl().clone();
        let thm = or_intro_drv(self, p, q, false)?;
        intern_concl(&thm, cons);
        Ok(thm)
    }
    fn or_elim(self, left: Self, right: Self) -> Result<Self> {
        or_elim_drv(self, left, right)
    }
    fn not_intro(self) -> Result<Self> {
        not_intro_drv(self)
    }
    fn not_intro_with<C: TrustedCons + ?Sized>(self, cons: &mut C) -> Result<Self> {
        let thm = not_intro_drv(self)?;
        intern_concl(&thm, cons);
        Ok(thm)
    }
    fn not_elim(self, other: Self) -> Result<Self> {
        not_elim_drv(self, other)
    }
    fn not_elim_with<C: TrustedCons + ?Sized>(self, other: Self, cons: &mut C) -> Result<Self> {
        let thm = not_elim_drv(self, other)?;
        intern_concl(&thm, cons);
        Ok(thm)
    }
    fn false_elim(self, p: Term) -> Result<Self> {
        false_elim_disp(self, p)
    }
    fn lem(p: Term) -> Result<Self> {
        lem_drv(p)
    }
    fn select_ax(p: Term, x: Term) -> Result<Self> {
        select_ax_drv(p, x)
    }
    fn spec_ax(t: Term, w: Term) -> Result<Self> {
        spec_ax_drv(t, w)
    }
    fn spec_rep_abs_fwd(
        spec: covalence_core::TypeSpec,
        args: impl Into<covalence_core::TypeList>,
        a: Term,
    ) -> Result<Self> {
        spec_rep_abs_fwd_drv(spec, args.into(), a)
    }
    fn succ_inj(m: Term, n: Term) -> Result<Self> {
        succ_inj_drv(m, n)
    }
    fn zero_ne_succ(n: Term) -> Result<Self> {
        zero_ne_succ_drv(n)
    }
}

// ============================================================================
// TypeDef splitting
// ============================================================================

/// Split a [`covalence_core::TypeDef`]'s bijection conjunction
/// `abs_rep ∧ (fwd ∧ back)` into the three `∀`-closed laws. The kernel's
/// `new_type_definition` no longer splits it (that used the deleted
/// `and_elim` rules); consumers derive the projections here instead.
pub trait TypeDefExt<L: HolTier> {
    /// `⊢ ∀a:τ. abs (rep a) = a`.
    fn abs_rep(&self) -> Result<Thm<L>>;
    /// `⊢ ∀r:α. P r ⟹ rep (abs r) = r`.
    fn rep_abs_fwd(&self) -> Result<Thm<L>>;
    /// `⊢ ∀r:α. rep (abs r) = r ⟹ P r`.
    fn rep_abs_back(&self) -> Result<Thm<L>>;
}

impl<L: HolTier> TypeDefExt<L> for TypeDef<L> {
    fn abs_rep(&self) -> Result<Thm<L>> {
        and_elim_drv(self.bijection.clone(), true)
    }
    fn rep_abs_fwd(&self) -> Result<Thm<L>> {
        and_elim_drv(and_elim_drv(self.bijection.clone(), false)?, true)
    }
    fn rep_abs_back(&self) -> Result<Thm<L>> {
        and_elim_drv(and_elim_drv(self.bijection.clone(), false)?, false)
    }
}
