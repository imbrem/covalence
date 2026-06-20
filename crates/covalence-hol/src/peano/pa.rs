//! **Peano arithmetic as a *proper* deep object theory** — pure-syntactic
//! derivability + a single internalized soundness theorem + one-step projection
//! (Phase B of `docs/peano-arithmetic-plan.md`, the
//! "proper-deep-embedding test" of `docs/theories-models-and-logics.md §5.5`).
//!
//! [`fol`](super::fol) reified PA's locally-nameless syntax + substitution;
//! [`sem`](super::sem) gave the **two-sorted HOAS semantic carrier**
//! `Φ_sem⟨'t,'r⟩` and the standard denotation `⟦·⟧` into HOL `nat`/`bool` *as a
//! single fold* (the re-packaging that makes the impredicative proof go
//! through). Here we build the two halves of a *proper* deep embedding:
//!
//! ## 1. `Derivable_PA` — pure syntactic data (no `Thm` inside)
//!
//! Exactly as [`crate::init::prop`]'s `Derivable_Prop`, derivability is the
//! impredicative Church predicate
//!
//! ```text
//!   Derivable_PA A  :=  ∀d:Φ_sem→bool. Closed_PA d ⟹ d A
//! ```
//!
//! A **PA derivation is a value `⊢ Derivable_PA ⌜A⌝`** — a derivability
//! witness over the reified syntax alone. It carries **no `⊢ ⟦A⟧`**: deriving a
//! theorem in PA never builds the corresponding HOL theorem. The derivation
//! constructors ([`derive_axiom`], [`derive_mp`]) are the way to obtain one
//! (the LCF discipline one level up); the quantifier/induction/Leibniz
//! constructors are deferred (see `peano/SKELETONS.md` — they need a
//! handler-threading motive encoding), though their `Closed_PA` *clauses* are
//! present and proved sound by [`soundness`].
//!
//! ## 2. The internalized soundness theorem (proved **once**)
//!
//! [`soundness`] proves `⊢ Derivable_PA A ⟹ ⟦A⟧` by **rule induction**: it
//! instantiates the impredicative predicate variable `d := ⟦·⟧`
//! ([`sem::denote_pred`]) and discharges `Closed_PA ⟦·⟧` clause by clause — each
//! PA axiom's denotation is its proven [`crate::init::nat`] theorem, modus
//! ponens is the kernel's `imp_elim`, and the **induction schema** discharges
//! to [`Thm::nat_induct`]. Two-sortedness — PA terms denote into `nat`,
//! formulas into `bool` — is handled entirely by [`sem`]'s two-result-type
//! Church fold; here it is just `inst_tfree 't := nat, 'r := bool`.
//!
//! ## 3. One-step projection
//!
//! [`project`] is *just* `soundness` applied to a finished derivation:
//! `Derivable_PA ⌜A⌝ ↦ ⊢ ⟦A⟧`, a single `imp_elim`. No re-derivation.
//!
//! ## The old lock-step path (secondary)
//!
//! [`LockstepDerivation`] (a `Fol` paired with its `Thm`, built together) is a
//! documented placeholder for the secondary "directly obtain a HOL fact" path;
//! it is **not** the primary structure. The pure [`derivable`] +
//! [`project`] path is what the acceptance test
//! (`project_axiom_in_one_step`) exercises: derive a `Derivable_PA` witness,
//! then project in one move.

use covalence_core::{Result, Term, Thm, Type};

use super::fol::Fol;
use super::sem;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::nat;

// ============================================================================
// PA syntax builders (the reified `Fol` AST)
// ============================================================================

/// The PA term `0`.
pub fn zero() -> Fol {
    Fol::Zero
}
/// The PA term `S t`.
pub fn succ(t: Fol) -> Fol {
    Fol::Succ(Box::new(t))
}
/// The PA term `a + b`.
pub fn add(a: Fol, b: Fol) -> Fol {
    Fol::Add(Box::new(a), Box::new(b))
}
/// The PA term `a · b`.
pub fn mul(a: Fol, b: Fol) -> Fol {
    Fol::Mul(Box::new(a), Box::new(b))
}
/// A PA free variable `fvar k`.
pub fn var(k: u64) -> Fol {
    Fol::FVar(k)
}

/// **PA1.** `∀x. ¬(0 = S x)` — zero is not a successor.
pub fn ax_zero_ne_succ() -> Fol {
    Fol::All(Box::new(Fol::Neg(Box::new(Fol::Eq(
        Box::new(Fol::Zero),
        Box::new(Fol::Succ(Box::new(Fol::BVar(0)))),
    )))))
}
/// **PA2.** `∀x y. S x = S y ⟹ x = y` — successor is injective.
pub fn ax_succ_inj() -> Fol {
    Fol::All(Box::new(Fol::All(Box::new(Fol::Imp(
        Box::new(Fol::Eq(
            Box::new(Fol::Succ(Box::new(Fol::BVar(1)))),
            Box::new(Fol::Succ(Box::new(Fol::BVar(0)))),
        )),
        Box::new(Fol::Eq(Box::new(Fol::BVar(1)), Box::new(Fol::BVar(0)))),
    )))))
}
/// **PA3.** `∀x. 0 + x = x` — addition's base equation.
pub fn ax_add_base() -> Fol {
    Fol::All(Box::new(Fol::Eq(
        Box::new(Fol::Add(Box::new(Fol::Zero), Box::new(Fol::BVar(0)))),
        Box::new(Fol::BVar(0)),
    )))
}
/// **PA4.** `∀x y. S x + y = S (x + y)` — addition's step equation.
pub fn ax_add_step() -> Fol {
    Fol::All(Box::new(Fol::All(Box::new(Fol::Eq(
        Box::new(Fol::Add(
            Box::new(Fol::Succ(Box::new(Fol::BVar(1)))),
            Box::new(Fol::BVar(0)),
        )),
        Box::new(Fol::Succ(Box::new(Fol::Add(
            Box::new(Fol::BVar(1)),
            Box::new(Fol::BVar(0)),
        )))),
    )))))
}
/// **PA5.** `∀x. 0 · x = 0` — multiplication's base equation.
pub fn ax_mul_base() -> Fol {
    Fol::All(Box::new(Fol::Eq(
        Box::new(Fol::Mul(Box::new(Fol::Zero), Box::new(Fol::BVar(0)))),
        Box::new(Fol::Zero),
    )))
}
/// **PA6.** `∀x y. S x · y = y + x · y` — multiplication's step equation.
pub fn ax_mul_step() -> Fol {
    Fol::All(Box::new(Fol::All(Box::new(Fol::Eq(
        Box::new(Fol::Mul(
            Box::new(Fol::Succ(Box::new(Fol::BVar(1)))),
            Box::new(Fol::BVar(0)),
        )),
        Box::new(Fol::Add(
            Box::new(Fol::BVar(0)),
            Box::new(Fol::Mul(Box::new(Fol::BVar(1)), Box::new(Fol::BVar(0)))),
        )),
    )))))
}

/// The six PA axioms (PA1–PA6), in order, each as a reified [`Fol`] formula.
pub fn axioms() -> [Fol; 6] {
    [
        ax_zero_ne_succ(),
        ax_succ_inj(),
        ax_add_base(),
        ax_add_step(),
        ax_mul_base(),
        ax_mul_step(),
    ]
}

/// `⊢ ⟦PAᵢ⟧` — the proven HOL `nat` theorem that is axiom `i`'s denotation
/// (`1`-based). These are the soundness leaves: each PA axiom *is* one of
/// [`crate::init::nat`]'s independently-proved theorems.
fn axiom_nat_thm(i: usize) -> Result<Thm> {
    Ok(match i {
        1 => nat::zero_ne_succ(),
        2 => nat::succ_inj(),
        3 => nat::add_base(),
        4 => nat::add_step(),
        5 => nat::mul_base(),
        6 => nat::mul_step(),
        _ => {
            return Err(covalence_core::Error::ConnectiveRule(format!(
                "pa: axiom index {i} out of range 1..=6"
            )));
        }
    })
}

// ============================================================================
// Carrier-type plumbing — the proof runs at the standard instance and at the
// polymorphic carrier; helpers convert between them.
// ============================================================================

fn nat_ty() -> Type {
    Type::nat()
}
fn bool_ty() -> Type {
    Type::bool()
}
fn phi() -> Type {
    sem::phi()
}
fn phi_std() -> Type {
    sem::phi_at_std()
}
/// `Φ_sem → bool` at the polymorphic carrier — the type of the predicate
/// variable `d` bound in `Derivable_PA`.
fn d_ty() -> Type {
    Type::fun(phi(), bool_ty())
}
/// The predicate variable `d : Φ_sem → bool` (polymorphic carrier).
fn d_var() -> Term {
    Term::free("d", d_ty())
}
/// `d A`.
fn d_at(a: &Term) -> Result<Term> {
    d_var().apply(a.clone())
}
/// Instantiate both carrier type variables to the standard instance.
fn inst_std(t: &Term) -> Term {
    let t = covalence_core::subst::subst_tfree_in_term(t, "t", &nat_ty());
    covalence_core::subst::subst_tfree_in_term(&t, "r", &bool_ty())
}

// ============================================================================
// `Closed_PA d` — the closure conditions defining derivability
//
// Clauses, in fold order:
//   1..6  axioms        d ⌜PAᵢ⌝
//   7     modus ponens  ∀A B. d A ∧ d ⌜A⟹B⌝ ⟹ d B
//   8     induction     ∀Q:'t→'r. d ⌜Q 0⌝
//                                  ⟹ (∀x:'t. d ⌜Q x⌝ ⟹ d ⌜Q (S x)⌝)
//                                  ⟹ d ⌜∀x. Q x⌝
//   9     specialize    ∀Q:'t→'r. ∀w:'t. d ⌜∀x. Q x⌝ ⟹ d ⌜Q w⌝
//   10    leibniz       ∀a b:'t. ∀P:'t→'r. d ⌜a = b⌝ ⟹ d ⌜P a⌝ ⟹ d ⌜P b⌝
//   11    generalize    ∀Q:'t→'r. (∀x:'t. d ⌜Q x⌝) ⟹ d ⌜∀x. Q x⌝
//
// Both induction premises are `d`-of-a-formula (matching what the caller's
// base/step derivability witnesses provide directly). The soundness proof
// discharges induction → `Thm::nat_induct`, specialise/generalise →
// `Thm::all_elim`/`all_intro`, Leibniz → `eq_mp` (substitutivity of equality),
// after β-reducing the formulas to the `nat`/`bool` shape.
// ============================================================================

/// The number of `Closed_PA` clauses (axioms + MP + induction + specialise +
/// Leibniz + generalise).
const N_CLAUSES: usize = 11;

/// `Closed_PA d` — the right-nested conjunction of the closure clauses, as a
/// single `bool` term over the predicate `d` (supplied as a closure so the
/// same code builds it for `d` the bound variable *and* for `d := ⟦·⟧`).
fn closed(d_apply: &dyn Fn(&Term) -> Result<Term>, t: &Type, r: &Type) -> Result<Term> {
    let mut clauses: Vec<Term> = Vec::new();

    // 1..6 — axiom clauses `d ⌜PAᵢ⌝`.
    for ax in axioms().iter() {
        let enc = sem::encode_form_at(ax, t, r);
        clauses.push(d_apply(&enc)?);
    }

    // 7 — modus ponens `∀A B. d A ∧ d ⌜A⟹B⌝ ⟹ d B`.
    {
        let phi_tr = sem::phi_at(t, r);
        let a = Term::free("A", phi_tr.clone());
        let b = Term::free("B", phi_tr.clone());
        let imp_ab = sem::imp_cons(t, r, &a, &b);
        let mp = d_apply(&a)?
            .and(d_apply(&imp_ab)?)?
            .imp(d_apply(&b)?)?
            .forall("A", phi_tr.clone())?
            .forall("B", phi_tr)?;
        clauses.push(mp);
    }

    // 8 — induction `∀Q. d⌜Q0⌝ ⟹ (∀x. d⌜Qx⌝ ⟹ d⌜Q(Sx)⌝) ⟹ d⌜∀x.Qx⌝`.
    {
        let q_ty = Type::fun(t.clone(), r.clone());
        let q = Term::free("Q", q_ty.clone());
        let x = Term::free("x", t.clone());

        let base = d_apply(&sem::q_at_zero(t, r, &q))?;
        let step = d_apply(&sem::q_at(t, r, &q, x.clone()))?
            .imp(d_apply(&sem::q_at_succ(t, r, &q, x.clone()))?)?
            .forall("x", t.clone())?;
        let concl = d_apply(&sem::all_cons(t, r, q.clone()))?;

        let ind = base.imp(step.imp(concl)?)?.forall("Q", q_ty)?;
        clauses.push(ind);
    }

    // 9 — specialisation `∀Q w. d ⌜∀x. Q x⌝ ⟹ d ⌜Q w⌝`.
    {
        let q_ty = Type::fun(t.clone(), r.clone());
        let q = Term::free("Q", q_ty.clone());
        let w = Term::free("w", t.clone());

        let univ = d_apply(&sem::all_cons(t, r, q.clone()))?;
        let inst = d_apply(&sem::q_at(t, r, &q, w.clone()))?;
        let spec = univ
            .imp(inst)?
            .forall("w", t.clone())?
            .forall("Q", q_ty)?;
        clauses.push(spec);
    }

    // 10 — Leibniz `∀a b P. d ⌜a=b⌝ ⟹ d ⌜P a⌝ ⟹ d ⌜P b⌝`.
    {
        let p_ty = Type::fun(t.clone(), r.clone());
        let a = Term::free("a", t.clone());
        let b = Term::free("b", t.clone());
        let p = Term::free("P", p_ty.clone());

        let eq = d_apply(&sem::eq_cons(t, r, a.clone(), b.clone()))?;
        let pa = d_apply(&sem::q_at(t, r, &p, a.clone()))?;
        let pb = d_apply(&sem::q_at(t, r, &p, b.clone()))?;
        let leib = eq
            .imp(pa.imp(pb)?)?
            .forall("P", p_ty)?
            .forall("b", t.clone())?
            .forall("a", t.clone())?;
        clauses.push(leib);
    }

    // 11 — generalisation `∀Q. (∀x. d ⌜Q x⌝) ⟹ d ⌜∀x. Q x⌝`.
    {
        let q_ty = Type::fun(t.clone(), r.clone());
        let q = Term::free("Q", q_ty.clone());
        let x = Term::free("x", t.clone());

        let premise = d_apply(&sem::q_at(t, r, &q, x.clone()))?.forall("x", t.clone())?;
        let concl = d_apply(&sem::all_cons(t, r, q.clone()))?;
        let gen_clause = premise.imp(concl)?.forall("Q", q_ty)?;
        clauses.push(gen_clause);
    }

    // Right-nested conjunction.
    let mut iter = clauses.into_iter().rev();
    let mut acc = iter.next().expect("at least one clause");
    for cl in iter {
        acc = cl.and(acc)?;
    }
    Ok(acc)
}

/// `Closed_PA d` at the polymorphic carrier, for the predicate variable `d`.
fn closed_poly() -> Result<Term> {
    closed(&|f| d_at(f), &sem::tty(), &sem::rty())
}

/// `Derivable_PA A := ∀d. Closed_PA d ⟹ d A` — the impredicative derivability
/// predicate over an encoded formula `A : Φ_sem`.
pub fn derivable(a: &Term) -> Result<Term> {
    let closed_d = closed_poly()?;
    let body = closed_d.imp(d_at(a)?)?;
    body.forall("d", d_ty())
}

// ============================================================================
// `nth_conjunct` — peel a right-nested conjunction.
// ============================================================================

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

// ============================================================================
// Derivation constructors — the ONLY way to obtain `⊢ Derivable_PA ⌜A⌝`.
// Each opens `∀d. Closed_PA d ⟹ d A`, assumes `Closed_PA d`, extracts the
// matching closure clause, and applies it. NONE builds `⊢ ⟦A⟧`.
// ============================================================================

/// `⊢ Derivable_PA ⌜PAᵢ⌝` — the `i`-th PA axiom (1-based), as a pure
/// derivability witness.
pub fn derive_axiom(i: usize) -> Result<Thm> {
    if !(1..=6).contains(&i) {
        return Err(covalence_core::Error::ConnectiveRule(format!(
            "derive_axiom: axiom index {i} out of range 1..=6"
        )));
    }
    let closed_t = closed_poly()?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d
    let clause = nth_conjunct(assumed, i - 1, N_CLAUSES)?; // ⊢ d ⌜PAᵢ⌝
    let enc = sem::encode_form(&axioms()[i - 1]);
    debug_assert_eq!(clause.concl(), &d_at(&enc)?);
    clause
        .imp_intro(&closed_t)?
        .all_intro("d", d_ty())
}

/// `⊢ Derivable_PA ⌜A⌝ ⟹ Derivable_PA ⌜A ⟹ B⌝ ⟹ Derivable_PA ⌜B⌝` — reified
/// modus ponens. From derivations of `A` and `A ⟹ B`, derive `B`.
pub fn derive_mp(a: &Fol, b: &Fol) -> Result<Thm> {
    let enc_a = sem::encode_form(a);
    let enc_b = sem::encode_form(b);
    let imp_ab = sem::imp_cons(&sem::tty(), &sem::rty(), &enc_a, &enc_b);

    let closed_t = closed_poly()?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d

    // d ⌜A⌝ and d ⌜A⟹B⌝ from the two derivability hypotheses.
    let der_a = Thm::assume(derivable(&enc_a)?)?;
    let da = der_a.all_elim(d_var())?.imp_elim(assumed.clone())?; // ⊢ d ⌜A⌝
    let der_ab = Thm::assume(derivable(&imp_ab)?)?;
    let dab = der_ab.all_elim(d_var())?.imp_elim(assumed.clone())?; // ⊢ d ⌜A⟹B⌝

    // The MP conjunct is clause 7 (index 6).
    let mp_clause = nth_conjunct(assumed, 6, N_CLAUSES)?; // ⊢ ∀A B. (d A ∧ d⌜A⟹B⌝)⟹ d B
    let mp_inst = mp_clause.all_elim(enc_b.clone())?.all_elim(enc_a.clone())?;
    let db = mp_inst.imp_elim(da.and_intro(dab)?)?; // ⊢ d ⌜B⌝

    let der_b = db
        .imp_intro(&closed_t)?
        .all_intro("d", d_ty())?; // {Der A, Der (A⟹B)} ⊢ Derivable_PA ⌜B⌝
    der_b
        .imp_intro(&derivable(&imp_ab)?)?
        .imp_intro(&derivable(&enc_a)?)
}

// ============================================================================
// The internalized soundness theorem (proved ONCE) + one-step projection
// ============================================================================

/// `⊢ Derivable_PA A ⟹ ⟦A⟧` for an arbitrary encoded formula `A` (free
/// `A : Φ_sem`). Proved by rule induction: `inst d := ⟦·⟧` and discharge
/// `Closed_PA ⟦·⟧` clause by clause. See the [module docs](self).
pub fn soundness() -> Result<Thm> {
    soundness_at(&Term::free("A", phi()))
}

/// Soundness for a *specific* encoded formula `a` (at `Φ_sem⟨'t,'r⟩` or already
/// standard): `⊢ Derivable_PA ⌜a⌝ ⟹ ⟦a⌝`.
pub fn soundness_at(a: &Term) -> Result<Thm> {
    let d_pred = sem::denote_pred(); // λA. ⟦A⟧  at Φ_sem⟨nat,bool⟩

    let a_std = inst_std(a);
    let deriv_std = inst_std(&derivable(a)?); // Derivable_PA a at 't:=nat,'r:=bool
    let assumed = Thm::assume(deriv_std.clone())?; // {Der a} ⊢ Der a
    let specialized = assumed.all_elim(d_pred.clone())?; // ⊢ Closed ⟦·⟧ ⟹ ⟦·⟧ a (under hyp)

    let closed_d = discharge_closed(&d_pred)?; // ⊢ Closed_PA ⟦·⟧
    let d_a = specialized.imp_elim(closed_d)?; // {Der a} ⊢ ⟦·⟧ a

    // ⟦·⟧ a β-reduces to ⟦a⟧.
    let d_app = d_pred.apply(a_std.clone())?;
    let beta = Thm::beta_conv(d_app)?; // ⊢ ⟦·⟧ a = ⟦a⟧
    let den_a = beta.eq_mp(d_a)?; // {Der a} ⊢ ⟦a⟧

    den_a.imp_intro(&deriv_std)
}

/// **Project** a finished pure-PA derivation to its HOL theorem in **one step**:
/// `⊢ Derivable_PA ⌜A⌝ ↦ ⊢ ⟦A⟧`. This is *just* [`soundness_at`] applied to the
/// derivation (a single `imp_elim`, no re-derivation) followed by β-normalising
/// the denotation fold to its `nat`/`bool` standard-model form — so the result
/// is the ordinary HOL fact (e.g. `∀x. 0+x=x`), not the Church redex. `der` must
/// be a hypothesis-free `⊢ Derivable_PA ⌜A⌝` (from the derivation constructors).
pub fn project(form: &Fol, der: Thm) -> Result<Thm> {
    let enc = sem::encode_form(form);
    let snd = soundness_at(&enc)?; // ⊢ Derivable_PA ⌜A⌝ ⟹ ⟦A⟧  (standard instance)
    let der_std = der.inst_tfree("t", nat_ty())?.inst_tfree("r", bool_ty())?;
    let denoted = snd.imp_elim(der_std)?; // ⊢ ⟦A⟧  (a Church-fold redex)
    // β-normalise the fold to the standard-model form.
    let to_nf = crate::init::eq::beta_nf(denoted.concl().clone()); // ⊢ ⟦A⟧ = nf
    to_nf.eq_mp(denoted)
}

/// Discharge `⊢ Closed_PA ⟦·⟧` for `d := ⟦·⟧` ([`sem::denote_pred`]) clause by
/// clause: axioms from [`crate::init::nat`], MP from `bool`, induction from
/// [`Thm::nat_induct`].
fn discharge_closed(d_pred: &Term) -> Result<Thm> {
    let n = nat_ty();
    let b = bool_ty();
    let mut clause_thms: Vec<Thm> = Vec::new();

    // 1..6 — axiom clauses `⟦·⟧ ⌜PAᵢ⌝`, from the proven nat theorems.
    for (idx, ax) in axioms().iter().enumerate() {
        let enc = sem::encode_form_at(ax, &n, &b); // ⌜PAᵢ⌝ at standard instance
        let nat_thm = axiom_nat_thm(idx + 1)?; // ⊢ ⟦PAᵢ⟧
        let clause = expand_to_pred(nat_thm, &enc, d_pred)?; // ⊢ ⟦·⟧ ⌜PAᵢ⌝
        clause_thms.push(clause);
    }

    // 7 — MP clause.
    clause_thms.push(discharge_mp(d_pred)?);

    // 8 — induction clause.
    clause_thms.push(discharge_induct(d_pred)?);

    // 9 — specialisation clause.
    clause_thms.push(discharge_specialize(d_pred)?);

    // 10 — Leibniz clause.
    clause_thms.push(discharge_leibniz(d_pred)?);

    // 11 — generalisation clause.
    clause_thms.push(discharge_generalize(d_pred)?);

    // Conjoin right-nested.
    let mut iter = clause_thms.into_iter().rev();
    let mut acc = iter.next().expect("clauses");
    for cl in iter {
        acc = cl.and_intro(acc)?;
    }
    Ok(acc)
}

/// Given `⊢ ⟦enc⟧` and the encoded `enc`, produce `⊢ ⟦·⟧ ⌜enc⌝` by β-expanding
/// `⟦enc⟧` to `(λA. ⟦A⟧) enc`.
fn expand_to_pred(den_thm: Thm, enc: &Term, d_pred: &Term) -> Result<Thm> {
    let app = d_pred.clone().apply(enc.clone())?; // (λA. ⟦A⟧) enc
    let beta = Thm::beta_conv(app)?; // ⊢ ⟦·⟧ ⌜enc⌝ = ⟦enc⟧
    // den_thm is ⊢ ⟦enc⟧; but ⟦enc⟧ from beta may differ from den_thm by β —
    // bridge through normalisation.
    let denoted = beta.concl().as_eq().expect("beta eq").1.clone();
    let bridged = bridge_eq(den_thm, &denoted)?; // ⊢ ⟦enc⟧ (in beta's RHS shape)
    beta.sym()?.eq_mp(bridged)
}

/// Bridge `Γ ⊢ p` to `Γ ⊢ p'` when `p` and `p'` β-normalise to the same term.
fn bridge_eq(thm: Thm, target: &Term) -> Result<Thm> {
    if thm.concl() == target {
        return Ok(thm);
    }
    let from_nf = crate::init::eq::beta_nf(thm.concl().clone());
    let to_nf = crate::init::eq::beta_nf(target.clone());
    let eq = from_nf.trans(to_nf.sym()?)?; // ⊢ p = p'
    eq.eq_mp(thm)
}

/// Discharge the MP closure clause for `d := ⟦·⟧`:
/// `⊢ ∀A B. ⟦·⟧ A ∧ ⟦·⟧ ⌜A⟹B⌝ ⟹ ⟦·⟧ B`.
fn discharge_mp(d_pred: &Term) -> Result<Thm> {
    let a = Term::free("A", phi_std());
    let b = Term::free("B", phi_std());
    let imp_ab = sem::imp_cons(&nat_ty(), &bool_ty(), &a, &b);

    // Full β-bridges `⊢ ⟦·⟧⌜…⌝ = nf` + the normal form, for each of the three.
    let br = |enc: Term| -> Result<(Thm, Term)> {
        let beta = Thm::beta_conv(d_pred.clone().apply(enc)?)?; // ⊢ ⟦·⟧⌜…⌝ = ⟦…⟧
        let denoted = beta.concl().as_eq().expect("eq").1.clone();
        let to_nf = crate::init::eq::beta_nf(denoted);
        let nf = to_nf.concl().as_eq().expect("eq").1.clone();
        Ok((beta.trans(to_nf)?, nf)) // ⊢ ⟦·⟧⌜…⌝ = nf
    };
    let (br_a, den_a) = br(a.clone())?; // nf = ⟦A⟧
    let (br_ab, den_ab) = br(imp_ab.clone())?; // nf = (⟦A⟧ ⟹ ⟦B⟧)
    let (br_b, _den_b) = br(b.clone())?; // nf = ⟦B⟧

    // The implication's consequent, read off `den_ab = (⟦A⟧ ⟹ ⟦B⟧)`, is the
    // *same* `⟦B⟧` we must rewrite back — take it from there so the final
    // `br_b.sym()` rewrite matches syntactically.
    let den_b = parse_imp_consequent(&den_ab)?;

    // Goal at the denotation level: (⟦A⟧ ∧ (⟦A⟧⟹⟦B⟧)) ⟹ ⟦B⟧ — ordinary MP.
    let h = den_a.clone().and(den_ab.clone())?;
    let assumed = Thm::assume(h.clone())?;
    let h_a = assumed.clone().and_elim_l()?; // ⊢ ⟦A⟧
    let h_ab = assumed.and_elim_r()?; // ⊢ ⟦A⟧⟹⟦B⟧
    let h_b = h_ab.imp_elim(h_a)?; // ⊢ ⟦B⟧
    debug_assert_eq!(h_b.concl(), &den_b);
    let mp_den = h_b.imp_intro(&h)?; // ⊢ (⟦A⟧ ∧ (⟦A⟧⟹⟦B⟧)) ⟹ ⟦B⟧

    // β-expand the three denotations back to ⟦·⟧-applications. Rewrite the
    // *implication* `⟦A⟧⟹⟦B⟧ → ⟦·⟧⌜A⟹B⌝` FIRST (it contains `⟦A⟧`/`⟦B⟧` as
    // sub-terms; rewriting them first would destroy its LHS), then the
    // standalone `⟦A⟧` (antecedent of the conjunction) and `⟦B⟧` (consequent).
    let clause = mp_den
        .rewrite(&br_ab.sym()?)?
        .rewrite(&br_a.sym()?)?
        .rewrite(&br_b.sym()?)?; // ⊢ (⟦·⟧A ∧ ⟦·⟧⌜A⟹B⌝) ⟹ ⟦·⟧B

    clause.all_intro("A", phi_std())?.all_intro("B", phi_std())
}

/// Read the consequent `B` off an implication term `A ⟹ B`.
fn parse_imp_consequent(imp: &Term) -> Result<Term> {
    let nae = || covalence_core::Error::NotAnEquation;
    let (head, conseq) = imp.as_app().ok_or_else(nae)?; // (imp A, B)
    let _ = head;
    Ok(conseq.clone())
}

/// Discharge the induction closure clause for `d := ⟦·⟧`:
/// `⊢ ∀Q:nat→bool. ⟦·⟧⌜Q 0⌝ ⟹ (∀x. ⟦·⟧⌜Q x⌝ ⟹ ⟦·⟧⌜Q(Sx)⌝) ⟹ ⟦·⟧⌜∀x. Q x⌝`,
/// which after β-reducing is exactly [`Thm::nat_induct`].
fn discharge_induct(d_pred: &Term) -> Result<Thm> {
    let n = nat_ty();
    let b = bool_ty();
    let q_ty = Type::fun(n.clone(), b.clone());
    let q = Term::free("Q", q_ty.clone());
    let x = Term::free("x", n.clone());

    let (br_base, _q0) = br_pred(d_pred, sem::q_at_zero(&n, &b, &q))?; // nf = Q 0
    let (br_qx, qx) = br_pred(d_pred, sem::q_at(&n, &b, &q, x.clone()))?; // nf = Q x
    let (br_qsx, qsx) = br_pred(d_pred, sem::q_at_succ(&n, &b, &q, x.clone()))?; // nf = Q (Sx)
    let (br_all, qall) = br_pred(d_pred, sem::all_cons(&n, &b, q.clone()))?; // nf = ∀x. Q x

    // The meta-step premise `∀x. ⟦·⟧⌜Qx⌝ ⟹ ⟦·⟧⌜Q(Sx)⌝`: assume it, specialise,
    // rewrite each `⟦·⟧⌜·⌝` to `Q·` to feed `nat_induct`.
    let pred_qx = br_qx.concl().as_eq().expect("eq").0.clone(); // ⟦·⟧⌜Q x⌝
    let pred_qsx = br_qsx.concl().as_eq().expect("eq").0.clone(); // ⟦·⟧⌜Q (Sx)⌝
    let step_premise = pred_qx.clone().imp(pred_qsx.clone())?.forall("x", n.clone())?;
    let step_assumed = Thm::assume(step_premise.clone())?; // {step} ⊢ ∀x. ⟦·⟧⌜Qx⌝⟹⟦·⟧⌜Q(Sx)⌝
    let step_x_pred = step_assumed.all_elim(x.clone())?; // {step} ⊢ ⟦·⟧⌜Qx⌝ ⟹ ⟦·⟧⌜Q(Sx)⌝
    let step_x = step_x_pred.rewrite(&br_qx)?.rewrite(&br_qsx)?; // {step} ⊢ Q x ⟹ Q (Sx)
    debug_assert_eq!(step_x.concl(), &qx.clone().imp(qsx.clone())?);

    // base: ⊢ Q 0 (rewrite the assumed ⟦·⟧⌜Q0⌝ to Q 0).
    let base_pred = br_base.concl().as_eq().expect("eq").0.clone(); // ⟦·⟧⌜Q 0⌝
    let base_assumed = Thm::assume(base_pred.clone())?; // {base} ⊢ ⟦·⟧⌜Q0⌝
    let base_h = br_base.clone().eq_mp(base_assumed)?; // {base} ⊢ Q 0

    let induct = Thm::nat_induct(base_h, step_x)?; // {base, step} ⊢ ∀x. Q x
    debug_assert_eq!(induct.concl(), &qall);
    let concl = br_all.sym()?.eq_mp(induct)?; // {base, step} ⊢ ⟦·⟧⌜∀x. Q x⌝

    // Discharge step then base premises (in clause order: base outer, step inner).
    let with_step = concl.imp_intro(&step_premise)?; // {base} ⊢ step ⟹ ⟦·⟧⌜∀x.Qx⌝
    let clause = with_step.imp_intro(&base_pred)?; // ⊢ ⟦·⟧⌜Q0⌝ ⟹ step ⟹ ⟦·⟧⌜∀x.Qx⌝
    clause.all_intro("Q", q_ty)
}

/// Discharge the specialisation closure clause for `d := ⟦·⟧`:
/// `⊢ ∀Q:nat→bool. ∀w:nat. ⟦·⟧⌜∀x. Q x⌝ ⟹ ⟦·⟧⌜Q w⌝`, which after β is
/// exactly `Thm::all_elim` (∀-elimination on `nat`).
fn discharge_specialize(d_pred: &Term) -> Result<Thm> {
    let n = nat_ty();
    let b = bool_ty();
    let q_ty = Type::fun(n.clone(), b.clone());
    let q = Term::free("Q", q_ty.clone());
    let w = Term::free("w", n.clone());

    let br = |enc: Term| -> Result<(Thm, Term)> {
        let beta = Thm::beta_conv(d_pred.clone().apply(enc)?)?;
        let denoted = beta.concl().as_eq().expect("eq").1.clone();
        let to_nf = crate::init::eq::beta_nf(denoted);
        let nf = to_nf.concl().as_eq().expect("eq").1.clone();
        Ok((beta.trans(to_nf)?, nf))
    };
    let (br_univ, univ_nf) = br(sem::all_cons(&n, &b, q.clone()))?; // nf = ∀x. Q x
    let (br_inst, inst_nf) = br(sem::q_at(&n, &b, &q, w.clone()))?; // nf = Q w

    // ∀x. Q x ⊢ Q w  by all_elim at w; then discharge.
    let assumed = Thm::assume(univ_nf.clone())?; // {∀x.Qx} ⊢ ∀x. Q x
    let inst = assumed.all_elim(w.clone())?; // {∀x.Qx} ⊢ Q w
    debug_assert_eq!(inst.concl(), &inst_nf);
    let imp = inst.imp_intro(&univ_nf)?; // ⊢ (∀x. Q x) ⟹ Q w

    let clause = imp.rewrite(&br_inst.sym()?)?.rewrite(&br_univ.sym()?)?;
    clause.all_intro("w", n).and_then(|t| t.all_intro("Q", q_ty))
}

/// β-bridge helper for the discharge functions: `⊢ ⟦·⟧⌜enc⌝ = nf` + the `nf`.
fn br_pred(d_pred: &Term, enc: Term) -> Result<(Thm, Term)> {
    let beta = Thm::beta_conv(d_pred.clone().apply(enc)?)?;
    let denoted = beta.concl().as_eq().expect("eq").1.clone();
    let to_nf = crate::init::eq::beta_nf(denoted);
    let nf = to_nf.concl().as_eq().expect("eq").1.clone();
    Ok((beta.trans(to_nf)?, nf))
}

/// Discharge the Leibniz closure clause for `d := ⟦·⟧`:
/// `⊢ ∀a b:nat. ∀P:nat→bool. ⟦·⟧⌜a=b⌝ ⟹ ⟦·⟧⌜P a⌝ ⟹ ⟦·⟧⌜P b⌝`, which after β
/// is substitutivity of equality (`eq_mp` through the congruence `P a = P b`).
fn discharge_leibniz(d_pred: &Term) -> Result<Thm> {
    let n = nat_ty();
    let b = bool_ty();
    let p_ty = Type::fun(n.clone(), b.clone());
    let a = Term::free("a", n.clone());
    let bb = Term::free("b", n.clone());
    let p = Term::free("P", p_ty.clone());

    let (br_eq, eq_nf) = br_pred(d_pred, sem::eq_cons(&n, &b, a.clone(), bb.clone()))?; // a=b
    let (br_pa, pa_nf) = br_pred(d_pred, sem::q_at(&n, &b, &p, a.clone()))?; // P a
    let (br_pb, _pb_nf) = br_pred(d_pred, sem::q_at(&n, &b, &p, bb.clone()))?; // P b

    // a=b, P a ⊢ P b   (cong on P then eq_mp).
    let eq_h = Thm::assume(eq_nf.clone())?; // {a=b} ⊢ a = b
    let pa_h = Thm::assume(pa_nf.clone())?; // {P a} ⊢ P a
    let cong = eq_h.cong_arg(p.clone())?; // {a=b} ⊢ P a = P b
    let pb = cong.eq_mp(pa_h)?; // {a=b, P a} ⊢ P b
    let imp = pb.imp_intro(&pa_nf)?.imp_intro(&eq_nf)?; // ⊢ (a=b) ⟹ (P a) ⟹ (P b)

    let clause = imp
        .rewrite(&br_eq.sym()?)?
        .rewrite(&br_pa.sym()?)?
        .rewrite(&br_pb.sym()?)?;
    clause
        .all_intro("P", p_ty)?
        .all_intro("b", n.clone())?
        .all_intro("a", n)
}

/// Discharge the generalisation closure clause for `d := ⟦·⟧`:
/// `⊢ ∀Q:nat→bool. (∀x. ⟦·⟧⌜Q x⌝) ⟹ ⟦·⟧⌜∀x. Q x⌝`, which after β is
/// `Thm::all_intro` (∀-introduction on `nat`).
fn discharge_generalize(d_pred: &Term) -> Result<Thm> {
    let n = nat_ty();
    let b = bool_ty();
    let q_ty = Type::fun(n.clone(), b.clone());
    let q = Term::free("Q", q_ty.clone());
    let x = Term::free("x", n.clone());

    let (br_qx, _qx_nf) = br_pred(d_pred, sem::q_at(&n, &b, &q, x.clone()))?; // ⟦·⟧⌜Qx⌝ = Q x
    let (br_all, all_nf) = br_pred(d_pred, sem::all_cons(&n, &b, q.clone()))?; // ∀x. Q x

    // The clause's premise is `∀x. ⟦·⟧⌜Q x⌝`; assume it and rewrite each body
    // `⟦·⟧⌜Q x⌝ → Q x` to reach `∀x. Q x` (= the conclusion's denotation), then
    // rewrite that to the conclusion `⟦·⟧⌜∀x. Q x⌝`. (Premise and conclusion are
    // distinct *before* the β-rewrites, so no aliasing.)
    let pred_qx = br_qx.concl().as_eq().expect("eq").0.clone(); // ⟦·⟧⌜Q x⌝
    let premise = pred_qx.forall("x", n.clone())?; // ∀x. ⟦·⟧⌜Q x⌝
    let assumed = Thm::assume(premise.clone())?; // {prem} ⊢ ∀x. ⟦·⟧⌜Q x⌝
    let at_x = assumed.all_elim(x.clone())?; // {prem} ⊢ ⟦·⟧⌜Q x⌝
    let qx = br_qx.clone().eq_mp(at_x)?; // {prem} ⊢ Q x
    let all_qx = qx.all_intro("x", n.clone())?; // {prem} ⊢ ∀x. Q x
    debug_assert_eq!(all_qx.concl(), &all_nf);
    let concl = br_all.sym()?.eq_mp(all_qx)?; // {prem} ⊢ ⟦·⟧⌜∀x. Q x⌝
    let imp = concl.imp_intro(&premise)?; // ⊢ (∀x. ⟦·⟧⌜Q x⌝) ⟹ ⟦·⟧⌜∀x. Q x⌝
    imp.all_intro("Q", q_ty)
}

// ============================================================================
// The old lock-step path (secondary convenience) — a `Fol` + its `Thm`,
// built together. NOT the primary structure; NOT the acceptance-test path.
// ============================================================================

/// A **lock-step PA derivation**: a reified PA formula together with a genuine
/// HOL theorem of its denotation. Kept as a convenience for directly obtaining
/// HOL facts; the *proper* deep-embedding path is [`derive_axiom`] etc. + the
/// one-step [`project`].
#[derive(Clone, Debug)]
pub struct LockstepDerivation {
    /// The reified PA formula.
    pub formula: Fol,
    /// `⊢ ⟦formula⟧`.
    pub thm: Thm,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "derivation is hypothesis-free");
        assert!(thm.has_no_obs(), "derivation is oracle-free");
    }

    /// A derivation's conclusion must be a `Derivable_PA ⌜form⌝` value (at the
    /// standard instance) — pure syntactic data — and **never** the denotation
    /// `⟦form⟧` (which `project` produces only at the very end). This witnesses
    /// "the derivation builds no HOL theorem".
    fn assert_is_derivable_not_denotation(thm: &Thm, form: &Fol) {
        // The constructors build `Derivable_PA ⌜A⌝` at the polymorphic carrier.
        let want = derivable(&sem::encode_form(form)).unwrap();
        assert_eq!(
            thm.concl(),
            &want,
            "derivation must be `Derivable_PA ⌜A⌝`, not `⟦A⟧`"
        );
        // Sanity: the denotation `⟦form⟧` is a *different* term, so the
        // derivation genuinely did not build it.
        let denotation = super::super::deep::denote_closed(form);
        assert_ne!(thm.concl(), &denotation, "derivation must not be ⟦A⟧");
    }

    /// Each PA axiom's derivability witness `⊢ Derivable_PA ⌜PAᵢ⌝` is genuine
    /// and carries NO `⟦PAᵢ⟧` theorem.
    #[test]
    fn axioms_are_derivable() {
        for i in 1..=6 {
            let der = derive_axiom(i).unwrap();
            assert_genuine(&der);
            // The derivation IS a `Derivable_PA ⌜PAᵢ⌝` value, NOT a `⟦PAᵢ⟧` HOL
            // theorem — it carries no denotation.
            assert_is_derivable_not_denotation(&der, &axioms()[i - 1]);
        }
    }

    /// Reified modus ponens `derive_mp` is genuine and projects soundly: from
    /// `Derivable_PA ⌜A⌝` and `Derivable_PA ⌜A ⟹ B⌝`, the combinator yields
    /// `Derivable_PA ⌜B⌝` (a pure derivability witness).
    #[test]
    fn mp_is_genuine() {
        // A := (0 = 0), B := (S0 = S0)  (concrete closed formulas).
        let a = Fol::Eq(Box::new(Fol::Zero), Box::new(Fol::Zero));
        let b = Fol::Eq(
            Box::new(Fol::Succ(Box::new(Fol::Zero))),
            Box::new(Fol::Succ(Box::new(Fol::Zero))),
        );
        let mp = derive_mp(&a, &b).unwrap();
        assert_genuine(&mp);
        // Shape: Der ⌜A⌝ ⟹ Der ⌜A⟹B⌝ ⟹ Der ⌜B⌝.
        let enc_a = sem::encode_form(&a);
        let enc_b = sem::encode_form(&b);
        let imp_ab = sem::imp_cons(&sem::tty(), &sem::rty(), &enc_a, &enc_b);
        let expected = derivable(&enc_a)
            .unwrap()
            .imp(
                derivable(&imp_ab)
                    .unwrap()
                    .imp(derivable(&enc_b).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(mp.concl(), &expected);
    }

    /// Soundness is a single genuine theorem of the right shape.
    #[test]
    fn soundness_is_genuine() {
        let thm = soundness().unwrap();
        assert_genuine(&thm);
    }

    /// **One-step projection.** Derive PA3 (`∀x. 0+x=x`) as a *pure* derivability
    /// witness (no HOL thm), then `project` in a single move to `⊢ ⟦PA3⟧`, which
    /// must equal `init::nat`'s independently-proved `add_base`.
    #[test]
    fn project_axiom_in_one_step() {
        let der = derive_axiom(3).unwrap(); // ⊢ Derivable_PA ⌜∀x. 0+x=x⌝  (pure data)
        // The derivation's conclusion is `Derivable_PA …`, NOT `⟦…⟧`.
        assert!(format!("{}", der.concl()).contains("bool.forall")); // it is the Derivable_PA term
        let projected = project(&ax_add_base(), der).unwrap(); // ⊢ ⟦∀x. 0+x=x⟧
        assert_genuine(&projected);
        assert_eq!(projected.concl(), nat::add_base().concl());
    }


    /// The `Closed_PA ⟦·⟧` the soundness proof discharges must match — clause by
    /// clause — the `Closed[d := ⟦·⟧]` the impredicative definition unfolds to
    /// (the invariant that makes `soundness`'s `imp_elim` typecheck).
    #[test]
    fn discharge_closed_matches_definition_clausewise() {
        let d_pred = sem::denote_pred();
        let expected =
            closed(&|f| d_pred.clone().apply(f.clone()), &nat_ty(), &bool_ty()).unwrap();
        let got = discharge_closed(&d_pred).unwrap().concl().clone();
        let split = |t: &Term| -> Vec<Term> {
            let mut out = Vec::new();
            let mut cur = t.clone();
            loop {
                if let Some((head, rhs)) = cur.as_app()
                    && let Some((and_op, lhs)) = head.as_app()
                    && format!("{and_op}").contains("bool.and")
                {
                    out.push(lhs.clone());
                    cur = rhs.clone();
                    continue;
                }
                out.push(cur);
                break;
            }
            out
        };
        let exp = split(&expected);
        let g = split(&got);
        assert_eq!(exp.len(), g.len(), "clause count");
        for (i, (e, gg)) in exp.iter().zip(g.iter()).enumerate() {
            assert_eq!(e, gg, "clause {i} mismatch");
        }
    }
}
