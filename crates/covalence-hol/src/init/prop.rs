//! The **first internal object logic**: propositional logic reified as
//! data *inside* HOL, with a soundness theorem proved by the metatheory
//! itself (`docs/metatheory.md` §8).
//!
//! This is the smallest end-to-end instance of "metatheory is the default
//! mode": an object language whose formulas are HOL data, whose
//! derivability is an ordinary HOL predicate, and whose denotation lands
//! back in HOL's own `bool` — with `⊢ Derivable_Prop A ⟹ ⟦A⟧` an honest
//! HOL theorem, proved with no new kernel TCB.
//!
//! ## Why a Church / impredicative encoding (the design choice)
//!
//! The generic recursion engine ([`crate::init::inductive`]) builds a
//! recursor + induction principle for a *carved kernel subtype* — the
//! heavyweight path `nat` takes. We deliberately do **not** use it here.
//! Two reasons:
//!
//! 1. **It is not needed for soundness.** Soundness is an induction over
//!    *derivations*, discharged case-by-case by the kernel's existing
//!    connective rules. An impredicative ("Church") encoding turns that
//!    induction into a single `inst` of a higher-order predicate variable —
//!    no recursor, no freeness proofs, no new type definition.
//! 2. **It stays rank-1 and TCB-free.** A formula is encoded as a
//!    polymorphic HOL term over a *free* result type variable `'r`; the
//!    denotation is recovered by `inst_tfree 'r := bool`. Nothing is added
//!    to `covalence-core` — the whole development rides on existing kernel
//!    primitives (`forall`/`imp`/`inst`/`beta`/the connective rules).
//!
//! Genuine reified syntax survives this choice: `enc(var 0)` and
//! `enc(pand (var 0) (var 0))` are *distinct HOL terms*, so formulas are
//! data, not their own meanings (this is not a shallow embedding).
//!
//! ## The encodings
//!
//! A propositional formula is encoded at a fresh result type `'r`:
//!
//! ```text
//!   Φ⟨'r⟩  :=  (nat → 'r)            -- var
//!            → ('r → 'r)            -- ¬
//!            → ('r → 'r → 'r)       -- ∧
//!            → ('r → 'r → 'r)       -- ∨
//!            → ('r → 'r → 'r)       -- ⟹
//!            → 'r
//! ```
//!
//! with constructors `var n`, `pneg A`, `pand A B`, `por A B`, `pimp A B`
//! the obvious folds. The **denotation** under a valuation `v : nat → bool`
//! instantiates `'r := bool` and feeds the real boolean operations:
//!
//! ```text
//!   ⟦A⟧ v  :=  A[bool] v (λp. ¬p) (∧) (∨) (⟹)
//! ```
//!
//! S-expressions ([`sexpr`](crate::init::sexpr)) are reified the same way
//! (atom/nil/cons), as
//! the universal syntax carrier the metatheory doc calls for; propositional
//! variables are `nat` indices (the simplest choice — no atom plumbing just
//! to name a variable).
//!
//! ## Derivability: a Hilbert system
//!
//! We pick a **Hilbert system** over `{¬, ∧, ∨, ⟹}` because it makes
//! soundness trivial: every axiom *schema instance denotes a propositional
//! tautology* (dischargeable by the complete propositional decision
//! procedure [`prop_eq`](crate::init::logic::prop_eq) against `T`) and the
//! single rule (modus ponens) is just [`Thm::imp_elim`] on the denotations.
//! `Derivable_Prop` is the impredicative "smallest predicate closed under
//! the axioms and MP":
//!
//! ```text
//!   Derivable_Prop A  :=  ∀d:Φ→bool. Closed d ⟹ d A
//! ```
//!
//! so **induction over derivations is `inst d := ⟦·⟧ v`** and the
//! `Closed`-premise obligations are exactly "the axioms are true" + "MP
//! preserves truth".
//!
//! ## What is proved
//!
//! [`soundness`] — `⊢ ∀v. Derivable_Prop A ⟹ ⟦A⟧ v` for an arbitrary
//! encoded formula `A` (a free variable of type `Φ⟨bool⟩`; the proof runs
//! at the `'r := bool` instance, the only one the denotation needs).
//! Specializing `A` to a concrete encoding ([`soundness_at`]) gives e.g.
//! `⊢ Derivable_Prop ⌜p ⟹ p⌝ ⟹ ⟦p ⟹ p⟧`.
//!
//! Everything here is genuine: hypothesis-free and oracle-free.

use covalence_core::{Result, Term, Thm, Type};

use crate::init::eq::beta_nf;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{prop_eq, truth};

// ============================================================================
// Result type variable and the formula carrier `Φ⟨'r⟩`
// ============================================================================

/// The fresh result type variable `'r` formulas fold into.
fn rty() -> Type {
    Type::tfree("r")
}

fn nat() -> Type {
    Type::nat()
}

fn bool_ty() -> Type {
    Type::bool()
}

/// The five handler binder names + slot-type builders, in fold order
/// `var ¬ ∧ ∨ ⟹`, each parametric in the result type `r`.
const HANDLERS: [(&str, fn(&Type) -> Type); 5] = [
    ("var", var_h_ty),
    ("neg", un_h_ty),
    ("and", bin_h_ty),
    ("or", bin_h_ty),
    ("imp", bin_h_ty),
];

/// `nat → r` — the `var` handler slot.
fn var_h_ty(r: &Type) -> Type {
    Type::fun(nat(), r.clone())
}

/// `r → r` — the unary (`¬`) handler slot.
fn un_h_ty(r: &Type) -> Type {
    Type::fun(r.clone(), r.clone())
}

/// `r → r → r` — a binary (`∧`/`∨`/`⟹`) handler slot.
fn bin_h_ty(r: &Type) -> Type {
    Type::fun(r.clone(), Type::fun(r.clone(), r.clone()))
}

/// `Φ⟨r⟩ = (nat→r)→(r→r)→(r→r→r)→(r→r→r)→(r→r→r)→r`,
/// the type of an encoded propositional formula at result type `r`.
fn phi_at(r: &Type) -> Type {
    let mut t = r.clone();
    for slot in [
        bin_h_ty(r),
        bin_h_ty(r),
        bin_h_ty(r),
        un_h_ty(r),
        var_h_ty(r),
    ] {
        t = Type::fun(slot, t);
    }
    t
}

/// `Φ⟨'r⟩` — the canonical polymorphic carrier (result type the free
/// type variable `'r`).
fn phi() -> Type {
    phi_at(&rty())
}

/// `Φ` with `'r := bool`.
fn phi_at_bool() -> Type {
    phi_at(&bool_ty())
}

/// `λvar neg and or imp. body` — wrap a fold `body : r` in the five
/// handler abstractions, yielding a `Φ⟨r⟩` value.
fn close_handlers(r: &Type, body: Term) -> Term {
    // Innermost binder is `imp` (last), outermost is `var` (first).
    let mut t = body;
    for (name, ty) in HANDLERS.iter().rev() {
        t = Term::abs(ty(r), covalence_core::subst::close(&t, name));
    }
    t
}

/// A free handler variable by name, at result type `r`.
fn handler(r: &Type, name: &str) -> Term {
    let ty = HANDLERS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, t)| t(r))
        .expect("handler name");
    Term::free(name, ty)
}

/// Apply an encoded formula `enc : Φ⟨r⟩` to the five handlers, producing
/// its fold `: r`. The inverse of [`close_handlers`] up to β.
fn apply_handlers(r: &Type, enc: Term) -> Term {
    let mut t = enc;
    for (name, _) in HANDLERS {
        t = Term::app(t, handler(r, name));
    }
    t
}

// ============================================================================
// Formula constructors (encoding `⌜·⌝`)
//
// Each builds at result type `r`; the public `p_*` builders default to
// the polymorphic `'r`. Soundness instantiates `r := bool` so the
// denotation typechecks — to keep the encoded sub-formulas and the
// `bool` folds in agreement, the bool-level discharge re-builds with the
// `*_at` forms at `r := bool`.
// ============================================================================

/// `enc(var n) : Φ⟨r⟩`.
pub fn p_var_at(r: &Type, n: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "var"), n))
}

/// `enc(¬A) : Φ⟨r⟩`.
pub fn p_neg_at(r: &Type, a: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "neg"), apply_handlers(r, a)))
}

fn p_bin_at(r: &Type, op: &str, a: Term, b: Term) -> Term {
    let body = Term::app(
        Term::app(handler(r, op), apply_handlers(r, a)),
        apply_handlers(r, b),
    );
    close_handlers(r, body)
}

/// `enc(A ∧ B) : Φ⟨r⟩`.
pub fn p_and_at(r: &Type, a: Term, b: Term) -> Term {
    p_bin_at(r, "and", a, b)
}

/// `enc(A ∨ B) : Φ⟨r⟩`.
pub fn p_or_at(r: &Type, a: Term, b: Term) -> Term {
    p_bin_at(r, "or", a, b)
}

/// `enc(A ⟹ B) : Φ⟨r⟩`.
pub fn p_imp_at(r: &Type, a: Term, b: Term) -> Term {
    p_bin_at(r, "imp", a, b)
}

/// `enc(var n) : Φ⟨'r⟩` — a propositional variable, indexed by `n : nat`.
pub fn p_var(n: Term) -> Term {
    p_var_at(&rty(), n)
}

/// `enc(var k)` for a literal index `k`.
pub fn p_var_lit(k: u32) -> Term {
    p_var(Term::nat_lit(covalence_types::Nat::from_inner(k.into())))
}

/// `enc(¬A)`.
pub fn p_neg(a: Term) -> Term {
    p_neg_at(&rty(), a)
}

/// `enc(A ∧ B)`.
pub fn p_and(a: Term, b: Term) -> Term {
    p_and_at(&rty(), a, b)
}

/// `enc(A ∨ B)`.
pub fn p_or(a: Term, b: Term) -> Term {
    p_or_at(&rty(), a, b)
}

/// `enc(A ⟹ B)`.
pub fn p_imp(a: Term, b: Term) -> Term {
    p_imp_at(&rty(), a, b)
}

// ============================================================================
// Denotation `⟦·⟧`
// ============================================================================

/// The five concrete `bool` handlers, in fold order, for `⟦·⟧ v`:
/// `(v, λp.¬p, ∧, ∨, ⟹)`.
fn bool_handlers(v: &Term) -> Result<[Term; 5]> {
    let p = Term::free("p", bool_ty());
    let q = Term::free("q", bool_ty());

    // λp. ¬p
    let neg = Term::abs(bool_ty(), covalence_core::subst::close(&p.clone().not()?, "p"));
    // λp q. p ⊙ q  for ⊙ ∈ {∧, ∨, ⟹}
    let bin = |body: Term| -> Term {
        let inner = Term::abs(bool_ty(), covalence_core::subst::close(&body, "q"));
        Term::abs(bool_ty(), covalence_core::subst::close(&inner, "p"))
    };
    let and = bin(p.clone().and(q.clone())?);
    let or = bin(p.clone().or(q.clone())?);
    let imp = bin(p.clone().imp(q.clone())?);
    Ok([v.clone(), neg, and, or, imp])
}

/// `⟦A⟧ v : bool` — the denotation of encoded formula `A` under
/// valuation `v : nat → bool`. Instantiates the formula's result type to
/// `bool` and folds with the real boolean operations: the *term*
/// `A[bool] v (λp.¬p) (∧) (∨) (⟹)`. Accepts `A` at `Φ⟨'r⟩` or `Φ⟨bool⟩`.
pub fn denote(a: Term, v: &Term) -> Result<Term> {
    // The formula carrier `Φ⟨'r⟩` is polymorphic in `'r`; the denotation
    // lives at `'r := bool`. Instantiate the type variable on the *term*
    // before feeding it the boolean handlers (a no-op if `a` is already
    // at `bool`).
    let mut t = covalence_core::subst::subst_tfree_in_term(&a, "r", &bool_ty());
    for h in bool_handlers(v)? {
        t = t.apply(h)?;
    }
    Ok(t)
}

// ============================================================================
// Derivability — the impredicative Hilbert system
// ============================================================================

/// `d : Φ⟨'r⟩ → bool` — the impredicative predicate variable bound in
/// `Derivable_Prop`.
fn d_var() -> Term {
    Term::free("d", Type::fun(phi(), bool_ty()))
}

/// `d A` for the predicate variable `d` and an encoded formula `A`.
fn d_at(a: &Term) -> Result<Term> {
    d_var().apply(a.clone())
}

/// The **Hilbert axiom schemas** as constructors over encoded
/// sub-formulas `A`, `B`, `C`. We use the standard `{⟹, ∧, ∨, ¬}`
/// presentation (Kleene-style), every instance a propositional tautology:
///
/// 1. `A ⟹ (B ⟹ A)`
/// 2. `(A ⟹ (B ⟹ C)) ⟹ ((A ⟹ B) ⟹ (A ⟹ C))`
/// 3. `A ⟹ (B ⟹ A ∧ B)`
/// 4. `A ∧ B ⟹ A`
/// 5. `A ∧ B ⟹ B`
/// 6. `A ⟹ A ∨ B`
/// 7. `B ⟹ A ∨ B`
/// 8. `(A ⟹ C) ⟹ ((B ⟹ C) ⟹ (A ∨ B ⟹ C))`
/// 9. `(A ⟹ B) ⟹ ((A ⟹ ¬B) ⟹ ¬A)`
/// 10. `¬¬A ⟹ A`   (classical — its denotation is decided by `prop_eq`,
///     which is `Thm::lem`-powered)
///
/// Returns the encoded axiom formula for the given schema index `1..=10`
/// over fresh formula variables `A`,`B`,`C`.
fn axiom_schema(r: &Type, i: usize, a: &Term, b: &Term, c: &Term) -> Term {
    let imp = |x: Term, y: Term| p_imp_at(r, x, y);
    let and = |x: Term, y: Term| p_and_at(r, x, y);
    let or = |x: Term, y: Term| p_or_at(r, x, y);
    let neg = |x: Term| p_neg_at(r, x);
    match i {
        1 => imp(a.clone(), imp(b.clone(), a.clone())),
        2 => imp(
            imp(a.clone(), imp(b.clone(), c.clone())),
            imp(imp(a.clone(), b.clone()), imp(a.clone(), c.clone())),
        ),
        3 => imp(a.clone(), imp(b.clone(), and(a.clone(), b.clone()))),
        4 => imp(and(a.clone(), b.clone()), a.clone()),
        5 => imp(and(a.clone(), b.clone()), b.clone()),
        6 => imp(a.clone(), or(a.clone(), b.clone())),
        7 => imp(b.clone(), or(a.clone(), b.clone())),
        8 => imp(
            imp(a.clone(), c.clone()),
            imp(imp(b.clone(), c.clone()), imp(or(a.clone(), b.clone()), c.clone())),
        ),
        9 => imp(
            imp(a.clone(), b.clone()),
            imp(imp(a.clone(), neg(b.clone())), neg(a.clone())),
        ),
        10 => imp(neg(neg(a.clone())), a.clone()),
        _ => panic!("axiom_schema: index out of range 1..=10"),
    }
}

/// Number of Hilbert axiom schemas.
const N_AXIOMS: usize = 10;

/// The free formula variables `A`, `B`, `C` used to state the schemas /
/// the closure conditions.
fn fvar(name: &str) -> Term {
    Term::free(name, phi())
}

/// `Closed d` — the conjunction of closure conditions on `d`:
///
/// - one `∀A B C. d ⌜axiom_i A B C⌝` per axiom schema, and
/// - the MP clause `∀A B. d ⌜A⌝ ∧ d ⌜A ⟹ B⌝ ⟹ d ⌜B⌝`.
///
/// Returned as a single `bool` term (a right-nested conjunction).
fn closed(d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
    let a = fvar("A");
    let b = fvar("B");
    let c = fvar("C");

    let mut clauses: Vec<Term> = Vec::new();

    // Axiom clauses: ∀A B C. d ⌜axiom_i⌝
    for i in 1..=N_AXIOMS {
        let ax = axiom_schema(&rty(), i, &a, &b, &c);
        let body = d_apply(&ax)?
            .forall("A", phi())?
            .forall("B", phi())?
            .forall("C", phi())?;
        clauses.push(body);
    }

    // MP clause: ∀A B. (d A ∧ d (A ⟹ B)) ⟹ d B
    let mp = {
        let da = d_apply(&a)?;
        let dab = d_apply(&p_imp(a.clone(), b.clone()))?;
        let db = d_apply(&b)?;
        da.and(dab)?
            .imp(db)?
            .forall("A", phi())?
            .forall("B", phi())?
    };
    clauses.push(mp);

    // Right-nested conjunction of all clauses.
    let mut iter = clauses.into_iter().rev();
    let mut acc = iter.next().expect("at least one clause");
    for cl in iter {
        acc = cl.and(acc)?;
    }
    Ok(acc)
}

/// `Derivable_Prop A := ∀d. Closed d ⟹ d A` — the impredicative
/// derivability predicate over an encoded formula `A`.
pub fn derivable(a: &Term) -> Result<Term> {
    let closed_d = closed(&|f| d_at(f))?;
    let body = closed_d.imp(d_at(a)?)?;
    body.forall("d", Type::fun(phi(), bool_ty()))
}

// ============================================================================
// LCF-style derivation constructors (metatheory.md §4)
//
// The *only* way to obtain `⊢ Derivable_Prop ⌜A⌝` is through these — the
// reified analogue of the kernel's `Thm` discipline one level up.
// Building a derivation and establishing `Derivable_Prop ⌜A⌝` are the same
// act. Each opens the `∀d. Closed d ⟹ d A` definition: assume `Closed d`,
// extract the matching closure clause, and apply it.
// ============================================================================

/// `⊢ Derivable_Prop ⌜axiom_i A B C⌝` — the `i`-th Hilbert axiom schema
/// instantiated at encoded sub-formulas `a`, `b`, `c` (each `Φ⟨'r⟩`).
///
/// Opens `∀d. Closed d ⟹ d ⌜ax⌝`: under the assumption `Closed d`, the
/// `i`-th conjunct is `∀A B C. d ⌜axiom_i A B C⌝`; specialise it to
/// `a, b, c` and discharge.
pub fn derive_axiom(i: usize, a: &Term, b: &Term, c: &Term) -> Result<Thm> {
    if !(1..=N_AXIOMS).contains(&i) {
        return Err(covalence_core::Error::ConnectiveRule(format!(
            "derive_axiom: schema index {i} out of range 1..={N_AXIOMS}"
        )));
    }
    let closed_t = closed(&|f| d_at(f))?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d
    // The axiom conjuncts come first (indices 0..N_AXIOMS), in order;
    // peel `i-1` `and_elim_r` then one `and_elim_l` to reach conjunct i.
    let clause = nth_conjunct(assumed, i - 1, N_AXIOMS + 1)?; // ⊢ ∀A B C. d ⌜axiom_i⌝
    let inst = clause
        .all_elim(c.clone())? // ∀C is outermost (built last in `closed`)
        .all_elim(b.clone())?
        .all_elim(a.clone())?; // {Closed d} ⊢ d ⌜axiom_i a b c⌝
    // Discharge `Closed d` and generalise `d` → `Derivable_Prop ⌜ax⌝`.
    inst.imp_intro(&closed_t)? // ⊢ Closed d ⟹ d ⌜ax⌝
        .all_intro("d", Type::fun(phi(), bool_ty()))
}

/// `⊢ Derivable_Prop ⌜A⌝ ⟹ Derivable_Prop ⌜A ⟹ B⌝ ⟹ Derivable_Prop ⌜B⌝`
/// — **modus ponens** at the reified level.
///
/// From `Derivable_Prop ⌜A⌝` and `Derivable_Prop ⌜A⟹B⌝`, under any
/// `Closed d` both give `d ⌜A⌝` and `d ⌜A⟹B⌝`; the MP conjunct of
/// `Closed d` then yields `d ⌜B⌝`.
pub fn derive_mp(a: &Term, b: &Term) -> Result<Thm> {
    let imp_ab = p_imp(a.clone(), b.clone());
    let closed_t = closed(&|f| d_at(f))?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d

    // `d ⌜A⌝` and `d ⌜A⟹B⌝` from the two derivability hyps.
    let der_a = Thm::assume(derivable(a)?)?; // {Der A} ⊢ Der A
    let da = der_a.all_elim(d_var())?.imp_elim(assumed.clone())?; // {Der A, Closed d} ⊢ d ⌜A⌝
    let der_ab = Thm::assume(derivable(&imp_ab)?)?; // {Der (A⟹B)} ⊢ …
    let dab = der_ab.all_elim(d_var())?.imp_elim(assumed.clone())?; // ⊢ d ⌜A⟹B⌝

    // The MP conjunct is the *last* of `closed` (index N_AXIOMS).
    let mp_clause = nth_conjunct(assumed, N_AXIOMS, N_AXIOMS + 1)?; // ⊢ ∀A B. (d A ∧ d(A⟹B)) ⟹ d B
    let mp_inst = mp_clause.all_elim(b.clone())?.all_elim(a.clone())?; // (d⌜A⌝ ∧ d⌜A⟹B⌝) ⟹ d⌜B⌝
    let db = mp_inst.imp_elim(da.and_intro(dab)?)?; // {…, Closed d} ⊢ d ⌜B⌝

    // Discharge `Closed d`, generalise `d`, then the two derivability hyps.
    let der_b = db
        .imp_intro(&closed_t)?
        .all_intro("d", Type::fun(phi(), bool_ty()))?; // {Der A, Der (A⟹B)} ⊢ Der B
    der_b
        .imp_intro(&derivable(&imp_ab)?)?
        .imp_intro(&derivable(a)?)
}

/// From a right-nested conjunction `c₀ ∧ (c₁ ∧ (… ∧ c_{n-1}))` of `n`
/// clauses, extract conjunct `k` (`0`-based): peel `k` right-projections,
/// then a left-projection (or return the whole thing for the last `k`).
fn nth_conjunct(mut thm: Thm, k: usize, n: usize) -> Result<Thm> {
    for _ in 0..k {
        thm = thm.and_elim_r()?;
    }
    if k + 1 < n {
        thm.and_elim_l()
    } else {
        Ok(thm) // last conjunct: no trailing `∧`.
    }
}

// ============================================================================
// Soundness
// ============================================================================

/// `⊢ Derivable_Prop A ⟹ ⟦A⟧ v` for an arbitrary encoded formula `A`
/// (free variable `A : Φ⟨'r⟩`) and arbitrary valuation `v : nat → bool`.
///
/// **Proof.** Instantiate `'r := bool` and the impredicative predicate
/// `d := λA. ⟦A⟧ v` in `Derivable_Prop A = ∀d. Closed d ⟹ d A`. This
/// reduces the goal to discharging `Closed (λA. ⟦A⟧ v)`:
///
/// - each **axiom clause** `∀A B C. ⟦axiom_i A B C⟧ v` is a propositional
///   tautology in the atoms `⟦A⟧ v`, `⟦B⟧ v`, `⟦C⟧ v`, closed by
///   [`prove_taut`] (β-normalise, then complete Shannon decision);
/// - the **MP clause** `∀A B. ⟦A⟧ v ∧ ⟦A ⟹ B⟧ v ⟹ ⟦B⟧ v` is, after
///   unfolding `⟦A ⟹ B⟧ v = (⟦A⟧ v ⟹ ⟦B⟧ v)`, ordinary modus ponens,
///   also a tautology in the atoms — likewise [`prove_taut`].
///
/// Returns `⊢ ∀v. Derivable_Prop A ⟹ ⟦A⟧ v` (closed over `v`; `A` free).
/// The proof runs at `'r := bool`, so the returned theorem is at that
/// instance — which is exactly the denotation semantics we want. Specialise
/// `A` with [`Thm::inst`] to a concrete encoded formula.
pub fn soundness() -> Result<Thm> {
    soundness_at(&fvar("A"))
}

/// Soundness for a *specific* encoded formula `a` (given at `Φ⟨'r⟩` or
/// `Φ⟨bool⟩`; instantiated to `'r := bool` internally).
pub fn soundness_at(a: &Term) -> Result<Thm> {
    let v = Term::free("v", Type::fun(nat(), bool_ty()));

    // The instantiation predicate D := λA:Φ⟨bool⟩. ⟦A⟧ v.
    // We build it at 'r := bool, since `denote` works at bool.
    let big_a = Term::free("A", phi_at_bool());
    let den_body = denote(big_a.clone(), &v)?; // ⟦A⟧ v with A free
    let d_pred = Term::abs(phi_at_bool(), covalence_core::subst::close(&den_body, "A"));

    // The whole proof runs at `'r := bool` (the only instance the
    // denotation needs); instantiate the formula and its derivability
    // statement there.
    let a_bool = inst_tfree_term(a);
    let deriv_bool = inst_tfree_term(&derivable(a)?);
    // ⊢ Derivable_Prop a ⟹ (Closed D ⟹ D a)  — by all_elim on the ∀d.
    let assumed = Thm::assume(deriv_bool.clone())?; // Derivable_Prop a ⊢ Derivable_Prop a
    let specialized = assumed.all_elim(d_pred.clone())?; // ⊢ Closed D ⟹ D a   (under hyp)

    // Discharge `Closed D`.
    let closed_d = discharge_closed(&v, &d_pred)?; // ⊢ Closed D
    let d_a = specialized.imp_elim(closed_d)?; // Derivable_Prop a ⊢ D a

    // D a β-reduces to ⟦a⟧ v.
    let d_a_beta = beta_to_denote(d_a, &a_bool, &v, &d_pred)?; // Derivable_Prop a ⊢ ⟦a⟧ v

    // ⊢ Derivable_Prop a ⟹ ⟦a⟧ v, then ∀v.
    d_a_beta
        .imp_intro(&deriv_bool)?
        .all_intro("v", Type::fun(nat(), bool_ty()))
}

/// Substitute `'r := bool` in a `bool`-typed term that may mention `'r`.
fn inst_tfree_term(t: &Term) -> Term {
    covalence_core::subst::subst_tfree_in_term(t, "r", &bool_ty())
}

/// Prove `⊢ p` for a propositional tautology `p` whose atoms are the
/// (un-reduced) denotation sub-terms. We first β-normalise `p` to expose
/// its connective skeleton, then decide it *completely* via Shannon
/// expansion ([`prop_eq`] against `T`) — `tauto`'s directed `simp` is
/// incomplete for schemas like `A ⟹ (B ⟹ A)` that need case analysis.
fn prove_taut(p: &Term) -> Result<Thm> {
    let to_nf = beta_nf(p.clone()); // ⊢ p = nf
    let nf = to_nf.concl().as_eq().expect("beta_nf equation").1.clone();
    let nf_is_t = prop_eq(&nf, &truth().concl().clone())?; // ⊢ nf = T   (T = ⊢ T's concl)
    // ⊢ p = T, then ⊢ p.
    to_nf.trans(nf_is_t)?.eqt_elim()
}

/// Prove `⊢ Closed D` where `D = λA. ⟦A⟧ v`, by proving each clause.
fn discharge_closed(v: &Term, d_pred: &Term) -> Result<Thm> {
    let a = Term::free("A", phi_at_bool());
    let b = Term::free("B", phi_at_bool());
    let c = Term::free("C", phi_at_bool());

    // Build proofs of each clause in the same order as `closed`.
    let mut clause_thms: Vec<Thm> = Vec::new();

    for i in 1..=N_AXIOMS {
        let ax = axiom_schema(&bool_ty(), i, &a, &b, &c);
        // D ⌜ax⌝ β-reduces to ⟦ax⟧ v, a tautology → prove_taut, then β-expand
        // back to D ⌜ax⌝, then ∀-close.
        let den = denote(ax.clone(), v)?; // ⟦ax⟧ v (a bool term)
        let den_taut = prove_taut(&den)?; // ⊢ ⟦ax⟧ v
        let as_d = expand_to_d(den_taut, &ax, d_pred)?; // ⊢ D ⌜ax⌝
        let closed = as_d
            .all_intro("A", phi_at_bool())?
            .all_intro("B", phi_at_bool())?
            .all_intro("C", phi_at_bool())?;
        clause_thms.push(closed);
    }

    // MP clause: ∀A B. (D A ∧ D (A⟹B)) ⟹ D B.
    let mp = {
        let imp_ab = p_imp_at(&bool_ty(), a.clone(), b.clone());
        // Work at the denotation level: assume ⟦A⟧v ∧ ⟦A⟹B⟧v, derive ⟦B⟧v.
        let da = denote(a.clone(), v)?;
        let dab = denote(imp_ab.clone(), v)?;
        let db = denote(b.clone(), v)?;

        // The whole implication is a propositional tautology in atoms
        // ⟦A⟧v, ⟦B⟧v once ⟦A⟹B⟧v is unfolded to (⟦A⟧v ⟹ ⟦B⟧v).
        // `prove_taut` β-normalises then decides it completely.
        let goal = da.and(dab)?.imp(db)?;
        let thm = prove_taut(&goal)?; // ⊢ (⟦A⟧v ∧ ⟦A⟹B⟧v) ⟹ ⟦B⟧v

        // β-expand the three denotations back to `D …`.
        let thm = expand_imp_to_d(thm, &a, &imp_ab, &b, d_pred)?;
        thm.all_intro("A", phi_at_bool())?
            .all_intro("B", phi_at_bool())?
    };
    clause_thms.push(mp);

    // Conjoin in the right-nested shape `closed` produced.
    let mut iter = clause_thms.into_iter().rev();
    let mut acc = iter.next().expect("clauses");
    for cl in iter {
        acc = cl.and_intro(acc)?;
    }
    Ok(acc)
}

/// Given `⊢ ⟦ax⟧ v` and the encoded `ax`, produce `⊢ D ⌜ax⌝` where
/// `D = λA. ⟦A⟧ v` — i.e. β-expand `⟦ax⟧ v` to `(λA. ⟦A⟧ v) ax`.
fn expand_to_d(den_thm: Thm, ax: &Term, d_pred: &Term) -> Result<Thm> {
    let d_app = d_pred.clone().apply(ax.clone())?; // (λA. ⟦A⟧v) ax
    // ⊢ D ⌜ax⌝ = ⟦ax⟧ v  (β), reverse, eq_mp.
    let beta = Thm::beta_conv(d_app)?; // ⊢ D ⌜ax⌝ = ⟦ax⟧ v
    beta.sym()?.eq_mp(den_thm)
}

/// β-expand the MP-clause tautology `⊢ (⟦A⟧v ∧ ⟦A⟹B⟧v) ⟹ ⟦B⟧v` back to
/// `⊢ (D A ∧ D (A⟹B)) ⟹ D B`.
fn expand_imp_to_d(
    thm: Thm,
    a: &Term,
    imp_ab: &Term,
    b: &Term,
    d_pred: &Term,
) -> Result<Thm> {
    // Rewrite each `⟦·⟧ v` occurrence with `⊢ ⟦·⟧ v = D ·` (sym of β).
    let beta_a = Thm::beta_conv(d_pred.clone().apply(a.clone())?)?.sym()?;
    let beta_ab = Thm::beta_conv(d_pred.clone().apply(imp_ab.clone())?)?.sym()?;
    let beta_b = Thm::beta_conv(d_pred.clone().apply(b.clone())?)?.sym()?;
    thm.rewrite(&beta_a)?
        .rewrite(&beta_ab)?
        .rewrite(&beta_b)
}

/// Given `Γ ⊢ D a` (with `D = λA. ⟦A⟧ v`), β-reduce to `Γ ⊢ ⟦a⟧ v`.
fn beta_to_denote(d_a: Thm, a: &Term, _v: &Term, d_pred: &Term) -> Result<Thm> {
    let d_app = d_pred.clone().apply(a.clone())?;
    let beta = Thm::beta_conv(d_app)?; // ⊢ D a = ⟦a⟧ v
    beta.eq_mp(d_a)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The generic soundness theorem is genuine (proved, oracle-free) and
    /// has the right shape `∀v. Derivable_Prop A ⟹ ⟦A⟧ v`.
    #[test]
    fn soundness_is_genuine() {
        let thm = soundness().expect("soundness proof");
        assert!(thm.hyps().is_empty(), "soundness is proved, not assumed");
        assert!(thm.has_no_obs(), "soundness is oracle-free");
        // Conclusion is a ∀v. (… ⟹ …) — a forall whose body is an imp.
        let v = Term::free("v", Type::fun(nat(), bool_ty()));
        let a = fvar("A");
        let expected = inst_tfree_term(&derivable(&a).unwrap())
            .imp(denote(a.clone(), &v).unwrap())
            .unwrap()
            .forall("v", Type::fun(nat(), bool_ty()))
            .unwrap();
        // After instantiating 'r := bool the soundness conclusion equals this.
        let thm_bool = thm.inst_tfree("r", bool_ty()).unwrap();
        assert_eq!(thm_bool.concl(), &expected);
    }

    /// Soundness specialises to a concrete formula `⌜p₀ ⟹ p₀⌝`:
    /// `⊢ Derivable_Prop ⌜p₀ ⟹ p₀⌝ ⟹ ⟦p₀ ⟹ p₀⟧ v`.
    #[test]
    fn soundness_at_concrete_formula() {
        let a = p_imp(p_var_lit(0), p_var_lit(0));
        let thm = soundness_at(&a).expect("soundness for p ⟹ p");
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // The conclusion is `∀v. Derivable_Prop ⌜a⌝ ⟹ ⟦a⟧ v`.
        let v = Term::free("v", Type::fun(nat(), bool_ty()));
        let expected = inst_tfree_term(&derivable(&a).unwrap())
            .imp(denote(a.clone(), &v).unwrap())
            .unwrap();
        assert_eq!(
            thm.inst_tfree("r", bool_ty())
                .unwrap()
                .all_elim(v)
                .unwrap()
                .concl(),
            &expected
        );
    }

    /// Constructors build distinct, well-typed `Φ⟨'r⟩` values.
    #[test]
    fn constructors_are_distinct_and_typed() {
        let p0 = p_var_lit(0);
        let p1 = p_var_lit(1);
        assert_eq!(p0.type_of().unwrap(), phi());
        assert_eq!(p_and(p0.clone(), p1.clone()).type_of().unwrap(), phi());
        assert_eq!(p_neg(p0.clone()).type_of().unwrap(), phi());
        // var 0 ≠ var 1 ≠ (var 0 ∧ var 0): genuine syntax, not denotation.
        assert_ne!(p0, p1);
        assert_ne!(p0, p_and(p0.clone(), p0.clone()));
    }

    /// `derive_axiom` yields a genuine `⊢ Derivable_Prop ⌜axiom_i⌝`, and
    /// chaining it through `soundness` discharges the denotation. This is
    /// the full pipeline: build a derivation, get its truth.
    #[test]
    fn derive_axiom_is_genuine_and_sound() {
        let a = p_var_lit(0);
        let b = p_var_lit(1);
        let c = p_var_lit(2);
        // ⊢ Derivable_Prop ⌜axiom_1 (= a ⟹ (b ⟹ a))⌝  (at 'r, no denotation)
        let der = derive_axiom(1, &a, &b, &c).expect("derive axiom 1");
        assert!(der.hyps().is_empty() && der.has_no_obs());
        let ax = axiom_schema(&rty(), 1, &a, &b, &c);
        assert_eq!(der.concl(), &derivable(&ax).unwrap());

        // Soundness ∘ derivation: ⊢ ⟦axiom_1⟧ v for all v. Soundness lives
        // at 'r := bool, so instantiate the derivation there first.
        let snd = soundness_at(&ax).expect("soundness for axiom 1"); // ∀v. Der ⌜ax⌝ ⟹ ⟦ax⟧ v
        let v = Term::free("v", Type::fun(nat(), bool_ty()));
        let der_bool = der.inst_tfree("r", bool_ty()).unwrap();
        let truth = snd.all_elim(v).unwrap().imp_elim(der_bool).unwrap(); // ⊢ ⟦ax⟧ v
        assert!(truth.hyps().is_empty() && truth.has_no_obs());
    }

    /// `derive_mp` is a genuine reified modus ponens.
    #[test]
    fn derive_mp_is_genuine() {
        let a = p_var_lit(0);
        let b = p_var_lit(1);
        let mp = derive_mp(&a, &b).expect("derive mp");
        assert!(mp.hyps().is_empty() && mp.has_no_obs());
        // Shape (at 'r): Der ⌜A⌝ ⟹ Der ⌜A⟹B⌝ ⟹ Der ⌜B⌝.
        let expected_r = derivable(&a)
            .unwrap()
            .imp(
                derivable(&p_imp(a.clone(), b.clone()))
                    .unwrap()
                    .imp(derivable(&b).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(mp.concl(), &expected_r);
    }

    /// The denotation of a concrete formula β-reduces as expected:
    /// `⟦var 0⟧ v = v 0`.
    #[test]
    fn denote_var_reduces() {
        let v = Term::free("v", Type::fun(nat(), bool_ty()));
        let den = denote(p_var_lit(0), &v).unwrap();
        // den : bool, and reduces to `v 0`.
        assert_eq!(den.type_of().unwrap(), bool_ty());
        let nf = crate::init::eq::beta_nf(den);
        let rhs = nf.concl().as_eq().unwrap().1.clone();
        let expected = v
            .apply(Term::nat_lit(covalence_types::Nat::from_inner(0u32.into())))
            .unwrap();
        assert_eq!(rhs, expected);
    }
}
