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
// Constructors as closed-λ constants (for the `.cov` surface / [`prop_env`]).
//
// As in `init::tree`, the `.cov` language applies a head symbol by curried
// `Term::app` (no β), so the constructors are exposed as closed λ CONSTANTS at
// the polymorphic carrier `Φ⟨'r⟩`; `(app prop.var n)` etc. β-reduces to the
// reduced encoding the seam lemmas are stated over.
// ============================================================================

/// `prop.var : nat → Φ⟨'r⟩` — the `var` constructor as a closed λ constant.
pub fn var_fn() -> Term {
    let n = Term::free("__n", nat());
    Term::abs(nat(), covalence_core::subst::close(&p_var(n.clone()), "__n"))
}

/// `prop.neg : Φ⟨'r⟩ → Φ⟨'r⟩` — the `¬` constructor as a closed λ constant.
pub fn neg_fn() -> Term {
    let a = Term::free("__a", phi());
    Term::abs(phi(), covalence_core::subst::close(&p_neg(a.clone()), "__a"))
}

/// A binary constructor `λA B. op A B` as a closed λ constant.
fn bin_fn(op: fn(Term, Term) -> Term) -> Term {
    let a = Term::free("__a", phi());
    let b = Term::free("__b", phi());
    let body = op(a.clone(), b.clone());
    let inner = Term::abs(phi(), covalence_core::subst::close(&body, "__b"));
    Term::abs(phi(), covalence_core::subst::close(&inner, "__a"))
}

/// `prop.and : Φ⟨'r⟩ → Φ⟨'r⟩ → Φ⟨'r⟩`.
pub fn and_fn() -> Term {
    bin_fn(p_and)
}

/// `prop.or : Φ⟨'r⟩ → Φ⟨'r⟩ → Φ⟨'r⟩`.
pub fn or_fn() -> Term {
    bin_fn(p_or)
}

/// `prop.imp : Φ⟨'r⟩ → Φ⟨'r⟩ → Φ⟨'r⟩`.
pub fn imp_fn() -> Term {
    bin_fn(p_imp)
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

/// `prop.derivable : Φ⟨'r⟩ → bool` — `Derivable_Prop` as a closed λ constant,
/// `λA. ∀d. Closed d ⟹ d A`, for the `.cov` surface. `(app prop.derivable A)`
/// β-reduces to `derivable(A)`.
pub fn derivable_fn() -> Term {
    let a = Term::free("__a", phi());
    let body = derivable(&a).expect("derivable_fn: body");
    Term::abs(phi(), covalence_core::subst::close(&body, "__a"))
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
// Rule induction over derivations — the reusable packaging
//
// `Derivable_Prop A := ∀d. Closed d ⟹ d A` is impredicative, so "induction
// on the derivation of A" is a SINGLE move: instantiate the predicate
// variable `d := P` and discharge the resulting `Closed P` obligation —
// "P holds at every axiom instance, and P is MP-closed". That is exactly the
// induction principle's premises; the conclusion `∀A. Derivable_Prop A ⟹ P A`
// is the induction hypothesis discharged for every derivable formula.
//
// `prop_induction` packages this once. `soundness` (`P := λA. ⟦A⟧ v`) and
// `derivable_closed_under_rules` (`P := λA. Derivable_Prop A`, cases via the
// derivation constructors) are two structurally different *instances*;
// `consistency` is a downstream soundness consequence.
// ============================================================================

/// **Rule induction over `Derivable_Prop`.** Given a predicate
/// `pred : Φ⟨bool⟩ → bool` and proofs that it is *closed under the Hilbert
/// system* — one per axiom schema and one for modus ponens — conclude
///
/// ```text
///   ⊢ ∀A. Derivable_Prop A ⟹ pred A
/// ```
///
/// This is the impredicative `inst d := pred` discharged against `Closed pred`.
/// The caller supplies the closure obligations as closures over **fixed free
/// formula variables** `A`, `B`, `C : Φ⟨bool⟩` (passed in so the case proofs
/// are generic — `prop_induction` does the `∀`-generalisation):
///
/// - `axiom_case(i, A, B, C)` must prove `⊢ pred ⌜axiom_i A B C⌝` (the schema
///   at the supplied sub-formula variables), for each `i ∈ 1..=N_AXIOMS`;
/// - `mp_case(A, B)` must prove `⊢ (pred A ∧ pred ⌜A ⟹ B⌝) ⟹ pred B`.
///
/// Everything runs at `'r := bool` (the encoding instance the predicate lives
/// at). The kernel re-checks every step, so a bogus case proof — one whose
/// conclusion is not the demanded clause — fails the conjunction build rather
/// than fabricating an induction.
pub fn prop_induction(
    pred: &Term,
    axiom_case: impl Fn(usize, &Term, &Term, &Term) -> Result<Thm>,
    mp_case: impl Fn(&Term, &Term) -> Result<Thm>,
) -> Result<Thm> {
    let a = Term::free("A", phi_at_bool());
    let b = Term::free("B", phi_at_bool());
    let c = Term::free("C", phi_at_bool());

    // Build `⊢ Closed pred` clause by clause, in the order `closed` lays them
    // out (axioms 1..=N, then MP), ∀-generalising each over its formula vars.
    let mut clause_thms: Vec<Thm> = Vec::new();
    for i in 1..=N_AXIOMS {
        let clause = axiom_case(i, &a, &b, &c)?
            .all_intro("A", phi_at_bool())?
            .all_intro("B", phi_at_bool())?
            .all_intro("C", phi_at_bool())?;
        clause_thms.push(clause);
    }
    let mp = mp_case(&a, &b)?
        .all_intro("A", phi_at_bool())?
        .all_intro("B", phi_at_bool())?;
    clause_thms.push(mp);

    // Conjoin into the right-nested `Closed pred` shape.
    let mut iter = clause_thms.into_iter().rev();
    let mut acc = iter.next().expect("at least the MP clause");
    for cl in iter {
        acc = cl.and_intro(acc)?;
    }
    let closed_pred_thm = acc; // ⊢ Closed pred

    // Now discharge the impredicative definition for an arbitrary `A`:
    //   Derivable_Prop A ⊢ Derivable_Prop A
    //                    ⊢ ∀d. Closed d ⟹ d A
    //         (inst d := pred) Closed pred ⟹ pred A
    //          (imp_elim Closed pred)       pred A
    //
    // `derivable` builds its `∀d:Φ⟨'r⟩→bool` + `Closed d` clauses at the
    // POLYMORPHIC carrier; instantiate the whole statement to `'r := bool`
    // (uniformly converting `A`, `d`, and the clauses to `Φ⟨bool⟩`) so it
    // agrees with `pred : Φ⟨bool⟩ → bool`.
    let deriv = inst_tfree_term(&derivable(&fvar("A"))?); // Derivable_Prop A at 'r := bool
    let assumed = Thm::assume(deriv.clone())?;
    let pred_a = assumed
        .all_elim(pred.clone())? // Closed pred ⟹ pred A
        .imp_elim(closed_pred_thm)?; // {Der A} ⊢ pred A

    // ⊢ ∀A. Derivable_Prop A ⟹ pred A.
    pred_a
        .imp_intro(&deriv)?
        .all_intro("A", phi_at_bool())
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

/// The **soundness predicate** `λA:Φ⟨bool⟩. ⟦A⟧ v` — the impredicative
/// instantiation `d := ⟦·⟧ v` that soundness uses.
fn denote_pred(v: &Term) -> Result<Term> {
    let big_a = Term::free("A", phi_at_bool());
    let den_body = denote(big_a, v)?; // ⟦A⟧ v with A free
    Ok(Term::abs(phi_at_bool(), covalence_core::subst::close(&den_body, "A")))
}

/// `⊢ pred ⌜axiom_i a b c⌝` for `pred = λA. ⟦A⟧ v` — the soundness *axiom
/// case* used by [`prop_induction`]: the schema's denotation is a tautology
/// ([`prove_taut`]), β-expanded back to `pred ⌜ax⌝`.
fn sound_axiom_case(v: &Term, d_pred: &Term, i: usize, a: &Term, b: &Term, c: &Term) -> Result<Thm> {
    let ax = axiom_schema(&bool_ty(), i, a, b, c);
    let den = denote(ax.clone(), v)?; // ⟦ax⟧ v (a bool term)
    let den_taut = prove_taut(&den)?; // ⊢ ⟦ax⟧ v
    expand_to_d(den_taut, &ax, d_pred) // ⊢ pred ⌜ax⌝
}

/// `⊢ (pred a ∧ pred ⌜a ⟹ b⌝) ⟹ pred b` for `pred = λA. ⟦A⟧ v` — the
/// soundness *MP case* used by [`prop_induction`]: at the denotation level it
/// is the modus-ponens tautology, β-expanded back to the `pred …` form.
fn sound_mp_case(v: &Term, d_pred: &Term, a: &Term, b: &Term) -> Result<Thm> {
    let imp_ab = p_imp_at(&bool_ty(), a.clone(), b.clone());
    let da = denote(a.clone(), v)?;
    let dab = denote(imp_ab.clone(), v)?;
    let db = denote(b.clone(), v)?;
    let goal = da.and(dab)?.imp(db)?;
    let thm = prove_taut(&goal)?; // ⊢ (⟦a⟧v ∧ ⟦a⟹b⟧v) ⟹ ⟦b⟧v
    expand_imp_to_d(thm, a, &imp_ab, b, d_pred) // ⊢ (pred a ∧ pred ⌜a⟹b⌝) ⟹ pred b
}

/// **Soundness, proved through [`prop_induction`]** — the principle's first
/// instance, and the form `soundness`/`soundness_at` are specialisations of.
///
/// Returns `⊢ ∀A. Derivable_Prop A ⟹ (λA. ⟦A⟧ v) A` (at `'r := bool`), `v`
/// free. The consequent is the soundness predicate `pred = λA. ⟦A⟧ v` *applied*
/// to the bound `A` — a single β-step short of `⟦A⟧ v`, which cannot be fired
/// under the `∀A` binder (it must be reduced per-instance after `all_elim`, as
/// [`consistency`] does). The two closure obligations are the tautology cases
/// [`sound_axiom_case`] / [`sound_mp_case`].
pub fn soundness_general(v: &Term) -> Result<Thm> {
    let d_pred = denote_pred(v)?;
    prop_induction(
        &d_pred,
        |i, a, b, c| sound_axiom_case(v, &d_pred, i, a, b, c),
        |a, b| sound_mp_case(v, &d_pred, a, b),
    ) // ⊢ ∀A. Derivable_Prop A ⟹ pred A
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

/// Prove `⊢ Closed D` where `D = λA. ⟦A⟧ v`, by proving each clause. This is
/// `Closed` of the *soundness* predicate built from the same per-clause case
/// provers ([`sound_axiom_case`] / [`sound_mp_case`]) [`prop_induction`] uses;
/// kept as a thin helper so [`soundness_at`] (the per-formula specialisation)
/// can still discharge `Closed D` directly.
fn discharge_closed(v: &Term, d_pred: &Term) -> Result<Thm> {
    let a = Term::free("A", phi_at_bool());
    let b = Term::free("B", phi_at_bool());
    let c = Term::free("C", phi_at_bool());

    // Build proofs of each clause in the same order as `closed`.
    let mut clause_thms: Vec<Thm> = Vec::new();
    for i in 1..=N_AXIOMS {
        let closed = sound_axiom_case(v, d_pred, i, &a, &b, &c)?
            .all_intro("A", phi_at_bool())?
            .all_intro("B", phi_at_bool())?
            .all_intro("C", phi_at_bool())?;
        clause_thms.push(closed);
    }
    let mp = sound_mp_case(v, d_pred, &a, &b)?
        .all_intro("A", phi_at_bool())?
        .all_intro("B", phi_at_bool())?;
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

// ============================================================================
// A SECOND instance of `prop_induction` — proving the packaging is general
// ============================================================================

/// **Derivability is closed under its own rules** —
/// `⊢ ∀A. Derivable_Prop A ⟹ Derivable_Prop A`, proved by [`prop_induction`]
/// with the predicate `pred := λA. Derivable_Prop A`.
///
/// This is a *second, structurally different* instance of the induction
/// packaging: the predicate is **not** the denotation (no `⟦·⟧`, no tautology
/// deciding), and the closure obligations are discharged by the **derivation
/// constructors** [`derive_axiom`] / [`derive_mp`] rather than `prove_taut`.
/// It witnesses that `prop_induction` is genuinely reusable — the same single
/// `inst d := P` + `Closed P` discharge works for any HOL predicate over
/// encoded formulas, not just soundness.
pub fn derivable_closed_under_rules() -> Result<Thm> {
    // pred := λA:Φ⟨bool⟩. Derivable_Prop A. Build `Derivable_Prop A` over the
    // POLYMORPHIC `A : Φ⟨'r⟩` (so the internal `∀d:Φ⟨'r⟩→bool` agrees with `A`),
    // THEN instantiate `'r := bool` uniformly, then abstract.
    let der_body = inst_tfree_term(&derivable(&fvar("A"))?); // Derivable_Prop A at bool
    let pred = Term::abs(phi_at_bool(), covalence_core::subst::close(&der_body, "A"));

    // β-expand `Derivable_Prop t` to `pred t` for the case proofs (whose
    // natural shape is `⊢ Derivable_Prop …` from the constructors).
    let expand = |thm: Thm, t: &Term| -> Result<Thm> {
        let beta = Thm::beta_conv(pred.clone().apply(t.clone())?)?.sym()?; // ⊢ Der t = pred t
        thm.rewrite(&beta)
    };

    let axiom_case = |i: usize, a: &Term, b: &Term, c: &Term| -> Result<Thm> {
        // `derive_axiom_thm(i)` is `∀A B C. Der ⌜axiom_i⌝` at the polymorphic
        // carrier; instantiate `'r := bool` then specialise to the (bool) case
        // variables `a, b, c : Φ⟨bool⟩` the principle hands us.
        let der = derive_axiom_thm(i)?
            .inst_tfree("r", bool_ty())?
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .all_elim(c.clone())?; // ⊢ Derivable_Prop ⌜axiom_i a b c⌝
        let ax = axiom_schema(&bool_ty(), i, a, b, c);
        expand(der, &ax)
    };
    let mp_case = |a: &Term, b: &Term| -> Result<Thm> {
        // `derive_mp_thm` is `∀A B. Der A ⟹ Der ⌜A⟹B⌝ ⟹ Der B` at the
        // polymorphic carrier; instantiate to `'r := bool` and the case vars.
        let imp_ab = p_imp_at(&bool_ty(), a.clone(), b.clone());
        let mp = derive_mp_thm()?
            .inst_tfree("r", bool_ty())?
            .all_elim(a.clone())?
            .all_elim(b.clone())?; // ⊢ Der A ⟹ (Der (A⟹B) ⟹ Der B)
        // Read the two (correctly bool-typed) antecedents `Der a`, `Der (a⟹b)`
        // straight off `mp`'s conclusion `Der a ⟹ (Der (a⟹b) ⟹ Der b)`.
        let nae = || covalence_core::Error::NotAnEquation;
        let (imp_da, rest) = mp.concl().as_app().ok_or_else(nae)?; // (imp (Der a), Der(a⟹b)⟹Der b)
        let (_imp, der_a) = imp_da.as_app().ok_or_else(nae)?;
        let der_a = der_a.clone();
        let (imp_dab, _der_b) = rest.as_app().ok_or_else(nae)?;
        let (_imp2, der_ab) = imp_dab.as_app().ok_or_else(nae)?;
        let der_ab = der_ab.clone();
        let hyp = der_a.clone().and(der_ab.clone())?;
        let assumed = Thm::assume(hyp.clone())?; // {H} ⊢ Der A ∧ Der (A⟹B)
        let h_a = assumed.clone().and_elim_l()?; // {H} ⊢ Der A
        let h_ab = assumed.and_elim_r()?; // {H} ⊢ Der (A⟹B)
        let der_b = mp.imp_elim(h_a)?.imp_elim(h_ab)?; // {H} ⊢ Der B
        let cnj = der_b.imp_intro(&hyp)?; // ⊢ (Der A ∧ Der (A⟹B)) ⟹ Der B
        // β-expand all three `Der …` to `pred …`.
        let beta_a = Thm::beta_conv(pred.clone().apply(a.clone())?)?.sym()?;
        let beta_ab = Thm::beta_conv(pred.clone().apply(imp_ab.clone())?)?.sym()?;
        let beta_b = Thm::beta_conv(pred.clone().apply(b.clone())?)?.sym()?;
        cnj.rewrite(&beta_a)?.rewrite(&beta_ab)?.rewrite(&beta_b)
    };

    prop_induction(&pred, axiom_case, mp_case)
}

/// **Consistency of the propositional Hilbert system** —
/// `⊢ ¬Derivable_Prop ⌜var 0⌝`: a bare propositional variable is *not*
/// derivable (it is not a tautology). A soundness *consequence*, the smallest
/// non-trivial metatheorem about the object logic.
///
/// **Proof.** [`soundness_general`] gives `∀A. Derivable_Prop A ⟹ ⟦A⟧ v`.
/// Specialise `A := ⌜var 0⌝` and the valuation `v := λ_:nat. F`: then
/// `⟦var 0⟧ (λ_. F)` β-reduces to `F`, so `Derivable_Prop ⌜var 0⌝ ⟹ F`, i.e.
/// `¬Derivable_Prop ⌜var 0⌝`.
pub fn consistency() -> Result<Thm> {
    let v_false = {
        // λ_:nat. F  — the all-false valuation.
        Term::abs(nat(), Term::bool_lit(false))
    };
    let var0 = inst_tfree_term(&p_var_lit(0)); // ⌜var 0⌝ at 'r := bool

    // ∀A. Der A ⟹ pred A   (v free, pred = λA. ⟦A⟧ v), specialise A then v.
    let v_free = Term::free("v", Type::fun(nat(), bool_ty()));
    let sound = soundness_general(&v_free)?;
    let at_var0 = sound.all_elim(var0.clone())?; // ⊢ Der ⌜var0⌝ ⟹ pred ⌜var0⌝
    let at_false = at_var0.inst("v", v_false)?; // ⊢ Der ⌜var0⌝ ⟹ pred[v:=λ_.F] ⌜var0⌝

    // Read the consequent `(λA. ⟦A⟧ (λ_.F)) ⌜var0⌝` straight off the theorem;
    // β-normalising it lands on `F` (`var0` selects `(λ_.F) 0 = F`). Turn it
    // into `F` by a TARGETED congruence on the implication (NOT `rewrite` —
    // `rewrite_conv` walks the enormous `Der ⌜var0⌝` antecedent, O(size²) → hang).
    // `at_false.concl() = imp (Der var0) consequent = App(App(imp, Der), cons)`.
    let nae = || covalence_core::Error::NotAnEquation;
    let (imp_der, consequent) = at_false.concl().as_app().ok_or_else(nae)?;
    let imp_der = imp_der.clone(); // `imp (Der var0)`
    let to_f = beta_nf(consequent.clone()); // ⊢ consequent = F
    let imp_eq = to_f.cong_arg(imp_der)?; // ⊢ (Der ⟹ consequent) = (Der ⟹ F)
    let at_f = imp_eq.eq_mp(at_false)?; // ⊢ Der ⌜var0⌝ ⟹ F
    // ¬Der ⌜var0⌝ is definitionally `Der ⌜var0⌝ ⟹ F`; `not_intro` packages it.
    at_f.not_intro()
}

/// [`consistency`] re-stated over the **applied constructor / predicate
/// constants** — `⊢ ¬(prop.derivable (prop.var 0))` — so it is citable from
/// `prop.cov` with an expressible `#concl`.
///
/// Bridges with **targeted single β-steps**, NOT full β-normalisation: the
/// reduced `Derivable_Prop ⌜var 0⌝` is an enormous Church fold (the 10-axiom
/// `Closed` conjunction), so `beta_nf`-based bridges (`tree::to_applied`) blow
/// up exponentially. Instead build `⊢ applied = reduced` from one
/// `beta_conv` on `var_fn` and one on `derivable_fn`, leaving the fold opaque.
pub fn consistency_app() -> Result<Thm> {
    let thm = consistency()?; // ⊢ ¬derivable(var0)   (reduced form)

    // The bool-pinned constant constructor forms.
    let var_fn_b = inst_tfree_term(&var_fn());
    let derivable_fn_b = inst_tfree_term(&derivable_fn());
    let zero = Term::nat_lit(0u32);

    // ⊢ var_fn 0 = var0   (single β-step; var_fn = λn. p_var n).
    let var_app = var_fn_b.apply(zero)?;
    let beta_var = Thm::beta_conv(var_app.clone())?; // ⊢ var_fn 0 = var0
    let var0 = beta_var.concl().as_eq().expect("eq").1.clone();

    // ⊢ derivable_fn var0 = derivable(var0)   (single β-step).
    let der_app = derivable_fn_b.clone().apply(var0)?;
    let beta_der = Thm::beta_conv(der_app)?; // ⊢ derivable_fn var0 = derivable var0

    // ⊢ derivable_fn (var_fn 0) = derivable var0, by transitivity:
    //   derivable_fn (var_fn 0) = derivable_fn var0   (cong_arg, fixed fn)
    //                           = derivable var0       (beta_der)
    let cong = beta_var.cong_arg(derivable_fn_b)?; // ⊢ derivable_fn (var_fn 0) = derivable_fn var0
    let bridge = cong.trans(beta_der)?; // ⊢ applied = derivable var0

    // `⊢ ¬applied = ¬reduced` by congruence on `¬` (one `mk_comb`), then
    // `eq_mp` against `consistency : ⊢ ¬reduced`. We deliberately avoid
    // `rewrite` here: its `rewrite_conv` walks the *whole* `¬derivable(var0)`
    // tree — and that tree is an enormous Church fold — making the rewrite
    // O(size²); the targeted congruence touches only the `¬` head.
    let not_eq = bridge.sym()?.cong_arg(covalence_core::defs::not())?; // ⊢ ¬reduced = ¬applied
    not_eq.eq_mp(thm)
}

// ============================================================================
// `.cov` seam — `prop_env` + the ported `prop.cov` theory
// ============================================================================

/// `⊢ ∀A B C. Derivable_Prop ⌜axiom_i A B C⌝` — the `i`-th Hilbert axiom
/// schema's derivability, ∀-closed over its formula variables. The
/// `.cov`-citable form of [`derive_axiom`].
pub fn derive_axiom_thm(i: usize) -> Result<Thm> {
    let a = fvar("A");
    let b = fvar("B");
    let c = fvar("C");
    derive_axiom(i, &a, &b, &c)?
        .all_intro("C", phi())?
        .all_intro("B", phi())?
        .all_intro("A", phi())
}

/// `⊢ ∀A B. Derivable_Prop A ⟹ Derivable_Prop ⌜A ⟹ B⌝ ⟹ Derivable_Prop B`
/// — reified modus ponens, ∀-closed. The `.cov`-citable form of
/// [`derive_mp`].
pub fn derive_mp_thm() -> Result<Thm> {
    let a = fvar("A");
    let b = fvar("B");
    derive_mp(&a, &b)?
        .all_intro("B", phi())?
        .all_intro("A", phi())
}

/// The `prop` seam environment for [`crate::init::prop::cov`] (`prop.cov`):
///
/// - the **constructor constants** `prop.var` / `prop.neg` / `prop.and` /
///   `prop.or` / `prop.imp` (closed λ at the polymorphic carrier `Φ⟨'r⟩`);
/// - the **derivation-system givens** (Rust-proved): `derive_mp` and
///   `derive_axiom_1` … `derive_axiom_10`, plus the metatheorems `soundness`
///   (`∀v. Derivable_Prop A ⟹ ⟦A⟧ v`, `A` free), `derivable_self`
///   (the second `prop_induction` instance) and `consistency`
///   (`¬Derivable_Prop ⌜var 0⌝`).
///
/// `Derivable_Prop` and `⟦·⟧` themselves are *not* exposed as `.cov` head
/// symbols (they are impredicative / valuation-parametric terms the script
/// surface cannot yet build — see `prop.cov`'s surface-gap notes); a `.cov`
/// proof consumes them only through these pre-proved givens.
pub fn prop_env() -> crate::script::Env {
    use crate::script::ConstDef;

    let mut e = crate::script::Env::empty();

    // -- constructors as closed-λ constants (Poly: re-instantiated per use) --
    e.define_const("prop.var", ConstDef::Poly(var_fn()));
    e.define_const("prop.neg", ConstDef::Poly(neg_fn()));
    e.define_const("prop.and", ConstDef::Poly(and_fn()));
    e.define_const("prop.or", ConstDef::Poly(or_fn()));
    e.define_const("prop.imp", ConstDef::Poly(imp_fn()));
    // `Derivable_Prop` as a constant — so `prop.cov` can WRITE the consistency
    // statement (the only metatheorem whose `#concl` is expressible: it
    // mentions `derivable` applied to a *closed* formula, not a bound var).
    e.define_const("prop.derivable", ConstDef::Poly(derivable_fn()));
    // SURFACE GAP: a `Poly` constant instantiates `'r` with a *fresh* metavar,
    // and `.cov` has no type-ascription syntax to pin `'r := bool`. The
    // `consistency` metatheorem lives at `'r := bool` (its proof goes through
    // the `bool` denotation), so we additionally expose the two constants it
    // needs **monomorphically at bool** — `prop.var.bool` / `prop.derivable.bool`
    // — so `consistency`'s `#concl` is writable and matches the seam given.
    e.define_const(
        "prop.var.bool",
        ConstDef::Op(inst_tfree_term(&var_fn())),
    );
    e.define_const(
        "prop.derivable.bool",
        ConstDef::Op(inst_tfree_term(&derivable_fn())),
    );

    // -- derivation-system + metatheory givens (Rust-proved) --
    e.define_lemma("derive_mp", derive_mp_thm().expect("prop_env: derive_mp"));
    for i in 1..=N_AXIOMS {
        e.define_lemma(
            format!("derive_axiom_{i}"),
            derive_axiom_thm(i).unwrap_or_else(|_| panic!("prop_env: derive_axiom_{i}")),
        );
    }
    e.define_lemma("soundness", soundness().expect("prop_env: soundness"));
    e.define_lemma(
        "derivable_self",
        derivable_closed_under_rules().expect("prop_env: derivable_self"),
    );
    // `consistency` in applied-constant form (its `#concl` is expressible).
    e.define_lemma(
        "consistency",
        consistency_app().expect("prop_env: consistency"),
    );

    e
}

crate::cov_theory! {
    /// `prop` propositional-logic metatheory ported to `prop.cov`, over `core`
    /// + the `propprim` seam env. The derivation constructors and the
    /// induction-proved metatheorems (`soundness`, `consistency`,
    /// `derivable_self`) are re-exported genuinely (each proof `all-elim`s /
    /// chains the seam givens).
    pub mod cov from "prop.cov" {
        import "core"     = crate::script::Env::core();
        import "propprim" = crate::init::prop::prop_env();
        "axiom1_shape_refl" => pub fn axiom1_shape_refl_cov;
        "consistency"       => pub fn consistency_cov;
    }
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

    // -- rule-induction packaging (deliverable 1) -------------------------

    /// `soundness_general` (the first `prop_induction` instance) is genuine and
    /// has the shape `∀A. Derivable_Prop A ⟹ ⟦A⟧ v`.
    #[test]
    fn soundness_general_is_genuine() {
        let v = Term::free("v", Type::fun(nat(), bool_ty()));
        let thm = soundness_general(&v).expect("soundness via prop_induction");
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // It is a `∀A. …` (a forall over the formula carrier).
        assert!(thm.concl().as_app().is_some());
    }

    /// The SECOND `prop_induction` instance — `∀A. Derivable_Prop A ⟹
    /// Derivable_Prop A`, proved with the derivation constructors as the
    /// closure cases (not the denotation). Proves the packaging is general.
    #[test]
    fn derivable_self_is_a_second_instance() {
        let thm = derivable_closed_under_rules().expect("derivable_self");
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
    }

    /// `consistency` — `⊢ ¬Derivable_Prop ⌜var 0⌝` — is genuine (a real
    /// metatheorem about the object logic, soundness-derived).
    #[test]
    fn consistency_is_genuine() {
        let thm = consistency().expect("consistency");
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // Conclusion is `¬(Derivable_Prop ⌜var 0⌝)`: build `Derivable_Prop A`
        // at the polymorphic carrier, instantiate `'r := bool`, then substitute
        // `A := ⌜var 0⌝` (the order `consistency` itself uses — `derivable`'s
        // internal `∀d:Φ⟨'r⟩→bool` must be built before `'r` is pinned).
        let der_a = inst_tfree_term(&derivable(&fvar("A")).unwrap());
        let var0 = inst_tfree_term(&p_var_lit(0));
        let expected = covalence_core::subst::subst_free(&der_a, "A", &var0)
            .not()
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    /// `consistency_app` is the same theorem bridged to applied-constant form
    /// (`¬(prop.derivable (prop.var 0))`), still genuine.
    #[test]
    fn consistency_app_is_genuine() {
        let thm = consistency_app().expect("consistency_app");
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let var0_app = inst_tfree_term(&Term::app(var_fn(), Term::nat_lit(0u32)));
        let applied = inst_tfree_term(&Term::app(derivable_fn(), var0_app));
        assert_eq!(thm.concl(), &applied.not().unwrap());
    }

    /// `prop_induction` rejects a bogus axiom case (its conclusion is not the
    /// demanded clause) rather than fabricating an induction.
    #[test]
    fn prop_induction_rejects_a_bogus_case() {
        // pred := λA. ⟦A⟧ v  (the soundness predicate).
        let v = Term::free("v", Type::fun(nat(), bool_ty()));
        let pred = denote_pred(&v).unwrap();
        // A bogus axiom case that returns ⊢ T instead of `pred ⌜axiom_i⌝`.
        let bogus = prop_induction(
            &pred,
            |_i, _a, _b, _c| truth().eqt_intro().and_then(|t| t.eqt_elim()),
            |a, b| sound_mp_case(&v, &pred, a, b),
        );
        // The conjunction/`imp_elim` against the real `Closed pred` shape fails.
        assert!(bogus.is_err(), "a bogus case must not fabricate an induction");
    }

    /// The constructor λ-constants are well-typed and `(app prop.var n)`
    /// β-reduces to the reduced encoding `var n`.
    #[test]
    fn constructor_constants_reduce() {
        assert_eq!(var_fn().type_of().unwrap(), Type::fun(nat(), phi()));
        assert_eq!(imp_fn().type_of().unwrap(), Type::fun(phi(), Type::fun(phi(), phi())));
        let app = Term::app(var_fn(), Term::nat_lit(0u32));
        let nf = beta_nf(app).concl().as_eq().unwrap().1.clone();
        assert_eq!(nf, beta_nf(p_var_lit(0)).concl().as_eq().unwrap().1.clone());
    }
}

#[cfg(test)]
mod cov_tests {
    use super::*;

    /// `consistency` from `prop.cov` must match the Rust `consistency_app`
    /// conclusion, proved genuinely in the script layer.
    #[test]
    fn consistency_cov_matches_rust() {
        let thm = cov::consistency_cov();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(thm.concl(), consistency_app().unwrap().concl());
    }

    /// `axiom1_shape_refl` from `prop.cov` proves the script builds reified
    /// propositional syntax (a self-equality of a `prop.imp`/`prop.var` term).
    #[test]
    fn axiom1_shape_refl_cov_is_genuine() {
        let thm = cov::axiom1_shape_refl_cov();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // It is an `=` whose sides are the built formula.
        assert!(thm.concl().as_eq().is_some());
    }

    /// A downstream `.cov` script can `(#import prop)` and consume the ported
    /// metatheorem.
    #[test]
    fn downstream_script_imports_prop() {
        let src = r#"
            (#import core) (#open core)
            (#import prop) (#open prop)
            (#thm var0_not_derivable
              (#concl (not (app prop.derivable.bool (app prop.var.bool 0))))
              (#by (derive (consistency))))
        "#;
        let thms = crate::init::check_script(src).expect("downstream prop script checks");
        assert_eq!(thms.len(), 1);
        assert!(thms[0].thm.hyps().is_empty() && thms[0].thm.has_no_obs());
    }
}
