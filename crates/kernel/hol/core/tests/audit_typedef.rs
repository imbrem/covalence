//! Audit / edge-case suite for the conservative-extension primitives:
//!
//! - `Thm::define`              (fresh defined constants)
//! - `Thm::new_type_definition` (fresh subtypes + abs/rep bijection)
//! - `Thm::inst_tfree`          (type-variable instantiation)
//!
//! These are part of the TCB. They mint *fresh* constants / types and
//! must be **conservative**:
//!
//! - `define` must reject bodies with "phantom" free type variables
//!   (a tvar in the body interior that does not appear in the body's
//!   overall type) and must yield `Def ≡ body` with a *fresh* `Def`
//!   identity per call (two `define`s of the same name+body produce
//!   DISTINCT defs — so you cannot `trans`/`sym` two equations for
//!   "the same name" into `body1 ≡ body2`).
//! - `new_type_definition` must require a witness of shape `P x` with
//!   `P : α → bool`, reject malformed witnesses, propagate the
//!   witness's hypotheses to all three returned theorems, and produce
//!   `abs`/`rep` with fresh identity tied to the typedef.
//! - `inst_tfree` must substitute a tvar consistently across hyps +
//!   concl while preserving `Def`/`abs`/`rep` identity.
//!
//! Tests assert against ACTUAL behaviour. Genuine soundness concerns
//! are flagged with `// SUSPECT:` rather than a failing test.

use covalence_core::subst::close;
use covalence_core::{Term, TermKind, Thm, Type, TypeDef, TypeKind};

// ---------------------------------------------------------------------------
// Helpers — build the HOL connectives that the kernel uses internally
// (the `hol` module is `pub(crate)`, so we reconstruct the shapes here).
// ---------------------------------------------------------------------------

/// HOL `lhs = rhs : bool` — `App(App(Eq(α), lhs), rhs)` where α is the
/// type of `lhs`.
fn hol_eq(lhs: Term, rhs: Term) -> Term {
    let alpha = lhs.type_of().expect("hol_eq: lhs well-typed");
    Term::app(Term::app(Term::eq_op(alpha), lhs), rhs)
}

/// Decompose a HOL equation `App(App(Eq(_), l), r)` into `(l, r)`.
fn parse_hol_eq(t: &Term) -> Option<(Term, Term)> {
    let TermKind::App(f, r) = t.kind() else {
        return None;
    };
    let TermKind::App(eq, l) = f.kind() else {
        return None;
    };
    let TermKind::Eq(_) = eq.kind() else {
        return None;
    };
    Some((l.clone(), r.clone()))
}

/// Pull the (first) `TermKind::Def` leaf out of a term tree, returning
/// its `ptr_id` identity.
fn find_def_ptr(t: &Term) -> Option<usize> {
    match t.kind() {
        TermKind::Def(d) => Some(d.ptr_id()),
        TermKind::App(f, x) => find_def_ptr(f).or_else(|| find_def_ptr(x)),
        TermKind::Abs(_, b) => find_def_ptr(b),
        _ => None,
    }
}

/// Build a witness theorem `P x ⊢ P x` where `P = λx:α. body_bool` and
/// `x = Free("x", α)`. The hypotheses propagate to typedef theorems.
fn witness_for(alpha: Type, body_bool: Term) -> Thm {
    let p = Term::abs(alpha.clone(), close(&body_bool, "x"));
    let x = Term::free("x", alpha);
    Thm::assume(Term::app(p, x)).expect("assume P x")
}

// ===========================================================================
// define — happy path
// ===========================================================================

#[test]
fn define_yields_def_eq_body() {
    let body = Term::nat_lit(7u32);
    let thm = Thm::define("seven", body.clone()).expect("define seven");

    // No hypotheses — a definition is unconditional.
    assert!(thm.hyps().is_empty());

    // Conclusion is a HOL equation Def ≡ body.
    let (l, r) = parse_hol_eq(thm.concl()).expect("conclusion is HOL =");

    // lhs is a Def leaf.
    let TermKind::Def(d) = l.kind() else {
        panic!("define lhs is not a Def leaf: {l}");
    };
    assert_eq!(d.name(), "seven");

    // rhs is exactly the body.
    assert_eq!(&r, &body);
    // The Def's body recovers the original body.
    assert_eq!(d.body(), body);
}

#[test]
fn define_def_instance_type_is_body_type() {
    let body = Term::nat_lit(0u32);
    let thm = Thm::define("z", body.clone()).expect("define");
    let (l, _) = parse_hol_eq(thm.concl()).unwrap();
    let TermKind::Def(d) = l.kind() else { panic!() };
    assert_eq!(d.instance_type(), &Type::nat());
}

#[test]
fn define_accepts_polymorphic_body() {
    // λx:α. x  :  α → α  — the tvar α appears in the body type, so it
    // is NOT phantom. This must be accepted.
    let alpha = Type::tfree("a");
    let id = Term::abs(alpha.clone(), Term::bound(0));
    let thm = Thm::define("id", id.clone()).expect("define id : a -> a");
    let (l, r) = parse_hol_eq(thm.concl()).unwrap();
    assert_eq!(&r, &id);
    let TermKind::Def(d) = l.kind() else { panic!() };
    assert_eq!(d.instance_type(), &Type::fun(alpha.clone(), alpha));
}

#[test]
fn define_polymorphic_over_spec_type_instantiates_without_panic() {
    // A `Def` whose body type is a `Spec` carrying a tvar (`set 'a`).
    // After `inst_tfree 'a := nat`, `Def::instance_type()` is `set nat`
    // ≠ the recorded `body_type` `set 'a`, so `Def::body()` must recover
    // the substitution via `match_types(set 'a, set nat)`. Before
    // `match_types` learned the `Spec` arm this panicked; forcing
    // `Def::body()` below must now succeed.
    let alpha = Type::tfree("a");
    let set_a = covalence_core::defs::set(alpha.clone());
    let body = Term::free("s", set_a.clone());
    let thm = Thm::define("poly_set", body).expect("define over set 'a");
    // body_type is set 'a; no instantiation yet.
    let inst = thm
        .inst_tfree("a", Type::nat())
        .expect("inst_tfree set spec");
    // The Def now reads at the instantiated type.
    let (l, _r) = parse_hol_eq(inst.concl()).unwrap();
    let TermKind::Def(d) = l.kind() else {
        panic!("lhs not a Def")
    };
    // Forces Def::body() -> match_types(set 'a, set nat).
    let _ = d.body();
    assert_eq!(d.instance_type(), &covalence_core::defs::set(Type::nat()));
}

// ===========================================================================
// define — freshness / non-conservativity guard
// ===========================================================================

#[test]
fn define_two_calls_same_name_body_distinct_identity() {
    let body = Term::nat_lit(42u32);
    let a = Thm::define("dup", body.clone()).expect("define a");
    let b = Thm::define("dup", body.clone()).expect("define b");

    let (la, _) = parse_hol_eq(a.concl()).unwrap();
    let (lb, _) = parse_hol_eq(b.concl()).unwrap();

    let pa = find_def_ptr(&la).expect("def a");
    let pb = find_def_ptr(&lb).expect("def b");

    // CRITICAL conservativity property: same name + same body, but the
    // two Defs are DISTINCT symbols. Otherwise a user could derive
    // body1 ≡ body2 by gluing two definitional equations.
    assert_ne!(
        pa, pb,
        "two define calls with same name+body must mint distinct Def identities"
    );

    // And they are NOT structurally equal terms either.
    assert_ne!(la, lb, "the two Def leaves must not compare equal");
}

#[test]
fn define_distinct_defs_have_distinct_terms_even_via_clone_of_body() {
    // Re-using the *same* Arc body term across two define calls still
    // gives distinct Defs (freshness is per-call, not per-body-Arc).
    let shared = Term::app(Term::eq_op(Type::nat()), Term::nat_lit(1u32));
    // shared : nat -> bool ; fine as a body.
    let a = Thm::define("f", shared.clone()).unwrap();
    let b = Thm::define("f", shared.clone()).unwrap();
    let (la, _) = parse_hol_eq(a.concl()).unwrap();
    let (lb, _) = parse_hol_eq(b.concl()).unwrap();
    assert_ne!(find_def_ptr(&la).unwrap(), find_def_ptr(&lb).unwrap());
}

// ===========================================================================
// define — phantom tvar rejection (the conservativity check)
// ===========================================================================

#[test]
fn define_rejects_phantom_tvar_in_abs_annotation() {
    // The phantom check DOES catch tvars carried by an `Abs` binder
    // annotation (these are collected by `collect_term_tvars`).
    //
    // body = λp:b. 0  : b -> nat. Here b IS in the type, so to make it
    // phantom we wrap so the binder type is lost from the result type.
    // Use: (λp:b. 0) applied to (some : b)  →  : nat, interior has b
    // via the binder annotation AND the argument's free var type.
    let p_lam = Term::abs(Type::tfree("b"), Term::nat_lit(0u32)); // b -> nat
    let arg = Term::free("y", Type::tfree("b")); // : b
    let body = Term::app(p_lam, arg); // : nat ; interior mentions tvar b
    let body_ty = body.type_of().expect("body well-typed");
    assert_eq!(body_ty, Type::nat());
    assert!(body_ty.free_tvars().is_empty(), "b is phantom in the type");

    // collect_term_tvars sees b via the Abs annotation + the Free arg,
    // so this IS rejected.
    let err = Thm::define("phantom", body).expect_err("phantom tvar must be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("free type variable") && msg.contains("\"b\""),
        "expected DefPhantomTFree mentioning b, got: {msg}"
    );
}

// Regression: `define`'s phantom-tvar conservativity check must descend
// into the type arguments carried by the `Eq(α)` / `Select(α)` /
// `Spec`/`SpecAbs`/`SpecRep` leaves. A tvar appearing *only* inside such
// a leaf — and absent from the body's overall type — is a phantom tvar:
// it would be invisible to `Def::body`'s `match_types` (which only sees
// `body_type`), so `inst_tfree` could specialise the `Def ≡ body`
// equation's RHS while the LHS `Def`'s recoverable body stayed pinned,
// breaking the `Def ≡ body` invariant.
//
// `λx:nat. (eq[b] = eq[b])` has overall type `nat → bool` (b vanishes)
// yet pins its interior `Eq` leaves at `b`. `define` must REJECT it with
// `DefPhantomTFree`. (Originally surfaced by the TCB audit; the gap was
// that `collect_term_tvars` skipped these leaves — now fixed.)
#[test]
fn phantom_tvar_via_eq_leaf_is_rejected() {
    let eqb = Term::eq_op(Type::tfree("b")); // : b -> b -> bool
    let inner = hol_eq(eqb.clone(), eqb); // (eqb = eqb) : bool ; carries tvar b
    let body = Term::abs(Type::nat(), inner); // : nat -> bool, interior has tvar b
    let body_ty = body.type_of().expect("body well-typed");
    assert_eq!(body_ty, Type::fun(Type::nat(), Type::bool()));
    assert!(
        body_ty.free_tvars().is_empty(),
        "body type has no tvars — b is phantom"
    );

    // The phantom tvar `b` (interior to the `Eq` leaves only) is caught.
    let err = Thm::define("phantom_eq", body)
        .expect_err("phantom tvar via Eq leaf must be rejected by define");
    assert!(
        matches!(err, covalence_core::Error::DefPhantomTFree { .. }),
        "expected DefPhantomTFree, got {err:?}"
    );
}

// A `Select(α)` (Hilbert ε) phantom tvar is likewise rejected — this is
// the soundness-critical case, since `ε` at different element types
// denotes genuinely different values.
#[test]
fn phantom_tvar_via_select_leaf_is_rejected() {
    // λx:nat. ε(λy:b. T) = ε(λy:b. T)  — overall type nat → bool, but the
    // ε leaves are pinned at the phantom tvar `b`.
    let sel = Term::app(
        Term::select_op(Type::tfree("b")),
        Term::abs(Type::tfree("b"), Term::bool_lit(true)),
    ); // : b
    let inner = hol_eq(sel.clone(), sel); // (ε = ε) : bool, carries b
    let body = Term::abs(Type::nat(), inner);
    assert!(body.type_of().unwrap().free_tvars().is_empty());
    let err = Thm::define("phantom_select", body)
        .expect_err("phantom tvar via Select leaf must be rejected");
    assert!(matches!(err, covalence_core::Error::DefPhantomTFree { .. }));
}

// Sanity: a tvar that DOES appear in the overall type is still accepted
// even when it also appears inside an `Eq` leaf (no false positive).
#[test]
fn non_phantom_tvar_in_eq_leaf_is_accepted() {
    // λx:a. (x = x) : a → bool — `a` is in the domain, not phantom.
    let x = Term::free("x", Type::tfree("a"));
    let body = Term::abs(Type::tfree("a"), close(&hol_eq(x.clone(), x), "x"));
    let _ = Thm::define("eq_refl_poly", body).expect("non-phantom tvar accepted");
}

#[test]
fn define_accepts_when_tvar_in_type() {
    // Contrast: a body whose tvar IS reflected in its type is fine.
    // λp:b. T  : b -> bool  (b appears in the type).
    let body = Term::abs(Type::tfree("b"), Term::bool_lit(true));
    let ty = body.type_of().unwrap();
    assert_eq!(ty, Type::fun(Type::tfree("b"), Type::bool()));
    Thm::define("kT", body).expect("non-phantom tvar accepted");
}

// ===========================================================================
// define — ill-typed body rejection
// ===========================================================================

#[test]
fn define_rejects_open_body() {
    // A dangling Bound index is not closed — type_of fails.
    let body = Term::bound(0);
    assert!(Thm::define("bad", body).is_err());
}

// ===========================================================================
// new_type_definition — happy path
// ===========================================================================

/// A monomorphic witness over α = nat with predicate `λx. x = x`.
fn nat_witness() -> Thm {
    let x = Term::free("x", Type::nat());
    witness_for(Type::nat(), hol_eq(x.clone(), x))
}

#[test]
fn typedef_happy_path_shapes() {
    let td: TypeDef =
        Thm::new_type_definition("tau", "myabs", "myrep", nat_witness()).expect("typedef over nat");

    // tau is a fresh FreshTyCon with no tvar args (α = nat is closed).
    let TypeKind::FreshTyCon(tau_leaf) = td.tau.kind() else {
        panic!("tau is not a FreshTyCon: {:?}", td.tau.kind());
    };
    assert!(
        tau_leaf.args().iter().next().is_none(),
        "nat has no tvars, tau is nullary"
    );
    assert!(td.tvars.is_empty());

    // abs : nat -> tau ; rep : tau -> nat.
    assert_eq!(
        td.abs.type_of().unwrap(),
        Type::fun(Type::nat(), td.tau.clone())
    );
    assert_eq!(
        td.rep.type_of().unwrap(),
        Type::fun(td.tau.clone(), Type::nat())
    );

    // abs / rep are FreshConst leaves.
    assert!(matches!(td.abs.kind(), TermKind::FreshConst(..)));
    assert!(matches!(td.rep.kind(), TermKind::FreshConst(..)));
}

#[test]
fn typedef_abs_rep_theorem_is_forall_eq() {
    let td = Thm::new_type_definition("t", "a", "r", nat_witness()).unwrap();

    // abs_rep : ⊢ ∀a:τ. abs (rep a) = a
    // Conclusion is `App(forall_spec, λa. abs(rep a) = a)`.
    let concl = td.abs_rep.concl();
    let TermKind::App(forall_head, lam) = concl.kind() else {
        panic!("abs_rep concl is not an application: {concl}");
    };
    // The head is the `forall` spec leaf.
    assert!(
        matches!(forall_head.kind(), TermKind::Spec(..)),
        "forall head should be a Spec leaf, got {forall_head}"
    );
    // The argument is a lambda over τ whose body is a HOL equation.
    let TermKind::Abs(binder_ty, eqbody) = lam.kind() else {
        panic!("forall arg is not a lambda: {lam}");
    };
    assert_eq!(binder_ty, &td.tau);
    let (l, r) = parse_hol_eq(eqbody).expect("body is HOL eq");
    // l = abs (rep (Bound 0)) ; r = Bound 0.
    assert_eq!(r.kind(), &TermKind::Bound(0));
    // l is abs applied to (rep applied to Bound 0).
    let TermKind::App(absf, repapp) = l.kind() else {
        panic!("eq lhs not app: {l}");
    };
    assert_eq!(*absf, td.abs);
    let TermKind::App(repf, inner) = repapp.kind() else {
        panic!("inner not app: {repapp}");
    };
    assert_eq!(*repf, td.rep);
    assert_eq!(inner.kind(), &TermKind::Bound(0));
}

#[test]
fn typedef_fwd_and_back_theorems_are_forall_imp() {
    let td = Thm::new_type_definition("t", "a", "r", nat_witness()).unwrap();

    for thm in [&td.rep_abs_fwd, &td.rep_abs_back] {
        let concl = thm.concl();
        // ∀r:α. (... ⟹ ...)
        let TermKind::App(forall_head, lam) = concl.kind() else {
            panic!("not forall app: {concl}");
        };
        assert!(matches!(forall_head.kind(), TermKind::Spec(..)));
        let TermKind::Abs(binder_ty, body) = lam.kind() else {
            panic!("forall arg not lambda: {lam}");
        };
        // binder over α = nat.
        assert_eq!(binder_ty, &Type::nat());
        // body is an implication: App(App(imp, ante), conseq).
        let TermKind::App(imp_app, _conseq) = body.kind() else {
            panic!("body not app: {body}");
        };
        let TermKind::App(imp_head, _ante) = imp_app.kind() else {
            panic!("imp not app: {imp_app}");
        };
        assert!(
            matches!(imp_head.kind(), TermKind::Spec(..)),
            "imp head should be Spec, got {imp_head}"
        );
    }
}

#[test]
fn typedef_propagates_witness_hyps() {
    // Witness P x ⊢ P x — one hypothesis. It must flow into all three
    // emitted theorems.
    let w = nat_witness();
    assert_eq!(w.hyps().len(), 1, "witness has its assumption as hyp");
    let hyp = w.hyps().iter().next().unwrap().clone();

    let td = Thm::new_type_definition("t", "a", "r", w).unwrap();

    for thm in [&td.abs_rep, &td.rep_abs_fwd, &td.rep_abs_back] {
        assert_eq!(thm.hyps().len(), 1, "each theorem carries the witness hyp");
        assert!(
            thm.hyps().contains(&hyp),
            "witness hyp not propagated to theorem: {}",
            thm.concl()
        );
    }
}

#[test]
fn typedef_polymorphic_witness_tracks_tvars() {
    // Witness over α = `c` (a tvar). τ becomes parametric in [c].
    let alpha = Type::tfree("c");
    let x = Term::free("x", alpha.clone());
    let w = witness_for(alpha.clone(), hol_eq(x.clone(), x));

    let td = Thm::new_type_definition("t", "a", "r", w).unwrap();
    assert_eq!(td.tvars, vec![smol_str::SmolStr::new("c")]);

    // tau is parametric: FreshTyCon with one arg = tfree c.
    let TypeKind::FreshTyCon(tau_leaf) = td.tau.kind() else {
        panic!("tau not FreshTyCon");
    };
    let argv: Vec<Type> = tau_leaf.args().iter().cloned().collect();
    assert_eq!(argv, vec![Type::tfree("c")]);

    // abs : c -> tau.
    assert_eq!(td.abs.type_of().unwrap(), Type::fun(alpha, td.tau.clone()));
}

#[test]
fn typedef_two_calls_distinct_tau_identity() {
    let a = Thm::new_type_definition("t", "a", "r", nat_witness()).unwrap();
    let b = Thm::new_type_definition("t", "a", "r", nat_witness()).unwrap();

    // Two typedefs over the same α must produce DISTINCT τ — otherwise
    // their abs/rep would be confusable and the extension non-conservative.
    let TypeKind::FreshTyCon(la) = a.tau.kind() else {
        panic!()
    };
    let TypeKind::FreshTyCon(lb) = b.tau.kind() else {
        panic!()
    };
    let (ia, ib) = (la.id(), lb.id());
    assert_ne!(
        ia.ptr_id(),
        ib.ptr_id(),
        "distinct typedefs must mint distinct tau tokens"
    );
    assert_ne!(ia, ib, "FreshId equality is pointer identity");
    assert_ne!(a.tau, b.tau, "the two tau types must not compare equal");

    // abs leaves are distinct too.
    let TermKind::FreshConst(la) = a.abs.kind() else {
        panic!()
    };
    let TermKind::FreshConst(lb) = b.abs.kind() else {
        panic!()
    };
    let (absa, absb) = (la.id(), lb.id());
    assert_ne!(absa.ptr_id(), absb.ptr_id(), "distinct abs identities");
    assert_ne!(a.abs, b.abs, "the two abs terms must not compare equal");
}

#[test]
fn typedef_abs_and_rep_have_distinct_identity() {
    let td = Thm::new_type_definition("t", "a", "r", nat_witness()).unwrap();
    let TermKind::FreshConst(la) = td.abs.kind() else {
        panic!()
    };
    let TermKind::FreshConst(lr) = td.rep.kind() else {
        panic!()
    };
    let (abs, rep) = (la.id(), lr.id());
    assert_ne!(
        abs.ptr_id(),
        rep.ptr_id(),
        "abs and rep must be distinct constants"
    );
}

// ===========================================================================
// new_type_definition — malformed witness rejection
// ===========================================================================

#[test]
fn typedef_rejects_non_application_witness() {
    // Witness conclusion is not `P x` — it's a bare equation T = T.
    let bad = Thm::refl(Term::bool_lit(true)).unwrap();
    // refl conclusion is App(App(Eq,_),_), which IS an application, so
    // it would decompose as P x with P = (Eq T), x = T. That would be
    // accepted shape-wise but P : bool -> bool, x : bool — let's
    // instead use a witness whose concl is a genuine non-application.
    let _ = bad;

    // A reflexive equation on a function: still an App. To get a
    // genuinely non-App conclusion we use a bool literal directly is
    // impossible (must be bool & an App for P x). Use `assume(Bool)`:
    // concl = T, kind = Bool(true), NOT an App.
    let w = Thm::assume(Term::bool_lit(true)).expect("assume T");
    assert!(matches!(w.concl().kind(), TermKind::Bool(true)));
    let err =
        Thm::new_type_definition("t", "a", "r", w).expect_err("non-application witness rejected");
    assert!(
        format!("{err}").contains("witness conclusion must have shape"),
        "expected BadTypeDefWitness, got {err}"
    );
}

#[test]
fn typedef_rejects_predicate_not_alpha_to_bool() {
    // Witness `P x` where P : nat -> nat (codomain not bool).
    // P = succ-like: λx:nat. x  has type nat -> nat.
    // Build P x as an application that type-checks but P's codomain is nat.
    let p = Term::abs(Type::nat(), Term::bound(0)); // λx:nat. x : nat -> nat
    let x = Term::free("x", Type::nat());
    let px = Term::app(p, x); // : nat
    // px : nat, not bool — Thm::assume requires bool. So we can't even
    // assume it. Confirm that, then build a witness Thm a different way
    // to drive the codomain check directly.
    assert!(Thm::assume(px).is_err(), "P x must be bool to be assumable");

    // Drive the P:α→bool check via a witness whose concl IS bool but
    // whose head P has a non-bool codomain. Application `(eq[nat] n) m`
    // is bool, with P = (eq[nat] n) : nat -> bool — that's VALID.
    // To violate, we need head not α→bool. Use a curried app:
    //   head = (λx:nat. λy:nat. x=y)  applied to one arg -> nat -> bool? no.
    // It is hard to make a bool-typed `P x` whose P is not α→bool, since
    // for `P x : bool` and `x : α`, P must be α→bool by typing. So this
    // rejection path (NotFunction / codomain-not-bool) is effectively
    // unreachable for a well-typed bool witness — the type system
    // already forces P : α→bool. We document that here.
}

#[test]
fn typedef_well_typed_bool_app_witness_forces_predicate_shape() {
    // Demonstrates the observation above: ANY assumable witness `P x`
    // (bool-typed application) automatically has P : α → bool, so the
    // explicit kernel checks are belt-and-suspenders. A valid eq-headed
    // witness is accepted.
    let n = Term::free("n", Type::nat());
    let m = Term::free("m", Type::nat());
    // (eq[nat] n) m : bool ; head P = (eq[nat] n) : nat -> bool.
    let px = Term::app(Term::app(Term::eq_op(Type::nat()), n), m);
    let w = Thm::assume(px).expect("assume n = m");
    let td = Thm::new_type_definition("t", "a", "r", w).expect("accepted");
    // α inferred from x = m : nat.
    assert_eq!(td.abs.type_of().unwrap(), Type::fun(Type::nat(), td.tau));
}

// ===========================================================================
// inst_tfree — type-variable substitution
// ===========================================================================

#[test]
fn inst_tfree_substitutes_concl_and_hyps() {
    // Theorem with a hypothesis and conclusion both mentioning tvar `a`.
    //   hyp:   (x:a) = (x:a)
    //   concl: (x:a) = (x:a)   (assume gives concl = hyp)
    let xa = Term::free("x", Type::tfree("a"));
    let thm = Thm::assume(hol_eq(xa.clone(), xa.clone())).expect("assume x=x : a");
    assert_eq!(thm.hyps().len(), 1);

    let inst = thm.inst_tfree("a", Type::nat()).expect("inst a := nat");

    // Conclusion now over nat.
    let (l, _r) = parse_hol_eq(inst.concl()).unwrap();
    assert_eq!(l.type_of().unwrap(), Type::nat());

    // Hypothesis substituted too.
    let hyp = inst.hyps().iter().next().unwrap();
    let (hl, _) = parse_hol_eq(hyp).unwrap();
    assert_eq!(hl.type_of().unwrap(), Type::nat());

    // The instantiated hyp matches the instantiated concl (assume invariant).
    assert_eq!(inst.hyps().iter().next().unwrap(), inst.concl());
}

#[test]
fn inst_tfree_noop_for_absent_tvar() {
    let xa = Term::free("x", Type::tfree("a"));
    let thm = Thm::assume(hol_eq(xa.clone(), xa)).unwrap();
    let inst = thm.clone().inst_tfree("z", Type::nat()).expect("inst z");
    // Substituting an absent tvar leaves the theorem unchanged.
    assert_eq!(inst.concl(), thm.concl());
}

#[test]
fn inst_tfree_preserves_def_identity() {
    // A definitional equation whose Def is polymorphic; inst_tfree must
    // update instance_type WITHOUT changing the Def's stable ptr_id.
    let alpha = Type::tfree("a");
    let id_body = Term::abs(alpha.clone(), Term::bound(0)); // λx:a. x : a -> a
    let def_thm = Thm::define("idf", id_body).expect("define idf");
    let before = find_def_ptr(def_thm.concl()).expect("def ptr before");

    let inst = def_thm.inst_tfree("a", Type::nat()).expect("inst a := nat");
    let after = find_def_ptr(inst.concl()).expect("def ptr after");

    assert_eq!(
        before, after,
        "inst_tfree must preserve the Def's original Arc identity"
    );

    // The instance_type updated to nat -> nat.
    let (l, _) = parse_hol_eq(inst.concl()).unwrap();
    let TermKind::Def(d) = l.kind() else { panic!() };
    assert_eq!(d.instance_type(), &Type::fun(Type::nat(), Type::nat()));
}

#[test]
fn inst_tfree_preserves_abs_rep_identity() {
    // A polymorphic typedef over tvar c; instantiating c must preserve
    // abs/rep FreshId identity (they substitute the type, not the token).
    let alpha = Type::tfree("c");
    let x = Term::free("x", alpha.clone());
    let w = witness_for(alpha.clone(), hol_eq(x.clone(), x));
    let td = Thm::new_type_definition("t", "a", "r", w).unwrap();

    let TermKind::FreshConst(abs_before) = td.abs.kind() else {
        panic!()
    };
    let abs_id = abs_before.id().ptr_id();

    // The abs_rep theorem mentions abs/rep; instantiate c := nat.
    let inst = td
        .abs_rep
        .clone()
        .inst_tfree("c", Type::nat())
        .expect("inst c");

    // Find the abs FreshConst leaf in the instantiated conclusion and
    // compare identity.
    fn first_fresh_id(t: &Term) -> Option<usize> {
        match t.kind() {
            TermKind::FreshConst(leaf) => Some(leaf.id().ptr_id()),
            TermKind::App(f, x) => first_fresh_id(f).or_else(|| first_fresh_id(x)),
            TermKind::Abs(_, b) => first_fresh_id(b),
            _ => None,
        }
    }
    let after = first_fresh_id(inst.concl()).expect("fresh const in instantiated concl");
    assert_eq!(
        abs_id, after,
        "inst_tfree must preserve abs/rep FreshId Arc identity"
    );
}

#[test]
fn inst_tfree_into_typedef_concl_retypes_binder() {
    // Instantiating the polymorphic abs_rep theorem retypes the bound
    // variable from c to nat.
    let alpha = Type::tfree("c");
    let x = Term::free("x", alpha.clone());
    let w = witness_for(alpha.clone(), hol_eq(x.clone(), x));
    let td = Thm::new_type_definition("t", "a", "r", w).unwrap();

    let inst = td
        .abs_rep
        .inst_tfree("c", Type::nat())
        .expect("inst c := nat");
    // ∀a:τ[nat]. abs (rep a) = a — the τ in the binder now has nat arg.
    let TermKind::App(_, lam) = inst.concl().kind() else {
        panic!()
    };
    let TermKind::Abs(binder_ty, _) = lam.kind() else {
        panic!()
    };
    let TypeKind::FreshTyCon(leaf) = binder_ty.kind() else {
        panic!("binder type not FreshTyCon: {binder_ty}");
    };
    let argv: Vec<Type> = leaf.args().iter().cloned().collect();
    assert_eq!(argv, vec![Type::nat()], "tau arg substituted to nat");
}
