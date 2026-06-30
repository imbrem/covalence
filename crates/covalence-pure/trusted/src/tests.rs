//! Stage-0 milestone tests, exercised through the public kernel API (the calculus
//! + gated injectors; field reads via the `lhs`/`rhs`/`lang` accessors).

use std::any::TypeId;

use crate::*;

// ---- Auxiliary test languages ----

/// A language admitting nothing — used to check the gates actually reject.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Empty;
impl Language for Empty {
    fn admits(&self, _rule: TypeId) -> bool {
        false
    }
    fn extends(&self, _parent: TypeId) -> bool {
        false
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

/// A child language that directly extends `()` and adds one axiom rule, `MyAx`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Cov2;

/// A toy axiom rule: `⊢ true` (i.e. `Val(true) = ⊤`).
struct MyAx;
impl Rule<Cov2> for MyAx {
    type Lhs = Val<bool>;
    type Rhs = True;
    fn conclude(self) -> Result<(Val<bool>, True), Error> {
        Ok((Val(true), True))
    }
}

// NOTE: `extends` is left empty in this hand-written child manifest — embedding a
// parent's `Manifest` by value in a `const` is the deferred const-eval wrinkle
// (the `language!` macro's job). The authoritative gate for `lift` is the
// `extends()` *function* below, which correctly names `()` as a direct parent.
static COV2_MANIFEST: Manifest = Manifest {
    ty: TypeId::of::<Cov2>(),
    extends: &[],
    admits: &[RuleRecord {
        ty: TypeId::of::<MyAx>(),
        metadata: RuleMeta,
    }],
    metadata: LangMeta,
};

impl Language for Cov2 {
    fn admits(&self, rule: TypeId) -> bool {
        rule == TypeId::of::<MyAx>() || ().admits(rule)
    }
    fn extends(&self, parent: TypeId) -> bool {
        parent == TypeId::of::<()>()
    }
    const MANIFEST: Option<&'static Manifest> = Some(&COV2_MANIFEST);
}

// ---- Milestone 1: a cong / trans chain establishing an equation in `()` ----

#[test]
fn cong_trans_chain() {
    // refl: false = false
    let base: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(false), ());
    // congruence under `Not`: ¬false = ¬false  (App<Not, Val<bool>>)
    let c1 = base.cong_app(Not);
    // a second proof of the same equation, to transit through
    let c2: Eqn<App<Not, Val<bool>>, App<Not, Val<bool>>, ()> = Eqn::refl(App(Not, Val(false)), ());
    // trans must match the middle term via trusted structural equality
    let chained = c1.trans(c2).expect("middle terms match");
    assert_eq!(chained.lhs(), &App(Not, Val(false)));
    assert_eq!(chained.rhs(), &App(Not, Val(false)));
}

#[test]
fn trans_rejects_mismatched_middle() {
    let a: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(true), ());
    // middle term is `Val(false)`, which does not match `a`'s rhs `Val(true)`
    let b: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(false), ());
    assert_eq!(a.trans(b).unwrap_err(), Error::TransMismatch);
}

#[test]
fn cong_pair_combines() {
    let l: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(true), ());
    let r: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(false), ());
    let p = l.cong_pair(r).expect("same language");
    assert_eq!(p.lhs(), &(Val(true), Val(false)));
}

// ---- Milestone 2: a propositional / boolean law ----

#[test]
fn boolean_law_and_true_true() {
    // canon evaluates `And` on the ground value `(true, true)` to `true`.
    // Boolean computation lives in `Bool` now — `()` is empty.
    let law = canon(And, (true, true), Bool).expect("Bool admits And");
    assert_eq!(law.rhs(), &Val(true));
    assert_eq!(law.lhs(), &App(And, Val((true, true))));

    let f = canon(And, (true, false), Bool).expect("Bool admits And");
    assert_eq!(f.rhs(), &Val(false));

    // Or / Not / Imp likewise:
    assert_eq!(canon(Or, (false, true), Bool).unwrap().rhs(), &Val(true));
    assert_eq!(canon(Not, true, Bool).unwrap().rhs(), &Val(false));
    assert_eq!(canon(Imp, (true, false), Bool).unwrap().rhs(), &Val(false));
}

#[test]
fn of_eq_leaf_equality() {
    // `of_eq` is UNGATED — leaf equality is intrinsic to a sort. It works in the
    // empty base `()`, with no admits involved.
    let e = of_eq(true, true, ()).expect("true == true");
    assert_eq!(e.lhs(), &Val(true));
    // `==`-unequal values give `None` (no equation):
    assert!(of_eq(true, false, ()).is_none());
}

// ---- Gating: the gates actually reject ----

#[test]
fn canon_gated_by_admits() {
    let err = canon(And, (true, true), Empty).unwrap_err();
    assert_eq!(err, Error::NotAdmitted(TypeId::of::<And>()));
    // `()` is empty too, so it does not admit the connectives:
    assert_eq!(
        canon(And, (true, true), ()).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<And>())
    );
}

// ---- apply + lift ----

#[test]
fn apply_axiom_then_inspect() {
    let thm: Thm<Val<bool>, Cov2> = apply(Cov2, MyAx).expect("Cov2 admits MyAx");
    assert_eq!(thm.lhs(), &Val(true));
    assert_eq!(thm.rhs(), &True);
}

#[test]
fn apply_gated() {
    // `()` does not admit `MyAx`.
    struct AxForUnit;
    impl Rule<()> for AxForUnit {
        type Lhs = Val<bool>;
        type Rhs = True;
        fn conclude(self) -> Result<(Val<bool>, True), Error> {
            Ok((Val(true), True))
        }
    }
    let err = apply((), AxForUnit).unwrap_err();
    assert_eq!(err, Error::NotAdmitted(TypeId::of::<AxForUnit>()));
}

/// Regression for the audit's `apply`-forgery hole: a downstream rule whose
/// `conclude` returns a FALSE equation (`⊢ False`) cannot mint, because `apply`
/// now gates on the rule's OWN `TypeId` — which `()` does not admit — and the
/// orphan rule blocks `impl Rule<()> for <an admitted framework marker>`. There is
/// no `Id` tag to borrow an admitted identity through.
#[test]
fn apply_cannot_forge_false() {
    struct Forge;
    impl Rule<()> for Forge {
        type Lhs = False; // ⊢ False = ⊤ would be catastrophic
        type Rhs = True;
        fn conclude(self) -> Result<(False, True), Error> {
            Ok((False, True))
        }
    }
    // The gate keys on TypeId::of::<Forge>(), which () never admits.
    assert_eq!(
        apply((), Forge).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<Forge>())
    );
}

#[test]
fn lift_one_layer() {
    let e: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(true), ());
    let up = e.lift(Cov2).expect("Cov2 extends ()");
    assert_eq!(up.lang(), &Cov2);
    assert_eq!(up.lhs(), &Val(true));
}

#[test]
fn lift_rejects_non_extender() {
    let e: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(true), ());
    // Empty does not extend ()
    assert_eq!(
        e.lift(Empty).unwrap_err(),
        Error::NotExtended(TypeId::of::<()>())
    );
}

// ---- Milestone 3: golden-ish check of `<() as Language>::MANIFEST` ----

#[test]
fn unit_manifest_is_empty() {
    // `()` is the trivial base: empty manifest, admits NOTHING. The equality
    // calculus (refl/sym/trans/cong) is ungated `Eqn` methods, not manifest rules.
    let m = <() as Language>::MANIFEST.expect("base has a static manifest");
    assert_eq!(m.ty, TypeId::of::<()>());
    assert!(m.extends.is_empty(), "base has no parents");
    assert!(m.admits.is_empty(), "() admits no gated rules");
    assert!(!().admits(TypeId::of::<And>()), "() admits nothing");
}

#[test]
fn bool_manifest_is_as_declared() {
    let m = <Bool as Language>::MANIFEST.expect("Bool has a static manifest");
    assert_eq!(m.ty, TypeId::of::<Bool>());

    let expected = [
        TypeId::of::<And>(),
        TypeId::of::<Or>(),
        TypeId::of::<Imp>(),
        TypeId::of::<Not>(),
    ];
    let got: Vec<TypeId> = m.admits.iter().map(|r| r.ty).collect();
    assert_eq!(
        got, expected,
        "Bool rule set must match the declared manifest"
    );

    // The gate agrees with the manifest it is derived from:
    for ty in expected {
        assert!(Bool.admits(ty), "admits must accept every manifest rule");
    }
    assert!(
        !Bool.admits(TypeId::of::<MyAx>()),
        "admits must reject out-of-tree rules"
    );
    // Bool inherits the trivial base `()`:
    assert!(Bool.extends(TypeId::of::<()>()), "Bool extends ()");
}

// ---- dyn expression: structural equality works behind a trait object ----

#[test]
fn derive_eq_is_structural_equality() {
    // `derive(Eq)` on the expression shapes IS the structural equality `trans`
    // uses — nested `App`/`Val` compare componentwise.
    let a = App(And, (Val(true), App(Not, Val(false))));
    let b = App(And, (Val(true), App(Not, Val(false))));
    let c = App(And, (Val(true), App(Not, Val(true))));
    assert_eq!(a, b);
    assert_ne!(a, c);
}

#[test]
fn dyn_expr_is_constructible() {
    // A dynamic expression is still a genuine `Expr` (sealed) — you can build and
    // hold it; it is just not `Eq`, so it cannot be a `trans` middle term.
    let _d: Box<dyn Expr<Ty = bool>> = Box::new(App(Not, Val(true)));
}
