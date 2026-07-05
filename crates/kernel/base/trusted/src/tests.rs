//! Kernel tests, exercised through the public API (the `Thm` calculus + gated
//! injectors + bool theory; reads via `prop`/`lhs`/`rhs`/`lang`).

use std::any::TypeId;
use std::rc::Rc;
use std::sync::Arc;

use crate::*;

// ============================ test languages ============================

/// Admits nothing, unions only with itself — checks the gates reject.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Empty;
impl Language for Empty {
    fn admits(&self, _: TypeId) -> bool {
        false
    }
    fn extends(&self, _: TypeId) -> bool {
        false
    }
    fn union(self, _: Self) -> Option<Self> {
        Some(self)
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

/// A hypothesis-bitset context: `union` is bitwise-OR (always succeeds), so two
/// theorems under different hypotheses combine.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Ctx(u8);
impl Language for Ctx {
    fn admits(&self, _: TypeId) -> bool {
        false
    }
    fn extends(&self, _: TypeId) -> bool {
        false
    }
    fn union(self, other: Self) -> Option<Self> {
        Some(Ctx(self.0 | other.0))
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

/// A context that only unions with an *identical* value — checks `union` failure
/// propagates to `trans` as `LangMismatch`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Exact(u8);
impl Language for Exact {
    fn admits(&self, _: TypeId) -> bool {
        false
    }
    fn extends(&self, _: TypeId) -> bool {
        false
    }
    fn union(self, other: Self) -> Option<Self> {
        (self.0 == other.0).then_some(self)
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

/// A computational language: admits a `CanonRule` (`Flip`), a truth axiom, an
/// implication axiom, a candidate-checker, and a rewrite; directly extends `()`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Calc;

/// Boolean negation as a canonical-eval op (for `canon`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Flip;
impl Op for Flip {
    type In = bool;
    type Out = bool;
}
impl CanonRule for Flip {
    fn eval(&self, b: &bool) -> bool {
        !b
    }
}

/// An axiom `⊢ ⊤` (a non-equality conclusion, for `mp`).
struct TruthAx;
impl Rule<Calc> for TruthAx {
    type Input = ();
    type Concl = True;
    fn decide(self, _: (), _: &Calc) -> Result<True, Error> {
        Ok(True)
    }
}

/// An axiom `⊢ (⊤ ⟹ ⊤)` (for `mp`).
struct ImpTT;
impl Rule<Calc> for ImpTT {
    type Input = ();
    type Concl = App<Imp, (True, True)>;
    fn decide(self, _: (), _: &Calc) -> Result<Self::Concl, Error> {
        Ok(App(Imp, (True, True)))
    }
}

impl Language for Calc {
    fn admits(&self, r: TypeId) -> bool {
        r == TypeId::of::<Flip>()
            || r == TypeId::of::<TruthAx>()
            || r == TypeId::of::<ImpTT>()
            || r == TypeId::of::<CheckEqn>()
            || r == TypeId::of::<ReflRw>()
    }
    fn extends(&self, p: TypeId) -> bool {
        p == TypeId::of::<()>()
    }
    fn union(self, _: Self) -> Option<Self> {
        Some(Calc)
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

/// A child of `()` admitting one axiom `MyAx: ⊢ Val(true)` (for apply/lift).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Cov2;
struct MyAx;
impl Rule<Cov2> for MyAx {
    type Input = ();
    type Concl = Val<bool>;
    fn decide(self, _: (), _: &Cov2) -> Result<Val<bool>, Error> {
        Ok(Val(true))
    }
}
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
    fn admits(&self, r: TypeId) -> bool {
        r == TypeId::of::<MyAx>()
    }
    fn extends(&self, p: TypeId) -> bool {
        p == TypeId::of::<()>()
    }
    fn union(self, _: Self) -> Option<Self> {
        Some(Cov2)
    }
    const MANIFEST: Option<&'static Manifest> = Some(&COV2_MANIFEST);
}

// ============================ equality calculus ============================

#[test]
fn refl_sym() {
    let e: Thm<(), Eqn<Val<u8>, Val<u8>>> = Thm::refl(Val(3), ());
    assert_eq!(e.lhs(), &Val(3));
    let s = e.sym();
    assert_eq!(s.lhs(), &Val(3));
}

#[test]
fn cong_then_trans() {
    let base: Thm<(), Eqn<Val<bool>, Val<bool>>> = Thm::refl(Val(false), ());
    let c1 = base.cong_app(Not); // ¬false = ¬false
    let c2: Thm<(), Eqn<App<Not, Val<bool>>, App<Not, Val<bool>>>> =
        Thm::refl(App(Not, Val(false)), ());
    let chained = c1.trans(c2).expect("middles match");
    assert_eq!(chained.lhs(), &App(Not, Val(false)));
}

#[test]
fn trans_rejects_mismatched_middle() {
    let a: Thm<(), Eqn<Val<bool>, Val<bool>>> = Thm::refl(Val(true), ());
    let b: Thm<(), Eqn<Val<bool>, Val<bool>>> = Thm::refl(Val(false), ());
    assert_eq!(a.trans(b).unwrap_err(), Error::TransMismatch);
}

#[test]
fn eqn_is_a_bool_expr_and_derive_eq_is_structural() {
    // `Eqn<A, B>` is a freely-constructible bool-sorted proposition; building it
    // proves nothing. `derive(Eq)` gives structural comparison (the `trans` middle).
    let a = Eqn(Val(true), App(Not, Val(false)));
    let b = Eqn(Val(true), App(Not, Val(false)));
    let c = Eqn(Val(true), App(Not, Val(true)));
    assert_eq!(a, b);
    assert_ne!(a, c);
    // it typechecks as an Expr<Ty = bool>:
    fn is_bool<E: Expr<Ty = bool>>(_: &E) {}
    is_bool(&a);
}

// ============================ union of contexts ============================

#[test]
fn trans_unions_hypotheses() {
    // `a = b` under Ctx(0b01), `b = c` under Ctx(0b10) ⇒ `a = c` under Ctx(0b11).
    let l: Thm<Ctx, Eqn<Val<u8>, Val<u8>>> = Thm::refl(Val(7), Ctx(0b01));
    let r: Thm<Ctx, Eqn<Val<u8>, Val<u8>>> = Thm::refl(Val(7), Ctx(0b10));
    let t = l.trans(r).expect("middles match, contexts union");
    assert_eq!(t.lang(), &Ctx(0b11));
}

#[test]
fn trans_fails_when_union_fails() {
    let l: Thm<Exact, Eqn<Val<u8>, Val<u8>>> = Thm::refl(Val(7), Exact(1));
    let r: Thm<Exact, Eqn<Val<u8>, Val<u8>>> = Thm::refl(Val(7), Exact(2));
    assert_eq!(l.trans(r).unwrap_err(), Error::LangMismatch);
}

#[test]
fn cong_pair_unions() {
    let l: Thm<Ctx, Eqn<Val<u8>, Val<u8>>> = Thm::refl(Val(1), Ctx(0b01));
    let r: Thm<Ctx, Eqn<Val<u8>, Val<u8>>> = Thm::refl(Val(2), Ctx(0b10));
    let p = l.cong_pair(r).expect("contexts union");
    assert_eq!(p.lang(), &Ctx(0b11));
    assert_eq!(p.lhs(), &(Val(1), Val(2)));
}

// ============================ Ref / TrustedDeref ============================

#[test]
fn ref_over_each_pointer() {
    // `Ref` works over &T, Box<T>, Rc<T>, Arc<T>; sort is the pointee.
    let _r: Ref<&u8> = Ref(&5);
    let _b: Ref<Box<u8>> = Ref(Box::new(5));
    let _rc: Ref<Rc<u8>> = Ref(Rc::new(5));
    let _arc: Ref<Arc<u8>> = Ref(Arc::new(5));

    // structural Eq compares pointees (so it is usable as a `trans` middle):
    assert_eq!(Ref(Rc::new(5u8)), Ref(Rc::new(5u8)));
    assert_ne!(Ref(Rc::new(5u8)), Ref(Rc::new(6u8)));

    let a: Thm<(), Eqn<Ref<Rc<u8>>, Ref<Rc<u8>>>> = Thm::refl(Ref(Rc::new(9)), ());
    let b: Thm<(), Eqn<Ref<Rc<u8>>, Ref<Rc<u8>>>> = Thm::refl(Ref(Rc::new(9)), ());
    let t = a.trans(b).expect("Rc pointees compare equal");
    assert_eq!(t.lhs(), &Ref(Rc::new(9)));
}

// ============================ bool theory ============================

#[test]
fn and_intro_then_elim() {
    let p = of_eq_with(true, true, ()).unwrap(); // ⊢ (true = true)
    let q = of_eq_with(false, false, ()).unwrap(); // ⊢ (false = false)
    let pq = p.and_intro(q).expect("contexts union"); // ⊢ (t=t) ∧ (f=f)
    assert_eq!(
        pq.prop(),
        &App(
            And,
            (Eqn(Val(true), Val(true)), Eqn(Val(false), Val(false)))
        )
    );
    let (p2, q2) = pq.and_elim(); // ⊢ (t=t), ⊢ (f=f)
    assert_eq!(p2.lhs(), &Val(true));
    assert_eq!(q2.lhs(), &Val(false));
}

#[test]
fn or_intro_both_sides() {
    let p = of_eq_with(true, true, ()).unwrap();
    let l = p.or_inl(False); // ⊢ (t=t) ∨ ⊥
    assert_eq!(l.prop(), &App(Or, (Eqn(Val(true), Val(true)), False)));

    let p2 = of_eq_with(true, true, ()).unwrap();
    let r = p2.or_inr(False); // ⊢ ⊥ ∨ (t=t)
    assert_eq!(r.prop(), &App(Or, (False, Eqn(Val(true), Val(true)))));
}

#[test]
fn modus_ponens() {
    let imp = apply0(Calc, ImpTT).expect("Calc admits ImpTT"); // ⊢ ⊤ ⟹ ⊤
    let t = apply0(Calc, TruthAx).expect("Calc admits TruthAx"); // ⊢ ⊤
    let q = imp.mp(t).expect("antecedent matches, contexts union"); // ⊢ ⊤
    assert_eq!(q.prop(), &True);
}

#[test]
fn eq_mp_transports_along_proven_equation() {
    // ⊢ P with P = (true = true), and ⊢ P = P (refl at the bool sort); eq_mp
    // matches the lhs structurally and re-mints the rhs under the union.
    let p = of_eq_with(true, true, Calc).expect("true == true"); // ⊢ P
    let refl_eq = Thm::refl(Eqn(Val(true), Val(true)), Calc); // ⊢ P = P
    let q = p.eq_mp(refl_eq).expect("lhs matches, contexts union");
    assert_eq!(q.prop(), &Eqn(Val(true), Val(true)));
}

#[test]
fn eq_mp_rejects_mismatched_lhs() {
    let p = of_eq_with(true, true, ()).expect("true == true"); // ⊢ (true = true)
    // ⊢ (false = false) = (false = false) — lhs ≠ p's proposition.
    let refl_eq = Thm::refl(Eqn(Val(false), Val(false)), ());
    assert!(p.eq_mp(refl_eq).is_none());
}

// ============================ gated minting ============================

#[test]
fn canon_evaluates_when_admitted() {
    let e = canon(Flip, true, Calc).expect("Calc admits Flip");
    assert_eq!(e.lhs(), &App(Flip, Val(true)));
    assert_eq!(e.rhs(), &Val(false));
}

#[test]
fn canon_rejected_when_not_admitted() {
    assert_eq!(
        canon(Flip, true, ()).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<Flip>())
    );
    assert_eq!(
        canon(Flip, true, Empty).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<Flip>())
    );
}

#[test]
fn of_eq_is_ungated() {
    // leaf equality is intrinsic — works in empty `()`, no admits.
    let e = of_eq_with(true, true, ()).expect("true == true");
    assert_eq!(e.lhs(), &Val(true));
    assert!(of_eq_with(true, false, ()).is_none());
    // `of_eq` uses the default language value:
    let d: Thm<(), Eqn<Val<u8>, Val<u8>>> = of_eq(9u8, 9u8).expect("9 == 9");
    assert_eq!(d.lhs(), &Val(9));
}

#[test]
fn semidecide_certificate() {
    let ok = semidecide(4u8, 4u8, ()).expect("4 == 4");
    assert_eq!(ok.lhs(), &Val(4));
    assert_eq!(ok.rhs(), &Val(4));
    assert_eq!(semidecide(4u8, 5u8, ()).unwrap_err(), Error::Undecided);
}

#[test]
fn apply_axiom() {
    let thm: Thm<Cov2, Val<bool>> = apply0(Cov2, MyAx).expect("Cov2 admits MyAx");
    assert_eq!(thm.prop(), &Val(true));
}

#[test]
fn apply_rejects_unadmitted() {
    struct AxForUnit;
    impl Rule<()> for AxForUnit {
        type Input = ();
        type Concl = True;
        fn decide(self, _: (), _: &()) -> Result<True, Error> {
            Ok(True)
        }
    }
    assert_eq!(
        apply0((), AxForUnit).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<AxForUnit>())
    );
}

/// Regression: `apply` gates on the rule's OWN `TypeId`, so a downstream rule that
/// concludes a FALSE proposition cannot mint where it isn't admitted (and cannot
/// impersonate an admitted rule — the orphan rule blocks `impl Rule<()> for And`).
#[test]
fn apply_cannot_forge_false() {
    struct Forge;
    impl Rule<()> for Forge {
        type Input = ();
        type Concl = False;
        fn decide(self, _: (), _: &()) -> Result<False, Error> {
            Ok(False) // ⊢ False would be catastrophic
        }
    }
    assert_eq!(
        apply0((), Forge).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<Forge>())
    );
}

// ============================ lift ============================

#[test]
fn lift_to_child() {
    let e: Thm<(), Eqn<Val<bool>, Val<bool>>> = Thm::refl(Val(true), ());
    let up = e.lift(Cov2).expect("Cov2 extends ()");
    assert_eq!(up.lang(), &Cov2);
}

#[test]
fn lift_rejects_non_extender() {
    let e: Thm<(), Eqn<Val<bool>, Val<bool>>> = Thm::refl(Val(true), ());
    assert_eq!(
        e.lift(Empty).unwrap_err(),
        Error::NotExtended(TypeId::of::<()>())
    );
}

// ============================ manifest / dyn ============================

#[test]
fn unit_manifest_is_empty() {
    let m = <() as Language>::MANIFEST.expect("base manifest");
    assert_eq!(m.ty, TypeId::of::<()>());
    assert!(m.admits.is_empty(), "() admits nothing");
    assert!(m.extends.is_empty());
    assert!(!().admits(TypeId::of::<Flip>()));
}

#[test]
fn dyn_expr_is_constructible() {
    let _d: Box<dyn Expr<Ty = bool>> = Box::new(App(Not, Val(true)));
}

// ============================ float value sorts ============================

#[test]
fn float_wrapper_canonicalizes_nan_and_splits_zero() {
    // Every NaN canonicalizes to one value ⇒ reflexive (bare f32 could not), so a
    // wrapped NaN is a usable `Eq` leaf and `refl` holds over it.
    assert_eq!(F32::new(f32::NAN), F32::new(f32::NAN));
    let r: Thm<(), Eqn<Val<F32>, Val<F32>>> = Thm::refl(Val(F32::new(f32::NAN)), ());
    assert_eq!(r.lhs(), r.rhs());
    // structural (bitwise) identity distinguishes +0.0 from -0.0.
    assert_ne!(F32::new(0.0), F32::new(-0.0));
    assert_ne!(F64::new(0.0), F64::new(-0.0));
}

#[test]
fn float_op_canon_is_gated() {
    // WASM float arithmetic ops are `CanonRule`s: `App<F32Add, Val(a,b)> = Val(a+b)`,
    // but reducing one is gated — `Calc` does not admit `F32Add`.
    let a = F32::new(1.5);
    let b = F32::new(2.25);
    assert_eq!(
        canon(F32Add, (a, b), Calc).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<F32Add>())
    );
}

// ============================ n-ary tuples ============================

#[test]
fn nary_tuple_is_an_expr() {
    let t = (Val(1u8), Val(2u16), Val(3u32), Val(4u64), Val(5u128));
    let e = Thm::refl(t, ());
    assert_eq!(e.lhs().0, Val(1u8));
    assert_eq!(e.lhs().4, Val(5u128));
}

// ============================ pointer equality ============================

// A type deliberately WITHOUT `Eq` — pointer equality must still work.
#[derive(Debug)]
struct NoEq(u8);

#[test]
fn of_ptr_eq_same_allocation() {
    let shared = Rc::new(NoEq(7));
    let e = of_ptr_eq(Ref(shared.clone()), Ref(shared.clone()), ()).expect("same allocation");
    assert_eq!((e.lhs().0).0, 7);
    // distinct allocations are not pointer-equal (no `Eq` to fall back on):
    assert!(of_ptr_eq(Ref(Rc::new(NoEq(7))), Ref(Rc::new(NoEq(7))), ()).is_none());
    // works for &T and Arc<T> too:
    let x = NoEq(1);
    assert!(of_ptr_eq(Ref(&x), Ref(&x), ()).is_some());
    let a = Arc::new(NoEq(2));
    assert!(of_ptr_eq(Ref(a.clone()), Ref(a.clone()), ()).is_some());
}

#[test]
fn trans_ptr_through_shared_middle() {
    let s = Rc::new(NoEq(9));
    let e1 = of_ptr_eq(Ref(s.clone()), Ref(s.clone()), ()).unwrap();
    let e2 = of_ptr_eq(Ref(s.clone()), Ref(s.clone()), ()).unwrap();
    // the two middles are the same pointer ⇒ trans_ptr succeeds without `Eq`.
    let chained = e1.trans_ptr(e2).expect("pointer-equal middle");
    assert_eq!((chained.lhs().0).0, 9);

    // different middle allocations ⇒ mismatch.
    let other = Rc::new(NoEq(1));
    let g1 = of_ptr_eq(Ref(s.clone()), Ref(s.clone()), ()).unwrap();
    let g2 = of_ptr_eq(Ref(other.clone()), Ref(other.clone()), ()).unwrap();
    assert_eq!(g1.trans_ptr(g2).unwrap_err(), Error::TransMismatch);
}

// ============================ Rule as a decision procedure ============================

/// A rule whose `Input` is a candidate equation (an `Eqn`) it validates: accept
/// only if the two proposed sides are the literally-equal value. `Eqn` replaces the
/// old `Cand`.
struct CheckEqn;
impl<L: Language> Rule<L> for CheckEqn {
    type Input = Eqn<Val<u8>, Val<u8>>;
    type Concl = Eqn<Val<u8>, Val<u8>>;
    fn decide(self, c: Self::Input, _: &L) -> Result<Self::Concl, Error> {
        if c.0 == c.1 {
            Ok(c)
        } else {
            Err(Error::Undecided)
        }
    }
}

#[test]
fn candidate_is_inert_until_decided() {
    // An `Eqn` candidate is freely constructible and proves nothing on its own.
    let good = Eqn(Val(3u8), Val(3u8));
    let e = apply(Calc, CheckEqn, good).expect("candidate validates");
    assert_eq!(e.lhs(), &Val(3));
    // a bad candidate is rejected by the rule's decision procedure:
    let bad = Eqn(Val(3u8), Val(4u8));
    assert_eq!(apply(Calc, CheckEqn, bad).unwrap_err(), Error::Undecided);
    // and the gate still rejects the whole rule where it is not admitted:
    assert_eq!(
        apply((), CheckEqn, Eqn(Val(3u8), Val(3u8))).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<CheckEqn>())
    );
}

// ============================ MatchApp / rewrite rules ============================

#[test]
fn match_app_hits_only_apps() {
    assert!(App(Not, Val(true)).as_app().is_ok());
    assert!(Val(5u8).as_app().is_err());
    assert!(True.as_app().is_err());
    assert!((Val(1u8), Val(2u8)).as_app().is_err());
    assert!(Eqn(Val(1u8), Val(2u8)).as_app().is_err());
}

/// A generic-method rewrite rule firing at ANY expression shape under ONE
/// `TypeId` — proves `e = e` (a box is transparent: `Box<A>` denotes its pointee).
struct ReflRw;
impl<L> Rewrite<L> for ReflRw {
    fn rewrite<E: MatchApp + Clone + 'static>(
        &self,
        e: E,
        _: &L,
    ) -> Result<(E, Box<dyn Expr<Ty = E::Ty>>), Error> {
        Ok((e.clone(), Box::new(e) as Box<dyn Expr<Ty = E::Ty>>))
    }
}

#[test]
fn apply_rewrite_gated_and_shape_polymorphic() {
    // one rule `TypeId` gates the rewrite at every shape:
    let a = apply_rewrite(Calc, ReflRw, App(Flip, Val(true))).expect("admitted");
    assert_eq!(a.lhs(), &App(Flip, Val(true)));
    let b = apply_rewrite(Calc, ReflRw, Val(7u8)).expect("admitted at another shape");
    assert_eq!(b.lhs(), &Val(7u8));
    // unadmitted ⇒ rejected on the rule's own TypeId. (The `Ok` type wraps a
    // non-`Debug` `Box<dyn Expr>`, so match rather than `unwrap_err`.)
    match apply_rewrite((), ReflRw, Val(7u8)) {
        Err(Error::NotAdmitted(id)) => assert_eq!(id, TypeId::of::<ReflRw>()),
        _ => panic!("unadmitted rewrite must be rejected"),
    }
}

// ============================ dynamic-op App + as_op ============================

#[derive(Debug)]
struct MyDynOp;
impl Op for MyDynOp {
    type In = u8;
    type Out = u8;
}
struct OtherDynOp;
impl Op for OtherDynOp {
    type In = u8;
    type Out = u8;
}
/// A distinct op type that (were `as_op` spoofable) might try to pass as `MyDynOp`.
/// With no downstream identity hook, the only identity is the real vtable `TypeId`.
struct Liar;
impl Op for Liar {
    type In = u8;
    type Out = u8;
}

#[test]
fn dynamic_op_app_is_a_first_class_expr() {
    // `App<Arc<dyn Op<..>>, _>` IS the dynamic application (no separate `DynApp`).
    let op: Arc<dyn Op<In = u8, Out = u8>> = Arc::new(MyDynOp);
    let app = App(op, Val(3u8));
    // it is a genuine Expr<Ty = u8> (Arc<dyn Op> is Clone ⇒ App is Clone):
    let _thm: Thm<(), Eqn<_, _>> = Thm::refl(app.clone(), ());
    // trusted downcast: recognizes the real operator, rejects the wrong one.
    assert!(app.as_op::<MyDynOp>().is_some());
    assert!(app.as_op::<OtherDynOp>().is_none());
}

/// Regression for the audit's `as_op` forgery: identity is the real vtable `TypeId`,
/// not any downstream hook, so a distinct op is never confused with `MyDynOp`.
#[test]
fn as_op_rejects_liar() {
    let op: Arc<dyn Op<In = u8, Out = u8>> = Arc::new(Liar);
    let app = App(op, Val(3u8));
    assert!(app.as_op::<MyDynOp>().is_none(), "must not be spoofed");
    assert!(app.as_op::<Liar>().is_some(), "sees the real op");
}

// ============================ Box/Arc/Rc general + Dyn pointer-eq ============================

#[test]
fn pointer_wrapped_expressions() {
    // Box/Arc/Rc of ANY expr (not just dyn) is an expression.
    let e: Thm<(), Eqn<Box<Val<u8>>, Box<Val<u8>>>> = Thm::refl(Box::new(Val(1)), ());
    assert_eq!(**e.lhs(), Val(1));
    let _a: Arc<App<Not, Val<bool>>> = Arc::new(App(Not, Val(false)));
    let _r: Rc<True> = Rc::new(True);
}

#[test]
fn dyn_pointer_equality_transits() {
    // `Dyn` is `Eq` by pointer identity, so it works as an ordinary `trans` middle
    // with NO `Eq` on the underlying expression.
    let d: Dyn<bool> = Dyn::new(App(Not, Val(true)));
    let e1: Thm<(), Eqn<Dyn<bool>, Dyn<bool>>> = Thm::refl(d.clone(), ());
    let e2: Thm<(), Eqn<Dyn<bool>, Dyn<bool>>> = Thm::refl(d.clone(), ());
    assert!(e1.trans(e2).is_ok()); // same allocation
    // distinct allocations of an equal expression are pointer-unequal:
    let x: Thm<(), Eqn<Dyn<bool>, Dyn<bool>>> = Thm::refl(Dyn::new(True), ());
    let y: Thm<(), Eqn<Dyn<bool>, Dyn<bool>>> = Thm::refl(Dyn::new(True), ());
    assert_eq!(x.trans(y).unwrap_err(), Error::TransMismatch);
}
