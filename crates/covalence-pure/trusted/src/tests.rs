//! Stage-0 tests, exercised through the public kernel API (the calculus + gated
//! injectors + bool theory; field reads via `lhs`/`rhs`/`lang`).

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
/// equations under different hypotheses combine.
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

/// A computational language: admits a `CanonRule` (`Flip`) and an axiom (`ImpTT`),
/// directly extends `()`.
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

/// An axiom `⊢ (⊤ ⟹ ⊤)` (for `mp`).
struct ImpTT;
impl Rule<Calc> for ImpTT {
    type Lhs = App<Imp, (True, True)>;
    type Rhs = True;
    fn conclude(self) -> Result<(Self::Lhs, Self::Rhs), Error> {
        Ok((App(Imp, (True, True)), True))
    }
}

impl Language for Calc {
    fn admits(&self, r: TypeId) -> bool {
        r == TypeId::of::<Flip>() || r == TypeId::of::<ImpTT>()
    }
    fn extends(&self, p: TypeId) -> bool {
        p == TypeId::of::<()>()
    }
    fn union(self, _: Self) -> Option<Self> {
        Some(Calc)
    }
    const MANIFEST: Option<&'static Manifest> = None;
}

/// A child of `()` admitting one axiom `MyAx: ⊢ true` (for apply/lift).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Cov2;
struct MyAx;
impl Rule<Cov2> for MyAx {
    type Lhs = Val<bool>;
    type Rhs = True;
    fn conclude(self) -> Result<(Self::Lhs, Self::Rhs), Error> {
        Ok((Val(true), True))
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
    let e: Eqn<Val<u8>, Val<u8>, ()> = Eqn::refl(Val(3), ());
    assert_eq!(e.lhs(), &Val(3));
    let s = e.sym();
    assert_eq!(s.lhs(), &Val(3));
}

#[test]
fn cong_then_trans() {
    let base: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(false), ());
    let c1 = base.cong_app(Not); // ¬false = ¬false
    let c2: Eqn<App<Not, Val<bool>>, App<Not, Val<bool>>, ()> = Eqn::refl(App(Not, Val(false)), ());
    let chained = c1.trans(c2).expect("middles match");
    assert_eq!(chained.lhs(), &App(Not, Val(false)));
}

#[test]
fn trans_rejects_mismatched_middle() {
    let a: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(true), ());
    let b: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(false), ());
    assert_eq!(a.trans(b).unwrap_err(), Error::TransMismatch);
}

#[test]
fn derive_eq_is_structural_equality() {
    let a = App(And, (Val(true), App(Not, Val(false))));
    let b = App(And, (Val(true), App(Not, Val(false))));
    let c = App(And, (Val(true), App(Not, Val(true))));
    assert_eq!(a, b);
    assert_ne!(a, c);
}

// ============================ union of contexts ============================

#[test]
fn trans_unions_hypotheses() {
    // `a = b` under Ctx(0b01), `b = c` under Ctx(0b10) ⇒ `a = c` under Ctx(0b11).
    let l: Eqn<Val<u8>, Val<u8>, Ctx> = Eqn::refl(Val(7), Ctx(0b01));
    let r: Eqn<Val<u8>, Val<u8>, Ctx> = Eqn::refl(Val(7), Ctx(0b10));
    let t = l.trans(r).expect("middles match, contexts union");
    assert_eq!(t.lang(), &Ctx(0b11));
}

#[test]
fn trans_fails_when_union_fails() {
    let l: Eqn<Val<u8>, Val<u8>, Exact> = Eqn::refl(Val(7), Exact(1));
    let r: Eqn<Val<u8>, Val<u8>, Exact> = Eqn::refl(Val(7), Exact(2));
    assert_eq!(l.trans(r).unwrap_err(), Error::LangMismatch);
}

#[test]
fn cong_pair_unions() {
    let l: Eqn<Val<u8>, Val<u8>, Ctx> = Eqn::refl(Val(1), Ctx(0b01));
    let r: Eqn<Val<u8>, Val<u8>, Ctx> = Eqn::refl(Val(2), Ctx(0b10));
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

    let a: Eqn<Ref<Rc<u8>>, Ref<Rc<u8>>, ()> = Eqn::refl(Ref(Rc::new(9)), ());
    let b: Eqn<Ref<Rc<u8>>, Ref<Rc<u8>>, ()> = Eqn::refl(Ref(Rc::new(9)), ());
    let t = a.trans(b).expect("Rc pointees compare equal");
    assert_eq!(t.lhs(), &Ref(Rc::new(9)));
}

// ============================ bool theory ============================

#[test]
fn and_intro_then_elim() {
    let p: Eqn<True, True, ()> = Eqn::refl(True, ()); // ⊢ ⊤
    let q: Eqn<True, True, ()> = Eqn::refl(True, ());
    let pq = p.and_intro(q).expect("contexts union"); // ⊢ ⊤ ∧ ⊤
    assert_eq!(pq.lhs(), &App(And, (True, True)));
    let (p2, q2) = pq.and_elim(); // ⊢ ⊤, ⊢ ⊤
    assert_eq!(p2.lhs(), &True);
    assert_eq!(q2.lhs(), &True);
}

#[test]
fn or_intro_both_sides() {
    let p: Eqn<True, True, ()> = Eqn::refl(True, ());
    let l = p.or_inl(False); // ⊢ ⊤ ∨ ⊥
    assert_eq!(l.lhs(), &App(Or, (True, False)));

    let p2: Eqn<True, True, ()> = Eqn::refl(True, ());
    let r = p2.or_inr(False); // ⊢ ⊥ ∨ ⊤
    assert_eq!(r.lhs(), &App(Or, (False, True)));
}

#[test]
fn modus_ponens() {
    let imp = apply(Calc, ImpTT).expect("Calc admits ImpTT"); // ⊢ ⊤ ⟹ ⊤
    let t: Eqn<True, True, Calc> = Eqn::refl(True, Calc); // ⊢ ⊤
    let q = imp.mp(t).expect("antecedent matches, contexts union"); // ⊢ ⊤
    assert_eq!(q.lhs(), &True);
}

#[test]
fn internalize_reflect_roundtrip() {
    let e: Eqn<Val<u8>, Val<u8>, ()> = Eqn::refl(Val(5), ()); // 5 = 5
    let prop = e.internalize(); // ⊢ (5 = 5)
    assert_eq!(prop.lhs(), &App(EqOp::<u8>::new(), (Val(5), Val(5))));
    let back = prop.reflect(); // 5 = 5
    assert_eq!(back.lhs(), &Val(5));
    assert_eq!(back.rhs(), &Val(5));
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
    let e = of_eq(true, true, ()).expect("true == true");
    assert_eq!(e.lhs(), &Val(true));
    assert!(of_eq(true, false, ()).is_none());
}

#[test]
fn apply_axiom() {
    let thm: Thm<Val<bool>, Cov2> = apply(Cov2, MyAx).expect("Cov2 admits MyAx");
    assert_eq!(thm.lhs(), &Val(true));
    assert_eq!(thm.rhs(), &True);
}

#[test]
fn apply_rejects_unadmitted() {
    struct AxForUnit;
    impl Rule<()> for AxForUnit {
        type Lhs = Val<bool>;
        type Rhs = True;
        fn conclude(self) -> Result<(Self::Lhs, Self::Rhs), Error> {
            Ok((Val(true), True))
        }
    }
    assert_eq!(
        apply((), AxForUnit).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<AxForUnit>())
    );
}

/// Regression: `apply` gates on the rule's OWN `TypeId`, so a downstream rule that
/// concludes a FALSE equation cannot mint where it isn't admitted (and cannot
/// impersonate an admitted rule — the orphan rule blocks `impl Rule<()> for And`).
#[test]
fn apply_cannot_forge_false() {
    struct Forge;
    impl Rule<()> for Forge {
        type Lhs = False;
        type Rhs = True;
        fn conclude(self) -> Result<(Self::Lhs, Self::Rhs), Error> {
            Ok((False, True)) // ⊢ False = ⊤ would be catastrophic
        }
    }
    assert_eq!(
        apply((), Forge).unwrap_err(),
        Error::NotAdmitted(TypeId::of::<Forge>())
    );
}

// ============================ lift ============================

#[test]
fn lift_to_child() {
    let e: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(true), ());
    let up = e.lift(Cov2).expect("Cov2 extends ()");
    assert_eq!(up.lang(), &Cov2);
}

#[test]
fn lift_rejects_non_extender() {
    let e: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(true), ());
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

// ============================ StructuralEq / decide ============================

#[test]
fn decide_true_and_false() {
    // A `StructuralEq` sort (u32) decides equality BOTH ways.
    let t = decide(5u32, 5u32, ());
    assert!(t.is_left(), "5 = 5 decided true");
    assert_eq!(t.left().unwrap().rhs(), &True);

    let f = decide(5u32, 6u32, ());
    assert!(f.is_right(), "5 = 6 decided false");
    assert_eq!(f.right().unwrap().rhs(), &False);
}

#[test]
fn semidecide_positive_only() {
    let ok = semidecide(3u8, 3u8, ()).expect("3 == 3");
    assert_eq!(ok.rhs(), &True);
    // plain `Eq` only trusts the true direction ⇒ inequality is Undecided.
    assert_eq!(semidecide(3u8, 4u8, ()).unwrap_err(), Error::Undecided);
}

#[test]
fn structural_eq_covers_component_types() {
    // Composite / covalence base types are decidable sorts.
    assert!(decide(vec![1u8, 2, 3], vec![1u8, 2, 3], ()).is_left());
    assert!(decide(Some(4u16), None, ()).is_right());
    assert!(decide((1u8, 2u16, 3u32), (1u8, 2u16, 3u32), ()).is_left());
    assert!(
        decide(
            covalence_types::Nat::from(7u32),
            covalence_types::Nat::from(7u32),
            ()
        )
        .is_left()
    );
}

#[test]
fn float_wrapper_canonicalizes_nan_and_splits_zero() {
    // Every NaN canonicalizes to one value ⇒ reflexive (bare f32 could not).
    assert_eq!(F32::new(f32::NAN), F32::new(f32::NAN));
    assert!(decide(F32::new(f32::NAN), F32::new(f32::NAN), ()).is_left());
    // structural (bitwise) identity distinguishes +0.0 from -0.0.
    assert_ne!(F32::new(0.0), F32::new(-0.0));
    assert!(decide(F64::new(0.0), F64::new(-0.0), ()).is_right());
}

// ============================ n-ary tuples ============================

#[test]
fn nary_tuple_is_an_expr() {
    let t = (Val(1u8), Val(2u16), Val(3u32), Val(4u64), Val(5u128));
    let e = Eqn::refl(t, ());
    assert_eq!(e.lhs().0, Val(1u8));
    assert_eq!(e.lhs().4, Val(5u128));
}

// ============================ pointer equality ============================

// A type deliberately WITHOUT `Eq` — pointer equality must still work. (`Debug`
// only so `Result::unwrap_err` can print the `Ok` side in the mismatch test.)
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

    // different middle allocations ⇒ mismatch (g1's middle is `s`, g2's is `other`).
    let other = Rc::new(NoEq(1));
    let g1 = of_ptr_eq(Ref(s.clone()), Ref(s.clone()), ()).unwrap();
    let g2 = of_ptr_eq(Ref(other.clone()), Ref(other.clone()), ()).unwrap();
    assert_eq!(g1.trans_ptr(g2).unwrap_err(), Error::TransMismatch);
}
