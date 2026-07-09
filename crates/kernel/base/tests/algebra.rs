//! Exercises `covalence_pure::algebra::CertificateAlgebra` through its
//! `EqnKernel` implementation — including a consumer function written
//! **generically over the algebra** (the shape `covalence-core` would take
//! after the migration): it cannot observe which base it runs on.

use std::any::TypeId;
use std::sync::Arc;

use covalence_pure::algebra::{CertificateAlgebra, EqnKernel};
use covalence_pure::{
    App, CanonRule, Eqn, Error, LangMeta, Language, Manifest, Op, Rel, RelErr, Rule, RuleMeta,
    RuleRecord, UntrustedFn, Val,
};

// ---- A tiny test language admitting one axiom, one canon op, one relation ----

/// Nullary axiom `⊢ Val(7) = Val(7)` (a stand-in for an admitted schema).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct SevenAx;

impl<L: Language> Rule<L> for SevenAx {
    type Input = ();
    type Concl = Eqn<Val<u8>, Val<u8>>;
    fn decide(self, _input: (), _lang: &L) -> Result<Self::Concl, Error> {
        Ok(Eqn(Val(7), Val(7)))
    }
}

/// Doubling op with canonical evaluation (`CanonRule`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
struct Double;
impl Op for Double {
    type In = u8;
    type Out = u8;
}
impl CanonRule for Double {
    fn eval(&self, arg: &u8) -> Option<u8> {
        arg.checked_mul(2)
    }
}

/// Untrusted successor function, viewed as the relation `Rel(SuccFn)`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct SuccFn;
impl UntrustedFn for SuccFn {
    type In = u8;
    type Out = u8;
    fn run(&self, a: &u8) -> Result<u8, RelErr> {
        a.checked_add(1).ok_or(RelErr::Refused)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct TestLang;

static TEST_MANIFEST: Manifest = Manifest {
    ty: TypeId::of::<TestLang>(),
    extends: &[],
    admits: &[
        RuleRecord {
            ty: TypeId::of::<SevenAx>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<Double>(),
            metadata: RuleMeta,
        },
        RuleRecord {
            ty: TypeId::of::<Rel<SuccFn>>(),
            metadata: RuleMeta,
        },
    ],
    metadata: LangMeta,
};

impl Language for TestLang {
    fn admits(&self, rule: TypeId) -> bool {
        TEST_MANIFEST.admits.iter().any(|r| r.ty == rule)
    }
    fn extends(&self, _parent: TypeId) -> bool {
        false
    }
    fn union(self, _other: Self) -> Option<Self> {
        Some(self)
    }
    const MANIFEST: Option<&'static Manifest> = Some(&TEST_MANIFEST);
}

// ---- A consumer generic over the algebra (core's future shape) ----

/// `⊢ Double(7) = Val(14)` transported to `⊢ Val(14) = Double(7)`, written
/// without naming the concrete base once.
#[allow(clippy::type_complexity)] // certificate signatures are inherently rich
fn canon_then_sym<B: CertificateAlgebra>()
-> Result<B::Thm<TestLang, Eqn<Val<u8>, App<Double, Val<u8>>>>, B::Error> {
    let eq = B::canon(Double, 7u8, TestLang)?;
    Ok(B::sym(eq))
}

#[test]
fn generic_consumer_cannot_tell_the_base() {
    let thm = canon_then_sym::<EqnKernel>().expect("canon admitted");
    let Eqn(lhs, rhs) = EqnKernel::prop(&thm);
    assert_eq!(*lhs, Val(14u8));
    assert_eq!(rhs.1, Val(7u8));
}

#[test]
fn mint_by_admitted_rule_and_transport() {
    // Group 1: gated mint (apply0 default method).
    let seven = EqnKernel::apply0(TestLang, SevenAx).expect("admitted");
    // Group 2: transport — trans with a refl, then eq_mp is exercised by
    // transporting the (bool-sorted) axiom conclusion along its own refl.
    let refl = EqnKernel::refl(Val(7u8), TestLang);
    let chained = EqnKernel::trans(seven.clone(), refl).expect("middles match");
    assert_eq!(*EqnKernel::prop(&chained), Eqn(Val(7u8), Val(7u8)));
    let eq_of_props = EqnKernel::refl(Eqn(Val(7u8), Val(7u8)), TestLang);
    let transported = EqnKernel::eq_mp(seven, eq_of_props).expect("props match");
    assert_eq!(*EqnKernel::prop(&transported), Eqn(Val(7u8), Val(7u8)));
    // cong_app / cong_pair.
    let under_double = EqnKernel::cong_app(chained, Double);
    assert_eq!(EqnKernel::prop(&under_double).0.1, Val(7u8));
    let r = EqnKernel::refl(Val(1u8), TestLang);
    let paired = EqnKernel::cong_pair(EqnKernel::refl(Val(0u8), TestLang), r).expect("union");
    assert_eq!(
        *EqnKernel::prop(&paired),
        Eqn((Val(0), Val(1)), (Val(0), Val(1)))
    );
}

#[test]
fn ungated_mint_is_rejected() {
    // The gate is the algebra's, not the test's: () admits nothing.
    let err = EqnKernel::apply0((), SevenAx).unwrap_err();
    assert_eq!(err, Error::NotAdmitted(TypeId::of::<SevenAx>()));
}

#[test]
fn positive_relation_facts() {
    // Group 3: execute mints observed membership `⊢ (3, 4) ∈ Rel(SuccFn)`.
    let ab = EqnKernel::execute(Rel(SuccFn), 3u8, TestLang).expect("admitted");
    let App(_, (a, b)) = EqnKernel::prop(&ab);
    assert_eq!((*a.0, *b.0), (3u8, 4u8));
    // compose with a second run `⊢ (4, 5) ∈ Rel(SuccFn)` (Arc middles compare
    // by pointee, so the shared value 4 matches).
    let bc = EqnKernel::execute(Rel(SuccFn), 4u8, TestLang).expect("admitted");
    let composed = EqnKernel::compose(ab, bc).expect("middle matches");
    let App(_, (a, c)) = EqnKernel::prop(&composed);
    assert_eq!((*a.0, *c.0), (3u8, 5u8));
    // transpose flips the observed pair.
    let flipped = EqnKernel::transpose(composed);
    let App(_, (c, a)) = EqnKernel::prop(&flipped);
    assert_eq!((*c.0, *a.0), (5u8, 3u8));
    // A refused run mints nothing (positive-only: no theorem about absence).
    assert!(EqnKernel::execute(Rel(SuccFn), u8::MAX, TestLang).is_err());
    // Zero-copy leaves really are Arcs (compile-time shape check).
    let _: &covalence_pure::Ref<Arc<u8>> = a;
}
