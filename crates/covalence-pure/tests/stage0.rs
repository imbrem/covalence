//! Stage-0 acceptance through the public `covalence_pure` facade (the re-exported
//! kernel API): a cong/trans chain, the bool theory, and a manifest inspection.
#![allow(clippy::type_complexity)] // type-level expressions ⇒ inherently rich types

use std::any::TypeId;

use covalence_pure::*;

#[test]
fn calculus_prop_and_manifest() {
    // cong + trans chain in the empty base `()`
    let base: Thm<(), Eqn<Val<bool>, Val<bool>>> = Thm::refl(Val(false), ());
    let c1 = base.cong_app(Not);
    let c2: Thm<(), Eqn<App<Not, Val<bool>>, App<Not, Val<bool>>>> =
        Thm::refl(App(Not, Val(false)), ());
    let chained = c1.trans(c2).expect("middles match");
    assert_eq!(chained.lhs(), &App(Not, Val(false)));

    // bool theory is available in every language (here `()`): ∧-intro/elim over two
    // proven equalities (which are bool propositions).
    let p = of_eq_with(5u8, 5u8, ()).expect("5 == 5");
    let q = of_eq_with(6u8, 6u8, ()).expect("6 == 6");
    let (p2, _q2) = p.and_intro(q).expect("union").and_elim();
    assert_eq!(p2.lhs(), &Val(5));

    // `()` is the trivial base — empty manifest.
    let m = <() as Language>::MANIFEST.expect("base manifest");
    assert_eq!(m.ty, TypeId::of::<()>());
    assert!(m.admits.is_empty());
}
