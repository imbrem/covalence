//! Stage-0 acceptance, exercised strictly through the public `covalence_pure`
//! facade (the re-exported kernel API). Mirrors the milestone: a cong/trans
//! chain, a boolean law, and a manifest inspection.
#![allow(clippy::type_complexity)] // type-level expressions ⇒ inherently rich types

use std::any::TypeId;

use covalence_pure::*;

#[test]
fn cong_trans_chain_and_manifest() {
    // cong + trans chain in `()`
    let base: Eqn<Val<bool>, Val<bool>, ()> = Eqn::refl(Val(false), ());
    let c1 = base.cong_app(Not);
    let c2: Eqn<App<Not, Val<bool>>, App<Not, Val<bool>>, ()> = Eqn::refl(App(Not, Val(false)), ());
    let chained = c1.trans(c2).expect("middle terms match");
    assert_eq!(chained.lhs(), &App(Not, Val(false)));

    // a boolean law by `canon`
    let law = canon(And, (true, true), ()).expect("() admits And");
    assert_eq!(law.rhs(), &Val(true));

    // the base manifest is what `()` declares
    let m = <() as Language>::MANIFEST.expect("base manifest");
    assert_eq!(m.ty, TypeId::of::<()>());
    assert_eq!(m.admits.len(), 9);
}
