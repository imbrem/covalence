//! The `covalence_pure::api` facade is a PURE re-export set: every item is
//! type-identical to its crate-root original (zero behavior change). This test
//! proves it by using the two paths interchangeably in one expression.

use covalence_pure::api;

#[test]
fn facade_items_are_type_identical_to_root() {
    // A theorem minted through root-path names…
    let root_thm: covalence_pure::Thm<(), covalence_pure::Eqn<covalence_pure::Val<u8>, _>> =
        covalence_pure::Thm::refl(covalence_pure::Val(7u8), ());
    // …is exactly an api-path theorem (same type, assignable with no coercion).
    let api_thm: api::Thm<(), api::Eqn<api::Val<u8>, api::Val<u8>>> = root_thm;
    assert_eq!(api_thm.prop().0, api::Val(7u8));

    // The calculus works identically through the facade.
    let sym = api_thm.sym();
    assert_eq!(sym.prop().1, covalence_pure::Val(7u8));

    // Error is the same enum.
    let e: api::Error = covalence_pure::Error::TransMismatch;
    assert_eq!(e, api::Error::TransMismatch);
}
