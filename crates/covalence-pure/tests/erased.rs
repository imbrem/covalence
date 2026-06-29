//! Type erasure to bare `Arc<dyn Any>` (context and prop) plus the
//! pointer-equality fallible union — exercised through the public API. Note the
//! prop/context positions hold the bare `Arc<dyn Any>` directly; no wrapper type.

use covalence_pure::{MThmExt, testing::TestCtx};

#[test]
fn erase_downcast_ctx_roundtrip() {
    let back = TestCtx::axiom(42u32)
        .erase_ctx()
        .downcast_ctx::<TestCtx>()
        .ok()
        .expect("same type downcasts");
    assert_eq!(back.into_parts().1, 42);
}

#[test]
fn downcast_ctx_wrong_type_refuses() {
    // The erased context holds `TestCtx`; it cannot be laundered into another.
    let t = TestCtx::axiom(1u32).erase_ctx();
    assert!(t.downcast_ctx::<u8>().is_err());
}

#[test]
fn erase_downcast_prop_roundtrip() {
    let back = TestCtx::axiom(7u32)
        .erase_prop()
        .downcast_prop::<u32>()
        .ok()
        .expect("same type downcasts");
    assert_eq!(back.into_parts().1, 7);
}

#[test]
fn erased_same_allocation_unions() {
    let t = TestCtx::axiom(1u32).erase_ctx(); // MThm<Arc<dyn Any>, u32>
    let (a, b) = (t.clone(), t); // both share the same Arc
    let z = a.try_zip_same(b).expect("same allocation must merge");
    assert_eq!(z.into_parts().1, (1, 1));
}

#[test]
fn erased_distinct_allocations_refuse() {
    let a = TestCtx::axiom(1u32).erase_ctx();
    let b = TestCtx::axiom(2u32).erase_ctx(); // independently erased ⇒ distinct Arc
    assert!(a.try_zip_same(b).is_err());
}

#[test]
fn erase_both_and_recover_independently() {
    // Erase both fields, then downcast them back in either order.
    let e = TestCtx::axiom(9u32).erase_both(); // MThm<Arc<dyn Any>, Arc<dyn Any>>
    let with_ctx = e.downcast_ctx::<TestCtx>().ok().expect("ctx type matches");
    let recovered = with_ctx
        .downcast_prop::<u32>()
        .ok()
        .expect("prop type matches");
    assert_eq!(recovered.into_parts().1, 9);

    // Wrong context type fails (no cross-domain laundering through erasure).
    let e2 = TestCtx::axiom(1u32).erase_both();
    assert!(e2.downcast_ctx::<u8>().is_err());
}
