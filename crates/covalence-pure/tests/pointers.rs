//! `TrustedDeref` / `TrustedTake` pointer support, exercised **only through the
//! public API**: theorems are minted via `TestCtx::axiom` (the real `deduce`
//! gate), never constructed directly — `MThm`'s field is private, so an
//! integration test physically cannot forge one.

use std::{rc::Rc, sync::Arc};

use covalence_pure::testing::TestCtx;

#[test]
fn wrap_unwrap_prop_roundtrip() {
    let (_, p) = TestCtx::axiom(7u32)
        .wrap_prop::<Arc<u32>>()
        .unwrap_prop()
        .into_parts();
    assert_eq!(p, 7);
}

#[test]
fn box_and_rc_roundtrip() {
    let (_, b) = TestCtx::axiom(1u32)
        .wrap_prop::<Box<u32>>()
        .unwrap_prop()
        .into_parts();
    assert_eq!(b, 1);
    let (_, r) = TestCtx::axiom(2u32)
        .wrap_prop::<Rc<u32>>()
        .unwrap_prop()
        .into_parts();
    assert_eq!(r, 2);
}

#[test]
fn box_unwrap_needs_no_clone() {
    // A non-`Clone` prop is fine through `Box` because unwrap *moves*.
    struct NoClone(u32);
    let (_, p) = TestCtx::axiom(Box::new(NoClone(9)))
        .unwrap_prop()
        .into_parts();
    assert_eq!(p.0, 9);
}

#[test]
fn wrap_unwrap_ctx_roundtrip() {
    let (c, _) = TestCtx::axiom(())
        .wrap_ctx::<Arc<TestCtx>>()
        .unwrap_ctx()
        .into_parts();
    assert_eq!(c, TestCtx);
}

#[test]
fn ptr_subst_same_allocation_transports() {
    let shared = Arc::new(42u32);
    let (_, p) = TestCtx::axiom(Arc::clone(&shared))
        .ptr_subst(Arc::clone(&shared))
        .expect("same allocation must transport")
        .into_parts();
    assert_eq!(*p, 42);
}

#[test]
fn ptr_subst_distinct_allocation_refuses() {
    // Equal value, different allocation: positive-only, so this proves nothing.
    let t = TestCtx::axiom(Arc::new(42u32));
    assert!(t.ptr_subst(Arc::new(42u32)).is_err());
}

#[test]
fn ref_ptr_subst_and_unwrap() {
    let x = 3u32;
    let (_, p) = TestCtx::axiom(&x)
        .ptr_subst(&x)
        .expect("same reference transports")
        .into_parts();
    assert_eq!(*p, 3);
    let (_, q) = TestCtx::axiom(&x).unwrap_prop().into_parts(); // clones the target
    assert_eq!(q, 3);
}
