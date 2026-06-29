//! Sequence props (`[T; N]`, `Vec<T>`, `&[T]`) as N-ary conjunction — exercised
//! through the public API via `TestCtx::axiom`.

use covalence_pure::{MThm, MThmVecExt, testing::TestCtx};

fn props<K, T>(thms: Vec<MThm<K, T>>) -> Vec<T> {
    thms.into_iter().map(|t| t.into_parts().1).collect()
}

#[test]
fn array_unpack() {
    let parts: [_; 3] = TestCtx::axiom([1u32, 2, 3]).unpack();
    assert_eq!(props(parts.into_iter().collect()), vec![1, 2, 3]);
}

#[test]
fn vec_unpack() {
    let parts = TestCtx::axiom(vec![10u32, 20]).unpack();
    assert_eq!(props(parts), vec![10, 20]);
}

#[test]
fn slice_unpack() {
    let data = [7u32, 8, 9];
    let parts = TestCtx::axiom(&data[..]).unpack();
    assert_eq!(props(parts), vec![7, 8, 9]);
}

#[test]
fn vec_build_via_empty_and_push_same() {
    let v = MThm::<TestCtx, Vec<u32>>::empty_vec(TestCtx)
        .push_same(TestCtx::axiom(1u32))
        .push_same(TestCtx::axiom(2u32));
    assert_eq!(props(v.unpack()), vec![1, 2]);
}

#[test]
fn vec_cross_context_push() {
    // The general primitive: `U: Union<K, K2>` (here both `TestCtx`), so the
    // output context needs annotating.
    let v: MThm<TestCtx, Vec<u32>> = MThm::<TestCtx, Vec<u32>>::empty_vec(TestCtx)
        .push::<TestCtx, TestCtx>(TestCtx::axiom(5u32));
    assert_eq!(props(v.unpack()), vec![5]);
}

#[test]
fn vec_ptr_subst_distinct_buffers_refuse() {
    // `Vec` is a `TrustedDeref` over its slice; two vecs with equal contents but
    // distinct buffers are not pointer-equal — positive-only, so this refuses.
    let v = TestCtx::axiom(vec![1u32, 2]);
    assert!(v.ptr_subst(vec![1u32, 2]).is_err());
}
