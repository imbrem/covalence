//! Smoke test: `BlockingKv` driving `MemoryKv` from synchronous code.

use std::sync::Arc;

use bytes::Bytes;
use covalence_kv::{BlockingKv, Error, MemoryKv};

fn build_rt() -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("tokio runtime")
}

#[test]
fn put_get_head_delete() {
    let rt = build_rt();
    let kv = BlockingKv::new(Arc::new(MemoryKv::new()), rt.handle().clone());

    kv.put("a/b", Bytes::from_static(b"hello")).unwrap();
    assert_eq!(kv.get("a/b").unwrap().as_ref(), b"hello");

    let meta = kv.head("a/b").unwrap();
    assert_eq!(meta.size, 5);

    kv.delete("a/b").unwrap();
    let err = kv.get("a/b").expect_err("expected NotFound");
    assert!(matches!(err, Error::NotFound { .. }));
}

#[test]
fn range_default_impl_works() {
    let rt = build_rt();
    let kv = BlockingKv::new(Arc::new(MemoryKv::new()), rt.handle().clone());

    kv.put("data", Bytes::from_static(b"0123456789")).unwrap();
    let mid = kv.get_range("data", 2..7).unwrap();
    assert_eq!(mid.as_ref(), b"23456");
}
