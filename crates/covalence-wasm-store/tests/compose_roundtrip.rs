//! Round-trip: build a `merge` composer over two single-blob
//! leaves and exercise `contains` through the wrapper.
//!
//! This validates the full Phase-1 stack:
//!
//! * Resource-typed WIT (`store` as a resource with `open` factory)
//! * Composer world (`import api; export api; export compose`)
//! * Host-side resource registration for the upstream
//! * `compose.build(list<store>)` factory invocation with a
//!   runtime-arity list of backings
//! * Linker shims forwarding `[method]store.contains` into the
//!   right backing
//!
//! `get` and `head` forwarding through the composer is stubbed in
//! the current `merge` composer (returns None); see
//! `crates/covalence-wasm-store/src/merge.rs` for the rationale.

use bytes::Bytes;
use covalence_hash::O256;
use covalence_store::{AsyncContentStore, BlobInfo, StoreError};
use covalence_wasm_store::{WasmStore, merge, single_blob};

fn build_leaf(blob: &[u8]) -> (O256, WasmStore) {
    let hash = O256::blob(blob);
    let bytes = single_blob::build_component(hash.as_bytes(), blob, None)
        .expect("build leaf");
    let store = WasmStore::from_component_bytes(&bytes).expect("instantiate leaf");
    (hash, store)
}

#[tokio::test]
async fn merge_composer_aggregates_contains() {
    let (alpha_hash, alpha) = build_leaf(b"alpha blob");
    let (beta_hash, beta) = build_leaf(b"beta blob");

    let composer_bytes = merge::build_component().expect("build merge composer");
    let composed = WasmStore::compose(&composer_bytes, vec![alpha, beta])
        .expect("compose");

    // Either leaf's hash hits.
    assert!(
        composed
            .contains(&alpha_hash.as_bytes().to_vec())
            .await
            .unwrap()
    );
    assert!(
        composed
            .contains(&beta_hash.as_bytes().to_vec())
            .await
            .unwrap()
    );

    // A hash neither leaf knows misses.
    let absent = vec![0xEE; 32];
    assert!(!composed.contains(&absent).await.unwrap());
}

#[tokio::test]
async fn merge_composer_with_zero_backings_is_empty() {
    // Degenerate case: no backings ⇒ every contains returns false.
    let composer_bytes = merge::build_component().expect("build merge composer");
    let composed =
        WasmStore::compose(&composer_bytes, Vec::<WasmStore>::new()).expect("compose");

    assert!(!composed.contains(&vec![0x00; 32]).await.unwrap());
}

#[tokio::test]
async fn merge_composer_forwards_get_first_hit_wins() {
    let alpha_bytes = b"alpha blob";
    let beta_bytes = b"beta blob";
    let (alpha_hash, alpha) = build_leaf(alpha_bytes);
    let (beta_hash, beta) = build_leaf(beta_bytes);

    let composer_bytes = merge::build_component().expect("build merge composer");
    let composed = WasmStore::compose(&composer_bytes, vec![alpha, beta])
        .expect("compose");

    // Each backing's blob comes back through the composer.
    let from_alpha = composed
        .get(&alpha_hash.as_bytes().to_vec())
        .await
        .expect("get alpha");
    assert_eq!(from_alpha, Bytes::copy_from_slice(alpha_bytes));

    let from_beta = composed
        .get(&beta_hash.as_bytes().to_vec())
        .await
        .expect("get beta");
    assert_eq!(from_beta, Bytes::copy_from_slice(beta_bytes));

    // Unknown hash misses through every backing.
    let err = composed.get(&vec![0xEE; 32]).await.unwrap_err();
    assert!(matches!(err, StoreError::NotFound), "got {err:?}");
}

#[tokio::test]
async fn merge_composer_forwards_head() {
    let alpha_bytes = b"a much larger blob to size up";
    let beta_bytes = b"tiny";
    let (alpha_hash, alpha) = build_leaf(alpha_bytes);
    let (beta_hash, beta) = build_leaf(beta_bytes);

    let composer_bytes = merge::build_component().expect("build merge composer");
    let composed = WasmStore::compose(&composer_bytes, vec![alpha, beta])
        .expect("compose");

    let alpha_info = composed
        .head(&alpha_hash.as_bytes().to_vec())
        .await
        .expect("head alpha");
    assert_eq!(
        alpha_info,
        BlobInfo {
            size: alpha_bytes.len() as u64
        }
    );

    let beta_info = composed
        .head(&beta_hash.as_bytes().to_vec())
        .await
        .expect("head beta");
    assert_eq!(
        beta_info,
        BlobInfo {
            size: beta_bytes.len() as u64
        }
    );

    let err = composed.head(&vec![0xEE; 32]).await.unwrap_err();
    assert!(matches!(err, StoreError::NotFound));
}

#[tokio::test]
async fn merge_composer_with_three_backings_routes_correctly() {
    // N > 2 — exercise the variable-arity path: every backing should
    // be reachable, and the composer iterates in order.
    let one_bytes = b"one";
    let two_bytes = b"two two";
    let three_bytes = b"three three three";
    let (one_hash, one) = build_leaf(one_bytes);
    let (two_hash, two) = build_leaf(two_bytes);
    let (three_hash, three) = build_leaf(three_bytes);

    let composer_bytes = merge::build_component().expect("build merge composer");
    let composed = WasmStore::compose(&composer_bytes, vec![one, two, three])
        .expect("compose");

    assert_eq!(
        composed.get(&one_hash.as_bytes().to_vec()).await.unwrap(),
        Bytes::from_static(one_bytes)
    );
    assert_eq!(
        composed.get(&two_hash.as_bytes().to_vec()).await.unwrap(),
        Bytes::from_static(two_bytes)
    );
    assert_eq!(
        composed.get(&three_hash.as_bytes().to_vec()).await.unwrap(),
        Bytes::from_static(three_bytes)
    );
}
