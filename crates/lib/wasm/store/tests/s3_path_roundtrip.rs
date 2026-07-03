//! End-to-end: an `s3_path` composer routes `get` / `contains` /
//! `head` through `prefix + hex(key)` to a backing store.
//!
//! For MVP the backing is a `single_blob` leaf whose embedded
//! "hash" is the UTF-8 bytes of the expected path. Once the kv side
//! lands and we have a `covalence-wasm-kv` adapter, the backing can
//! be a real S3 KV; the WAT stays the same.

use bytes::Bytes;
use covalence_store::{AsyncContentStore, BlobInfo, StoreError};
use covalence_wasm_store::{WasmStore, s3_path, single_blob};

/// Build a backing store that responds to a single "path key" with
/// the given bytes. The `path_key` is the UTF-8 path the composer
/// will look up (e.g. `"blobs/abcd…"`).
fn build_path_keyed_leaf(path_key: &str, blob: &[u8]) -> WasmStore {
    let bytes = single_blob::build_component(path_key.as_bytes(), blob, None).expect("build leaf");
    WasmStore::from_component_bytes(&bytes).expect("instantiate leaf")
}

#[tokio::test]
async fn s3_path_get_routes_through_prefix_plus_hex() {
    let prefix = "blobs/";
    let key = vec![0xab, 0xcd, 0xef, 0x12];
    let blob = b"the stored blob";

    // The backing store recognises the exact path the composer will
    // construct: "blobs/abcdef12".
    let path = format!("{prefix}{}", s3_path::hex_encode(&key));
    let backing = build_path_keyed_leaf(&path, blob);

    let composer_bytes = s3_path::build_component(prefix).expect("build composer");
    let composed = WasmStore::compose(&composer_bytes, vec![backing]).expect("compose");

    let got = composed.get(&key).await.expect("get");
    assert_eq!(got, Bytes::copy_from_slice(blob));
}

#[tokio::test]
async fn s3_path_miss_returns_not_found() {
    let prefix = "blobs/";
    let known_key = vec![0xde, 0xad];
    let known_path = format!("{prefix}{}", s3_path::hex_encode(&known_key));
    let backing = build_path_keyed_leaf(&known_path, b"present");

    let composer_bytes = s3_path::build_component(prefix).expect("build composer");
    let composed = WasmStore::compose(&composer_bytes, vec![backing]).expect("compose");

    let missing_key = vec![0xbe, 0xef];
    let err = composed.get(&missing_key).await.unwrap_err();
    assert!(matches!(err, StoreError::NotFound), "got {err:?}");
}

#[tokio::test]
async fn s3_path_contains_and_head_route_through_prefix() {
    let prefix = "v1/objects/";
    let key = vec![0xca, 0xfe, 0xba, 0xbe];
    let path = format!("{prefix}{}", s3_path::hex_encode(&key));
    let blob = b"sized blob payload";
    let backing = build_path_keyed_leaf(&path, blob);

    let composer_bytes = s3_path::build_component(prefix).expect("build composer");
    let composed = WasmStore::compose(&composer_bytes, vec![backing]).expect("compose");

    assert!(composed.contains(&key).await.unwrap());
    assert!(!composed.contains(&vec![0; 4]).await.unwrap());

    let info = composed.head(&key).await.expect("head");
    assert_eq!(
        info,
        BlobInfo {
            size: blob.len() as u64
        }
    );
}

#[tokio::test]
async fn s3_path_with_two_backings_picks_first_match() {
    // Multiple backings: composer iterates and the first one with
    // the constructed path wins. Demonstrates the variable-arity
    // path inherited from the merge composer template.
    let prefix = "blobs/";
    let key = vec![0x33, 0x44];
    let path = format!("{prefix}{}", s3_path::hex_encode(&key));

    let primary = build_path_keyed_leaf(&path, b"primary copy");
    let secondary = build_path_keyed_leaf(&path, b"secondary copy");

    let composer_bytes = s3_path::build_component(prefix).expect("build composer");
    let composed = WasmStore::compose(&composer_bytes, vec![primary, secondary]).expect("compose");

    // First match wins — primary's bytes come back.
    assert_eq!(
        composed.get(&key).await.unwrap(),
        Bytes::from_static(b"primary copy")
    );
}

#[tokio::test]
async fn s3_path_different_prefix_different_path() {
    // Confirm the prefix actually shapes the path: a backing keyed
    // on the wrong prefix's path doesn't match.
    let key = vec![0x12, 0x34];
    let wrong_path = format!("other/{}", s3_path::hex_encode(&key));
    let backing = build_path_keyed_leaf(&wrong_path, b"wrong-prefix data");

    let composer_bytes = s3_path::build_component("blobs/").expect("build composer");
    let composed = WasmStore::compose(&composer_bytes, vec![backing]).expect("compose");

    let err = composed.get(&key).await.unwrap_err();
    assert!(matches!(err, StoreError::NotFound));
}
