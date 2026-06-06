//! End-to-end: build a single-blob component, wrap it as a
//! [`WasmStore`], and exercise every method of [`AsyncContentStore`].

use bytes::Bytes;
use covalence_hash::O256;
use covalence_store::{AsyncContentStore, BlobInfo, StoreError, StoreManifest, StoreRef};
use covalence_wasm_store::{WasmStore, single_blob};

fn build(hash: &[u8], blob: &[u8]) -> WasmStore {
    let bytes = single_blob::build_component(hash, blob, None).expect("build component");
    WasmStore::from_component_bytes(&bytes).expect("instantiate")
}

#[tokio::test]
async fn get_hits_on_known_hash() {
    let blob = b"a known blob".as_slice();
    let hash = O256::blob(blob);
    let store = build(hash.as_bytes(), blob);

    let key = hash.as_bytes().to_vec();
    let got = store.get(&key).await.expect("get");
    assert_eq!(got, Bytes::copy_from_slice(blob));
}

#[tokio::test]
async fn get_misses_on_unknown_hash() {
    let blob = b"something".as_slice();
    let hash = O256::blob(blob);
    let store = build(hash.as_bytes(), blob);

    let bad_key = vec![0xCD; 32];
    let err = store.get(&bad_key).await.unwrap_err();
    assert!(matches!(err, StoreError::NotFound), "got {err:?}");
}

#[tokio::test]
async fn head_returns_blob_size() {
    let blob = b"size me up please".as_slice();
    let hash = O256::blob(blob);
    let store = build(hash.as_bytes(), blob);

    let info = store.head(&hash.as_bytes().to_vec()).await.expect("head");
    assert_eq!(
        info,
        BlobInfo {
            size: blob.len() as u64
        }
    );

    let err = store.head(&vec![0u8; 32]).await.unwrap_err();
    assert!(matches!(err, StoreError::NotFound));
}

#[tokio::test]
async fn contains_reflects_hits() {
    let blob = b"present".as_slice();
    let hash = O256::blob(blob);
    let store = build(hash.as_bytes(), blob);

    assert!(store.contains(&hash.as_bytes().to_vec()).await.unwrap());
    assert!(!store.contains(&vec![0xff; 32]).await.unwrap());
}

#[tokio::test]
async fn get_slice_clips_within_blob() {
    let blob = b"0123456789".as_slice();
    let hash = O256::blob(blob);
    let store = build(hash.as_bytes(), blob);

    let key = hash.as_bytes().to_vec();
    let mid = store.get_slice(&key, 2..5).await.expect("slice");
    assert_eq!(mid, Bytes::from_static(b"234"));
}

#[tokio::test]
async fn embedded_manifest_round_trips_through_wasm_store() {
    let blob = b"described blob".as_slice();
    let hash = O256::blob(blob);

    let mut manifest = StoreManifest::new("single-blob-fixture", "single-blob");
    manifest.description = Some("knows one (hash → blob) pair".into());
    manifest.depends_on.push(StoreRef {
        name: "kernel-cas".into(),
        manifest: None,
        extra: Default::default(),
    });

    let bytes = single_blob::build_component(hash.as_bytes(), blob, Some(&manifest))
        .expect("build with manifest");

    // 1. Standalone extraction recovers the manifest.
    let extracted = covalence_wasm_store::extract_manifest(&bytes)
        .expect("extract")
        .expect("manifest present");
    assert_eq!(extracted, manifest);

    // 2. WasmStore caches the same value at construction.
    let store = WasmStore::from_component_bytes(&bytes).expect("instantiate");
    assert_eq!(store.manifest(), Some(&manifest));

    // 3. The execution path still works — manifest section does not
    //    perturb the wasm body.
    let got = store
        .get(&hash.as_bytes().to_vec())
        .await
        .expect("get");
    assert_eq!(got, Bytes::copy_from_slice(blob));
}

#[tokio::test]
async fn store_identity_is_component_hash() {
    // Same code + different manifest ⇒ different identity. The
    // central design contract for store identity.
    let blob = b"identity".as_slice();
    let hash = O256::blob(blob);

    let a = single_blob::build_component(
        hash.as_bytes(),
        blob,
        Some(&StoreManifest::new("a", "single-blob")),
    )
    .unwrap();
    let b = single_blob::build_component(
        hash.as_bytes(),
        blob,
        Some(&StoreManifest::new("b", "single-blob")),
    )
    .unwrap();
    assert_ne!(O256::blob(&a), O256::blob(&b));

    // Determinism: rebuilding the same inputs yields the same hash.
    let a2 = single_blob::build_component(
        hash.as_bytes(),
        blob,
        Some(&StoreManifest::new("a", "single-blob")),
    )
    .unwrap();
    assert_eq!(O256::blob(&a), O256::blob(&a2));
}

#[tokio::test]
async fn key_wrong_length_does_not_match() {
    // 32-byte hash committed in component; a 16-byte key must miss.
    let blob = b"data".as_slice();
    let hash = O256::blob(blob);
    let store = build(hash.as_bytes(), blob);

    let short = vec![0u8; 16];
    assert!(!store.contains(&short).await.unwrap());
    assert!(matches!(
        store.get(&short).await,
        Err(StoreError::NotFound)
    ));
}
