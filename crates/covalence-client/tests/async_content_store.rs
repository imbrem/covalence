//! End-to-end test: drive the `AsyncContentStore<O256>` impl on
//! `AsyncHttpBackend` against an in-process `covalence-serve` over a
//! Unix domain socket.
//!
//! Validates that the HTTP `Range:` / `Content-Range:` wire format the
//! server emits round-trips through the client's parser cleanly.

#![cfg(feature = "async")]

use std::time::Duration;

use bytes::Bytes;
use covalence_client::AsyncHttpBackend;
use covalence_serve::{AppState, build_router, new_tagged_store};
use covalence_shell::Kernel;
use covalence_store::{AsyncContentStore, BlobInfo, ByteRange, ResolvedRange, StoreError};

async fn spawn_server() -> (AsyncHttpBackend, tempfile::TempDir) {
    let tempdir = tempfile::tempdir().expect("tempdir");
    let socket_path = tempdir.path().join("serve.sock");

    let tagged_store = new_tagged_store();
    let object_store = covalence_store::GitTaggedObjectStore::new(tagged_store.clone());
    let state = AppState {
        version: "test",
        target: "test",
        started: std::time::Instant::now(),
        kernel: Kernel::new(),
        tagged_store,
        object_store,
    };

    let app = build_router(state, true);

    let _ = std::fs::remove_file(&socket_path);
    let listener = tokio::net::UnixListener::bind(&socket_path).expect("bind");

    // Spawn the server in the background; it runs forever (until the test ends).
    tokio::spawn(async move {
        let _ = axum::serve(listener, app).await;
    });

    // Brief wait so the bind+listen is observable before we connect.
    tokio::time::sleep(Duration::from_millis(20)).await;

    let backend = AsyncHttpBackend::unix(socket_path.display().to_string());
    (backend, tempdir)
}

#[tokio::test]
async fn round_trip_insert_get_head() {
    let (backend, _td) = spawn_server().await;
    let hash = backend
        .insert(Bytes::from_static(b"hello, covalence!"))
        .await
        .expect("insert");

    let info = backend.head(&hash).await.expect("head");
    assert_eq!(info, BlobInfo { size: 17 });

    let full = backend.get(&hash).await.expect("get");
    assert_eq!(full, b"hello, covalence!"[..]);

    let exists = backend.contains(&hash).await.expect("contains");
    assert!(exists);
}

#[tokio::test]
async fn missing_key_is_not_found() {
    let (backend, _td) = spawn_server().await;
    let missing = covalence_hash::O256::blob(b"nope");

    assert!(matches!(
        backend.head(&missing).await,
        Err(StoreError::NotFound)
    ));
    assert!(matches!(
        backend.get(&missing).await,
        Err(StoreError::NotFound)
    ));
    assert!(!backend.contains(&missing).await.expect("contains"));
}

#[tokio::test]
async fn get_slice_native_range() {
    let (backend, _td) = spawn_server().await;
    let hash = backend
        .insert(Bytes::from_static(b"0123456789"))
        .await
        .expect("insert");

    // Half-open range
    let bytes = backend.get_slice(&hash, 2..5).await.expect("get_slice");
    assert_eq!(bytes, b"234"[..]);

    // End past blob silently clamps (POSIX read semantics)
    let bytes = backend
        .get_slice(&hash, 8..999)
        .await
        .expect("get_slice clamp");
    assert_eq!(bytes, b"89"[..]);
}

#[tokio::test]
async fn get_slice_past_end_is_416() {
    let (backend, _td) = spawn_server().await;
    let hash = backend
        .insert(Bytes::from_static(b"five!"))
        .await
        .expect("insert");

    match backend.get_slice(&hash, 100..200).await {
        Err(StoreError::RangeNotSatisfiable { total }) => assert_eq!(total, 5),
        other => panic!("expected RangeNotSatisfiable, got {other:?}"),
    }
}

#[tokio::test]
async fn get_range_one_round_trip() {
    let (backend, _td) = spawn_server().await;
    let hash = backend
        .insert(Bytes::from_static(b"0123456789"))
        .await
        .expect("insert");

    // Suffix range — relies on parsing Content-Range from the response.
    let (bytes, resolved) = backend
        .get_range(&hash, ByteRange::Suffix { length: 3 })
        .await
        .expect("get_range");
    assert_eq!(bytes, b"789"[..]);
    assert_eq!(
        resolved,
        ResolvedRange {
            start: 7,
            end: 9,
            total: 10
        }
    );

    // Open-ended `From`.
    let (bytes, resolved) = backend
        .get_range(&hash, ByteRange::From { start: 5 })
        .await
        .expect("get_range from");
    assert_eq!(bytes, b"56789"[..]);
    assert_eq!(resolved.total, 10);
    assert_eq!(resolved.start, 5);
    assert_eq!(resolved.end, 9);
}

#[tokio::test]
async fn put_verifies_hash() {
    let (backend, _td) = spawn_server().await;
    let data = Bytes::from_static(b"verify me");
    let expected = covalence_hash::O256::blob(&data);

    // Correct key — succeeds.
    backend.put(expected, data.clone()).await.expect("put");

    // Wrong key — server-computed hash mismatch.
    let wrong = covalence_hash::O256::blob(b"different");
    assert!(matches!(
        backend.put(wrong, data).await,
        Err(StoreError::Io(_))
    ));
}
