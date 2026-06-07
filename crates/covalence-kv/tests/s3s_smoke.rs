//! In-process smoke test: covalence-kv against an `s3s-fs` filesystem-backed
//! S3 server. No Docker, no network — the server runs on an ephemeral
//! localhost port inside the test.

use bytes::Bytes;
use covalence_kv::{Error, KvStore, aws};
use hyper::server::conn::http1;
use hyper_util::rt::TokioIo;
use s3s::auth::SimpleAuth;
use s3s::service::S3ServiceBuilder;
use s3s_fs::FileSystem;
use tempfile::TempDir;

const KEY_ID: &str = "AKIAIOSFODNN7EXAMPLE";
const SECRET: &str = "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY";
const BUCKET: &str = "covalence-test";
const REGION: &str = "us-east-1";

async fn start_server() -> (std::net::SocketAddr, TempDir) {
    let tmp = TempDir::new().expect("tempdir");
    // s3s-fs uses subdirectories as buckets; pre-create the bucket dir.
    std::fs::create_dir(tmp.path().join(BUCKET)).unwrap();

    let fs = FileSystem::new(tmp.path()).expect("filesystem backend");
    let service = {
        let mut b = S3ServiceBuilder::new(fs);
        b.set_auth(SimpleAuth::from_single(KEY_ID, SECRET));
        b.build()
    };

    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();

    tokio::spawn(async move {
        loop {
            let Ok((stream, _)) = listener.accept().await else {
                break;
            };
            let svc = service.clone();
            tokio::spawn(async move {
                let io = TokioIo::new(stream);
                let _ = http1::Builder::new().serve_connection(io, svc).await;
            });
        }
    });

    (addr, tmp)
}

fn build_client(addr: std::net::SocketAddr) -> aws::S3Kv {
    let store = aws::Config::custom(format!("http://{addr}"), REGION, BUCKET, KEY_ID, SECRET)
        .with_allow_http(true)
        .build()
        .expect("build AmazonS3");
    aws::S3Kv::new(store)
}

#[tokio::test]
async fn roundtrip_put_get_head_delete() {
    let (addr, _tmp) = start_server().await;
    let kv = build_client(addr);

    kv.put("foo/bar.txt", Bytes::from_static(b"hello, s3s"))
        .await
        .expect("put");

    let body = kv.get("foo/bar.txt").await.expect("get");
    assert_eq!(body.as_ref(), b"hello, s3s");

    let meta = kv.head("foo/bar.txt").await.expect("head");
    assert_eq!(meta.size, 10);

    kv.delete("foo/bar.txt").await.expect("delete");
    let err = kv.get("foo/bar.txt").await.expect_err("expected NotFound");
    assert!(matches!(err, Error::NotFound { .. }), "got: {err:?}");

    // Note: idempotent re-delete works on real S3 (204 No Content) but
    // s3s-fs returns a malformed DeleteObjects XML response when the key
    // is already gone, so we don't exercise that path here.
}

#[tokio::test]
async fn ranged_read_real_backend_path() {
    let (addr, _tmp) = start_server().await;
    let kv = build_client(addr);

    kv.put("range/value", Bytes::from_static(b"0123456789abcdef"))
        .await
        .unwrap();

    // Backend-side range (overrides the default fetch-and-slice).
    let mid = kv.get_range("range/value", 4..10).await.unwrap();
    assert_eq!(mid.as_ref(), b"456789");

    let head = kv.get_range("range/value", 0..4).await.unwrap();
    assert_eq!(head.as_ref(), b"0123");
}

#[tokio::test]
async fn invalid_key_is_recoverable_error() {
    let (addr, _tmp) = start_server().await;
    let kv = build_client(addr);

    // object_store::Path rejects DEL (0x7F) and other control characters.
    let err = kv.get("bad\x7Fkey").await.expect_err("expected InvalidKey");
    assert!(
        matches!(err, Error::InvalidKey { .. }),
        "expected InvalidKey, got {err:?}"
    );
}
