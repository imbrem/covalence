//! HTTP `Range:` plumbing for blob GET / HEAD endpoints.
//!
//! Mirrors RFC 9110 §14 directly via [`covalence_store::ByteRange`]
//! (request side) and [`covalence_store::ResolvedRange`] (response
//! side). Single and multi-range are both handled; multi-range emits
//! `multipart/byteranges`.
//!
//! The two entry points are [`serve_blob_get`] and [`serve_blob_head`].
//! Both are generic over any `ContentStore<O256>`, so a single helper
//! covers `/api/blobs`, `/api/tagged`, etc.

use axum::body::Body;
use axum::http::{HeaderMap, StatusCode, header};
use axum::response::{IntoResponse, Response};
use covalence_hash::O256;
use covalence_store::{ByteRange, ContentStore, ResolvedRange, StoreError, fetch_ranges};

/// Boundary for `multipart/byteranges` bodies.
///
/// A static value is acceptable: blobs are content-addressed binary data,
/// so the probability of this 32-byte string appearing inside one is
/// negligible. RFC 7233 §4.1-compliant clients parse by boundary anyway.
const MULTIPART_BOUNDARY: &str = "cov-byteranges-7c1f9aXXX-boundary";

enum RangeRequest {
    Single(ByteRange),
    Multi(Vec<ByteRange>),
}

/// `Ok(Some(req))` = valid Range header parsed; `Ok(None)` = no Range
/// header present; `Err(())` = header was present but malformed.
fn parse_range_header(headers: &HeaderMap) -> Result<Option<RangeRequest>, ()> {
    let Some(v) = headers.get(header::RANGE) else {
        return Ok(None);
    };
    let v = v.to_str().map_err(|_| ())?;
    if let Some(single) = ByteRange::parse_http_header(v) {
        return Ok(Some(RangeRequest::Single(single)));
    }
    if let Some(multi) = ByteRange::parse_http_header_multi(v) {
        // Single-range input is also accepted by `_multi`; treat
        // `bytes=A-B` (no comma) as Single for the simpler response.
        if multi.len() == 1 {
            return Ok(Some(RangeRequest::Single(multi[0])));
        }
        return Ok(Some(RangeRequest::Multi(multi)));
    }
    Err(())
}

fn unsatisfiable_response(total: u64) -> Response {
    Response::builder()
        .status(StatusCode::RANGE_NOT_SATISFIABLE)
        .header(header::CONTENT_RANGE, format!("bytes */{total}"))
        .body(Body::empty())
        .unwrap()
}

fn build_multipart_body(parts: &[(Vec<u8>, ResolvedRange)], content_type: &str) -> Vec<u8> {
    let mut body = Vec::new();
    for (bytes, resolved) in parts {
        body.extend_from_slice(b"--");
        body.extend_from_slice(MULTIPART_BOUNDARY.as_bytes());
        body.extend_from_slice(b"\r\n");
        body.extend_from_slice(format!("Content-Type: {content_type}\r\n").as_bytes());
        body.extend_from_slice(
            format!("Content-Range: {}\r\n\r\n", resolved.to_content_range()).as_bytes(),
        );
        body.extend_from_slice(bytes);
        body.extend_from_slice(b"\r\n");
    }
    body.extend_from_slice(b"--");
    body.extend_from_slice(MULTIPART_BOUNDARY.as_bytes());
    body.extend_from_slice(b"--\r\n");
    body
}

/// GET a blob, honoring HTTP `Range:` semantics.
///
/// | Request | Response |
/// |---|---|
/// | no `Range:` | `200` + full body + `Content-Length` + `Accept-Ranges: bytes` |
/// | single `Range:` | `206` + sliced body + `Content-Range` + `Accept-Ranges` |
/// | multi `Range:` | `206` + `multipart/byteranges` body |
/// | range out of bounds | `416` + `Content-Range: bytes */N` |
/// | malformed `Range:` | `400` |
/// | unknown key | `404` |
pub fn serve_blob_get<S: ContentStore<O256> + ?Sized>(
    store: &S,
    hash: &O256,
    headers: &HeaderMap,
    content_type: &'static str,
) -> Response {
    let range = match parse_range_header(headers) {
        Err(()) => {
            return (StatusCode::BAD_REQUEST, "malformed Range header").into_response();
        }
        Ok(None) => {
            return match store.get(hash) {
                Some(data) => Response::builder()
                    .status(StatusCode::OK)
                    .header(header::CONTENT_TYPE, content_type)
                    .header(header::ACCEPT_RANGES, "bytes")
                    .header(header::CONTENT_LENGTH, data.len())
                    .body(Body::from(data))
                    .unwrap(),
                None => (StatusCode::NOT_FOUND, "blob not found").into_response(),
            };
        }
        Ok(Some(r)) => r,
    };

    match range {
        RangeRequest::Single(byte_range) => match store.get_range(hash, byte_range) {
            Ok(Some((bytes, resolved))) => Response::builder()
                .status(StatusCode::PARTIAL_CONTENT)
                .header(header::CONTENT_TYPE, content_type)
                .header(header::CONTENT_RANGE, resolved.to_content_range())
                .header(header::ACCEPT_RANGES, "bytes")
                .header(header::CONTENT_LENGTH, bytes.len())
                .body(Body::from(bytes))
                .unwrap(),
            Ok(None) => (StatusCode::NOT_FOUND, "blob not found").into_response(),
            Err(StoreError::RangeNotSatisfiable { total }) => unsatisfiable_response(total),
            Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, format!("{e}")).into_response(),
        },
        RangeRequest::Multi(ranges) => match fetch_ranges(store, hash, &ranges) {
            Ok(Some(parts)) => {
                let body = build_multipart_body(&parts, content_type);
                let ct = format!("multipart/byteranges; boundary={MULTIPART_BOUNDARY}");
                Response::builder()
                    .status(StatusCode::PARTIAL_CONTENT)
                    .header(header::CONTENT_TYPE, ct)
                    .header(header::ACCEPT_RANGES, "bytes")
                    .header(header::CONTENT_LENGTH, body.len())
                    .body(Body::from(body))
                    .unwrap()
            }
            Ok(None) => (StatusCode::NOT_FOUND, "blob not found").into_response(),
            Err(StoreError::RangeNotSatisfiable { total }) => unsatisfiable_response(total),
            Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, format!("{e}")).into_response(),
        },
    }
}

/// HEAD on a blob — `Content-Length` from `head()`, `Accept-Ranges: bytes`.
pub fn serve_blob_head<S: ContentStore<O256> + ?Sized>(
    store: &S,
    hash: &O256,
    content_type: &'static str,
) -> Response {
    match store.head(hash) {
        Some(info) => Response::builder()
            .status(StatusCode::OK)
            .header(header::CONTENT_TYPE, content_type)
            .header(header::ACCEPT_RANGES, "bytes")
            .header(header::CONTENT_LENGTH, info.size)
            .body(Body::empty())
            .unwrap(),
        None => StatusCode::NOT_FOUND.into_response(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::http::HeaderValue;
    use covalence_store::SharedMemoryStore;
    use http_body_util::BodyExt;

    fn headers_with_range(value: &str) -> HeaderMap {
        let mut h = HeaderMap::new();
        h.insert(header::RANGE, HeaderValue::from_str(value).unwrap());
        h
    }

    async fn collect_body(resp: Response) -> Vec<u8> {
        resp.into_body().collect().await.unwrap().to_bytes().to_vec()
    }

    fn setup() -> (SharedMemoryStore, O256) {
        let store = SharedMemoryStore::new();
        let hash = store.insert(b"0123456789").unwrap();
        (store, hash)
    }

    #[tokio::test]
    async fn full_get_no_range_header() {
        let (store, hash) = setup();
        let resp = serve_blob_get(&store, &hash, &HeaderMap::new(), "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::OK);
        assert_eq!(resp.headers()[header::CONTENT_LENGTH], "10");
        assert_eq!(resp.headers()[header::ACCEPT_RANGES], "bytes");
        assert!(!resp.headers().contains_key(header::CONTENT_RANGE));
        assert_eq!(collect_body(resp).await, b"0123456789");
    }

    #[tokio::test]
    async fn single_range_closed() {
        let (store, hash) = setup();
        let h = headers_with_range("bytes=2-5");
        let resp = serve_blob_get(&store, &hash, &h, "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::PARTIAL_CONTENT);
        assert_eq!(resp.headers()[header::CONTENT_RANGE], "bytes 2-5/10");
        assert_eq!(resp.headers()[header::CONTENT_LENGTH], "4");
        assert_eq!(collect_body(resp).await, b"2345");
    }

    #[tokio::test]
    async fn single_range_suffix() {
        let (store, hash) = setup();
        let h = headers_with_range("bytes=-3");
        let resp = serve_blob_get(&store, &hash, &h, "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::PARTIAL_CONTENT);
        assert_eq!(resp.headers()[header::CONTENT_RANGE], "bytes 7-9/10");
        assert_eq!(collect_body(resp).await, b"789");
    }

    #[tokio::test]
    async fn single_range_open_ended() {
        let (store, hash) = setup();
        let h = headers_with_range("bytes=7-");
        let resp = serve_blob_get(&store, &hash, &h, "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::PARTIAL_CONTENT);
        assert_eq!(resp.headers()[header::CONTENT_RANGE], "bytes 7-9/10");
        assert_eq!(collect_body(resp).await, b"789");
    }

    #[tokio::test]
    async fn range_unsatisfiable_returns_416() {
        let (store, hash) = setup();
        let h = headers_with_range("bytes=100-");
        let resp = serve_blob_get(&store, &hash, &h, "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::RANGE_NOT_SATISFIABLE);
        assert_eq!(resp.headers()[header::CONTENT_RANGE], "bytes */10");
    }

    #[tokio::test]
    async fn malformed_range_returns_400() {
        let (store, hash) = setup();
        let h = headers_with_range("garbage");
        let resp = serve_blob_get(&store, &hash, &h, "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::BAD_REQUEST);
    }

    #[tokio::test]
    async fn missing_key_returns_404() {
        let store = SharedMemoryStore::new();
        let missing = O256::blob(b"absent");
        let resp = serve_blob_get(&store, &missing, &HeaderMap::new(), "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::NOT_FOUND);
    }

    #[tokio::test]
    async fn multi_range_returns_multipart() {
        let (store, hash) = setup();
        let h = headers_with_range("bytes=0-2, 5-7");
        let resp = serve_blob_get(&store, &hash, &h, "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::PARTIAL_CONTENT);
        let ct = resp.headers()[header::CONTENT_TYPE].to_str().unwrap();
        assert!(
            ct.starts_with("multipart/byteranges; boundary="),
            "got Content-Type: {ct}"
        );
        let body = collect_body(resp).await;
        let body_str = String::from_utf8_lossy(&body);
        assert!(body_str.contains("Content-Range: bytes 0-2/10"));
        assert!(body_str.contains("Content-Range: bytes 5-7/10"));
        assert!(body_str.contains("012"));
        assert!(body_str.contains("567"));
        // Ends with the closing boundary marker
        assert!(body_str.contains("--cov-byteranges-7c1f9aXXX-boundary--\r\n"));
    }

    #[tokio::test]
    async fn head_includes_content_length() {
        let (store, hash) = setup();
        let resp = serve_blob_head(&store, &hash, "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::OK);
        assert_eq!(resp.headers()[header::CONTENT_LENGTH], "10");
        assert_eq!(resp.headers()[header::ACCEPT_RANGES], "bytes");
        assert_eq!(collect_body(resp).await, b"");
    }

    #[tokio::test]
    async fn head_missing_returns_404() {
        let store = SharedMemoryStore::new();
        let missing = O256::blob(b"absent");
        let resp = serve_blob_head(&store, &missing, "application/octet-stream");
        assert_eq!(resp.status(), StatusCode::NOT_FOUND);
    }
}
