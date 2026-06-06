use std::ops::Range;

use async_trait::async_trait;
use covalence_hash::O256;
use covalence_shell::{AsyncBackend, BackendInfo, KernelError};
use covalence_store::{
    AsyncContentStore, BlobInfo, ByteRange, ResolvedRange, StoreError,
};
use http_body_util::{BodyExt, Full};
use hyper::HeaderMap;
use hyper::body::Bytes;
use hyper_util::client::legacy::Client;
use hyper_util::rt::TokioExecutor;

use crate::types::{BlobStatsResponse, HashResponse};

type HttpClient = Client<hyper_util::client::legacy::connect::HttpConnector, Full<Bytes>>;

/// Async HTTP backend using hyper. Supports TCP and Unix domain sockets.
pub struct AsyncHttpBackend {
    base_url: String,
    /// If set, connect via Unix domain socket instead of TCP.
    socket_path: Option<String>,
    /// Reusable HTTP client for TCP connections.
    client: HttpClient,
}

impl AsyncHttpBackend {
    /// Create a new async HTTP backend connecting to the given URL (TCP).
    pub fn new(base_url: String) -> Self {
        Self {
            base_url,
            socket_path: None,
            client: Client::builder(TokioExecutor::new()).build_http(),
        }
    }

    /// Create a new async HTTP backend connecting via a Unix domain socket.
    pub fn unix(socket_path: String) -> Self {
        Self {
            base_url: "http://localhost".to_string(),
            socket_path: Some(socket_path),
            client: Client::builder(TokioExecutor::new()).build_http(),
        }
    }

    async fn get(&self, path: &str) -> Result<Vec<u8>, KernelError> {
        let url = format!("{}{}", self.base_url, path);

        if let Some(ref socket_path) = self.socket_path {
            self.unix_get(socket_path, path).await
        } else {
            self.tcp_get(&url).await
        }
    }

    async fn tcp_get(&self, url: &str) -> Result<Vec<u8>, KernelError> {
        let uri: hyper::Uri = url
            .parse()
            .map_err(|e| KernelError::Store(format!("invalid URL: {e}")))?;
        let resp = self
            .client
            .get(uri)
            .await
            .map_err(|e| KernelError::Store(format!("request: {e}")))?;

        let status = resp.status().as_u16();
        let body = resp
            .into_body()
            .collect()
            .await
            .map_err(|e| KernelError::Store(format!("read body: {e}")))?
            .to_bytes()
            .to_vec();

        if status == 404 {
            return Err(KernelError::NotFound("not found".to_string()));
        }
        if status >= 400 {
            let msg = String::from_utf8_lossy(&body).to_string();
            return Err(KernelError::Store(format!("HTTP {status}: {msg}")));
        }
        Ok(body)
    }

    async fn unix_get(&self, socket_path: &str, path: &str) -> Result<Vec<u8>, KernelError> {
        use hyper::Request;
        use hyper_util::rt::TokioIo;
        use tokio::net::UnixStream;

        let stream = UnixStream::connect(socket_path)
            .await
            .map_err(|e| KernelError::Store(format!("unix connect: {e}")))?;
        let io = TokioIo::new(stream);

        let (mut sender, conn) = hyper::client::conn::http1::handshake(io)
            .await
            .map_err(|e| KernelError::Store(format!("handshake: {e}")))?;
        tokio::spawn(conn);

        let req = Request::get(path)
            .header("host", "localhost")
            .body(Full::<Bytes>::new(Bytes::new()))
            .map_err(|e| KernelError::Store(format!("build request: {e}")))?;

        let resp = sender
            .send_request(req)
            .await
            .map_err(|e| KernelError::Store(format!("request: {e}")))?;

        let status = resp.status().as_u16();
        let body = resp
            .into_body()
            .collect()
            .await
            .map_err(|e| KernelError::Store(format!("read body: {e}")))?
            .to_bytes()
            .to_vec();

        if status == 404 {
            return Err(KernelError::NotFound("not found".to_string()));
        }
        if status >= 400 {
            let msg = String::from_utf8_lossy(&body).to_string();
            return Err(KernelError::Store(format!("HTTP {status}: {msg}")));
        }
        Ok(body)
    }

    async fn head_status(&self, path: &str) -> Result<u16, KernelError> {
        if let Some(ref socket_path) = self.socket_path {
            self.unix_head(socket_path, path).await
        } else {
            let url = format!("{}{}", self.base_url, path);
            self.tcp_head(&url).await
        }
    }

    async fn tcp_head(&self, url: &str) -> Result<u16, KernelError> {
        let uri: hyper::Uri = url
            .parse()
            .map_err(|e| KernelError::Store(format!("invalid URL: {e}")))?;

        let req = hyper::Request::builder()
            .method("HEAD")
            .uri(uri)
            .body(Full::new(Bytes::new()))
            .map_err(|e| KernelError::Store(format!("build request: {e}")))?;

        let resp = self
            .client
            .request(req)
            .await
            .map_err(|e| KernelError::Store(format!("request: {e}")))?;

        Ok(resp.status().as_u16())
    }

    async fn unix_head(&self, socket_path: &str, path: &str) -> Result<u16, KernelError> {
        use hyper::Request;
        use hyper_util::rt::TokioIo;
        use tokio::net::UnixStream;

        let stream = UnixStream::connect(socket_path)
            .await
            .map_err(|e| KernelError::Store(format!("unix connect: {e}")))?;
        let io = TokioIo::new(stream);

        let (mut sender, conn) = hyper::client::conn::http1::handshake(io)
            .await
            .map_err(|e| KernelError::Store(format!("handshake: {e}")))?;
        tokio::spawn(conn);

        let req = Request::head(path)
            .header("host", "localhost")
            .body(Full::<Bytes>::new(Bytes::new()))
            .map_err(|e| KernelError::Store(format!("build request: {e}")))?;

        let resp = sender
            .send_request(req)
            .await
            .map_err(|e| KernelError::Store(format!("request: {e}")))?;

        Ok(resp.status().as_u16())
    }

    async fn post_bytes(&self, path: &str, data: &[u8]) -> Result<Vec<u8>, KernelError> {
        if let Some(ref socket_path) = self.socket_path {
            self.unix_post(socket_path, path, data).await
        } else {
            let url = format!("{}{}", self.base_url, path);
            self.tcp_post(&url, data).await
        }
    }

    async fn tcp_post(&self, url: &str, data: &[u8]) -> Result<Vec<u8>, KernelError> {
        let uri: hyper::Uri = url
            .parse()
            .map_err(|e| KernelError::Store(format!("invalid URL: {e}")))?;

        let req = hyper::Request::builder()
            .method("POST")
            .uri(uri)
            .header("content-type", "application/octet-stream")
            .body(Full::new(Bytes::from(data.to_vec())))
            .map_err(|e| KernelError::Store(format!("build request: {e}")))?;

        let resp = self
            .client
            .request(req)
            .await
            .map_err(|e| KernelError::Store(format!("request: {e}")))?;

        let status = resp.status().as_u16();
        let body = resp
            .into_body()
            .collect()
            .await
            .map_err(|e| KernelError::Store(format!("read body: {e}")))?
            .to_bytes()
            .to_vec();

        if status == 404 {
            return Err(KernelError::NotFound("not found".to_string()));
        }
        if status >= 400 {
            let msg = String::from_utf8_lossy(&body).to_string();
            return Err(KernelError::Store(format!("HTTP {status}: {msg}")));
        }
        Ok(body)
    }

    async fn unix_post(
        &self,
        socket_path: &str,
        path: &str,
        data: &[u8],
    ) -> Result<Vec<u8>, KernelError> {
        use hyper::Request;
        use hyper_util::rt::TokioIo;
        use tokio::net::UnixStream;

        let stream = UnixStream::connect(socket_path)
            .await
            .map_err(|e| KernelError::Store(format!("unix connect: {e}")))?;
        let io = TokioIo::new(stream);

        let (mut sender, conn) = hyper::client::conn::http1::handshake(io)
            .await
            .map_err(|e| KernelError::Store(format!("handshake: {e}")))?;
        tokio::spawn(conn);

        let req = Request::post(path)
            .header("host", "localhost")
            .header("content-type", "application/octet-stream")
            .body(Full::new(Bytes::from(data.to_vec())))
            .map_err(|e| KernelError::Store(format!("build request: {e}")))?;

        let resp = sender
            .send_request(req)
            .await
            .map_err(|e| KernelError::Store(format!("request: {e}")))?;

        let status = resp.status().as_u16();
        let body = resp
            .into_body()
            .collect()
            .await
            .map_err(|e| KernelError::Store(format!("read body: {e}")))?
            .to_bytes()
            .to_vec();

        if status == 404 {
            return Err(KernelError::NotFound("not found".to_string()));
        }
        if status >= 400 {
            let msg = String::from_utf8_lossy(&body).to_string();
            return Err(KernelError::Store(format!("HTTP {status}: {msg}")));
        }
        Ok(body)
    }
}

// ---------------------------------------------------------------------------
// Full-response helper + AsyncContentStore impl
// ---------------------------------------------------------------------------

impl AsyncHttpBackend {
    /// Issue an HTTP request and return `(status, headers, body)` so the
    /// `AsyncContentStore` impl can read `Content-Length` / `Content-Range`.
    async fn request_full(
        &self,
        method: &str,
        path: &str,
        range_header: Option<&str>,
        body: Bytes,
    ) -> Result<(u16, HeaderMap, Vec<u8>), StoreError> {
        if let Some(ref socket_path) = self.socket_path {
            self.unix_request_full(socket_path, method, path, range_header, body)
                .await
        } else {
            let url = format!("{}{}", self.base_url, path);
            self.tcp_request_full(&url, method, range_header, body).await
        }
    }

    async fn tcp_request_full(
        &self,
        url: &str,
        method: &str,
        range_header: Option<&str>,
        body: Bytes,
    ) -> Result<(u16, HeaderMap, Vec<u8>), StoreError> {
        let uri: hyper::Uri = url
            .parse()
            .map_err(|e| StoreError::Io(format!("invalid URL: {e}")))?;

        let mut req = hyper::Request::builder().method(method).uri(uri);
        if let Some(r) = range_header {
            req = req.header("range", r);
        }
        if method == "POST" || method == "PUT" {
            req = req.header("content-type", "application/octet-stream");
        }
        let req = req
            .body(Full::new(body))
            .map_err(|e| StoreError::Io(format!("build request: {e}")))?;

        let resp = self
            .client
            .request(req)
            .await
            .map_err(|e| StoreError::Io(format!("request: {e}")))?;

        let status = resp.status().as_u16();
        let headers = resp.headers().clone();
        let bytes = resp
            .into_body()
            .collect()
            .await
            .map_err(|e| StoreError::Io(format!("read body: {e}")))?
            .to_bytes()
            .to_vec();
        Ok((status, headers, bytes))
    }

    async fn unix_request_full(
        &self,
        socket_path: &str,
        method: &str,
        path: &str,
        range_header: Option<&str>,
        body: Bytes,
    ) -> Result<(u16, HeaderMap, Vec<u8>), StoreError> {
        use hyper::Request;
        use hyper_util::rt::TokioIo;
        use tokio::net::UnixStream;

        let stream = UnixStream::connect(socket_path)
            .await
            .map_err(|e| StoreError::Io(format!("unix connect: {e}")))?;
        let io = TokioIo::new(stream);
        let (mut sender, conn) = hyper::client::conn::http1::handshake(io)
            .await
            .map_err(|e| StoreError::Io(format!("handshake: {e}")))?;
        tokio::spawn(conn);

        let mut req = Request::builder()
            .method(method)
            .uri(path)
            .header("host", "localhost");
        if let Some(r) = range_header {
            req = req.header("range", r);
        }
        if method == "POST" || method == "PUT" {
            req = req.header("content-type", "application/octet-stream");
        }
        let req = req
            .body(Full::new(body))
            .map_err(|e| StoreError::Io(format!("build request: {e}")))?;

        let resp = sender
            .send_request(req)
            .await
            .map_err(|e| StoreError::Io(format!("request: {e}")))?;

        let status = resp.status().as_u16();
        let headers = resp.headers().clone();
        let bytes = resp
            .into_body()
            .collect()
            .await
            .map_err(|e| StoreError::Io(format!("read body: {e}")))?
            .to_bytes()
            .to_vec();
        Ok((status, headers, bytes))
    }
}

/// Parse `Content-Range: bytes A-B/total` into a [`ResolvedRange`].
fn parse_content_range(value: &str) -> Option<ResolvedRange> {
    let rest = value.strip_prefix("bytes ")?;
    let (range_part, total_part) = rest.split_once('/')?;
    let (start_part, end_part) = range_part.split_once('-')?;
    Some(ResolvedRange {
        start: start_part.parse().ok()?,
        end: end_part.parse().ok()?,
        total: total_part.parse().ok()?,
    })
}

/// Parse `bytes */N` (the 416 form of `Content-Range`) and extract `N`.
fn parse_unsatisfiable_total(value: &str) -> Option<u64> {
    value.strip_prefix("bytes */")?.parse().ok()
}

#[async_trait]
impl AsyncContentStore<O256> for AsyncHttpBackend {
    async fn get_slice(&self, key: &O256, range: Range<u64>) -> Result<Bytes, StoreError> {
        // Empty range: existence check via head + empty result.
        if range.start >= range.end {
            self.head(key).await?;
            return Ok(Bytes::new());
        }
        let byte_range = ByteRange::Closed {
            start: range.start,
            end: range.end - 1,
        };
        let path = format!("/api/blobs/{key}");
        let (status, hdrs, body) = self
            .request_full("GET", &path, Some(&byte_range.to_http_header()), Bytes::new())
            .await?;
        match status {
            // 206 is the normal partial response; 200 means the server
            // ignored the Range: header and sent the whole blob.
            200 | 206 => Ok(Bytes::from(body)),
            404 => Err(StoreError::NotFound),
            416 => Err(StoreError::RangeNotSatisfiable {
                total: hdrs
                    .get(hyper::header::CONTENT_RANGE)
                    .and_then(|v| v.to_str().ok())
                    .and_then(parse_unsatisfiable_total)
                    .unwrap_or(0),
            }),
            _ => Err(StoreError::Io(format!(
                "HTTP {status}: {}",
                String::from_utf8_lossy(&body)
            ))),
        }
    }

    async fn head(&self, key: &O256) -> Result<BlobInfo, StoreError> {
        let path = format!("/api/blobs/{key}");
        let (status, hdrs, _body) = self
            .request_full("HEAD", &path, None, Bytes::new())
            .await?;
        match status {
            200 => {
                let size = hdrs
                    .get(hyper::header::CONTENT_LENGTH)
                    .and_then(|v| v.to_str().ok())
                    .and_then(|s| s.parse::<u64>().ok())
                    .ok_or_else(|| StoreError::Io("missing Content-Length".into()))?;
                Ok(BlobInfo { size })
            }
            404 => Err(StoreError::NotFound),
            _ => Err(StoreError::Io(format!("HTTP {status}"))),
        }
    }

    async fn insert(&self, data: Bytes) -> Result<O256, StoreError> {
        let (status, _hdrs, body) = self
            .request_full("POST", "/api/blobs", None, data)
            .await?;
        if !(200..300).contains(&status) {
            return Err(StoreError::Io(format!(
                "HTTP {status}: {}",
                String::from_utf8_lossy(&body)
            )));
        }
        let json: HashResponse = serde_json::from_slice(&body)
            .map_err(|e| StoreError::Io(format!("parse: {e}")))?;
        O256::from_hex(&json.hash)
            .ok_or_else(|| StoreError::Io(format!("invalid hash: {}", json.hash)))
    }

    async fn put(&self, key: O256, data: Bytes) -> Result<(), StoreError> {
        // The /api/blobs surface is content-addressed and POST-only; we
        // upload via POST and verify the server's computed hash matches
        // the caller's expectation.
        let computed = self.insert(data).await?;
        if computed != key {
            return Err(StoreError::Io(format!(
                "hash mismatch: expected {key}, got {computed}"
            )));
        }
        Ok(())
    }

    /// One HTTP round trip — the server returns `body + Content-Range`
    /// together, so we beat the default `head` + `get_slice` chain.
    async fn get_range(
        &self,
        key: &O256,
        range: ByteRange,
    ) -> Result<(Bytes, ResolvedRange), StoreError> {
        let path = format!("/api/blobs/{key}");
        let (status, hdrs, body) = self
            .request_full("GET", &path, Some(&range.to_http_header()), Bytes::new())
            .await?;
        match status {
            206 => {
                let resolved = hdrs
                    .get(hyper::header::CONTENT_RANGE)
                    .and_then(|v| v.to_str().ok())
                    .and_then(parse_content_range)
                    .ok_or_else(|| {
                        StoreError::Io("missing or malformed Content-Range".into())
                    })?;
                Ok((Bytes::from(body), resolved))
            }
            200 => {
                // Server didn't honor Range: header — synthesize ResolvedRange
                // from the full body length.
                let total = body.len() as u64;
                Ok((
                    Bytes::from(body),
                    ResolvedRange {
                        start: 0,
                        end: total.saturating_sub(1),
                        total,
                    },
                ))
            }
            404 => Err(StoreError::NotFound),
            416 => Err(StoreError::RangeNotSatisfiable {
                total: hdrs
                    .get(hyper::header::CONTENT_RANGE)
                    .and_then(|v| v.to_str().ok())
                    .and_then(parse_unsatisfiable_total)
                    .unwrap_or(0),
            }),
            _ => Err(StoreError::Io(format!(
                "HTTP {status}: {}",
                String::from_utf8_lossy(&body)
            ))),
        }
    }
}

impl AsyncBackend for AsyncHttpBackend {
    fn info(&self) -> BackendInfo {
        BackendInfo {
            kind: "http".to_string(),
            target: if let Some(ref path) = self.socket_path {
                format!("unix:{path}")
            } else {
                self.base_url.clone()
            },
        }
    }

    async fn store_blob(&self, data: &[u8]) -> Result<O256, KernelError> {
        let resp = self.post_bytes("/api/blobs", data).await?;
        let json: HashResponse =
            serde_json::from_slice(&resp).map_err(|e| KernelError::Store(format!("parse: {e}")))?;
        O256::from_hex(&json.hash)
            .ok_or_else(|| KernelError::Store(format!("invalid hash: {}", json.hash)))
    }

    async fn get_blob(&self, hash: &O256) -> Result<Option<Vec<u8>>, KernelError> {
        let path = format!("/api/blobs/{hash}");
        match self.get(&path).await {
            Ok(data) => Ok(Some(data)),
            Err(KernelError::NotFound(_)) => Ok(None),
            Err(e) => Err(e),
        }
    }

    async fn has_blob(&self, hash: &O256) -> Result<bool, KernelError> {
        let path = format!("/api/blobs/{hash}");
        match self.head_status(&path).await {
            Ok(status) => Ok(status == 200),
            Err(KernelError::NotFound(_)) => Ok(false),
            Err(e) => Err(e),
        }
    }

    async fn blob_count(&self) -> Result<Option<usize>, KernelError> {
        let resp = self.get("/api/blobs").await?;
        let json: BlobStatsResponse =
            serde_json::from_slice(&resp).map_err(|e| KernelError::Store(format!("parse: {e}")))?;
        Ok(json.count)
    }

}
