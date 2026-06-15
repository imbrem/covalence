use covalence_hash::O256;
use covalence_shell::{BackendInfo, KernelError, SyncBackend};

use crate::types::{BlobStatsResponse, HashResponse};

/// Blocking HTTP backend using ureq (TCP) or raw HTTP/1.1 (Unix domain socket).
pub struct SyncHttpBackend {
    base_url: String,
    /// If set, connect via Unix domain socket instead of TCP.
    socket_path: Option<String>,
}

impl SyncHttpBackend {
    /// Create a new HTTP backend connecting to the given URL (TCP).
    pub fn new(base_url: String) -> Self {
        Self {
            base_url,
            socket_path: None,
        }
    }

    /// Create a new HTTP backend connecting via a Unix domain socket.
    pub fn unix(socket_path: String) -> Self {
        Self {
            base_url: "http://localhost".to_string(),
            socket_path: Some(socket_path),
        }
    }

    fn get(&self, path: &str) -> Result<Vec<u8>, KernelError> {
        if let Some(ref socket) = self.socket_path {
            unix_get(socket, path)
        } else {
            let url = format!("{}{}", self.base_url, path);
            let resp = ureq::get(&url).call().map_err(ureq_error)?;
            resp.into_body()
                .read_to_vec()
                .map_err(|e| KernelError::Store(format!("read body: {e}")))
        }
    }

    fn head(&self, path: &str) -> Result<u16, KernelError> {
        if let Some(ref socket) = self.socket_path {
            unix_head(socket, path)
        } else {
            let url = format!("{}{}", self.base_url, path);
            let resp = ureq::head(&url).call().map_err(ureq_error)?;
            Ok(resp.status().as_u16())
        }
    }

    fn post_bytes(&self, path: &str, body: &[u8]) -> Result<Vec<u8>, KernelError> {
        if let Some(ref socket) = self.socket_path {
            unix_post(socket, path, body)
        } else {
            let url = format!("{}{}", self.base_url, path);
            let resp = ureq::post(&url)
                .header("content-type", "application/octet-stream")
                .send(body)
                .map_err(ureq_error)?;
            resp.into_body()
                .read_to_vec()
                .map_err(|e| KernelError::Store(format!("read body: {e}")))
        }
    }

    fn post_json(&self, path: &str, body: &str) -> Result<Vec<u8>, KernelError> {
        if let Some(ref socket) = self.socket_path {
            unix_post_json(socket, path, body.as_bytes())
        } else {
            let url = format!("{}{}", self.base_url, path);
            let resp = ureq::post(&url)
                .header("content-type", "application/json")
                .send(body.as_bytes())
                .map_err(ureq_error)?;
            resp.into_body()
                .read_to_vec()
                .map_err(|e| KernelError::Store(format!("read body: {e}")))
        }
    }
}

/// Perform a GET request over a Unix domain socket using raw HTTP/1.1.
#[cfg(unix)]
fn unix_get(socket_path: &str, path: &str) -> Result<Vec<u8>, KernelError> {
    use std::io::{Read, Write};
    use std::os::unix::net::UnixStream;

    let mut stream = UnixStream::connect(socket_path)
        .map_err(|e| KernelError::Store(format!("unix connect: {e}")))?;

    let request = format!("GET {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    stream
        .write_all(request.as_bytes())
        .map_err(|e| KernelError::Store(format!("write: {e}")))?;

    let mut response = Vec::new();
    stream
        .read_to_end(&mut response)
        .map_err(|e| KernelError::Store(format!("read: {e}")))?;

    parse_http_response(&response)
}

/// Perform a POST request over a Unix domain socket using raw HTTP/1.1.
#[cfg(unix)]
fn unix_post(socket_path: &str, path: &str, body: &[u8]) -> Result<Vec<u8>, KernelError> {
    unix_post_with(socket_path, path, body, "application/octet-stream")
}

#[cfg(unix)]
fn unix_post_json(socket_path: &str, path: &str, body: &[u8]) -> Result<Vec<u8>, KernelError> {
    unix_post_with(socket_path, path, body, "application/json")
}

#[cfg(unix)]
fn unix_post_with(
    socket_path: &str,
    path: &str,
    body: &[u8],
    content_type: &str,
) -> Result<Vec<u8>, KernelError> {
    use std::io::{Read, Write};
    use std::os::unix::net::UnixStream;

    let mut stream = UnixStream::connect(socket_path)
        .map_err(|e| KernelError::Store(format!("unix connect: {e}")))?;

    let request = format!(
        "POST {path} HTTP/1.1\r\nHost: localhost\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream
        .write_all(request.as_bytes())
        .map_err(|e| KernelError::Store(format!("write: {e}")))?;
    stream
        .write_all(body)
        .map_err(|e| KernelError::Store(format!("write body: {e}")))?;

    let mut response = Vec::new();
    stream
        .read_to_end(&mut response)
        .map_err(|e| KernelError::Store(format!("read: {e}")))?;

    parse_http_response(&response)
}

/// Perform a HEAD request over a Unix domain socket using raw HTTP/1.1.
#[cfg(unix)]
fn unix_head(socket_path: &str, path: &str) -> Result<u16, KernelError> {
    use std::io::{Read, Write};
    use std::os::unix::net::UnixStream;

    let mut stream = UnixStream::connect(socket_path)
        .map_err(|e| KernelError::Store(format!("unix connect: {e}")))?;

    let request = format!("HEAD {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    stream
        .write_all(request.as_bytes())
        .map_err(|e| KernelError::Store(format!("write: {e}")))?;

    let mut response = Vec::new();
    stream
        .read_to_end(&mut response)
        .map_err(|e| KernelError::Store(format!("read: {e}")))?;

    // Parse just the status line
    let header_end = response
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .ok_or_else(|| KernelError::Store("malformed HTTP response".to_string()))?;
    let header_str = std::str::from_utf8(&response[..header_end])
        .map_err(|_| KernelError::Store("invalid HTTP headers".to_string()))?;
    let status_line = header_str
        .lines()
        .next()
        .ok_or_else(|| KernelError::Store("empty response".to_string()))?;
    let status: u16 = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .ok_or_else(|| KernelError::Store("malformed HTTP status line".to_string()))?;
    Ok(status)
}

#[cfg(not(unix))]
fn unix_head(_socket_path: &str, _path: &str) -> Result<u16, KernelError> {
    Err(KernelError::Store(
        "Unix domain sockets not supported on this platform".to_string(),
    ))
}

#[cfg(not(unix))]
fn unix_get(_socket_path: &str, _path: &str) -> Result<Vec<u8>, KernelError> {
    Err(KernelError::Store(
        "Unix domain sockets not supported on this platform".to_string(),
    ))
}

#[cfg(not(unix))]
fn unix_post(_socket_path: &str, _path: &str, _body: &[u8]) -> Result<Vec<u8>, KernelError> {
    Err(KernelError::Store(
        "Unix domain sockets not supported on this platform".to_string(),
    ))
}

#[cfg(not(unix))]
fn unix_post_json(_socket_path: &str, _path: &str, _body: &[u8]) -> Result<Vec<u8>, KernelError> {
    Err(KernelError::Store(
        "Unix domain sockets not supported on this platform".to_string(),
    ))
}

/// Parse a raw HTTP/1.1 response, extracting status and body.
fn parse_http_response(response: &[u8]) -> Result<Vec<u8>, KernelError> {
    // Find the end of headers
    let header_end = response
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .ok_or_else(|| KernelError::Store("malformed HTTP response".to_string()))?;

    let header_str = std::str::from_utf8(&response[..header_end])
        .map_err(|_| KernelError::Store("invalid HTTP headers".to_string()))?;

    // Parse status line
    let status_line = header_str
        .lines()
        .next()
        .ok_or_else(|| KernelError::Store("empty response".to_string()))?;
    let status: u16 = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .ok_or_else(|| KernelError::Store("malformed HTTP status line".to_string()))?;

    let body = response[header_end + 4..].to_vec();

    if status == 404 {
        return Err(KernelError::NotFound("not found".to_string()));
    }
    if status >= 400 {
        let msg = String::from_utf8_lossy(&body).to_string();
        return Err(KernelError::Store(format!("HTTP {status}: {msg}")));
    }
    Ok(body)
}

impl SyncBackend for SyncHttpBackend {
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

    fn store_blob(&self, data: &[u8]) -> Result<O256, KernelError> {
        let resp = self.post_bytes("/api/blobs", data)?;
        let json: HashResponse =
            serde_json::from_slice(&resp).map_err(|e| KernelError::Store(format!("parse: {e}")))?;
        O256::from_hex(&json.hash)
            .ok_or_else(|| KernelError::Store(format!("invalid hash: {}", json.hash)))
    }

    fn get_blob(&self, hash: &O256) -> Result<Option<Vec<u8>>, KernelError> {
        let path = format!("/api/blobs/{hash}");
        match self.get(&path) {
            Ok(data) => Ok(Some(data)),
            Err(KernelError::NotFound(_)) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn has_blob(&self, hash: &O256) -> Result<bool, KernelError> {
        let path = format!("/api/blobs/{hash}");
        match self.head(&path) {
            Ok(status) => Ok(status == 200),
            Err(KernelError::NotFound(_)) => Ok(false),
            Err(e) => Err(e),
        }
    }

    fn blob_count(&self) -> Result<Option<usize>, KernelError> {
        let resp = self.get("/api/blobs")?;
        let json: BlobStatsResponse =
            serde_json::from_slice(&resp).map_err(|e| KernelError::Store(format!("parse: {e}")))?;
        Ok(json.count)
    }

    fn register_tag(&self, tag: &str, content_hash: O256) -> Result<O256, KernelError> {
        let body = format!("{{\"tag\":{:?},\"contentHash\":\"{}\"}}", tag, content_hash);
        let resp = self.post_json("/api/objects/tag", &body)?;
        let json: HashResponse = serde_json::from_slice::<TagRegisterResponse>(&resp)
            .map(|r| HashResponse { hash: r.keyed })
            .map_err(|e| KernelError::Store(format!("parse: {e}")))?;
        O256::from_hex(&json.hash)
            .ok_or_else(|| KernelError::Store(format!("invalid keyed hash: {}", json.hash)))
    }

    fn lookup_tag(&self, keyed: &O256) -> Result<Option<(String, O256)>, KernelError> {
        let path = format!("/api/objects/tag/{keyed}");
        let resp = match self.get(&path) {
            Ok(data) => data,
            Err(KernelError::NotFound(_)) => return Ok(None),
            Err(e) => return Err(e),
        };
        let json: TagLookupResponse =
            serde_json::from_slice(&resp).map_err(|e| KernelError::Store(format!("parse: {e}")))?;
        let content_hash = O256::from_hex(&json.content_hash).ok_or_else(|| {
            KernelError::Store(format!("invalid content hash: {}", json.content_hash))
        })?;
        Ok(Some((json.tag, content_hash)))
    }
}

#[derive(serde::Deserialize)]
struct TagRegisterResponse {
    keyed: String,
}

#[derive(serde::Deserialize)]
struct TagLookupResponse {
    tag: String,
    #[serde(rename = "contentHash")]
    content_hash: String,
}

fn ureq_error(e: ureq::Error) -> KernelError {
    match &e {
        ureq::Error::StatusCode(status) if *status == 404 => KernelError::NotFound(e.to_string()),
        ureq::Error::StatusCode(_) => KernelError::Store(e.to_string()),
        _ => KernelError::Store(format!("connection: {e}")),
    }
}
