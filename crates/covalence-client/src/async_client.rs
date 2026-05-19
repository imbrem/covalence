use covalence_hash::O256;
use covalence_kernel::{AsyncBackend, BackendInfo, Decision, KernelError};
use http_body_util::{BodyExt, Full};
use hyper::body::Bytes;
use hyper_util::client::legacy::Client;
use hyper_util::rt::TokioExecutor;
use serde::Deserialize;

/// Async HTTP backend using hyper. Supports TCP and Unix domain sockets.
pub struct AsyncHttpBackend {
    base_url: String,
    /// If set, connect via Unix domain socket instead of TCP.
    socket_path: Option<String>,
}

impl AsyncHttpBackend {
    /// Create a new async HTTP backend connecting to the given URL (TCP).
    pub fn new(base_url: String) -> Self {
        Self {
            base_url,
            socket_path: None,
        }
    }

    /// Create a new async HTTP backend connecting via a Unix domain socket.
    pub fn unix(socket_path: String) -> Self {
        Self {
            base_url: "http://localhost".to_string(),
            socket_path: Some(socket_path),
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
        let client = Client::builder(TokioExecutor::new()).build_http::<Full<Bytes>>();
        let uri: hyper::Uri = url
            .parse()
            .map_err(|e| KernelError::Store(format!("invalid URL: {e}")))?;
        let resp = client
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

    async fn post_bytes(&self, path: &str, data: &[u8]) -> Result<Vec<u8>, KernelError> {
        if let Some(ref socket_path) = self.socket_path {
            self.unix_post(socket_path, path, data).await
        } else {
            let url = format!("{}{}", self.base_url, path);
            self.tcp_post(&url, data).await
        }
    }

    async fn tcp_post(&self, url: &str, data: &[u8]) -> Result<Vec<u8>, KernelError> {
        let client = Client::builder(TokioExecutor::new()).build_http::<Full<Bytes>>();
        let uri: hyper::Uri = url
            .parse()
            .map_err(|e| KernelError::Store(format!("invalid URL: {e}")))?;

        let req = hyper::Request::builder()
            .method("POST")
            .uri(uri)
            .header("content-type", "application/octet-stream")
            .body(Full::new(Bytes::from(data.to_vec())))
            .map_err(|e| KernelError::Store(format!("build request: {e}")))?;

        let resp = client
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

#[derive(Deserialize)]
struct HashResponse {
    hash: String,
}

#[derive(Deserialize)]
struct BlobCountResponse {
    count: Option<usize>,
}

#[derive(Deserialize)]
struct DecideResponse {
    result: String,
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
        match self.get(&path).await {
            Ok(_) => Ok(true),
            Err(KernelError::NotFound(_)) => Ok(false),
            Err(e) => Err(e),
        }
    }

    async fn blob_count(&self) -> Result<Option<usize>, KernelError> {
        let resp = self.get("/api/blobs").await?;
        let json: BlobCountResponse =
            serde_json::from_slice(&resp).map_err(|e| KernelError::Store(format!("parse: {e}")))?;
        Ok(json.count)
    }

    async fn decide(&self, hash: &O256) -> Result<Decision, KernelError> {
        let path = format!("/api/decide/{hash}");
        let resp = self.get(&path).await?;
        let json: DecideResponse =
            serde_json::from_slice(&resp).map_err(|e| KernelError::Store(format!("parse: {e}")))?;
        json.result
            .parse()
            .map_err(|e: String| KernelError::Store(e))
    }
}
