use axum::Json;
use axum::body::Bytes;
use axum::extract::Path;
use axum::extract::ws::{Message, WebSocket, WebSocketUpgrade};
use axum::http::StatusCode;
use axum::response::IntoResponse;
use covalence_hash::O256;
use covalence_kernel::{Kernel, SyncBackend};
use covalence_store::ContentStore;
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Existing endpoints
// ---------------------------------------------------------------------------

#[derive(Serialize)]
pub struct InfoResponse {
    pub version: String,
    pub cog_version: String,
    pub target: String,
    pub cwd: String,
}

pub async fn info(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
) -> Json<InfoResponse> {
    let cwd = std::env::current_dir()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|_| "unknown".into());

    Json(InfoResponse {
        version: state.version.to_owned(),
        cog_version: covalence_git::VERSION.to_owned(),
        target: state.target.to_owned(),
        cwd,
    })
}

#[derive(Serialize)]
pub struct HealthResponse {
    pub status: &'static str,
    pub version: String,
    pub cog_version: String,
    pub target: String,
    pub uptime_secs: f64,
}

pub async fn health(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
) -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "ok",
        version: state.version.to_owned(),
        cog_version: covalence_git::VERSION.to_owned(),
        target: state.target.to_owned(),
        uptime_secs: state.started.elapsed().as_secs_f64(),
    })
}

// ---------------------------------------------------------------------------
// WebSocket REPL (legacy, kept for backward compat)
// ---------------------------------------------------------------------------

pub async fn repl_ws(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    ws: WebSocketUpgrade,
) -> impl IntoResponse {
    let kernel = state.kernel.clone();
    ws.on_upgrade(move |socket| handle_repl_ws(socket, kernel))
}

async fn handle_repl_ws(mut socket: WebSocket, kernel: Kernel) {
    let mut session = crate::eval::server_session(kernel);

    while let Some(Ok(msg)) = socket.recv().await {
        let input = match msg {
            Message::Text(t) => t.to_string(),
            Message::Close(_) => break,
            _ => continue,
        };

        let result = tokio::task::spawn_blocking(move || {
            let result = session.eval(&input);
            (session, result)
        })
        .await;

        match result {
            Ok((s, output)) => {
                session = s;
                if socket.send(Message::Text(output.into())).await.is_err() {
                    break;
                }
            }
            Err(e) => {
                let _ = socket
                    .send(Message::Text(format!("error: {e}").into()))
                    .await;
                break;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Blob endpoints
// ---------------------------------------------------------------------------

#[derive(Serialize)]
pub struct HashResponse {
    pub hash: String,
}

/// POST /api/blobs — store blob (body = raw bytes) → 201 { "hash": "<hex>" }
pub async fn blob_store(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    body: Bytes,
) -> impl IntoResponse {
    let hash = state.kernel.store().insert(&body);
    (
        StatusCode::CREATED,
        Json(HashResponse {
            hash: hash.to_string(),
        }),
    )
}

/// GET /api/blobs — blob count → { "count": N }
pub async fn blob_list(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
) -> Json<BlobStatsResponse> {
    let count = state.kernel.store().len();
    Json(BlobStatsResponse { count })
}

#[derive(Serialize)]
pub struct BlobStatsResponse {
    pub count: Option<usize>,
}

/// GET /api/blobs/:hash — get blob → raw bytes (application/octet-stream)
pub async fn blob_get(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = match O256::from_hex(&hash_hex) {
        Some(h) => h,
        None => return Err((StatusCode::BAD_REQUEST, "invalid hash")),
    };
    match state.kernel.store().get(&hash) {
        Some(data) => Ok((
            [(axum::http::header::CONTENT_TYPE, "application/octet-stream")],
            data,
        )),
        None => Err((StatusCode::NOT_FOUND, "blob not found")),
    }
}

/// HEAD /api/blobs/:hash — check if blob exists → 200 or 404
pub async fn blob_head(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> StatusCode {
    let hash = match O256::from_hex(&hash_hex) {
        Some(h) => h,
        None => return StatusCode::BAD_REQUEST,
    };
    if state.kernel.store().contains(&hash) {
        StatusCode::OK
    } else {
        StatusCode::NOT_FOUND
    }
}

// ---------------------------------------------------------------------------
// Eval endpoint
// ---------------------------------------------------------------------------

/// POST /api/eval — evaluate S-expression (body = text/plain) → text/plain result
pub async fn eval(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    body: String,
) -> impl IntoResponse {
    let kernel = state.kernel.clone();
    let result = tokio::task::spawn_blocking(move || {
        let mut session = crate::eval::server_session(kernel);
        session.eval(&body)
    })
    .await
    .unwrap_or_else(|e| format!("error: {e}"));

    ([(axum::http::header::CONTENT_TYPE, "text/plain")], result)
}

// ---------------------------------------------------------------------------
// Decide endpoint
// ---------------------------------------------------------------------------

/// GET /api/decide/:hash — decide proposition → { "result": "true"|"unknown"|"false" }
pub async fn decide(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = match O256::from_hex(&hash_hex) {
        Some(h) => h,
        None => return Err((StatusCode::BAD_REQUEST, "invalid hash".to_string())),
    };
    let kernel = state.kernel.clone();
    let result =
        tokio::task::spawn_blocking(move || kernel.decide(&hash).map_err(|e| e.to_string()))
            .await
            .unwrap_or_else(|e| Err(format!("task error: {e}")));

    match result {
        Ok(r) => Ok(Json(DecideResponse {
            result: r.to_string(),
        })),
        Err(e) => Err((StatusCode::BAD_REQUEST, e)),
    }
}

#[derive(Serialize)]
pub struct DecideResponse {
    pub result: String,
}

// ---------------------------------------------------------------------------
// Convenience endpoints
// ---------------------------------------------------------------------------

/// POST /api/blobs/url — fetch URL, store as blob → 201 { "hash": "<hex>" }
pub async fn blob_store_url(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Json(req): Json<UrlRequest>,
) -> impl IntoResponse {
    let kernel = state.kernel.clone();
    let result = tokio::task::spawn_blocking(move || {
        let body = ureq::get(&req.url)
            .call()
            .map_err(|e| format!("fetch error: {e}"))?
            .into_body()
            .read_to_vec()
            .map_err(|e| format!("read error: {e}"))?;
        let hash = kernel.store().insert(&body);
        Ok::<_, String>(hash)
    })
    .await
    .unwrap_or_else(|e| Err(format!("task error: {e}")));

    match result {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((StatusCode::BAD_REQUEST, e)),
    }
}

#[derive(Deserialize)]
pub struct UrlRequest {
    pub url: String,
}

/// POST /api/blobs/file — store file → 201 { "hash": "<hex>" }
pub async fn blob_store_file(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Json(req): Json<FileRequest>,
) -> impl IntoResponse {
    match std::fs::read(&req.path) {
        Ok(data) => {
            let hash = state.kernel.store().insert(&data);
            Ok((
                StatusCode::CREATED,
                Json(HashResponse {
                    hash: hash.to_string(),
                }),
            ))
        }
        Err(e) => Err((StatusCode::BAD_REQUEST, format!("read error: {e}"))),
    }
}

#[derive(Deserialize)]
pub struct FileRequest {
    pub path: String,
}
