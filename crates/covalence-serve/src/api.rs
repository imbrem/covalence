use axum::Json;
use axum::body::Bytes;
use axum::extract::Path;
use axum::extract::ws::{Message, WebSocket, WebSocketUpgrade};
use axum::http::{HeaderMap, StatusCode};
use axum::response::{IntoResponse, Response};
use covalence_hash::O256;
use covalence_object::{
    Dir, DirMode, DirRow, Sha256Identity, Table, TableBuilder, git_tree_bytes_mapped,
    git_tree_to_dir_rows_mapped,
};
use covalence_shell::Kernel;
use covalence_store::{Blob, ContentStore, GitObjectType, ObjectStore, StoreError, Tree};
use serde::{Deserialize, Serialize};

use crate::range_http::{serve_blob_get, serve_blob_head};

const BLOB_CONTENT_TYPE: &str = "application/octet-stream";

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
// WebSocket REPL
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
// TEMPORARY / DEMO: Metamath import WebSocket
//
// Powers the `/metamath` demo page in apps/covalence-web. Streams a
// per-theorem HOL-kernel import of a Metamath `.mm` database. This is a
// throwaway UX endpoint, not part of the stable API surface.
// ---------------------------------------------------------------------------

/// GET /api/mm/import — temporary streaming Metamath-import WebSocket.
///
/// **Two-phase, live-status protocol** (all frames are JSON text):
///   - first client frame: the raw `.mm` source.
///   - server, once parsed: `{"type":"parsed","total":N}` (N = logical `$p`
///     count).
///   - **graph phase** — the whole static declaration graph streams first, in
///     batches: `{"type":"decl","items":[{label,mm,ess,deps,proof}, …]}`
///     (every theorem shown immediately, *pending*), terminated by
///     `{"type":"graphDone"}`.
///   - **prove phase** — a parallel worker pool flips each theorem live:
///     `{"type":"proving","label"}` when a worker picks it up, then
///     `{"type":"proved","done","total","label","ok",hyps?,genuine?,
///     holPreview?,importMs?,error?}` on completion (static fields are NOT
///     repeated — they came in `decl`).
///   - finally `{"type":"done","ok","total","elapsedMs"}`.
///   - parse failure → `{"type":"error","message"}`.
///
/// This is the seed of a general **task view** of a covalence proof DB: each
/// theorem is a task with a status (`pending`/`proving`/`proved`/`error`); a
/// future multi-logic view would add e.g. a `translating` state and per-logic
/// columns over the same graph.
pub async fn mm_import_ws(
    axum::extract::State(_state): axum::extract::State<crate::AppState>,
    ws: WebSocketUpgrade,
) -> impl IntoResponse {
    ws.on_upgrade(handle_mm_import_ws)
}

async fn handle_mm_import_ws(mut socket: WebSocket) {
    // The first message carries the raw `.mm` source.
    let source = loop {
        match socket.recv().await {
            Some(Ok(Message::Text(t))) => break t.to_string(),
            Some(Ok(Message::Close(_))) | None => return,
            Some(Ok(_)) => continue, // ignore pings/binary
            Some(Err(_)) => return,
        }
    };

    // Stream results from the blocking import task over an mpsc channel.
    let (tx, mut rx) = tokio::sync::mpsc::channel::<String>(64);

    std::thread::spawn(move || mm_import_worker(source, tx));

    while let Some(msg) = rx.recv().await {
        if socket.send(Message::Text(msg.into())).await.is_err() {
            break;
        }
    }
    let _ = socket.send(Message::Close(None)).await;
}

/// Build a `{"type":"error",...}` frame.
fn mm_err_frame(message: impl std::fmt::Display) -> String {
    serde_json::json!({ "type": "error", "message": message.to_string() }).to_string()
}

/// Compute the **static** declaration data for one theorem label: the rendered
/// Metamath conclusion (`mm`), essential hypotheses (`ess`), proof code
/// (`proof`), and the deduped logical (`|-`) dependency list (`deps`). This is
/// the graph-phase payload — everything about a theorem that doesn't depend on
/// (re-)deriving its proof through the kernel.
fn mm_decl_item(db: &covalence_hol::metamath::Database, label: &str) -> serde_json::Value {
    use covalence_metamath::database::{Proof, Statement};
    use covalence_metamath::{ProofStep, proof_steps};

    let (mm, ess, proof, deps) = match db.statement_by_label(label) {
        Some(Statement::Assert(a)) => {
            let proof = match &a.proof {
                Some(Proof::Normal(labels)) => labels.join(" "),
                Some(Proof::Compressed { labels, letters }) => format!(
                    "( {} ) {}",
                    labels.join(" "),
                    String::from_utf8_lossy(letters)
                ),
                None => String::new(),
            };
            // Deduped (first-seen order) logical assertions referenced by the
            // proof. Skip Save/Heap steps and syntax formers (typecode != "|-").
            // kind: thm if the dep has its own proof, else df* → def, else axiom.
            let mut deps: Vec<serde_json::Value> = Vec::new();
            let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
            if let Ok(steps) = proof_steps(db, a) {
                for step in &steps {
                    let ProofStep::Label(l) = step else { continue };
                    if seen.contains(l) {
                        continue;
                    }
                    let Some(Statement::Assert(dep)) = db.statement_by_label(l) else {
                        continue;
                    };
                    if dep.conclusion.typecode() != "|-" {
                        continue;
                    }
                    seen.insert(l.clone());
                    let kind = if dep.proof.is_some() {
                        "thm"
                    } else if l.starts_with("df") {
                        "def"
                    } else {
                        "axiom"
                    };
                    deps.push(serde_json::json!({ "label": l, "kind": kind }));
                }
            }
            (
                a.conclusion.render(),
                a.frame.essentials.iter().map(|h| h.expr.render()).collect::<Vec<_>>(),
                proof,
                deps,
            )
        }
        _ => (String::new(), Vec::new(), String::new(), Vec::new()),
    };
    serde_json::json!({
        "label": label, "mm": mm, "ess": ess, "proof": proof, "deps": deps,
    })
}

/// The blocking import worker: a **two-phase** stream.
///
/// 1. **Graph phase** — parse, then stream the static declaration graph for
///    every logical (`|-`) `$p` theorem in batches of `decl` frames (each
///    theorem shown immediately, *pending*), terminated by `graphDone`. The
///    `parsed` total goes out first.
/// 2. **Prove phase** — derive each theorem **in parallel** across a thread
///    pool: `proving` when a worker picks a label up, `proved` (ok/error) on
///    completion. Static fields are not repeated (they came in `decl`). The
///    `done` field is a monotonic 1..total counter for the progress bar.
///
/// Runs on a dedicated thread (the `std::thread::scope` pool blocks it until the
/// whole import finishes). `tx` clones are cheap; the `on_pick`/`on_each`
/// closures send through clones from worker threads.
fn mm_import_worker(source: String, tx: tokio::sync::mpsc::Sender<String>) {
    use covalence_hol::metalogic::mm_import::{import_theorems_parallel, theorem_labels};
    use std::sync::atomic::{AtomicUsize, Ordering};

    let started = std::time::Instant::now();

    let db = match covalence_hol::metamath::parse(&source) {
        Ok(db) => db,
        Err(e) => {
            let _ = tx.blocking_send(mm_err_frame(format!("parse error: {e}")));
            return;
        }
    };

    // --- Phase 1: graph -----------------------------------------------------
    let labels = theorem_labels(&db);
    let total = labels.len();
    let _ = tx.blocking_send(serde_json::json!({ "type": "parsed", "total": total }).to_string());

    const DECL_BATCH: usize = 1000;
    let mut batch: Vec<serde_json::Value> = Vec::with_capacity(DECL_BATCH);
    for label in &labels {
        batch.push(mm_decl_item(&db, label));
        if batch.len() >= DECL_BATCH {
            let _ = tx.blocking_send(
                serde_json::json!({ "type": "decl", "items": batch }).to_string(),
            );
            batch = Vec::with_capacity(DECL_BATCH);
        }
    }
    if !batch.is_empty() {
        let _ = tx.blocking_send(serde_json::json!({ "type": "decl", "items": batch }).to_string());
    }
    let _ = tx.blocking_send(serde_json::json!({ "type": "graphDone" }).to_string());

    // --- Phase 2: prove -----------------------------------------------------
    let n_ok = AtomicUsize::new(0);
    let grand_total = AtomicUsize::new(0);
    let pick_tx = tx.clone();

    import_theorems_parallel(
        &db,
        0, // 0 → use available_parallelism
        |total| {
            grand_total.store(total, Ordering::Relaxed);
        },
        |label| {
            let _ = pick_tx
                .blocking_send(serde_json::json!({ "type": "proving", "label": label }).to_string());
        },
        |done, total, label, result, elapsed| {
            let import_ms = elapsed.as_micros() as f64 / 1000.0;
            let frame = match result {
                Ok(thm) => {
                    n_ok.fetch_add(1, Ordering::Relaxed);
                    let full = format!("{}", thm.concl());
                    let hol_preview: String = full.chars().take(400).collect();
                    serde_json::json!({
                        "type": "proved", "done": done, "total": total,
                        "label": label, "ok": true,
                        "hyps": thm.hyps().len(),
                        "genuine": thm.has_no_obs(),
                        "holPreview": hol_preview,
                        "importMs": import_ms,
                    })
                }
                Err(e) => serde_json::json!({
                    "type": "proved", "done": done, "total": total,
                    "label": label, "ok": false, "error": e.to_string(),
                    "importMs": import_ms,
                }),
            };
            let _ = tx.blocking_send(frame.to_string());
        },
    );

    let _ = tx.blocking_send(
        serde_json::json!({
            "type": "done",
            "ok": n_ok.load(Ordering::Relaxed),
            "total": grand_total.load(Ordering::Relaxed),
            "elapsedMs": started.elapsed().as_millis() as u64,
        })
        .to_string(),
    );
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
    match state.kernel.store().insert(&body) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
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

/// GET /api/blobs/:hash — get blob, honoring HTTP `Range:`.
///
/// Returns 200 + full body (no Range), 206 + sliced body (single range),
/// 206 + `multipart/byteranges` (multi-range), 416 (unsatisfiable), or
/// 400 (malformed Range header).
pub async fn blob_get(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
    headers: HeaderMap,
) -> Response {
    let hash = match O256::from_hex(&hash_hex) {
        Some(h) => h,
        None => return (StatusCode::BAD_REQUEST, "invalid hash").into_response(),
    };
    serve_blob_get(state.kernel.store(), &hash, &headers, BLOB_CONTENT_TYPE)
}

/// HEAD /api/blobs/:hash — `Content-Length` + `Accept-Ranges: bytes` if present.
pub async fn blob_head(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> Response {
    let hash = match O256::from_hex(&hash_hex) {
        Some(h) => h,
        None => return StatusCode::BAD_REQUEST.into_response(),
    };
    serve_blob_head(state.kernel.store(), &hash, BLOB_CONTENT_TYPE)
}

// ---------------------------------------------------------------------------
// Eval endpoint
// ---------------------------------------------------------------------------

/// POST /api/eval — stateless: evaluate S-expression (body = text/plain) → text/plain result
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
        let hash = kernel
            .store()
            .insert(&body)
            .map_err(|e| format!("store error: {e}"))?;
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
    let data = match std::fs::read(&req.path) {
        Ok(d) => d,
        Err(e) => return Err((StatusCode::BAD_REQUEST, format!("read error: {e}"))),
    };
    match state.kernel.store().insert(&data) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}

#[derive(Deserialize)]
pub struct FileRequest {
    pub path: String,
}

// ---------------------------------------------------------------------------
// Tagged store endpoints
// ---------------------------------------------------------------------------

fn parse_hash_param(hex: &str) -> Result<O256, (StatusCode, String)> {
    O256::from_hex(hex).ok_or((StatusCode::BAD_REQUEST, "invalid hash".to_string()))
}

/// POST /api/tagged — insert blob → 201 { "hash": "<hex>" }
pub async fn tagged_insert(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    body: Bytes,
) -> impl IntoResponse {
    match ContentStore::insert(&state.tagged_store, &body) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}

/// GET /api/tagged — count → { "count": N }
pub async fn tagged_count(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
) -> Json<BlobStatsResponse> {
    Json(BlobStatsResponse {
        count: ContentStore::len(&state.tagged_store),
    })
}

/// GET /api/tagged/:hash — get blob data, honoring HTTP `Range:`.
pub async fn tagged_get(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
    headers: HeaderMap,
) -> Response {
    let hash = match O256::from_hex(&hash_hex) {
        Some(h) => h,
        None => return (StatusCode::BAD_REQUEST, "invalid hash").into_response(),
    };
    serve_blob_get(&state.tagged_store, &hash, &headers, BLOB_CONTENT_TYPE)
}

/// PUT /api/tagged/:hash — put blob data
pub async fn tagged_put(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
    body: Bytes,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    match ContentStore::put(&state.tagged_store, hash, &body) {
        Ok(()) => Ok(StatusCode::OK),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}

/// HEAD /api/tagged/:hash — `Content-Length` + `Accept-Ranges: bytes` if present.
pub async fn tagged_head(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> Response {
    let hash = match O256::from_hex(&hash_hex) {
        Some(h) => h,
        None => return StatusCode::BAD_REQUEST.into_response(),
    };
    serve_blob_head(&state.tagged_store, &hash, BLOB_CONTENT_TYPE)
}

/// POST /api/tagged/kind/:kind — insert_tagged → 201 { "hash": "<hex>" }
pub async fn tagged_insert_tagged(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(kind): Path<String>,
    body: Bytes,
) -> impl IntoResponse {
    let tag = GitObjectType::new(kind);
    match state.tagged_store.insert_tagged(tag, &body) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}

/// GET /api/tagged/repr/:hash — get_repr → bytes + X-Object-Type header
pub async fn tagged_get_repr(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    match state.tagged_store.get_repr(&hash) {
        Some(data) => {
            let tag = state
                .tagged_store
                .get_tag(&hash)
                .map(|t| t.as_str().to_owned())
                .unwrap_or_default();
            Ok((
                [
                    (
                        axum::http::header::CONTENT_TYPE,
                        "application/octet-stream".to_owned(),
                    ),
                    (
                        axum::http::header::HeaderName::from_static("x-object-type"),
                        tag,
                    ),
                ],
                data,
            ))
        }
        None => Err((StatusCode::NOT_FOUND, "not found".to_string())),
    }
}

/// GET /api/tagged/tag/:hash — get_tag → { "tag": "..." }
pub async fn tagged_get_tag(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    match state.tagged_store.get_tag(&hash) {
        Some(tag) => Ok(Json(TagResponse {
            tag: tag.as_str().to_owned(),
        })),
        None => Err((StatusCode::NOT_FOUND, "not found".to_string())),
    }
}

#[derive(Serialize)]
pub struct TagResponse {
    pub tag: String,
}

// ---------------------------------------------------------------------------
// Object store endpoints
// ---------------------------------------------------------------------------

/// POST /api/objects/blob — insert blob → 201 { "hash": "<hex>" }
pub async fn object_insert_blob(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    body: Bytes,
) -> impl IntoResponse {
    match ObjectStore::insert(&state.object_store, &Blob(body.to_vec())) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}

/// POST /api/objects/tree — insert tree → 201 { "hash": "<hex>" }
pub async fn object_insert_tree(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    body: Bytes,
) -> impl IntoResponse {
    match ObjectStore::insert(&state.object_store, &Tree(body.to_vec())) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}

/// GET /api/objects/blob/:hash — get blob → bytes or 404 or error
pub async fn object_get_blob(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    let result: Result<Option<Blob>, StoreError> = ObjectStore::get(&state.object_store, &hash);
    match result {
        Ok(Some(blob)) => Ok((
            [(axum::http::header::CONTENT_TYPE, "application/octet-stream")],
            blob.0,
        )),
        Ok(None) => {
            // Fall back to the kernel blob store (REPL `(store ...)` data)
            match state.kernel.store().get(&hash) {
                Some(data) => Ok((
                    [(axum::http::header::CONTENT_TYPE, "application/octet-stream")],
                    data,
                )),
                None => Err((StatusCode::NOT_FOUND, "not found".to_string())),
            }
        }
        Err(e) => Err((StatusCode::CONFLICT, format!("{e}"))),
    }
}

/// GET /api/objects/tree/:hash — get tree → bytes or 404 or error
pub async fn object_get_tree(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    let result: Result<Option<Tree>, StoreError> = ObjectStore::get(&state.object_store, &hash);
    match result {
        Ok(Some(tree)) => Ok((
            [(axum::http::header::CONTENT_TYPE, "application/octet-stream")],
            tree.0,
        )),
        Ok(None) => Err((StatusCode::NOT_FOUND, "not found".to_string())),
        Err(e) => Err((StatusCode::CONFLICT, format!("{e}"))),
    }
}

/// HEAD /api/objects/:hash — contains (any type) → 200/404
pub async fn object_head(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> StatusCode {
    let Ok(hash) = parse_hash_param(&hash_hex) else {
        return StatusCode::BAD_REQUEST;
    };
    // Check both blob and tree types (contains() checks both for KeyedObjectStore).
    if ObjectStore::<_, Blob>::contains(&state.object_store, &hash)
        || ObjectStore::<_, Tree>::contains(&state.object_store, &hash)
    {
        StatusCode::OK
    } else {
        StatusCode::NOT_FOUND
    }
}

/// GET /api/objects/any/:hash — get_any → bytes + X-Object-Kind header
pub async fn object_get_any(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    match state.object_store.get_any(&hash) {
        Ok(Some(obj)) => {
            let kind = format!("{:?}", obj.kind).to_lowercase();
            Ok((
                [
                    (
                        axum::http::header::CONTENT_TYPE,
                        "application/octet-stream".to_owned(),
                    ),
                    (
                        axum::http::header::HeaderName::from_static("x-object-kind"),
                        kind,
                    ),
                ],
                obj.data,
            ))
        }
        Ok(None) => Err((StatusCode::NOT_FOUND, "not found".to_string())),
        Err(e) => Err((StatusCode::INTERNAL_SERVER_ERROR, format!("{e}"))),
    }
}

/// POST /api/objects/any/:kind — insert_any → 201 { "hash": "<hex>" }
pub async fn object_insert_any(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(kind): Path<String>,
    body: Bytes,
) -> impl IntoResponse {
    let obj_kind = match kind.as_str() {
        "blob" => covalence_store::ObjectKind::Blob,
        "tree" => covalence_store::ObjectKind::Tree,
        "commit" => covalence_store::ObjectKind::Commit,
        "tag" => covalence_store::ObjectKind::Tag,
        _ => return Err((StatusCode::BAD_REQUEST, format!("unknown kind: {kind}"))),
    };
    let obj = covalence_store::AnyObject {
        kind: obj_kind,
        data: body.to_vec(),
    };
    match state.object_store.insert_any(&obj) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}

// ---------------------------------------------------------------------------
// Object info endpoint
// ---------------------------------------------------------------------------

#[derive(Serialize)]
pub struct ObjectInfoResponse {
    pub kind: String,
    pub size: usize,
    /// When the requested hash is a *keyed identity* (registered in the
    /// kernel's tag registry), the tag string and the underlying content
    /// hash. `None` for plain blobs.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tag: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none", rename = "contentHash")]
    pub content_hash: Option<String>,
}

/// GET /api/objects/info/{hash} — object metadata → { "kind": "...", "size": N, … }
///
/// Resolution order:
///  1. **Tag registry** — when the hash is a keyed identity, returns
///     `kind: "tagged"` plus the tag string and the underlying content
///     hash. Size = size of the content blob.
///  2. Typed object store (trees, tagged blobs).
///  3. Kernel blob store fallback.
pub async fn object_info(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    use covalence_shell::SyncBackend;
    let hash = parse_hash_param(&hash_hex)?;

    // 1. Tag registry — keyed identities override magic-byte sniffing.
    if let Ok(Some((tag, content_hash))) = state.kernel.lookup_tag(&hash) {
        let size = state
            .kernel
            .store()
            .get(&content_hash)
            .map(|b| b.len())
            .unwrap_or(0);
        return Ok(Json(ObjectInfoResponse {
            kind: "tagged".into(),
            size,
            tag: Some(tag),
            content_hash: Some(content_hash.to_string()),
        }));
    }

    // 2. Check the typed object store (trees, tagged blobs, etc.)
    match state.object_store.get_any(&hash) {
        Ok(Some(obj)) => {
            return Ok(Json(ObjectInfoResponse {
                kind: format!("{:?}", obj.kind).to_lowercase(),
                size: obj.data.len(),
                tag: None,
                content_hash: None,
            }));
        }
        Err(e) => {
            return Err((StatusCode::INTERNAL_SERVER_ERROR, format!("{e}")));
        }
        Ok(None) => {}
    }

    // 3. Fall back to the kernel blob store
    if let Some(data) = state.kernel.store().get(&hash) {
        return Ok(Json(ObjectInfoResponse {
            kind: "blob".to_string(),
            size: data.len(),
            tag: None,
            content_hash: None,
        }));
    }

    Err((StatusCode::NOT_FOUND, "not found".to_string()))
}

// ---------------------------------------------------------------------------
// Tag registry endpoints
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
pub struct RegisterTagRequest {
    pub tag: String,
    /// Hex-encoded 32-byte content hash.
    #[serde(rename = "contentHash")]
    pub content_hash: String,
}

#[derive(Serialize)]
pub struct RegisterTagResponse {
    /// Hex-encoded 32-byte keyed identity.
    pub keyed: String,
}

#[derive(Serialize)]
pub struct LookupTagResponse {
    pub tag: String,
    /// Hex-encoded 32-byte content hash.
    #[serde(rename = "contentHash")]
    pub content_hash: String,
}

/// POST /api/objects/tag — body `{ tag, contentHash }` → `{ keyed }`.
pub async fn register_tag(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Json(req): Json<RegisterTagRequest>,
) -> Result<(StatusCode, Json<RegisterTagResponse>), (StatusCode, String)> {
    use covalence_shell::SyncBackend;
    let content_hash = O256::from_hex(&req.content_hash)
        .ok_or((StatusCode::BAD_REQUEST, "bad content hash".to_string()))?;
    let keyed = state
        .kernel
        .register_tag(&req.tag, content_hash)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    Ok((
        StatusCode::CREATED,
        Json(RegisterTagResponse {
            keyed: keyed.to_string(),
        }),
    ))
}

/// GET /api/objects/tag/{hash} → `{ tag, contentHash }` or 404.
pub async fn lookup_tag(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    use covalence_shell::SyncBackend;
    let hash = parse_hash_param(&hash_hex)?;
    match state.kernel.lookup_tag(&hash) {
        Ok(Some((tag, content_hash))) => Ok(Json(LookupTagResponse {
            tag,
            content_hash: content_hash.to_string(),
        })),
        Ok(None) => Err((StatusCode::NOT_FOUND, "not found".to_string())),
        Err(e) => Err((StatusCode::INTERNAL_SERVER_ERROR, e.to_string())),
    }
}

// ---------------------------------------------------------------------------
// Tree API endpoints
// ---------------------------------------------------------------------------

#[derive(Serialize)]
pub struct TreeEntryResponse {
    pub name: String,
    pub mode: String,
    pub hash: String,
}

fn mode_from_name(s: &str) -> Result<DirMode, (StatusCode, String)> {
    match s {
        "blob" | "regular" => Ok(DirMode::REGULAR),
        "executable" => Ok(DirMode::EXECUTABLE),
        "symlink" => Ok(DirMode::SYMLINK),
        "dir" => Ok(DirMode::DIR),
        "submodule" => Ok(DirMode::SUBMODULE),
        _ => Err((StatusCode::BAD_REQUEST, format!("unknown mode: {s}"))),
    }
}

fn get_tree_data(state: &crate::AppState, hash: &O256) -> Result<Vec<u8>, (StatusCode, String)> {
    let result: Result<Option<Tree>, StoreError> = ObjectStore::get(&state.object_store, hash);
    match result {
        Ok(Some(tree)) => Ok(tree.0),
        Ok(None) => Err((StatusCode::NOT_FOUND, "tree not found".to_string())),
        Err(e) => Err((StatusCode::CONFLICT, format!("{e}"))),
    }
}

/// GET /api/objects/tree/{hash}/ls — list tree entries → JSON array
pub async fn tree_ls(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    let data = get_tree_data(&state, &hash)?;
    let table = Table::parse(data, Dir)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("parse error: {e}")))?;

    let mut entries = Vec::with_capacity(table.num_entries());
    for i in 0..table.num_entries() {
        let row = table
            .row(i)
            .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, format!("row error: {e}")))?;
        entries.push(TreeEntryResponse {
            name: String::from_utf8_lossy(row.name).into_owned(),
            mode: row.mode.name().to_string(),
            hash: row.child.to_string(),
        });
    }
    Ok::<_, (StatusCode, String)>(Json(entries))
}

/// GET /api/objects/tree/{hash}/path/{*path} — get entry at path → JSON entry
pub async fn tree_get_path(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path((hash_hex, path)): Path<(String, String)>,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    let segments: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
    if segments.is_empty() {
        return Err((StatusCode::BAD_REQUEST, "empty path".to_string()));
    }

    let mut current_hash = hash;
    for (i, seg) in segments.iter().enumerate() {
        let data = get_tree_data(&state, &current_hash)?;
        let table = Table::parse(data, Dir)
            .map_err(|e| (StatusCode::BAD_REQUEST, format!("parse error: {e}")))?;

        let row = table.get(seg.as_bytes()).map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                format!("lookup error: {e}"),
            )
        })?;

        match row {
            Some(row) => {
                if i + 1 < segments.len() {
                    // Must be a directory to traverse further
                    if !row.mode.is_dir() {
                        return Err((StatusCode::BAD_REQUEST, format!("{seg} is not a directory")));
                    }
                    current_hash = row.child;
                } else {
                    return Ok(Json(TreeEntryResponse {
                        name: String::from_utf8_lossy(row.name).into_owned(),
                        mode: row.mode.name().to_string(),
                        hash: row.child.to_string(),
                    }));
                }
            }
            None => return Err((StatusCode::NOT_FOUND, format!("entry not found: {seg}"))),
        }
    }
    Err((StatusCode::INTERNAL_SERVER_ERROR, "unreachable".to_string()))
}

#[derive(Deserialize)]
pub struct TreeEntryInput {
    pub name: String,
    pub mode: String,
    pub hash: String,
}

/// POST /api/objects/tree/json — insert tree from JSON → { "hash": "..." }
pub async fn tree_insert_json(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Json(entries): Json<Vec<TreeEntryInput>>,
) -> impl IntoResponse {
    let mut builder = TableBuilder::new(Dir);
    for entry in entries {
        let mode = mode_from_name(&entry.mode)?;
        let child = O256::from_hex(&entry.hash).ok_or((
            StatusCode::BAD_REQUEST,
            format!("invalid hash: {}", entry.hash),
        ))?;
        builder.push_row(DirRow {
            name: entry.name.into_bytes(),
            mode,
            child,
        });
    }
    let table = builder.build();
    match ObjectStore::insert(&state.object_store, &Tree(table.into_bytes())) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}

/// GET /api/objects/tree/{hash}/git — get tree as git bytes → application/octet-stream
pub async fn tree_get_git(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = parse_hash_param(&hash_hex)?;
    let data = get_tree_data(&state, &hash)?;
    let table = Table::parse(data, Dir)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("parse error: {e}")))?;

    let mut rows = Vec::with_capacity(table.num_entries());
    for i in 0..table.num_entries() {
        let row = table
            .row(i)
            .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, format!("row error: {e}")))?;
        rows.push(DirRow {
            name: row.name.to_vec(),
            mode: row.mode,
            child: row.child,
        });
    }

    let git_bytes = git_tree_bytes_mapped(&rows, &Sha256Identity)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, format!("git error: {e}")))?;

    Ok::<_, (StatusCode, String)>((
        [(axum::http::header::CONTENT_TYPE, "application/octet-stream")],
        git_bytes,
    ))
}

/// POST /api/objects/tree/git — insert tree from git bytes → { "hash": "..." }
pub async fn tree_insert_git(
    axum::extract::State(state): axum::extract::State<crate::AppState>,
    body: Bytes,
) -> impl IntoResponse {
    let rows = git_tree_to_dir_rows_mapped(&body, &Sha256Identity)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("parse error: {e}")))?;

    let mut builder = TableBuilder::new(Dir);
    for row in rows {
        builder.push_row(row);
    }
    let table = builder.build();

    match ObjectStore::insert(&state.object_store, &Tree(table.into_bytes())) {
        Ok(hash) => Ok((
            StatusCode::CREATED,
            Json(HashResponse {
                hash: hash.to_string(),
            }),
        )),
        Err(e) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("store error: {e}"),
        )),
    }
}
