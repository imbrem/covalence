//! TEMPORARY / THROWAWAY DEMO SURFACE — the `/metamath` web page's backend.
//!
//! Clean REST for data + a thin WebSocket for live status only. The server is
//! **stateful**: a `.mm` source is parsed once into a cached [`MmSession`]
//! (keyed by content hash + optional user), then:
//!
//!   - graph + per-theorem data are served by **REST** (cacheable, immutable
//!     for a given session),
//!   - the parallel kernel import is kicked off by a **REST** `POST /prove`,
//!   - and live per-theorem status is forwarded over a **thin status WS** that
//!     only carries `snapshot`/`proving`/`proved`/`done` frames.
//!
//! This is NOT part of the stable API surface — it powers a throwaway UX
//! experiment (a "task view" of a covalence proof DB) and is expected to be
//! deleted/rewritten wholesale.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock, RwLock};

use axum::Json;
use axum::extract::ws::{Message, WebSocket, WebSocketUpgrade};
use axum::extract::{Path, Query, State};
use axum::http::{StatusCode, header};
use axum::response::{IntoResponse, Response};
use covalence_hash::O256;
use serde::Deserialize;
use serde_json::{Value, json};

use crate::AppState;

// ---------------------------------------------------------------------------
// Session registry
// ---------------------------------------------------------------------------

/// `(file-hash-hex, optional-user-key)` — sessions are cached per source per
/// user, so re-POSTing the same `.mm` reuses the parsed database.
pub type SessionKey = (String, Option<String>);

/// All live Metamath demo sessions. Lives in [`AppState`] as an `Arc`.
pub type MmSessions = Mutex<HashMap<SessionKey, Arc<MmSession>>>;

/// One parsed-and-cached Metamath database, ready to serve.
pub struct MmSession {
    /// The parsed database, shared read-only across the prove threads.
    pub db: Arc<covalence_hol::metamath::Database>,
    /// Logical (`|-`) `$p` theorem count.
    pub total: usize,
    /// Cached graph JSON (computed once on first GET `/graph`).
    pub graph: OnceLock<String>,
    /// label → proved-result JSON (filled as the prove task completes).
    pub results: RwLock<HashMap<String, Value>>,
    /// Broadcast channel for live status frames.
    pub status_tx: tokio::sync::broadcast::Sender<String>,
    /// CAS guard so the prove task is launched at most once per session.
    pub proving: AtomicBool,
}

/// `?user=<opt>` query for every endpoint.
#[derive(Deserialize, Default)]
pub struct UserQ {
    pub user: Option<String>,
}

/// `?user=<opt>&workers=N` query for the prove endpoint.
#[derive(Deserialize, Default)]
pub struct ProveQ {
    pub user: Option<String>,
    pub workers: Option<usize>,
}

fn lookup(state: &AppState, hash: &str, user: &Option<String>) -> Option<Arc<MmSession>> {
    let key: SessionKey = (hash.to_string(), user.clone());
    state.mm.lock().unwrap().get(&key).cloned()
}

// ---------------------------------------------------------------------------
// Rendering helpers (static per-theorem data from the database)
// ---------------------------------------------------------------------------

/// Render one theorem's proof code (Normal labels joined, or Compressed
/// `( labels ) letters`).
fn render_proof(a: &covalence_metamath::database::Assertion) -> String {
    use covalence_metamath::database::Proof;
    match &a.proof {
        Some(Proof::Normal(labels)) => labels.join(" "),
        Some(Proof::Compressed { labels, letters }) => {
            format!("( {} ) {}", labels.join(" "), String::from_utf8_lossy(letters))
        }
        None => String::new(),
    }
}

/// The deduped (first-seen order) logical (`|-`) dependency list of a proof:
/// `[{label, kind}]` with kind axiom/def/thm (thm if the dep has its own proof,
/// else `df*` → def, else axiom).
fn render_deps(db: &covalence_hol::metamath::Database, a: &covalence_metamath::database::Assertion) -> Vec<Value> {
    use covalence_metamath::database::Statement;
    use covalence_metamath::{ProofStep, proof_steps};

    let mut deps: Vec<Value> = Vec::new();
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
            deps.push(json!({ "label": l, "kind": kind }));
        }
    }
    deps
}

/// The graph-phase item for one theorem: `{label, mm, deps}`.
fn graph_item(db: &covalence_hol::metamath::Database, label: &str) -> Value {
    use covalence_metamath::database::Statement;
    match db.statement_by_label(label) {
        Some(Statement::Assert(a)) => json!({
            "label": label,
            "mm": a.conclusion.render(),
            "deps": render_deps(db, a),
        }),
        _ => json!({ "label": label, "mm": "", "deps": [] }),
    }
}

/// Build the proved-result JSON for one finished theorem (stored in `results`
/// and broadcast over the status WS).
fn proved_result(
    result: &covalence_core::Result<covalence_core::Thm>,
    import_ms: f64,
) -> Value {
    match result {
        Ok(thm) => {
            let full = format!("{}", thm.concl());
            let hol_preview: String = full.chars().take(400).collect();
            json!({
                "status": "proved",
                "ok": true,
                "hyps": thm.hyps().len(),
                "genuine": thm.has_no_obs(),
                "holPreview": hol_preview,
                "importMs": import_ms,
            })
        }
        Err(e) => json!({
            "status": "error",
            "ok": false,
            "error": e.to_string(),
            "importMs": import_ms,
        }),
    }
}

// ---------------------------------------------------------------------------
// POST /api/metamath/db — parse (or reuse) a session
// ---------------------------------------------------------------------------

/// POST `/api/metamath/db?user=<opt>` — body = raw `.mm` source. Computes the
/// content hash; if `(hash, user)` is not already cached, parses the database
/// (off the async runtime) and inserts a new [`MmSession`]. Returns
/// `{"file": <hash>, "total": N}`.
pub async fn create_db(
    State(state): State<AppState>,
    Query(q): Query<UserQ>,
    body: axum::body::Bytes,
) -> Response {
    let hash = O256::blob(&body).to_string();
    let key: SessionKey = (hash.clone(), q.user.clone());

    if let Some(sess) = state.mm.lock().unwrap().get(&key).cloned() {
        return Json(json!({ "file": hash, "total": sess.total })).into_response();
    }

    // Parse off the async runtime (set.mm parse is ~1s).
    let source = match String::from_utf8(body.to_vec()) {
        Ok(s) => s,
        Err(_) => return (StatusCode::BAD_REQUEST, "source is not valid UTF-8").into_response(),
    };
    let parsed = tokio::task::spawn_blocking(move || covalence_hol::metamath::parse(&source))
        .await
        .unwrap_or_else(|e| panic!("parse task panicked: {e}"));

    let db = match parsed {
        Ok(db) => db,
        Err(e) => return (StatusCode::BAD_REQUEST, format!("parse error: {e}")).into_response(),
    };

    let total = covalence_hol::metalogic::mm_import::theorem_labels(&db).len();
    let (status_tx, _rx) = tokio::sync::broadcast::channel::<String>(1024);
    let session = Arc::new(MmSession {
        db: Arc::new(db),
        total,
        graph: OnceLock::new(),
        results: RwLock::new(HashMap::new()),
        status_tx,
        proving: AtomicBool::new(false),
    });

    state.mm.lock().unwrap().insert(key, session);
    Json(json!({ "file": hash, "total": total })).into_response()
}

// ---------------------------------------------------------------------------
// GET /api/metamath/db/{hash}/graph — the cached static graph
// ---------------------------------------------------------------------------

/// GET `/api/metamath/db/{hash}/graph?user=<opt>` — the whole static
/// declaration graph: `{"total": N, "theorems": [{label, mm, deps}]}`. Computed
/// once into the session's `graph` `OnceLock`, then served verbatim. The graph
/// is immutable for a given session, so it is served with strong-caching
/// headers (`ETag` = the file hash, long `Cache-Control`).
pub async fn graph(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };

    let body = sess
        .graph
        .get_or_init(|| {
            let labels = covalence_hol::metalogic::mm_import::theorem_labels(&sess.db);
            let theorems: Vec<Value> = labels.iter().map(|l| graph_item(&sess.db, l)).collect();
            json!({ "total": sess.total, "theorems": theorems }).to_string()
        })
        .clone();

    let etag = format!("\"{hash}\"");
    (
        [
            (header::CONTENT_TYPE, "application/json".to_string()),
            (header::CACHE_CONTROL, "public, max-age=31536000, immutable".to_string()),
            (header::ETAG, etag),
        ],
        body,
    )
        .into_response()
}

// ---------------------------------------------------------------------------
// GET /api/metamath/db/{hash}/theorem/{name} — one theorem's full detail
// ---------------------------------------------------------------------------

/// GET `/api/metamath/db/{hash}/theorem/{name}?user=<opt>` — full per-theorem
/// detail: `{label, mm, ess, deps, proof, status, ok?, hyps?, genuine?,
/// holPreview?, importMs?, error?}`. Static fields render from the db; dynamic
/// fields come from the `results` cache (`status:"pending"` if not yet proved).
pub async fn theorem(
    State(state): State<AppState>,
    Path((hash, name)): Path<(String, String)>,
    Query(q): Query<UserQ>,
) -> Response {
    use covalence_metamath::database::Statement;

    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };

    let Some(Statement::Assert(a)) = sess.db.statement_by_label(&name) else {
        return (StatusCode::NOT_FOUND, "no such theorem").into_response();
    };
    if a.conclusion.typecode() != "|-" {
        return (StatusCode::NOT_FOUND, "not a logical theorem").into_response();
    }

    let ess: Vec<String> = a.frame.essentials.iter().map(|h| h.expr.render()).collect();
    let mut out = json!({
        "label": name,
        "mm": a.conclusion.render(),
        "ess": ess,
        "deps": render_deps(&sess.db, a),
        "proof": render_proof(a),
        "status": "pending",
    });

    if let Some(res) = sess.results.read().unwrap().get(&name) {
        if let (Value::Object(base), Value::Object(extra)) = (&mut out, res) {
            for (k, v) in extra {
                base.insert(k.clone(), v.clone());
            }
        }
    }

    Json(out).into_response()
}

// ---------------------------------------------------------------------------
// POST /api/metamath/db/{hash}/prove — kick off the parallel import
// ---------------------------------------------------------------------------

/// POST `/api/metamath/db/{hash}/prove?user=<opt>&workers=N` — start the
/// parallel kernel import (idempotent via a CAS on `proving`). Returns 202
/// `{"started": true|false}`. `workers` 0/absent = auto. Results are stored in
/// the session's `results` cache and broadcast over the status WS.
pub async fn prove(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<ProveQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };

    // CAS: only the first caller wins and spawns the prove thread.
    if sess
        .proving
        .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
        .is_err()
    {
        return (StatusCode::ACCEPTED, Json(json!({ "started": false }))).into_response();
    }

    let workers = q.workers.unwrap_or(0);
    let sess2 = sess.clone();
    std::thread::spawn(move || prove_worker(sess2, workers));

    (StatusCode::ACCEPTED, Json(json!({ "started": true }))).into_response()
}

/// The blocking prove worker: derive every logical theorem in parallel, storing
/// each result in `results` and broadcasting `proving`/`proved`/`done` frames.
fn prove_worker(sess: Arc<MmSession>, workers: usize) {
    use covalence_hol::metalogic::mm_import::import_theorems_parallel;

    let started = std::time::Instant::now();
    let n_ok = AtomicUsize::new(0);
    let grand_total = AtomicUsize::new(0);
    let tx = &sess.status_tx;

    import_theorems_parallel(
        &sess.db,
        workers,
        |total| {
            grand_total.store(total, Ordering::Relaxed);
        },
        |label| {
            let _ = tx.send(json!({ "type": "proving", "label": label }).to_string());
        },
        |done, total, label, result, elapsed| {
            let import_ms = elapsed.as_micros() as f64 / 1000.0;
            let res_json = proved_result(result, import_ms);
            if result.is_ok() {
                n_ok.fetch_add(1, Ordering::Relaxed);
            }
            // Store the result for late REST GETs / WS snapshots.
            sess.results
                .write()
                .unwrap()
                .insert(label.to_string(), res_json.clone());
            // Broadcast the live frame.
            let mut frame = json!({
                "type": "proved",
                "done": done,
                "total": total,
                "label": label,
            });
            if let (Value::Object(f), Value::Object(r)) = (&mut frame, &res_json) {
                for (k, v) in r {
                    if k == "status" {
                        continue; // the frame `type` already carries this
                    }
                    f.insert(k.clone(), v.clone());
                }
            }
            let _ = tx.send(frame.to_string());
        },
    );

    let _ = tx.send(
        json!({
            "type": "done",
            "ok": n_ok.load(Ordering::Relaxed),
            "total": grand_total.load(Ordering::Relaxed),
            "elapsedMs": started.elapsed().as_millis() as u64,
        })
        .to_string(),
    );
}

// ---------------------------------------------------------------------------
// WS /api/metamath/db/{hash}/status — thin live status forwarder
// ---------------------------------------------------------------------------

/// WS `/api/metamath/db/{hash}/status?user=<opt>` — on connect, send a snapshot
/// of already-proved results (so a late joiner is current), then subscribe to
/// the session's broadcast channel and forward each frame verbatim.
pub async fn status_ws(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
    ws: WebSocketUpgrade,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    ws.on_upgrade(move |socket| handle_status_ws(socket, sess))
}

async fn handle_status_ws(mut socket: WebSocket, sess: Arc<MmSession>) {
    // Subscribe BEFORE building the snapshot, so no frame between the snapshot
    // and the first forwarded message is lost.
    let mut rx = sess.status_tx.subscribe();

    // Minimal snapshot: just label+ok for already-proved theorems.
    let snapshot = {
        let results = sess.results.read().unwrap();
        let entries: Vec<Value> = results
            .iter()
            .map(|(label, v)| json!({ "label": label, "ok": v.get("ok").and_then(Value::as_bool).unwrap_or(false) }))
            .collect();
        json!({ "type": "snapshot", "total": sess.total, "results": entries }).to_string()
    };
    if socket.send(Message::Text(snapshot.into())).await.is_err() {
        return;
    }

    loop {
        match rx.recv().await {
            Ok(msg) => {
                if socket.send(Message::Text(msg.into())).await.is_err() {
                    break;
                }
            }
            // Lagged: a slow client missed frames; keep going (the next GET
            // /theorem or a reconnect-snapshot recovers state).
            Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
            Err(tokio::sync::broadcast::error::RecvError::Closed) => break,
        }
    }
    let _ = socket.send(Message::Close(None)).await;
}
