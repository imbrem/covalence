//! TEMPORARY / THROWAWAY DEMO: native `/api/lisp` + `/api/forsp` REPL endpoints.
//!
//! Each browser tab gets a PERSISTENT server-side session keyed by a client
//! `session` id, so `defun`s (Lisp) / `$x` bindings + word defs (Forsp)
//! accumulate across cells — a real REPL over the **native kernel**, no
//! client-side WASM. `Session` is `Send + Sync` (its `Defs` uses `Arc`), so it
//! lives in the shared [`AppState`]. Not part of the stable API surface.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::sync::Mutex;

use axum::Json;
use axum::extract::State;
use axum::response::IntoResponse;
use serde::Deserialize;
use serde_json::{Value, json};

use crate::AppState;

/// Persistent Lisp sessions, keyed by a client-supplied id.
pub type LispSessions = Mutex<HashMap<String, covalence_lisp::session::Session>>;
/// Persistent Forsp sessions, keyed by a client-supplied id.
pub type ForspSessions = Mutex<HashMap<String, covalence_forsp::Forsp<()>>>;

/// `{ "session": "<id>", "src": "<one cell>" }`.
#[derive(Deserialize)]
pub struct CellRequest {
    pub session: String,
    pub src: String,
}

/// `{ "session": "<id>" }`.
#[derive(Deserialize)]
pub struct SessionRequest {
    pub session: String,
}

fn reply(out: Result<String, String>) -> Json<Value> {
    match out {
        Ok(result) => Json(json!({ "ok": true, "result": result })),
        Err(error) => Json(json!({ "ok": false, "error": error })),
    }
}

/// POST /api/lisp — evaluate one Lisp cell in the persistent session `session`.
/// Every printed value is read off a genuine kernel theorem (the `Session`
/// honesty invariant). Use `src = "#show EXPR"` to fetch the theorem itself.
pub async fn lisp_eval(
    State(state): State<AppState>,
    Json(req): Json<CellRequest>,
) -> impl IntoResponse {
    let sessions = state.lisp.clone();
    let out = tokio::task::spawn_blocking(move || {
        let CellRequest { session, src } = req;
        let mut map = sessions.lock().unwrap();
        let sess = match map.entry(session) {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(v) => match covalence_lisp::session::Session::new() {
                Ok(s) => v.insert(s),
                Err(e) => return Err(format!("failed to start Lisp session: {e}")),
            },
        };
        sess.eval_cell(&src).map_err(|e| e.to_string())
    })
    .await
    .unwrap_or_else(|e| Err(format!("task error: {e}")));
    reply(out)
}

/// POST /api/lisp/reset — drop a session's accumulated `defun`s.
pub async fn lisp_reset(
    State(state): State<AppState>,
    Json(req): Json<SessionRequest>,
) -> impl IntoResponse {
    state.lisp.lock().unwrap().remove(&req.session);
    Json(json!({ "ok": true }))
}

/// POST /api/forsp — evaluate one Forsp cell; returns the top-of-stack value.
pub async fn forsp_eval(
    State(state): State<AppState>,
    Json(req): Json<CellRequest>,
) -> impl IntoResponse {
    let sessions = state.forsp.clone();
    let out = tokio::task::spawn_blocking(move || {
        let CellRequest { session, src } = req;
        let mut map = sessions.lock().unwrap();
        let f = map.entry(session).or_insert_with(covalence_forsp::Forsp::new);
        f.run(&src).map_err(|e| e.to_string())?;
        Ok(match f.try_peek() {
            Ok(top) => f.show(top),
            Err(_) => "()".to_string(),
        })
    })
    .await
    .unwrap_or_else(|e| Err(format!("task error: {e}")));
    reply(out)
}

/// POST /api/forsp/reset — drop a Forsp session's bindings + word defs.
pub async fn forsp_reset(
    State(state): State<AppState>,
    Json(req): Json<SessionRequest>,
) -> impl IntoResponse {
    state.forsp.lock().unwrap().remove(&req.session);
    Json(json!({ "ok": true }))
}
