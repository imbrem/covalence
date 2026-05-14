use axum::Json;
use axum::extract::ws::{Message, WebSocket, WebSocketUpgrade};
use axum::response::IntoResponse;
use serde::Serialize;

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

/// WebSocket REPL endpoint. Each connection gets its own Session.
pub async fn repl_ws(ws: WebSocketUpgrade) -> impl IntoResponse {
    ws.on_upgrade(handle_repl_ws)
}

async fn handle_repl_ws(mut socket: WebSocket) {
    let mut session = match crate::eval::Session::new(false) {
        Ok(s) => s,
        Err(e) => {
            let _ = socket
                .send(Message::Text(
                    format!("error: failed to create session: {e}").into(),
                ))
                .await;
            return;
        }
    };

    while let Some(Ok(msg)) = socket.recv().await {
        let input = match msg {
            Message::Text(t) => t.to_string(),
            Message::Close(_) => break,
            _ => continue,
        };

        // Run eval in a blocking task since wasmtime is CPU-bound
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
