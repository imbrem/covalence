use axum::Json;
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
