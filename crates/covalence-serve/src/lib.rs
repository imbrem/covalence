mod api;
mod static_files;

use axum::Router;
use eyre::{Result, WrapErr};
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;

#[derive(Clone)]
pub struct AppState {
    pub version: &'static str,
    pub target: &'static str,
}

pub struct ServeConfig {
    pub version: &'static str,
    pub target: &'static str,
    pub port: u16,
    pub open: bool,
}

pub async fn run_serve(config: ServeConfig) -> Result<()> {
    let state = AppState {
        version: config.version,
        target: config.target,
    };

    let app = Router::new()
        .route("/api/info", axum::routing::get(api::info))
        .route("/{*path}", axum::routing::get(static_files::serve_static))
        .fallback(axum::routing::get(static_files::serve_index))
        .layer(CorsLayer::permissive())
        .layer(TraceLayer::new_for_http())
        .with_state(state);

    let addr = format!("127.0.0.1:{}", config.port);
    let listener = tokio::net::TcpListener::bind(&addr)
        .await
        .wrap_err_with(|| format!("failed to bind to {addr}"))?;

    let url = format!("http://{addr}");
    tracing::info!("{url}");

    if config.open {
        if let Err(e) = open::that(&url) {
            tracing::warn!("failed to open browser: {e}");
        }
    }

    axum::serve(listener, app).await.wrap_err("server error")?;

    Ok(())
}
