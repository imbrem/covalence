mod api;
pub mod eval;
#[cfg(feature = "static")]
mod static_files;

use axum::Router;
use covalence_kernel::Kernel;
use covalence_store::{BlobStore, O256};
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;

#[derive(Debug, thiserror::Error)]
pub enum ServeError {
    #[error("failed to create kernel: {0}")]
    Kernel(#[from] covalence_kernel::KernelError),
    #[error("service registration failed: {0}")]
    Registration(#[from] covalence_proto::DiscoveryError),
    #[error("failed to bind to {addr}: {source}")]
    Bind {
        addr: String,
        #[source]
        source: std::io::Error,
    },
    #[error("server error: {0}")]
    Io(#[from] std::io::Error),
}

#[derive(Clone)]
pub struct AppState {
    pub version: &'static str,
    pub target: &'static str,
    pub started: std::time::Instant,
    pub kernel: Kernel,
}

pub struct ServeConfig {
    pub version: &'static str,
    pub target: &'static str,
    pub port: u16,
    pub open: bool,
    pub api_only: bool,
    /// If true, only listen on Unix socket (no TCP).
    pub socket_only: bool,
    /// Blob store to use. Defaults to in-memory if not specified.
    pub store: BlobStore<O256>,
}

pub async fn run_serve(config: ServeConfig) -> Result<(), ServeError> {
    let kernel = Kernel::with_store(config.store)?;
    let state = AppState {
        version: config.version,
        target: config.target,
        started: std::time::Instant::now(),
        kernel,
    };

    let app = build_router(state, config.api_only);

    // Register with service discovery
    let registration = covalence_proto::discovery::register(
        config.version,
        if config.socket_only {
            None
        } else {
            Some(config.port)
        },
        config.socket_only,
    )?;

    let socket_path = registration.socket_path.clone();
    tracing::info!("registered as {}", registration.id);

    // Ensure cleanup on exit
    let _guard = RegistrationGuard(registration);

    if config.socket_only {
        // Socket-only mode
        let _ = std::fs::remove_file(&socket_path);
        let uds =
            tokio::net::UnixListener::bind(&socket_path).map_err(|source| ServeError::Bind {
                addr: socket_path.display().to_string(),
                source,
            })?;
        tracing::info!("listening on {}", socket_path.display());
        axum::serve(uds, app).await?;
    } else {
        // TCP + Unix socket
        let addr = format!("127.0.0.1:{}", config.port);
        let tcp = tokio::net::TcpListener::bind(&addr)
            .await
            .map_err(|source| ServeError::Bind {
                addr: addr.clone(),
                source,
            })?;

        let url = format!("http://{addr}");
        tracing::info!("{url}");

        if config.open {
            if let Err(e) = open::that(&url) {
                tracing::warn!("failed to open browser: {e}");
            }
        }

        // Also listen on Unix socket
        let _ = std::fs::remove_file(&socket_path);
        let uds =
            tokio::net::UnixListener::bind(&socket_path).map_err(|source| ServeError::Bind {
                addr: socket_path.display().to_string(),
                source,
            })?;
        tracing::info!("unix socket: {}", socket_path.display());

        // Serve both concurrently
        tokio::select! {
            r = axum::serve(tcp, app.clone()).into_future() => {
                r?;
            }
            r = axum::serve(uds, app).into_future() => {
                r?;
            }
        }
    }

    Ok(())
}

/// RAII guard that unregisters the server on drop.
struct RegistrationGuard(covalence_proto::discovery::Registration);

impl Drop for RegistrationGuard {
    fn drop(&mut self) {
        tracing::info!("unregistering service {}", self.0.id);
        covalence_proto::discovery::unregister(&self.0);
    }
}

/// Build the axum Router with all API routes.
pub fn build_router(state: AppState, api_only: bool) -> Router {
    use axum::routing::{get, post};

    let app = Router::new()
        // Existing
        .route("/api/info", get(api::info))
        .route("/api/health", get(api::health))
        .route("/api/repl", get(api::repl_ws))
        // Blob endpoints (concrete paths before parameterized)
        .route("/api/blobs", post(api::blob_store).get(api::blob_list))
        .route("/api/blobs/url", post(api::blob_store_url))
        .route("/api/blobs/file", post(api::blob_store_file))
        .route("/api/blobs/{hash}", get(api::blob_get).head(api::blob_head))
        // Eval endpoint
        .route("/api/eval", post(api::eval))
        // WAT/WASM endpoints
        .route("/api/wat/module", post(api::wat_module))
        .route("/api/wat/component", post(api::wat_component))
        .route("/api/wat/{hash}", get(api::wat_decompile))
        // Parse/analysis endpoints
        .route("/api/parse/module/{hash}", get(api::parse_module))
        .route("/api/parse/component/{hash}", get(api::parse_component))
        .route("/api/decide/{hash}", get(api::decide));

    #[cfg(feature = "static")]
    let app = if !api_only {
        app.route("/{*path}", get(static_files::serve_static))
            .fallback(get(static_files::serve_index))
    } else {
        app
    };

    #[cfg(not(feature = "static"))]
    let _ = api_only;

    app.layer(CorsLayer::permissive())
        .layer(TraceLayer::new_for_http())
        .with_state(state)
}
