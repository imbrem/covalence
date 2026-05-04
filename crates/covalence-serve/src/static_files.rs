use axum::http::{StatusCode, header};
use axum::response::{IntoResponse, Response};
use rust_embed::Embed;

#[derive(Embed)]
#[folder = "../../apps/covalence-web/build/"]
struct WebAssets;

pub async fn serve_static(axum::extract::Path(path): axum::extract::Path<String>) -> Response {
    serve_file(&path)
}

pub async fn serve_index() -> Response {
    serve_file("index.html")
}

fn serve_file(path: &str) -> Response {
    match WebAssets::get(path) {
        Some(file) => {
            let mime = mime_guess::from_path(path).first_or_octet_stream();
            (
                StatusCode::OK,
                [(header::CONTENT_TYPE, mime.as_ref().to_owned())],
                file.data.to_vec(),
            )
                .into_response()
        }
        // SPA fallback: serve index.html for unmatched paths
        None => match WebAssets::get("index.html") {
            Some(file) => (
                StatusCode::OK,
                [(header::CONTENT_TYPE, "text/html".to_owned())],
                file.data.to_vec(),
            )
                .into_response(),
            None => (StatusCode::NOT_FOUND, "web app not built").into_response(),
        },
    }
}
