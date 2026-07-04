use axum::http::{StatusCode, header};
use axum::response::{IntoResponse, Response};
use rust_embed::Embed;

#[derive(Embed)]
#[folder = "../../../apps/covalence-web/build/"]
struct WebAssets;

const NOT_EMBEDDED_HTML: &str = r#"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Covalence</title>
<style>
  body { font-family: system-ui, sans-serif; max-width: 40em; margin: 4em auto; padding: 0 1em; color: #333; }
  h1 { font-size: 1.4em; }
  code { background: #f0f0f0; padding: 0.15em 0.4em; border-radius: 3px; font-size: 0.95em; }
  pre { background: #f0f0f0; padding: 1em; border-radius: 6px; overflow-x: auto; }
</style>
</head>
<body>
<h1>Site not embedded</h1>
<p>This server was built without the web frontend. To include it, build the web app first:</p>
<pre>bun run build:web     # build the SvelteKit frontend
bun run build:serve   # build frontend + server binary</pre>
<p>Or run the dev server alongside the API:</p>
<pre>cov serve --api       # API only on :3100
bun run dev:web       # Vite dev server with HMR</pre>
<p>The API is available at <code>/api</code>.</p>
</body>
</html>
"#;

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
            None => (
                StatusCode::OK,
                [(header::CONTENT_TYPE, "text/html".to_owned())],
                NOT_EMBEDDED_HTML,
            )
                .into_response(),
        },
    }
}
