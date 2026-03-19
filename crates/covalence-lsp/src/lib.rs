use lsp_server::{Request, Response};
use lsp_types::{InitializeResult, ServerCapabilities, ServerInfo};

pub fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities::default()
}

pub fn initialize_result() -> InitializeResult {
    InitializeResult {
        capabilities: server_capabilities(),
        server_info: Some(ServerInfo {
            name: "covalence-lsp".into(),
            version: Some(env!("CARGO_PKG_VERSION").into()),
        }),
    }
}

const MESSAGE: &str = "Hello from Covalence LSP!";

pub fn handle_request(req: &Request) -> Option<Response> {
    match req.method.as_str() {
        "covalence/helloWorld" => {
            let result = serde_json::json!({
                "message": MESSAGE
            });
            Some(Response::new_ok(req.id.clone(), result))
        }
        _ => Some(Response::new_err(
            req.id.clone(),
            lsp_server::ErrorCode::MethodNotFound as i32,
            format!("unknown method: {}", req.method),
        )),
    }
}

pub fn handle_notification(_not: &lsp_server::Notification) {}
