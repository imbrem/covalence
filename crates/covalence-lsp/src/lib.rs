use lsp_server::{Request, Response};
use lsp_types::{
    Diagnostic, DiagnosticSeverity, InitializeResult, Position, PublishDiagnosticsParams, Range,
    ServerCapabilities, ServerInfo, TextDocumentSyncCapability, TextDocumentSyncKind,
};

pub fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        ..Default::default()
    }
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

pub fn diagnose(text: &str) -> Vec<Diagnostic> {
    use covalence_ion::ion_rs::Element;

    match Element::read_all(text.as_bytes()) {
        Ok(_) => vec![],
        Err(e) => vec![Diagnostic {
            range: Range::new(Position::new(0, 0), Position::new(u32::MAX, u32::MAX)),
            severity: Some(DiagnosticSeverity::ERROR),
            message: e.to_string(),
            ..Default::default()
        }],
    }
}

fn publish_diagnostics(
    uri: lsp_types::Uri,
    text: &str,
) -> lsp_server::Notification {
    let diagnostics = diagnose(text);
    let params = PublishDiagnosticsParams {
        uri,
        diagnostics,
        version: None,
    };
    lsp_server::Notification {
        method: "textDocument/publishDiagnostics".to_owned(),
        params: serde_json::to_value(params).unwrap(),
    }
}

pub fn handle_notification(not: &lsp_server::Notification) -> Vec<lsp_server::Notification> {
    match not.method.as_str() {
        "textDocument/didOpen" => {
            let params: lsp_types::DidOpenTextDocumentParams =
                serde_json::from_value(not.params.clone()).unwrap();
            vec![publish_diagnostics(
                params.text_document.uri,
                &params.text_document.text,
            )]
        }
        "textDocument/didChange" => {
            let params: lsp_types::DidChangeTextDocumentParams =
                serde_json::from_value(not.params.clone()).unwrap();
            if let Some(change) = params.content_changes.into_iter().last() {
                vec![publish_diagnostics(
                    params.text_document.uri,
                    &change.text,
                )]
            } else {
                vec![]
            }
        }
        _ => vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn well_formed_ion_no_diagnostics() {
        assert!(diagnose("{ name: \"hello\", value: 42 }").is_empty());
        assert!(diagnose("null").is_empty());
        assert!(diagnose("true false 1 2 3").is_empty());
        assert!(diagnose("").is_empty());
    }

    #[test]
    fn malformed_ion_has_errors() {
        assert!(!diagnose("{ name: }").is_empty());
    }
}
