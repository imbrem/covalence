use lsp_server::{Request, Response};
use lsp_types::{
    Diagnostic, DiagnosticSeverity, InitializeResult, Position, PublishDiagnosticsParams, Range,
    ServerCapabilities, ServerInfo, TextDocumentSyncCapability, TextDocumentSyncKind,
    notification::Notification as _,
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

pub fn handle_request(req: &Request) -> Option<Response> {
    match req.method.as_str() {
        "covalence/serializeBinaryIon" => {
            let params: serde_json::Value = serde_json::from_value(req.params.clone()).ok()?;
            let text = params.get("text")?.as_str()?;
            let result = serialize_binary_ion(text);
            Some(Response::new_ok(req.id.clone(), serde_json::to_value(result).unwrap()))
        }
        _ => Some(Response::new_err(
            req.id.clone(),
            lsp_server::ErrorCode::MethodNotFound as i32,
            format!("unknown method: {}", req.method),
        )),
    }
}

fn serialize_binary_ion(text: &str) -> serde_json::Value {
    use covalence_ion::ion_rs::{Element, v1_0::Binary};

    match Element::read_all(text.as_bytes()) {
        Ok(sequence) => match sequence.encode_as(Binary) {
            Ok(bytes) => serde_json::json!({ "byteCount": bytes.len() }),
            Err(e) => serde_json::json!({ "error": e.to_string() }),
        },
        Err(e) => serde_json::json!({ "error": e.to_string() }),
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

fn publish_diagnostics(uri: lsp_types::Uri, text: &str) -> lsp_server::Notification {
    let diagnostics = diagnose(text);
    let params = PublishDiagnosticsParams {
        uri,
        diagnostics,
        version: None,
    };
    lsp_server::Notification::new(
        lsp_types::notification::PublishDiagnostics::METHOD.to_owned(),
        serde_json::to_value(params).unwrap(),
    )
}

pub fn handle_notification(not: lsp_server::Notification) -> Option<lsp_server::Notification> {
    let lsp_server::Notification { method, params } = not;
    match method.as_str() {
        lsp_types::notification::DidOpenTextDocument::METHOD => {
            let params: lsp_types::DidOpenTextDocumentParams =
                serde_json::from_value(params).ok()?;
            Some(publish_diagnostics(
                params.text_document.uri,
                &params.text_document.text,
            ))
        }
        lsp_types::notification::DidChangeTextDocument::METHOD => {
            let params: lsp_types::DidChangeTextDocumentParams =
                serde_json::from_value(params).ok()?;
            let change = params.content_changes.into_iter().last()?;
            Some(publish_diagnostics(params.text_document.uri, &change.text))
        }
        _ => None,
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
