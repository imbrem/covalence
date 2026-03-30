use std::collections::HashMap;

use lsp_server::{Request, Response};
use lsp_types::{
    Diagnostic, DiagnosticSeverity, DocumentFormattingParams, InitializeResult, OneOf, Position,
    PublishDiagnosticsParams, Range, ServerCapabilities, ServerInfo, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextEdit, Uri,
    notification::Notification as _,
    request::Request as _,
};

pub fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        document_formatting_provider: Some(OneOf::Left(true)),
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

pub struct Server {
    documents: HashMap<Uri, String>,
}

impl Server {
    pub fn new() -> Self {
        Server {
            documents: HashMap::new(),
        }
    }

    pub fn handle_request(&self, req: &Request) -> Option<Response> {
        match req.method.as_str() {
            "covalence/helloWorld" => {
                let result = serde_json::json!({
                    "message": MESSAGE
                });
                Some(Response::new_ok(req.id.clone(), result))
            }
            lsp_types::request::Formatting::METHOD => {
                let params: DocumentFormattingParams =
                    serde_json::from_value(req.params.clone()).ok()?;
                let result = self.handle_formatting(&params);
                Some(Response::new_ok(
                    req.id.clone(),
                    serde_json::to_value(result).unwrap(),
                ))
            }
            _ => Some(Response::new_err(
                req.id.clone(),
                lsp_server::ErrorCode::MethodNotFound as i32,
                format!("unknown method: {}", req.method),
            )),
        }
    }

    fn handle_formatting(&self, params: &DocumentFormattingParams) -> Option<Vec<TextEdit>> {
        let uri = &params.text_document.uri;
        let text = self.documents.get(uri)?;

        use covalence_ion::ion_rs::Element;
        let ast = Element::read_all(text.as_bytes()).ok()?;

        let mut buf = Vec::new();
        covalence_ion::prettyprint(&ast, &mut buf).ok()?;
        let formatted = String::from_utf8(buf).ok()?;

        // Add trailing newline
        let formatted = if formatted.is_empty() {
            formatted
        } else {
            formatted + "\n"
        };

        Some(vec![TextEdit {
            range: Range::new(Position::new(0, 0), Position::new(u32::MAX, u32::MAX)),
            new_text: formatted,
        }])
    }

    pub fn handle_notification(
        &mut self,
        not: lsp_server::Notification,
    ) -> Option<lsp_server::Notification> {
        let lsp_server::Notification { method, params } = not;
        match method.as_str() {
            lsp_types::notification::DidOpenTextDocument::METHOD => {
                let params: lsp_types::DidOpenTextDocumentParams =
                    serde_json::from_value(params).ok()?;
                let uri = params.text_document.uri.clone();
                let text = params.text_document.text.clone();
                self.documents.insert(uri, text.clone());
                Some(publish_diagnostics(params.text_document.uri, &text))
            }
            lsp_types::notification::DidChangeTextDocument::METHOD => {
                let params: lsp_types::DidChangeTextDocumentParams =
                    serde_json::from_value(params).ok()?;
                let change = params.content_changes.into_iter().last()?;
                let uri = params.text_document.uri.clone();
                self.documents.insert(uri, change.text.clone());
                Some(publish_diagnostics(params.text_document.uri, &change.text))
            }
            lsp_types::notification::DidCloseTextDocument::METHOD => {
                let params: lsp_types::DidCloseTextDocumentParams =
                    serde_json::from_value(params).ok()?;
                self.documents.remove(&params.text_document.uri);
                None
            }
            _ => None,
        }
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

fn publish_diagnostics(uri: Uri, text: &str) -> lsp_server::Notification {
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
