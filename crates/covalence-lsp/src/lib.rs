use std::collections::HashMap;

use lsp_server::{Request, Response};
use lsp_types::{
    Diagnostic, DiagnosticSeverity, DocumentFormattingParams, InitializeResult, OneOf, Position,
    PublishDiagnosticsParams, Range, ServerCapabilities, ServerInfo, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextEdit, Uri, notification::Notification as _, request::Request as _,
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

pub struct Server {
    documents: HashMap<Uri, String>,
}

/// Check if a URI refers to an S-expression file (.smt or .alethe).
fn is_sexp_file(uri: &Uri) -> bool {
    let path = uri.as_str();
    path.ends_with(".smt") || path.ends_with(".smt2") || path.ends_with(".alethe")
}

impl Server {
    pub fn new() -> Self {
        Server {
            documents: HashMap::new(),
        }
    }

    pub fn handle_request(&self, req: &Request) -> Option<Response> {
        match req.method.as_str() {
            "covalence/serializeBinaryIon" => {
                let result = match req.params.get("text").and_then(|v| v.as_str()) {
                    Some(text) => serialize_binary_ion(text),
                    None => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InvalidParams as i32,
                            "missing or invalid \"text\" parameter".to_owned(),
                        ));
                    }
                };
                Some(Response::new_ok(req.id.clone(), result))
            }
            "covalence/decodeBinaryIon" => {
                let result = match req.params.get("path").and_then(|v| v.as_str()) {
                    Some(path) => decode_binary_ion_file(path),
                    None => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InvalidParams as i32,
                            "missing or invalid \"path\" parameter".to_owned(),
                        ));
                    }
                };
                Some(Response::new_ok(req.id.clone(), result))
            }
            "covalence/encodeBinaryIon" => {
                let path = req.params.get("path").and_then(|v| v.as_str());
                let text = req.params.get("text").and_then(|v| v.as_str());
                let result = match (path, text) {
                    (Some(path), Some(text)) => encode_binary_ion_file(path, text),
                    _ => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InvalidParams as i32,
                            "missing or invalid \"path\" and/or \"text\" parameter".to_owned(),
                        ));
                    }
                };
                Some(Response::new_ok(req.id.clone(), result))
            }
            lsp_types::request::Formatting::METHOD => {
                let params: DocumentFormattingParams =
                    match serde_json::from_value(req.params.clone()) {
                        Ok(p) => p,
                        Err(e) => {
                            return Some(Response::new_err(
                                req.id.clone(),
                                lsp_server::ErrorCode::InvalidParams as i32,
                                e.to_string(),
                            ));
                        }
                    };
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

        let formatted = if is_sexp_file(uri) {
            let sexps = covalence_ion::sexp::parse(text).ok()?;
            let mut buf = Vec::new();
            covalence_ion::sexp::prettyprint(&sexps, &mut buf).ok()?;
            String::from_utf8(buf).ok()?
        } else {
            use covalence_ion::ion_rs::Element;
            let ast = Element::read_all(text.as_bytes()).ok()?;
            let mut buf = Vec::new();
            covalence_ion::prettyprint(&ast, &mut buf).ok()?;
            String::from_utf8(buf).ok()?
        };

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
                let uri = params.text_document.uri;
                let text = params.text_document.text;
                let diagnostics = publish_diagnostics(uri.clone(), &text);
                self.documents.insert(uri, text);
                Some(diagnostics)
            }
            lsp_types::notification::DidChangeTextDocument::METHOD => {
                let params: lsp_types::DidChangeTextDocumentParams =
                    serde_json::from_value(params).ok()?;
                let change = params.content_changes.into_iter().last()?;
                let uri = params.text_document.uri;
                let diagnostics = publish_diagnostics(uri.clone(), &change.text);
                self.documents.insert(uri, change.text);
                Some(diagnostics)
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

fn decode_binary_ion_file(path: &str) -> serde_json::Value {
    use covalence_ion::ion_rs::Element;

    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => return serde_json::json!({ "error": format!("file read error: {e}") }),
    };

    match Element::read_all(&bytes) {
        Ok(sequence) => {
            let mut buf = Vec::new();
            match covalence_ion::prettyprint(&sequence, &mut buf) {
                Ok(()) => {
                    let text = String::from_utf8(buf).unwrap_or_default();
                    let text = if text.is_empty() { text } else { text + "\n" };
                    serde_json::json!({ "text": text })
                }
                Err(e) => serde_json::json!({ "error": format!("prettyprint error: {e}") }),
            }
        }
        Err(e) => serde_json::json!({ "error": format!("Ion parse error: {e}") }),
    }
}

fn encode_binary_ion_file(path: &str, text: &str) -> serde_json::Value {
    use covalence_ion::ion_rs::{Element, v1_0::Binary};

    match Element::read_all(text.as_bytes()) {
        Ok(sequence) => match sequence.encode_as(Binary) {
            Ok(bytes) => match std::fs::write(path, &bytes) {
                Ok(()) => serde_json::json!({}),
                Err(e) => serde_json::json!({ "error": format!("file write error: {e}") }),
            },
            Err(e) => serde_json::json!({ "error": format!("binary encode error: {e}") }),
        },
        Err(e) => serde_json::json!({ "error": format!("Ion parse error: {e}") }),
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
    diagnose_ion(text)
}

fn diagnose_ion(text: &str) -> Vec<Diagnostic> {
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

pub fn diagnose_sexp(text: &str) -> Vec<Diagnostic> {
    match covalence_ion::sexp::parse(text) {
        Ok(_) => vec![],
        Err(e) => {
            let (line, col) = covalence_ion::sexp::offset_to_line_col(text, e.offset);
            vec![Diagnostic {
                range: Range::new(Position::new(line, col), Position::new(line, col)),
                severity: Some(DiagnosticSeverity::ERROR),
                message: e.message,
                ..Default::default()
            }]
        }
    }
}

fn publish_diagnostics(uri: Uri, text: &str) -> lsp_server::Notification {
    let diagnostics = if is_sexp_file(&uri) {
        diagnose_sexp(text)
    } else {
        diagnose_ion(text)
    };
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

    #[test]
    fn binary_ion_roundtrip() {
        use covalence_ion::ion_rs::{Element, v1_0::Binary};

        // Simple roundtrip
        let text = r#"{ name: "hello", value: 42, tags: [a, b, c], nested: { x: 1, y: 2 } }"#;
        let sequence = Element::read_all(text.as_bytes()).expect("parse text Ion");
        let bytes = sequence.encode_as(Binary).expect("encode as binary");
        let decoded = Element::read_all(&bytes).expect("decode binary Ion");
        assert_eq!(sequence, decoded);
    }

    #[test]
    fn binary_ion_roundtrip_multi_value() {
        use covalence_ion::ion_rs::{Element, v1_0::Binary};

        // Multiple top-level values with quoted symbols, strings-in-list, null.struct
        let text = r#"{ name: "hello", value: 42, tags: ["a", "b", "c"], nested: { x: 1, y: 2 } }
null.struct
['+', 1, 2]
[true, false, null]"#;
        let sequence = Element::read_all(text.as_bytes()).expect("parse text Ion");
        let bytes = sequence.encode_as(Binary).expect("encode as binary");
        let decoded = Element::read_all(&bytes).expect("decode binary Ion roundtrip");
        assert_eq!(sequence, decoded);
    }

    #[test]
    fn encode_decode_binary_ion_file_roundtrip() {
        // Test the actual encode/decode file functions used by the LSP
        let text = r#"{ name: "hello", value: 42, tags: ["a", "b", "c"], nested: { x: 1, y: 2 } }
null.struct
['+', 1, 2]
[true, false, null]"#;

        let tmp = std::env::temp_dir().join("covalence_test_roundtrip.ion");
        let path = tmp.to_str().unwrap();

        let encode_result = encode_binary_ion_file(path, text);
        assert!(
            encode_result.get("error").is_none(),
            "encode error: {:?}",
            encode_result
        );

        let decode_result = decode_binary_ion_file(path);
        assert!(
            decode_result.get("error").is_none(),
            "decode error: {:?}",
            decode_result
        );

        std::fs::remove_file(&tmp).ok();
    }
}
