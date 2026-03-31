use std::collections::HashMap;
use std::str::FromStr;

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
    store: Option<covalence_store::ContentStore>,
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
            store: None,
        }
    }

    /// Create a server with a content-addressed store at the given DB path.
    pub fn with_store(store_path: &str) -> Self {
        let store = match covalence_store::ContentStore::open(store_path) {
            Ok(s) => Some(s),
            Err(e) => {
                eprintln!("failed to open content store: {e}");
                None
            }
        };
        Server {
            documents: HashMap::new(),
            store,
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
            "covalence/storeFile" => {
                let uri_str = match req.params.get("uri").and_then(|v| v.as_str()) {
                    Some(u) => u,
                    None => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InvalidParams as i32,
                            "missing or invalid \"uri\" parameter".to_owned(),
                        ));
                    }
                };
                let uri = match Uri::from_str(uri_str) {
                    Ok(u) => u,
                    Err(e) => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InvalidParams as i32,
                            format!("invalid URI: {e}"),
                        ));
                    }
                };
                let text = match self.documents.get(&uri) {
                    Some(t) => t,
                    None => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InvalidParams as i32,
                            "document not open".to_owned(),
                        ));
                    }
                };
                let store = match &self.store {
                    Some(s) => s,
                    None => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InternalError as i32,
                            "content store not available".to_owned(),
                        ));
                    }
                };
                match store.store(text.as_bytes()) {
                    Ok(hash) => {
                        let hex: String = hash.iter().map(|b| format!("{b:02x}")).collect();
                        Some(Response::new_ok(
                            req.id.clone(),
                            serde_json::json!({ "hash": hex }),
                        ))
                    }
                    Err(e) => Some(Response::new_err(
                        req.id.clone(),
                        lsp_server::ErrorCode::InternalError as i32,
                        format!("store error: {e}"),
                    )),
                }
            }
            "covalence/lookupHash" => {
                let hex = match req.params.get("hash").and_then(|v| v.as_str()) {
                    Some(h) => h,
                    None => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InvalidParams as i32,
                            "missing or invalid \"hash\" parameter".to_owned(),
                        ));
                    }
                };
                let hash = match parse_hex_hash(hex) {
                    Some(h) => h,
                    None => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InvalidParams as i32,
                            "hash must be a 64-character hex string".to_owned(),
                        ));
                    }
                };
                let store = match &self.store {
                    Some(s) => s,
                    None => {
                        return Some(Response::new_err(
                            req.id.clone(),
                            lsp_server::ErrorCode::InternalError as i32,
                            "content store not available".to_owned(),
                        ));
                    }
                };
                match store.lookup(&hash) {
                    Ok(Some(data)) => {
                        let text = String::from_utf8_lossy(&data).into_owned();
                        Some(Response::new_ok(
                            req.id.clone(),
                            serde_json::json!({ "content": text }),
                        ))
                    }
                    Ok(None) => Some(Response::new_ok(
                        req.id.clone(),
                        serde_json::json!({ "error": "hash not found" }),
                    )),
                    Err(e) => Some(Response::new_err(
                        req.id.clone(),
                        lsp_server::ErrorCode::InternalError as i32,
                        format!("store error: {e}"),
                    )),
                }
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

/// Parse a 64-character hex string into a 32-byte hash.
fn parse_hex_hash(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut hash = [0u8; 32];
    for (i, chunk) in hex.as_bytes().chunks(2).enumerate() {
        let s = std::str::from_utf8(chunk).ok()?;
        hash[i] = u8::from_str_radix(s, 16).ok()?;
    }
    Some(hash)
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
    use std::str::FromStr;

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

    // --- Integration tests: diagnostics via Server.handle_notification ---

    /// Build a `textDocument/didOpen` notification for the given URI and content.
    fn did_open(uri: &str, text: &str) -> lsp_server::Notification {
        lsp_server::Notification::new(
            lsp_types::notification::DidOpenTextDocument::METHOD.to_owned(),
            serde_json::to_value(lsp_types::DidOpenTextDocumentParams {
                text_document: lsp_types::TextDocumentItem {
                    uri: Uri::from_str(uri).unwrap(),
                    language_id: String::new(),
                    version: 0,
                    text: text.to_owned(),
                },
            })
            .unwrap(),
        )
    }

    /// Extract diagnostics from a `textDocument/publishDiagnostics` notification.
    fn extract_diagnostics(notif: &lsp_server::Notification) -> Vec<Diagnostic> {
        assert_eq!(
            notif.method,
            lsp_types::notification::PublishDiagnostics::METHOD
        );
        let params: PublishDiagnosticsParams =
            serde_json::from_value(notif.params.clone()).unwrap();
        params.diagnostics
    }

    // -- Valid Alethe/S-expression that is invalid Ion --
    //
    // SMT-LIB/Alethe uses `:keyword` syntax and `|pipe-quoted symbols|`,
    // neither of which is valid in Ion's text grammar.

    const ALETHE_WITH_KEYWORDS_AND_PIPES: &str = "(set-info :status |my proof|)";

    #[test]
    fn alethe_keywords_and_pipes_valid_on_alethe_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open(
                "file:///proof.alethe",
                ALETHE_WITH_KEYWORDS_AND_PIPES,
            ))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "expected no errors for valid Alethe with keywords/pipes: {diags:?}"
        );
    }

    #[test]
    fn alethe_keywords_and_pipes_valid_on_smt2_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open(
                "file:///problem.smt2",
                ALETHE_WITH_KEYWORDS_AND_PIPES,
            ))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "expected no errors for valid S-expression on .smt2: {diags:?}"
        );
    }

    #[test]
    fn alethe_keywords_and_pipes_errors_on_ion_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///data.ion", ALETHE_WITH_KEYWORDS_AND_PIPES))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            !diags.is_empty(),
            "expected Ion parse errors for Alethe keywords/pipes"
        );
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::ERROR));
    }

    // -- Valid Ion that is also valid S-expression (no errors on either) --
    //
    // Ion's text format includes S-expressions `(...)`, structs `{...}`,
    // and lists `[...]`. The sexp parser is very permissive: `{`, `}`, `[`,
    // `]` are all parsed as atoms, so Ion content does not produce sexp
    // errors. We verify both parsers accept this content and that the
    // server routes to the correct one based on file extension.

    const ION_STRUCT: &str = "{ name: \"hello\", value: 42 }";

    #[test]
    fn ion_struct_no_diagnostics_on_ion_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///data.ion", ION_STRUCT))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "expected no errors for valid Ion struct: {diags:?}"
        );
    }

    #[test]
    fn ion_struct_no_diagnostics_on_alethe_file() {
        // The sexp parser is permissive: `{`, `}` etc. are valid atoms,
        // so this content parses without error even on an Alethe file.
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///proof.alethe", ION_STRUCT))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "sexp parser is permissive; Ion struct tokens parse as atoms: {diags:?}"
        );
    }

    // -- Realistic Alethe proof: valid sexp, invalid Ion --
    //
    // Alethe proofs use `:rule`, `:premises` keywords that Ion rejects.

    const ALETHE_PROOF: &str = "\
(assume h1 (not (= (+ x 1) 2)))
(step t1 (cl (= x 1)) :rule resolution :premises (h1))";

    #[test]
    fn alethe_proof_valid_on_alethe_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///proof.alethe", ALETHE_PROOF))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "expected no errors for Alethe proof: {diags:?}"
        );
    }

    #[test]
    fn alethe_proof_errors_on_ion_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///proof.ion", ALETHE_PROOF))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            !diags.is_empty(),
            "expected Ion parse errors for Alethe proof (`:rule` etc. are invalid Ion)"
        );
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::ERROR));
    }

    // -- Realistic Ion document with struct/list/sexp --

    const ION_DOCUMENT: &str = "\
{
  theorem: resolution,
  premises: [h1, h2],
  conclusion: (= x 1),
}";

    #[test]
    fn ion_document_valid_on_ion_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///data.ion", ION_DOCUMENT))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "expected no errors for valid Ion document: {diags:?}"
        );
    }

    #[test]
    fn ion_document_no_errors_on_alethe_file() {
        // Sexp parser treats `{`, `}`, `[`, `]`, `,` as atom characters,
        // so this valid Ion document also parses as valid (though meaningless)
        // S-expressions.
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///proof.alethe", ION_DOCUMENT))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "sexp parser is permissive; Ion document tokens parse as atoms: {diags:?}"
        );
    }

    // -- Pipe-quoted symbol is valid sexp, invalid Ion --

    #[test]
    fn pipe_quoted_symbol_valid_sexp_invalid_ion() {
        assert!(diagnose_sexp("|hello world|").is_empty());
        assert!(!diagnose_ion("|hello world|").is_empty());
    }

    // -- SMT keyword is valid sexp, invalid Ion --

    #[test]
    fn smt_keyword_valid_sexp_invalid_ion() {
        assert!(diagnose_sexp(":status").is_empty());
        assert!(!diagnose_ion(":status").is_empty());
    }

    // -- File extension routing: .smt uses sexp diagnostics --

    #[test]
    fn smt_extension_routes_to_sexp_diagnostics() {
        // `:status` is a valid sexp atom but invalid Ion.
        // On a .smt file the sexp parser should be used → no errors.
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///problem.smt", ":status"))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "expected .smt to use sexp parser (no errors for keyword): {diags:?}"
        );
    }

    #[test]
    fn ion_extension_routes_to_ion_diagnostics() {
        // `:status` is invalid Ion. On a .ion file the Ion parser should be used → errors.
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///data.ion", ":status"))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(
            !diags.is_empty(),
            "expected .ion to use Ion parser (errors for keyword): {diags:?}"
        );
    }

    // -- Malformed content produces errors on the matching file type --

    #[test]
    fn unclosed_paren_errors_on_alethe_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///proof.alethe", "(assert (= x 0)"))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(!diags.is_empty(), "expected sexp error for unclosed paren");
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::ERROR));
    }

    #[test]
    fn malformed_ion_struct_errors_on_ion_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///data.ion", "{ name: }"))
            .expect("should produce diagnostics notification");
        let diags = extract_diagnostics(&notif);
        assert!(!diags.is_empty(), "expected Ion error for malformed struct");
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::ERROR));
    }
}
