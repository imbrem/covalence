use std::collections::HashMap;

use lsp_server::{Connection, Message, Request, Response};
use lsp_types::{
    Diagnostic, DiagnosticSeverity, DocumentFormattingParams, InitializeParams, InitializeResult,
    OneOf, Position, PublishDiagnosticsParams, Range, ServerCapabilities, ServerInfo,
    TextDocumentSyncCapability, TextDocumentSyncKind, TextEdit, Uri,
    notification::Notification as _, request::Request as _,
};

pub struct LspConfig<'a> {
    pub version: &'a str,
    pub target: &'a str,
}

pub fn run_lsp(config: &LspConfig) {
    let (connection, io_threads) = Connection::stdio();

    let (init_id, _init_params) = connection.initialize_start().unwrap();
    let _init_params: InitializeParams = serde_json::from_value(_init_params).unwrap();

    let init_result = initialize_result(config);
    connection
        .initialize_finish(init_id, serde_json::to_value(init_result).unwrap())
        .unwrap();

    eprintln!("Covalence LSP initialized");

    let mut server = Server::new();

    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req).unwrap_or(false) {
                    break;
                }
                if let Some(resp) = server.handle_request(&req) {
                    connection.sender.send(Message::Response(resp)).unwrap();
                }
            }
            Message::Notification(not) => {
                if let Some(n) = server.handle_notification(not) {
                    connection.sender.send(Message::Notification(n)).unwrap();
                }
            }
            Message::Response(_) => {}
        }
    }

    io_threads.join().unwrap();
}

pub fn run_diagnose(path: &str) {
    let text = std::fs::read_to_string(path).unwrap();
    let diagnostics = if is_smt_path(path) {
        diagnose_smt(&text)
    } else if is_cov_path(path) {
        diagnose_sexp(&text)
    } else if is_wat_path(path) {
        diagnose_wat(&text)
    } else {
        vec![]
    };
    for d in &diagnostics {
        let severity = match d.severity {
            Some(DiagnosticSeverity::ERROR) => "error",
            Some(DiagnosticSeverity::WARNING) => "warning",
            _ => "info",
        };
        eprintln!("{severity}: {}", d.message);
    }
    std::process::exit(if diagnostics.is_empty() { 0 } else { 1 });
}

pub fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        document_formatting_provider: Some(OneOf::Left(true)),
        ..Default::default()
    }
}

pub fn initialize_result(config: &LspConfig) -> InitializeResult {
    InitializeResult {
        capabilities: server_capabilities(),
        server_info: Some(ServerInfo {
            name: "covalence-lsp".into(),
            version: Some(format!("{} ({})", config.version, config.target)),
        }),
    }
}

pub struct Server {
    documents: HashMap<Uri, String>,
}

/// Check if a URI refers to an S-expression file (any dialect).
fn is_sexp_file(uri: &Uri) -> bool {
    is_sexp_path(uri.as_str())
}

/// Check if a URI refers to an SMT-LIB file.
fn is_smt_file(uri: &Uri) -> bool {
    is_smt_path(uri.as_str())
}

/// Check if a path refers to an SMT-LIB file.
fn is_smt_path(path: &str) -> bool {
    path.ends_with(".smt") || path.ends_with(".smt2") || path.ends_with(".alethe")
}

/// Check if a path refers to a Covalence file.
fn is_cov_path(path: &str) -> bool {
    path.ends_with(".cov")
}

/// Check if a path refers to an S-expression file (any dialect).
fn is_sexp_path(path: &str) -> bool {
    is_smt_path(path) || is_cov_path(path)
}

/// Check if a URI refers to a WAT file.
fn is_wat_file(uri: &Uri) -> bool {
    uri.as_str().ends_with(".wat")
}

/// Check if a path refers to a WAT file.
fn is_wat_path(path: &str) -> bool {
    path.ends_with(".wat")
}

/// Parse sexp using the right dialect for the given URI.
fn parse_sexp_for_uri(
    uri: &Uri,
    text: &str,
) -> Result<Vec<covalence_sexp::SExpr>, covalence_sexp::ParseError> {
    if is_smt_file(uri) {
        covalence_sexp::parse_smt(text)
    } else {
        covalence_sexp::parse(text)
    }
}

impl Server {
    pub fn new() -> Self {
        Server {
            documents: HashMap::new(),
        }
    }

    pub fn handle_request(&self, req: &Request) -> Option<Response> {
        match req.method.as_str() {
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

        if is_sexp_file(uri) {
            let sexps = parse_sexp_for_uri(uri, text).ok()?;
            let mut buf = Vec::new();
            covalence_sexp::prettyprint(&sexps, &mut buf).ok()?;
            let formatted = String::from_utf8(buf).ok()?;
            let formatted = if formatted.is_empty() {
                formatted
            } else {
                formatted + "\n"
            };
            Some(vec![TextEdit {
                range: Range::new(Position::new(0, 0), Position::new(u32::MAX, u32::MAX)),
                new_text: formatted,
            }])
        } else {
            None
        }
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

pub fn diagnose_sexp(text: &str) -> Vec<Diagnostic> {
    diagnose_parse_result(covalence_sexp::parse(text), text)
}

pub fn diagnose_smt(text: &str) -> Vec<Diagnostic> {
    diagnose_parse_result(covalence_sexp::parse_smt(text), text)
}

fn diagnose_parse_result(
    result: Result<Vec<covalence_sexp::SExpr>, covalence_sexp::ParseError>,
    text: &str,
) -> Vec<Diagnostic> {
    match result {
        Ok(_) => vec![],
        Err(e) => {
            let (line, col) = covalence_sexp::offset_to_line_col(text, e.offset);
            vec![Diagnostic {
                range: Range::new(Position::new(line, col), Position::new(line, col)),
                severity: Some(DiagnosticSeverity::ERROR),
                message: e.message,
                ..Default::default()
            }]
        }
    }
}

pub fn diagnose_wat(text: &str) -> Vec<Diagnostic> {
    match covalence_wasm::compile_wat(text) {
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
    let diagnostics = if is_smt_file(&uri) {
        diagnose_smt(text)
    } else if is_sexp_file(&uri) {
        diagnose_sexp(text)
    } else if is_wat_file(&uri) {
        diagnose_wat(text)
    } else {
        vec![]
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

    // --- Direct diagnostic tests ---

    #[test]
    fn valid_sexp_no_diagnostics() {
        assert!(diagnose_sexp("(assert (= x 0))").is_empty());
        assert!(diagnose_sexp("").is_empty());
        assert!(diagnose_sexp(":keyword").is_empty());
        assert!(diagnose_sexp("|quoted symbol|").is_empty());
    }

    #[test]
    fn unclosed_paren_has_errors() {
        let diags = diagnose_sexp("(assert (= x 0)");
        assert!(!diags.is_empty());
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::ERROR));
    }

    #[test]
    fn valid_wat_module_no_diagnostics() {
        assert!(diagnose_wat("(module)").is_empty());
    }

    #[test]
    fn valid_wat_component_no_diagnostics() {
        assert!(diagnose_wat("(component)").is_empty());
    }

    #[test]
    fn valid_wat_with_func_no_diagnostics() {
        let wat = r#"(module (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add))"#;
        assert!(diagnose_wat(wat).is_empty());
    }

    #[test]
    fn invalid_wat_has_errors() {
        let diags = diagnose_wat("(module (func (invalid_instruction))");
        assert!(!diags.is_empty());
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::ERROR));
    }

    #[test]
    fn empty_wat_has_errors() {
        assert!(!diagnose_wat("").is_empty());
    }

    // --- Integration tests: diagnostics via Server.handle_notification ---

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

    fn extract_diagnostics(notif: &lsp_server::Notification) -> Vec<Diagnostic> {
        assert_eq!(
            notif.method,
            lsp_types::notification::PublishDiagnostics::METHOD
        );
        let params: PublishDiagnosticsParams =
            serde_json::from_value(notif.params.clone()).unwrap();
        params.diagnostics
    }

    // -- S-expression file routing --

    const ALETHE_PROOF: &str = "\
(assume h1 (not (= (+ x 1) 2)))
(step t1 (cl (= x 1)) :rule resolution :premises (h1))";

    #[test]
    fn alethe_file_uses_sexp_parser() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///proof.alethe", ALETHE_PROOF))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "valid Alethe should have no errors: {diags:?}"
        );
    }

    #[test]
    fn smt2_file_uses_sexp_parser() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open(
                "file:///problem.smt2",
                "(set-info :status |proof|)",
            ))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "valid SMT-LIB should have no errors: {diags:?}"
        );
    }

    #[test]
    fn cov_file_uses_sexp_parser() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///theorem.cov", "(define x 42)"))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "valid .cov should have no errors: {diags:?}"
        );
    }

    #[test]
    fn unclosed_paren_errors_on_alethe_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///proof.alethe", "(assert (= x 0)"))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(!diags.is_empty(), "expected sexp error for unclosed paren");
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::ERROR));
    }

    #[test]
    fn unclosed_paren_errors_on_cov_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///theorem.cov", "(define x"))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(
            !diags.is_empty(),
            "expected sexp error for unclosed paren on .cov"
        );
    }

    // -- WAT file routing --

    #[test]
    fn wat_file_validates_module() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///test.wat", "(module)"))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "valid WAT module should have no errors: {diags:?}"
        );
    }

    #[test]
    fn wat_file_validates_component() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///test.wat", "(component)"))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "valid WAT component should have no errors: {diags:?}"
        );
    }

    #[test]
    fn invalid_wat_errors_on_wat_file() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///test.wat", "not valid wat"))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(!diags.is_empty(), "invalid WAT should have errors");
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::ERROR));
    }

    // -- Unknown file type --

    #[test]
    fn unknown_file_type_no_diagnostics() {
        let mut server = Server::new();
        let notif = server
            .handle_notification(did_open("file:///data.txt", "random content {{{"))
            .expect("should produce diagnostics");
        let diags = extract_diagnostics(&notif);
        assert!(
            diags.is_empty(),
            "unknown file type should produce no diagnostics"
        );
    }
}
