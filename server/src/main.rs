/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

use tracing::info;

use lsp_server::{Connection, ExtractError, Message, RequestId, Response};
use lsp_types::{
    notification::{
        DidChangeTextDocument, DidOpenTextDocument, DidSaveTextDocument,
        Notification as NotificationTrait,
    },
    request::Request,
    Diagnostic, DiagnosticSeverity, DidChangeTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams, InitializeParams, NumberOrString,
    Position, PublishDiagnosticsParams, Range, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, Url,
};

use covalence_kernel::sexpr::{Commands, LocatingSlice, Parser};

fn main() -> eyre::Result<()> {
    // Configure tracing to output to stderr instead of stdout
    // This is crucial for LSP servers since stdout is used for LSP protocol messages
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_ansi(false)
        .init();
    info!("Initializing Covalence Language Server");

    // Create the transport. Includes the stdio (stdin and stdout) versions but this could
    // also be implemented to use sockets or HTTP.
    let (connection, io_threads) = Connection::stdio();

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    let server_capabilities = serde_json::to_value(&ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        ..Default::default()
    })
    .unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;
    main_loop(connection, initialization_params)?;
    io_threads.join()?;

    // Shut down gracefully.
    info!("Shutting down Covalence Language Server");
    Ok(())
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CheckAletheParams {
    pub folder: Url,
}

pub enum CheckAletheRequest {}
impl Request for CheckAletheRequest {
    type Params = CheckAletheParams;
    type Result = u32;
    const METHOD: &'static str = "covalence-lsp/checkAlethe";
}

fn main_loop(connection: Connection, params: serde_json::Value) -> eyre::Result<()> {
    let _params: InitializeParams = serde_json::from_value(params).unwrap();
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }
                match cast::<CheckAletheRequest>(req.clone()) {
                    Ok((id, params)) => {
                        info!("Received checkAlethe request #{} {}", id, params.folder);
                        let result = count_files_in_directory(params.folder.path());
                        let json = serde_json::to_value(result).unwrap();
                        let resp = Response {
                            id,
                            result: Some(json),
                            error: None,
                        };
                        connection.sender.send(Message::Response(resp))?;
                        continue;
                    }
                    Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                    Err(ExtractError::MethodMismatch(req)) => req,
                };
            }
            Message::Response(_resp) => {}
            Message::Notification(not) => {
                match not.method.as_str() {
                    DidOpenTextDocument::METHOD => {
                        let params: DidOpenTextDocumentParams =
                            serde_json::from_value(not.params).unwrap();
                        let uri = params.text_document.uri;
                        let text = params.text_document.text;

                        if uri.path().ends_with(".smt2") || uri.path().ends_with(".sy") {
                            if let Err(err) =
                                parse_document_and_publish_diagnostics(&connection, uri, &text)
                            {
                                info!("Failed to parse document: {}", err);
                            }
                        }
                    }
                    DidChangeTextDocument::METHOD => {
                        let params: DidChangeTextDocumentParams =
                            serde_json::from_value(not.params).unwrap();
                        let uri = params.text_document.uri;

                        if uri.path().ends_with(".smt2") || uri.path().ends_with(".sy") {
                            // Get the full text from the last change
                            if let Some(change) = params.content_changes.last() {
                                if let Err(err) = parse_document_and_publish_diagnostics(
                                    &connection,
                                    uri,
                                    &change.text,
                                ) {
                                    info!("Failed to parse document: {}", err);
                                }
                            }
                        }
                    }
                    DidSaveTextDocument::METHOD => {
                        let params: DidSaveTextDocumentParams =
                            serde_json::from_value(not.params).unwrap();
                        let uri = params.text_document.uri;

                        if uri.path().ends_with(".smt2") || uri.path().ends_with(".sy") {
                            if let Some(text) = params.text {
                                if let Err(err) =
                                    parse_document_and_publish_diagnostics(&connection, uri, &text)
                                {
                                    info!("Failed to parse document: {}", err);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

fn cast<R>(
    req: lsp_server::Request,
) -> Result<(RequestId, R::Params), ExtractError<lsp_server::Request>>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}

fn count_files_in_directory(path: &str) -> usize {
    WalkDir::new(path)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_file())
        .count()
}

fn parse_document_and_publish_diagnostics(
    connection: &Connection,
    uri: Url,
    text: &str,
) -> eyre::Result<()> {
    info!("Parsing document: {}", uri);
    let mut diagnostics = Vec::new();

    // Parse the entire document as S-expressions
    let result = Commands::parser.parse(LocatingSlice::new(text));

    match result {
        Ok(commands) => {
            info!("Document parsed successfully");
            // Successfully parsed - create a blue diagnostic covering the entire document
            let lines: Vec<&str> = text.lines().collect();
            let last_line = lines.len().saturating_sub(1) as u32;
            let last_character = lines
                .last()
                .map(|line| line.len() as u32)
                .unwrap_or(0);

            let diagnostic = Diagnostic {
                range: Range::new(
                    Position::new(0, 0),
                    Position::new(last_line, last_character),
                ),
                severity: Some(DiagnosticSeverity::INFORMATION),
                code: Some(NumberOrString::String("parse-success".to_string())),
                message: format!("{} S-expressions parsed successfully", commands.0.len()),
                source: Some("covalence-lsp".to_string()),
                ..Default::default()
            };
            
            diagnostics.push(diagnostic);
        }
        Err(err) => {
            info!("Parse error: {}", err);
            // Create a diagnostic that covers the entire document (turn everything red)
            let lines: Vec<&str> = text.lines().collect();
            let last_line = lines.len().saturating_sub(1) as u32;
            let last_character = lines
                .last()
                .map(|line| line.len() as u32)
                .unwrap_or(0);

            let diagnostic = Diagnostic {
                range: Range::new(
                    Position::new(0, 0),
                    Position::new(last_line, last_character),
                ),
                severity: Some(DiagnosticSeverity::ERROR),
                code: Some(NumberOrString::String("parse-error".to_string())),
                message: format!("S-expression parse error: {}", err),
                source: Some("covalence-lsp".to_string()),
                ..Default::default()
            };
            
            diagnostics.push(diagnostic);
        }
    }

    // Publish diagnostics
    let params = PublishDiagnosticsParams {
        uri,
        diagnostics,
        version: None,
    };
    let notification = lsp_server::Notification {
        method: "textDocument/publishDiagnostics".to_string(),
        params: serde_json::to_value(params)?,
    };
    connection
        .sender
        .send(Message::Notification(notification))?;

    Ok(())
}
