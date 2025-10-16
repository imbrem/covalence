/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/
use tracing::info;

use lsp_server::{Connection, Message};
use lsp_types::{
    Diagnostic, DiagnosticSeverity, InitializeParams, NumberOrString, Position,
    PublishDiagnosticsParams, Range, ServerCapabilities, TextDocumentSyncCapability,
    TextDocumentSyncKind, Url,
};

use covalence_kernel::sexpr::{Commands, LocatingSlice, Parser};

mod server;

use server::CovalenceLsp;

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
    let params: InitializeParams =
        serde_json::from_value(connection.initialize(server_capabilities)?).unwrap();
    let mut lsp = CovalenceLsp::new(connection, params);
    lsp.main_loop()?;
    io_threads.join()?;

    // Shut down gracefully.
    info!("Shutting down Covalence Language Server");
    Ok(())
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
            let last_character = lines.last().map(|line| line.len() as u32).unwrap_or(0);

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
            let last_character = lines.last().map(|line| line.len() as u32).unwrap_or(0);

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
