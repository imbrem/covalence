/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/
use tracing::info;

use lsp_server::Connection;
use lsp_types::{
    InitializeParams, ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind,
};

mod server;

use server::CovalenceLsp;

pub mod utils;

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
