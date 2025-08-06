/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

use tracing::info;

use lsp_server::{Connection, ExtractError, Message, RequestId, Response};
use lsp_types::{
    request::{GotoDefinition, Request},
    GotoDefinitionResponse, InitializeParams, Location, OneOf, ServerCapabilities, Url,
};

fn main() -> eyre::Result<()> {
    tracing_subscriber::fmt::init();
    info!("Initializing Covalence Language Server");

    // Create the transport. Includes the stdio (stdin and stdout) versions but this could
    // also be implemented to use sockets or HTTP.
    let (connection, io_threads) = Connection::stdio();

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    let server_capabilities = serde_json::to_value(&ServerCapabilities {
        definition_provider: Some(OneOf::Left(true)),
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
pub struct CountFilesParams {
    pub folder: Url,
}

pub enum CountFilesRequest {}
impl Request for CountFilesRequest {
    type Params = CountFilesParams;
    type Result = u32;
    const METHOD: &'static str = "covalence-lsp/countFiles";
}

fn main_loop(connection: Connection, params: serde_json::Value) -> eyre::Result<()> {
    let _params: InitializeParams = serde_json::from_value(params).unwrap();
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }
                match cast::<GotoDefinition>(req.clone()) {
                    Ok((id, params)) => {
                        let uri = params.text_document_position_params.text_document.uri;
                        info!(
                            "Received gotoDefinition request #{} {}",
                            id,
                            uri.to_string()
                        );
                        let loc = Location::new(
                            uri,
                            lsp_types::Range::new(
                                lsp_types::Position::new(0, 0),
                                lsp_types::Position::new(0, 0),
                            ),
                        );
                        let result = Some(GotoDefinitionResponse::Array(vec![loc]));
                        let result = serde_json::to_value(result).unwrap();
                        let resp = Response {
                            id,
                            result: Some(result),
                            error: None,
                        };
                        connection.sender.send(Message::Response(resp))?;
                        continue;
                    }
                    Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                    Err(ExtractError::MethodMismatch(req)) => req,
                };
                match cast::<CountFilesRequest>(req.clone()) {
                    Ok((id, params)) => {
                        info!("Received countFiles request #{} {}", id, params.folder);
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
            Message::Notification(_not) => {}
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
