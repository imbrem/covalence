use tracing::info;

use lsp_server::{Connection, Message, Notification, Request, Response};
use lsp_types::{
    notification::{
        DidChangeTextDocument, DidOpenTextDocument, DidSaveTextDocument,
        Notification as NotificationTrait,
    },
    DidChangeTextDocumentParams, DidOpenTextDocumentParams, DidSaveTextDocumentParams,
    InitializeParams, Url,
};

use crate::parse_document_and_publish_diagnostics;

/// The covalence LSP
pub struct CovalenceLsp {
    /// The LSP connection
    connection: Connection,
    /// The initialization parameters
    _params: InitializeParams,
}

/// A file kind `covalence` knows how to handle
pub enum FileKind {
    Smt,
    Alethe,
}

impl CovalenceLsp {
    /// Create a new CovalenceLSP
    pub fn new(connection: Connection, params: InitializeParams) -> Self {
        Self {
            connection,
            _params: params,
        }
    }

    /// Handle a message
    pub fn handle_message(&mut self, msg: Message) -> eyre::Result<()> {
        match msg {
            Message::Request(req) => self.handle_request(req)?,
            Message::Response(resp) => self.handle_response(resp)?,
            Message::Notification(not) => self.handle_notification(not)?,
        }
        Ok(())
    }

    /// Handle a request
    pub fn handle_request(&mut self, req: Request) -> eyre::Result<()> {
        if self.connection.handle_shutdown(&req)? {
            return Ok(());
        }
        Ok(())
    }

    /// Handle a response
    pub fn handle_response(&mut self, _resp: Response) -> eyre::Result<()> {
        Ok(())
    }

    /// Handle a notification
    pub fn handle_notification(&mut self, not: Notification) -> eyre::Result<()> {
        match not.method.as_str() {
            DidOpenTextDocument::METHOD => {
                self.did_open_text_document(serde_json::from_value(not.params).unwrap())?
            }
            DidChangeTextDocument::METHOD => {
                self.did_change_text_document(serde_json::from_value(not.params).unwrap())?
            }
            DidSaveTextDocument::METHOD => {
                self.did_save_text_document(serde_json::from_value(not.params).unwrap())?
            }
            _ => info!("Ignored notification: {}", not.method),
        }
        Ok(())
    }

    pub fn file_kind(&mut self, url: &Url) -> Option<FileKind> {
        if url.path().ends_with(".smt2") {
            Some(FileKind::Smt)
        } else if url.path().ends_with(".alethe") {
            Some(FileKind::Alethe)
        } else {
            None
        }
    }

    pub fn did_open_text_document(
        &mut self,
        params: DidOpenTextDocumentParams,
    ) -> eyre::Result<()> {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let Some(_kind) = self.file_kind(&uri) else {
            return Ok(());
        };
        if let Err(err) = parse_document_and_publish_diagnostics(&self.connection, uri, &text) {
            info!("Failed to parse document: {}", err);
        }
        Ok(())
    }

    pub fn did_change_text_document(
        &mut self,
        params: DidChangeTextDocumentParams,
    ) -> eyre::Result<()> {
        let uri = params.text_document.uri;
        let Some(_kind) = self.file_kind(&uri) else {
            return Ok(());
        };
        // Get the full text from the last change
        if let Some(change) = params.content_changes.last() {
            if let Err(err) =
                parse_document_and_publish_diagnostics(&self.connection, uri, &change.text)
            {
                info!("Failed to parse document: {}", err);
            }
        }
        Ok(())
    }

    pub fn did_save_text_document(
        &mut self,
        params: DidSaveTextDocumentParams,
    ) -> eyre::Result<()> {
        let uri = params.text_document.uri;
        let Some(_kind) = self.file_kind(&uri) else {
            return Ok(());
        };

        if let Some(text) = params.text {
            if let Err(err) = parse_document_and_publish_diagnostics(&self.connection, uri, &text) {
                info!("Failed to parse document: {}", err);
            }
        }
        Ok(())
    }

    /// Run the main loop of the LSP
    pub fn main_loop(&mut self) -> eyre::Result<()> {
        let receiver = self.connection.receiver.clone();
        for msg in &receiver {
            self.handle_message(msg)?;
        }
        Ok(())
    }
}
