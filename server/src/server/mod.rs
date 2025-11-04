use covalence::kernel::Kernel;
use covalence::sexpr::{Commands, LocatingSlice, Parser};
use indexmap::IndexMap;
use tracing::{info, warn};

use lsp_server::{Connection, Message, Notification, Request, Response};
use lsp_types::{
    notification::{
        DidChangeTextDocument, DidOpenTextDocument, DidSaveTextDocument,
        Notification as NotificationTrait,
    },
    Diagnostic, DiagnosticSeverity, DidChangeTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams, InitializeParams, NumberOrString, Position,
    PublishDiagnosticsParams, Range, TextDocumentItem, Url,
};

use crate::{smt::SmtProblem, utils::LineMap};

/// The covalence LSP
pub struct CovalenceLsp {
    /// The LSP connection
    connection: Connection,
    /// The initialization parameters
    _params: InitializeParams,
    /// Currently open files
    file_data: IndexMap<Url, FileData>,
    /// Currently initialized `covalence` kernels
    kernels: Vec<Kernel>,
}

/// An internal identifier for an open file
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct FileId(usize);

/// Data maintained for each currently open file
#[derive(Debug, Clone, PartialEq)]
pub struct FileData {
    /// This file's interpretation
    interp: FileState,
    /// This file's version number
    version: i32,
    /// This file's associated Alethe kernel, if any
    kernel: Option<KernelId>,
}

/// A kernel ID for the `covalence` LSP
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct KernelId(pub usize);

/// A type of file the `covalence` LSP can handle
#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum FileState {
    /// An SMT file
    Smt(SmtState),
    /// An Alethe proof file
    Alethe(AletheState),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct SmtState {
    /// The kernel to use
    kid: KernelId,
    /// The SMT problem state
    problem: SmtProblem,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct AletheState {}

/// An event
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum FileEvent {
    /// A file was opened
    Open(String),
    /// A file was changed, and updated contents provided
    Change(Option<Range>, String),
    /// A file was saved, and updated contents (optionally) provided
    Save(Option<String>),
}

impl FileEvent {
    /// Get the text associated with this event, if any
    ///
    /// A change with a given range is mapped to `None`
    pub fn full_text(&self) -> Option<&str> {
        match self {
            FileEvent::Open(text) | FileEvent::Change(None, text) => Some(text),
            FileEvent::Change(Some(_), _) => None,
            FileEvent::Save(opt_text) => opt_text.as_deref(),
        }
    }
}

impl CovalenceLsp {
    /// Create a new CovalenceLSP
    pub fn new(connection: Connection, params: InitializeParams) -> Self {
        Self {
            connection,
            _params: params,
            file_data: IndexMap::default(),
            kernels: Vec::new(),
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

    /// Initialize a new kernel
    pub fn new_kernel(&mut self) -> KernelId {
        let kid = KernelId(self.kernels.len());
        self.kernels.push(Kernel::default());
        kid
    }

    /// Get an available kernel for SMT use
    pub fn get_free_smt_kernel(&mut self) -> KernelId {
        //TODO: enable kernel recycling, sharing, etc.
        self.new_kernel()
    }

    /// Open a text document, if we can give it an interpretation
    pub fn open_document(&mut self, doc: &TextDocumentItem) -> Option<FileId> {
        // Existing file information overrides old file information
        if let Some(id) = self.file_id(&doc.uri) {
            return Some(id);
        };
        let interp = match &*doc.language_id {
            "smt" => {
                let kid = self.get_free_smt_kernel();
                let problem = SmtProblem::new(&mut self.kernels[kid.0]);
                FileState::Smt(SmtState { kid, problem })
            }
            //TODO: implement Alethe proof support
            "alethe" => FileState::Alethe(AletheState {}),
            _ => return None,
        };
        let (fid, old) = self.file_data.insert_full(
            doc.uri.clone(),
            FileData {
                interp,
                version: doc.version,
                kernel: None,
            },
        );
        assert_eq!(old, None);
        Some(FileId(fid))
    }

    /// Get the file ID corresponding to a URI
    pub fn file_id(&self, uri: &Url) -> Option<FileId> {
        self.file_data.get_index_of(uri).map(FileId)
    }

    /// Get the URI corresponding to a file ID
    pub fn file_uri(&self, fid: FileId) -> &Url {
        self.file_data.get_index(fid.0).expect("invalid file ID").0
    }

    pub fn did_open_text_document(
        &mut self,
        params: DidOpenTextDocumentParams,
    ) -> eyre::Result<()> {
        let Some(fid) = self.open_document(&params.text_document) else {
            return Ok(());
        };
        self.handle_file_event(fid, FileEvent::Open(params.text_document.text))?;
        Ok(())
    }

    pub fn did_change_text_document(
        &mut self,
        mut params: DidChangeTextDocumentParams,
    ) -> eyre::Result<()> {
        let uri = params.text_document.uri;
        let Some(fid) = self.file_id(&uri) else {
            return Ok(());
        };

        let current_version = self.file_data[fid.0].version;
        let new_version = params.text_document.version;
        if current_version >= new_version {
            warn!("out of order change to file {uri}: current version {current_version} ≥ new version {new_version}")
        }
        self.file_data[fid.0].version = new_version;

        if let Some(change) = params.content_changes.pop() {
            self.handle_file_event(fid, FileEvent::Change(change.range, change.text))?;
        }
        Ok(())
    }

    pub fn did_save_text_document(
        &mut self,
        params: DidSaveTextDocumentParams,
    ) -> eyre::Result<()> {
        let uri = params.text_document.uri;
        let Some(fid) = self.file_id(&uri) else {
            return Ok(());
        };
        self.handle_file_event(fid, FileEvent::Save(params.text))?;
        Ok(())
    }

    pub fn handle_file_event(&mut self, fid: FileId, event: FileEvent) -> eyre::Result<()> {
        // For now, we don't support partial updates
        let Some(text) = event.full_text() else {
            return Ok(());
        };

        // TODO: once we parse things, we should actually _do_ something
        // - step 1: use SMT state to parse SMT files to contexts
        // - step 2: use Alethe files to derive contradictions
        // - step 3: use model files to mark contexts as having models, and separately export
        //   those models as needed
        self.parse_document_and_publish_diagnostics(self.file_uri(fid).clone(), text)?;

        Ok(())
    }

    fn parse_document_and_publish_diagnostics(&self, uri: Url, text: &str) -> eyre::Result<()> {
        let mut diagnostics = Vec::new();

        // Parse the entire document as S-expressions
        let result = Commands::parser.parse(LocatingSlice::new(text));

        match result {
            Ok(commands) => {
                // Create a line map for efficient byte-to-position conversion
                let line_map = LineMap::new(text);

                // Create a diagnostic for each S-expression
                for (index, spanned_sexpr) in commands.0.iter().enumerate() {
                    let start_pos = line_map.byte_offset_to_position(text, spanned_sexpr.start);
                    let end_pos = line_map.byte_offset_to_position(text, spanned_sexpr.end);

                    let diagnostic = Diagnostic {
                        range: Range::new(start_pos, end_pos),
                        severity: Some(DiagnosticSeverity::INFORMATION),
                        code: Some(NumberOrString::String("sexpr".to_string())),
                        message: format!("S-expression {}/{}", index, commands.0.len()),
                        source: Some("covalence-lsp".to_string()),
                        ..Default::default()
                    };

                    diagnostics.push(diagnostic);
                }
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
                    message: format!("S-expression parse error: {err}"),
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
        self.connection
            .sender
            .send(Message::Notification(notification))?;

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
