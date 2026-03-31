use lsp_server::{Connection, Message};
use lsp_types::InitializeParams;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.get(1).is_some_and(|a| a == "--diagnose") {
        let path = args.get(2).expect("usage: covalence-lsp --diagnose <file>");
        let text = std::fs::read_to_string(path).unwrap();
        let is_sexp =
            path.ends_with(".smt") || path.ends_with(".smt2") || path.ends_with(".alethe");
        let diagnostics = if is_sexp {
            covalence_lsp::diagnose_sexp(&text)
        } else {
            covalence_lsp::diagnose(&text)
        };
        for d in &diagnostics {
            let severity = match d.severity {
                Some(lsp_types::DiagnosticSeverity::ERROR) => "error",
                Some(lsp_types::DiagnosticSeverity::WARNING) => "warning",
                _ => "info",
            };
            eprintln!("{}: {}", severity, d.message);
        }
        std::process::exit(if diagnostics.is_empty() { 0 } else { 1 });
    }

    let (connection, io_threads) = Connection::stdio();

    let (init_id, _init_params) = connection.initialize_start().unwrap();
    let _init_params: InitializeParams = serde_json::from_value(_init_params).unwrap();

    let init_result = covalence_lsp::initialize_result();
    connection
        .initialize_finish(init_id, serde_json::to_value(init_result).unwrap())
        .unwrap();

    eprintln!("Covalence LSP initialized");

    let mut server = covalence_lsp::Server::new();

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
