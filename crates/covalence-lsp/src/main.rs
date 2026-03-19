use lsp_server::{Connection, Message};
use lsp_types::InitializeParams;

fn main() {
    let (connection, io_threads) = Connection::stdio();

    let (init_id, _init_params) = connection.initialize_start().unwrap();
    let _init_params: InitializeParams =
        serde_json::from_value(_init_params).unwrap();

    let init_result = covalence_lsp::initialize_result();
    connection
        .initialize_finish(init_id, serde_json::to_value(init_result).unwrap())
        .unwrap();

    eprintln!("Covalence LSP initialized");

    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req).unwrap_or(false) {
                    break;
                }
                if let Some(resp) = covalence_lsp::handle_request(&req) {
                    connection.sender.send(Message::Response(resp)).unwrap();
                }
            }
            Message::Notification(not) => {
                covalence_lsp::handle_notification(&not);
            }
            Message::Response(_) => {}
        }
    }

    io_threads.join().unwrap();
}
