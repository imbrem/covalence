use clap::Subcommand;

#[cfg(feature = "cogit")]
pub mod cog;
#[cfg(feature = "hol")]
pub mod hol;
#[cfg(feature = "lsp")]
pub mod lsp;
#[cfg(feature = "repl")]
pub mod repl;
#[cfg(feature = "serve")]
pub mod serve;

#[derive(Subcommand)]
pub enum Command {
    /// Cogit VCS
    #[cfg(feature = "cogit")]
    Cog(cog::CogArgs),

    /// HOL Light kernel
    #[cfg(feature = "hol")]
    Hol(hol::HolArgs),

    /// Start the LSP server
    #[cfg(feature = "lsp")]
    Lsp(lsp::LspArgs),

    /// Start the web server
    #[cfg(feature = "serve")]
    Serve(serve::ServeArgs),

    /// Start the interactive REPL
    #[cfg(feature = "repl")]
    Repl(repl::ReplArgs),
}

/// Run a fallible command, printing errors and exiting on failure.
#[cfg(not(target_family = "wasm"))]
pub fn run_or_exit(result: eyre::Result<()>) {
    if let Err(e) = result {
        eprintln!("{e:?}");
        std::process::exit(1);
    }
}

/// Create a backend from a `--connect` value.
/// Paths (starting with `/` or `./`) and `unix:` prefixed strings use Unix domain sockets;
/// everything else is treated as an HTTP URL.
#[cfg(not(target_family = "wasm"))]
pub fn connect_backend(addr: &str) -> Box<dyn covalence_kernel::SyncBackend> {
    if let Some(path) = addr.strip_prefix("unix:") {
        Box::new(covalence_client::SyncHttpBackend::unix(path.to_string()))
    } else if addr.starts_with('/') || addr.starts_with("./") {
        Box::new(covalence_client::SyncHttpBackend::unix(addr.to_string()))
    } else {
        Box::new(covalence_client::SyncHttpBackend::new(addr.to_string()))
    }
}

#[cfg(not(target_family = "wasm"))]
pub fn resolve_store(
    store_arg: Option<String>,
) -> eyre::Result<covalence_store::BlobStore<covalence_store::O256>> {
    use covalence_store::{BlobStore, SharedMemoryStore};

    match store_arg {
        None => Ok(BlobStore::new(SharedMemoryStore::new())),
        Some(path) => {
            let db_path = if path.is_empty() {
                covalence_proto::config::default_store_path()
                    .ok_or_else(|| eyre::eyre!("cannot determine default store path"))?
            } else {
                std::path::PathBuf::from(&path)
            };
            if let Some(parent) = db_path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            tracing::info!("store: {}", db_path.display());
            let sqlite = covalence_store::SqliteStore::open(&db_path)
                .map_err(|e| eyre::eyre!("open store: {e}"))?;
            Ok(BlobStore::new(sqlite))
        }
    }
}
