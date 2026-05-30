use clap::Subcommand;

#[cfg(feature = "cogit")]
pub mod cog;
pub mod decide;
#[cfg(all(feature = "hol", not(target_family = "wasm")))]
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
    #[cfg(all(feature = "hol", not(target_family = "wasm")))]
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

    /// Decide a proposition from a WAT or WASM file
    Decide(decide::DecideArgs),
}

/// Run a fallible command, printing errors and exiting on failure.
#[cfg(not(target_family = "wasm"))]
pub fn run_or_exit(result: eyre::Result<()>) {
    if let Err(e) = result {
        eprintln!("{e:?}");
        std::process::exit(1);
    }
}

/// Load persisted covalence tree hashes from a GitStore's `cov_trees` table
/// and register them with the kernel so `is_tree()` returns true.
#[cfg(all(feature = "cogit", not(target_family = "wasm")))]
pub fn load_git_trees(kernel: &covalence_kernel::Kernel, store_arg: Option<&str>) {
    let db_path = match store_arg {
        None => return, // in-memory store — no persisted trees
        Some("") => match covalence_proto::config::default_store_path() {
            Some(p) => p,
            None => return,
        },
        Some(path) => std::path::PathBuf::from(path),
    };
    let git_store =
        match covalence_git::store::GitStore::open(&db_path, covalence_git::gix_hash::Kind::Sha1) {
            Ok(s) => s,
            Err(_) => return, // store doesn't exist or can't be opened — skip silently
        };
    let hashes = git_store.cov_tree_hashes();
    for hash in hashes {
        kernel.register_tree(hash);
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
