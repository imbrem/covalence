#[derive(clap::Args)]
pub struct ServeArgs {
    /// Port to listen on
    #[arg(long, default_value_t = 3100)]
    port: u16,

    /// Open browser after starting
    #[arg(long)]
    open: bool,

    /// Serve API only (no static frontend)
    #[arg(long)]
    api: bool,

    /// Listen on Unix socket only (no TCP)
    #[arg(long)]
    socket_only: bool,

    /// Use SQLite store for persistence (optional path; defaults to XDG data dir)
    #[arg(long, num_args = 0..=1, default_missing_value = "")]
    store: Option<String>,

    /// Use in-memory store (default, conflicts with --store)
    #[arg(long, conflicts_with = "store")]
    memory: bool,
}

#[cfg(not(target_family = "wasm"))]
pub fn run(args: ServeArgs) -> eyre::Result<()> {
    let store = super::resolve_store(args.store)?;
    let config = covalence_serve::ServeConfig {
        version: covalence::VERSION,
        target: covalence::TARGET,
        port: args.port,
        open: args.open,
        api_only: args.api,
        socket_only: args.socket_only,
        store,
    };

    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?
        .block_on(covalence_serve::run_serve(config))?;
    Ok(())
}
