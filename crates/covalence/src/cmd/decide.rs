#[derive(Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum InputFormat {
    /// Auto-detect from file extension and magic bytes
    Auto,
    /// Force WAT (WebAssembly Text) interpretation
    Wat,
    /// Force WASM (compiled WebAssembly component) interpretation
    Wasm,
}

#[derive(clap::Args)]
pub struct DecideArgs {
    /// Input format (auto-detect by default)
    #[arg(long, value_enum, default_value_t = InputFormat::Auto)]
    format: InputFormat,

    /// Force standalone mode (no server discovery)
    #[arg(long)]
    standalone: bool,

    /// Connect to a specific server (Unix socket path or HTTP URL)
    #[arg(long)]
    connect: Option<String>,

    /// Use SQLite store for persistence (optional path; defaults to XDG data dir)
    #[arg(long, num_args = 0..=1, default_missing_value = "")]
    store: Option<String>,

    /// Use in-memory store (default, conflicts with --store)
    #[arg(long, conflicts_with = "store")]
    memory: bool,

    /// Print timing statistics to stderr
    #[arg(long)]
    stats: bool,

    /// Paths to WAT or WASM files to decide
    files: Vec<std::path::PathBuf>,
}

#[cfg(not(target_family = "wasm"))]
pub fn run(args: DecideArgs) -> eyre::Result<()> {
    use std::time::Instant;

    if args.files.is_empty() {
        eyre::bail!("no input files");
    }

    let backend: Box<dyn covalence_kernel::SyncBackend> = if let Some(ref addr) = args.connect {
        super::connect_backend(addr)
    } else if args.standalone {
        let store = super::resolve_store(args.store)?;
        let kernel = covalence_kernel::Kernel::with_store(store).map_err(|e| eyre::eyre!("{e}"))?;
        Box::new(kernel)
    } else {
        let cwd = std::env::current_dir().ok();
        let servers = covalence_proto::discovery::discover_servers(cwd.as_deref());
        if let Some(url) = servers.first().and_then(|(_, desc)| desc.url.as_ref()) {
            if args.stats {
                eprintln!(
                    "connected to server {} (pid {})",
                    servers[0].1.id, servers[0].1.pid
                );
            }
            Box::new(covalence_client::SyncHttpBackend::new(url.clone()))
        } else {
            let store = super::resolve_store(args.store)?;
            let kernel =
                covalence_kernel::Kernel::with_store(store).map_err(|e| eyre::eyre!("{e}"))?;
            Box::new(kernel)
        }
    };

    let t_start = Instant::now();

    for path in &args.files {
        let raw = std::fs::read(path).map_err(|e| eyre::eyre!("read {}: {e}", path.display()))?;

        let is_wat = match args.format {
            InputFormat::Wat => true,
            InputFormat::Wasm => false,
            InputFormat::Auto => {
                if path.extension().is_some_and(|ext| ext == "wat") {
                    true
                } else if path.extension().is_some_and(|ext| ext == "wasm") {
                    false
                } else {
                    // Magic bytes: WASM binary starts with \0asm
                    !raw.starts_with(b"\0asm")
                }
            }
        };

        let wasm = if is_wat {
            let text = std::str::from_utf8(&raw)
                .map_err(|e| eyre::eyre!("{}: not valid UTF-8: {e}", path.display()))?;
            covalence_wasm::compile_wat(text).map_err(|e| eyre::eyre!("{}: {e}", path.display()))?
        } else {
            raw
        };

        let hash = backend.store_blob(&wasm).map_err(|e| eyre::eyre!("{e}"))?;

        let t_decide = Instant::now();
        let output = backend.decide(&hash).map_err(|e| eyre::eyre!("{e}"))?;
        let decide_elapsed = t_decide.elapsed();

        for proved_hash in &output.proved {
            println!("{proved_hash} true");
        }
        println!("{hash} {}", output.decision);

        if args.stats {
            eprintln!(
                "{}: decided in {:.3}ms",
                path.display(),
                decide_elapsed.as_secs_f64() * 1000.0,
            );
        }
    }

    if args.stats {
        eprintln!("total: {:.3}ms", t_start.elapsed().as_secs_f64() * 1000.0);
    }

    Ok(())
}
