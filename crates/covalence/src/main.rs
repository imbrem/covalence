use clap::{Parser, Subcommand};

#[cfg(all(feature = "repl", not(target_family = "wasm")))]
mod highlight;

const VERSION_LONG: &str = concat!(env!("CARGO_PKG_VERSION"), " (", env!("COV_TARGET"), ")");

#[derive(Parser)]
#[command(name = "cov", about = "Covalence theorem prover CLI", version = VERSION_LONG)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Cogit VCS
    #[cfg(feature = "cogit")]
    Cog(CogArgs),

    /// Start the LSP server
    #[cfg(feature = "lsp")]
    Lsp(LspArgs),

    /// Start the web server
    #[cfg(feature = "serve")]
    Serve(ServeArgs),

    /// Start the interactive REPL
    #[cfg(feature = "repl")]
    Repl(ReplArgs),
}

#[cfg(feature = "cogit")]
#[derive(clap::Args)]
struct CogArgs {
    #[command(subcommand)]
    command: Option<CogCommand>,
}

#[cfg(feature = "cogit")]
#[derive(Subcommand)]
enum CogCommand {
    /// Hash file contents with one or more algorithms
    HashBlob(HashBlobArgs),
}

#[cfg(feature = "cogit")]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
#[clap(rename_all = "snake_case")]
enum HashAlgo {
    Blake3,
    GitSha1,
    GitSha256,
    Sha256,
}

#[cfg(feature = "cogit")]
#[derive(clap::Args)]
struct HashBlobArgs {
    /// Hash algorithm(s) to use (repeatable)
    #[arg(long = "hash", value_name = "ALGO")]
    algos: Vec<HashAlgo>,

    /// Shorthand for --hash blake3
    #[arg(long)]
    blake3: bool,

    /// Shorthand for --hash sha256
    #[arg(long)]
    sha256: bool,

    /// Shorthand for --hash git_sha1
    #[arg(long)]
    git: bool,

    /// Output as JSONL (one JSON object per file)
    #[arg(long)]
    json: bool,

    /// Paths to files to hash
    paths: Vec<std::path::PathBuf>,
}

#[cfg(feature = "lsp")]
#[derive(clap::Args)]
struct LspArgs {
    /// Run diagnostics on a file and exit
    #[arg(long)]
    diagnose: Option<String>,

    /// Print version and exit
    #[arg(long)]
    version: bool,

    /// Run inside VSCode WASI host
    #[arg(long, hide = true)]
    vscode: bool,
}

#[cfg(feature = "serve")]
#[derive(clap::Args)]
struct ServeArgs {
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

#[cfg(feature = "repl")]
#[derive(clap::Args)]
struct ReplArgs {
    /// Force standalone mode (no server discovery)
    #[arg(long)]
    standalone: bool,

    /// Connect to a specific server (Unix socket path or HTTP URL)
    #[arg(long)]
    connect: Option<String>,

    /// Syntax highlighting: auto (default), always, or never.
    /// Respects NO_COLOR env var when set to auto.
    #[arg(long, default_value = "auto")]
    color: ColorMode,

    /// Use SQLite store for persistence (optional path; defaults to XDG data dir)
    #[arg(long, num_args = 0..=1, default_missing_value = "")]
    store: Option<String>,

    /// Use in-memory store (default, conflicts with --store)
    #[arg(long, conflicts_with = "store")]
    memory: bool,
}

#[cfg(feature = "repl")]
#[derive(Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
enum ColorMode {
    Auto,
    Always,
    Never,
}

fn main() {
    init_tracing();

    #[cfg(not(target_family = "wasm"))]
    color_eyre::install().expect("color-eyre");

    let cli = Cli::parse();

    match cli.command {
        None => println!("covalence {VERSION_LONG}"),

        #[cfg(feature = "cogit")]
        Some(Command::Cog(args)) => match args.command {
            None => println!("cogit {} ({})", covalence_git::VERSION, covalence::TARGET),
            Some(CogCommand::HashBlob(args)) => {
                let mut algos: Vec<HashAlgo> = args.algos;
                if args.blake3 {
                    algos.push(HashAlgo::Blake3);
                }
                if args.sha256 {
                    algos.push(HashAlgo::Sha256);
                }
                if args.git {
                    algos.push(HashAlgo::GitSha1);
                }
                algos.sort();
                algos.dedup();
                if algos.is_empty() {
                    algos.push(HashAlgo::Blake3);
                }
                let algos: Vec<covalence_git::HashAlgo> = algos
                    .iter()
                    .map(|a| match a {
                        HashAlgo::Blake3 => covalence_git::HashAlgo::Blake3,
                        HashAlgo::GitSha1 => covalence_git::HashAlgo::GitSha1,
                        HashAlgo::GitSha256 => covalence_git::HashAlgo::GitSha256,
                        HashAlgo::Sha256 => covalence_git::HashAlgo::Sha256,
                    })
                    .collect();
                if let Err(e) = covalence_git::hash_blob(&args.paths, &algos, args.json) {
                    eprintln!("{e}");
                    std::process::exit(1);
                }
            }
        },

        #[cfg(feature = "lsp")]
        Some(Command::Lsp(args)) => {
            if args.version {
                println!("covalence-lsp {VERSION_LONG}");
                return;
            }
            let config = covalence_lsp::LspConfig {
                version: covalence::VERSION,
                target: covalence::TARGET,
            };
            if let Some(path) = &args.diagnose {
                covalence_lsp::run_diagnose(path);
            } else {
                covalence_lsp::run_lsp(&config);
            }
        }

        #[cfg(feature = "serve")]
        Some(Command::Serve(_args)) => {
            #[cfg(target_family = "wasm")]
            {
                eprintln!("cov serve: not available on WASM targets");
                std::process::exit(1);
            }
            #[cfg(not(target_family = "wasm"))]
            {
                if let Err(e) = cmd_serve(_args) {
                    eprintln!("{e:?}");
                    std::process::exit(1);
                }
            }
        }

        #[cfg(feature = "repl")]
        Some(Command::Repl(_args)) => {
            #[cfg(target_family = "wasm")]
            {
                eprintln!("cov repl: not available on WASM targets");
                std::process::exit(1);
            }
            #[cfg(not(target_family = "wasm"))]
            {
                if let Err(e) = cmd_repl(_args) {
                    eprintln!("{e:?}");
                    std::process::exit(1);
                }
            }
        }
    }
}

fn init_tracing() {
    use tracing_subscriber::EnvFilter;

    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info,hyper=warn,tower=warn"));

    tracing_subscriber::fmt().with_env_filter(filter).init();
}

#[cfg(all(feature = "repl", not(target_family = "wasm")))]
fn cmd_repl(args: ReplArgs) -> eyre::Result<()> {
    use rustyline::Editor;

    let color = match args.color {
        ColorMode::Always => true,
        ColorMode::Never => false,
        ColorMode::Auto => {
            // Respect NO_COLOR convention; also check if stdout is a terminal
            std::env::var_os("NO_COLOR").is_none()
                && std::io::IsTerminal::is_terminal(&std::io::stdout())
        }
    };

    let backend: Box<dyn covalence_kernel::SyncBackend> = if let Some(ref url) = args.connect {
        Box::new(covalence_client::SyncHttpBackend::new(url.clone()))
    } else if args.standalone {
        let store = resolve_store(args.store)?;
        let kernel = covalence_kernel::Kernel::with_store(store).map_err(|e| eyre::eyre!("{e}"))?;
        Box::new(kernel)
    } else {
        // Auto-discovery: try to find a running server, fall back to kernel
        let cwd = std::env::current_dir().ok();
        let servers = covalence_proto::discovery::discover_servers(cwd.as_deref());
        if let Some(url) = servers.first().and_then(|(_, desc)| desc.url.as_ref()) {
            println!(
                "connected to server {} (pid {})",
                servers[0].1.id, servers[0].1.pid
            );
            Box::new(covalence_client::SyncHttpBackend::new(url.clone()))
        } else {
            let store = resolve_store(args.store)?;
            let kernel =
                covalence_kernel::Kernel::with_store(store).map_err(|e| eyre::eyre!("{e}"))?;
            Box::new(kernel)
        }
    };

    let mut session = covalence_repl::Session::new(backend, true, true);

    println!("covalence {VERSION_LONG}");
    println!("Type (help) for available commands.\n");

    let helper = highlight::SexpHelper { color };
    let mut rl = Editor::new()?;
    rl.set_helper(Some(helper));
    let mut buf = String::new();

    loop {
        let prompt = if buf.is_empty() { "cov> " } else { "...> " };
        match rl.readline(prompt) {
            Ok(line) => {
                let line = line.trim_end();
                if buf.is_empty() && line.is_empty() {
                    continue;
                }
                if !buf.is_empty() {
                    buf.push('\n');
                }
                buf.push_str(line);

                // Check if parens are balanced before evaluating.
                if !parens_balanced(&buf) {
                    continue;
                }

                let input = buf.trim();
                if !input.is_empty() {
                    let _ = rl.add_history_entry(input);
                    let result = session.eval(input);
                    if !result.is_empty() {
                        println!("{}", highlight::highlight_output(&result, color));
                    }
                }
                buf.clear();
            }
            Err(
                rustyline::error::ReadlineError::Interrupted | rustyline::error::ReadlineError::Eof,
            ) => {
                break;
            }
            Err(e) => {
                eprintln!("readline error: {e}");
                break;
            }
        }
    }

    Ok(())
}

/// Check if parentheses are balanced (accounting for strings).
#[cfg(all(feature = "repl", not(target_family = "wasm")))]
fn parens_balanced(input: &str) -> bool {
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut escape = false;
    for ch in input.chars() {
        if escape {
            escape = false;
            continue;
        }
        if in_string {
            match ch {
                '\\' => escape = true,
                '"' => in_string = false,
                _ => {}
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth -= 1,
            ';' => break, // rest is comment
            _ => {}
        }
    }
    depth <= 0
}

#[cfg(not(target_family = "wasm"))]
fn resolve_store(
    store_arg: Option<String>,
) -> eyre::Result<covalence_store::BlobStore<covalence_store::O256>> {
    use covalence_store::{BlobStore, SharedMemoryStore};

    match store_arg {
        None => Ok(BlobStore::new(SharedMemoryStore::new())),
        Some(path) if path.is_empty() => {
            // --store with no argument: use XDG default path
            let db_path = covalence_proto::config::default_store_path()
                .ok_or_else(|| eyre::eyre!("cannot determine default store path"))?;
            if let Some(parent) = db_path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            tracing::info!("store: {}", db_path.display());
            let sqlite = covalence_store::SqliteStore::open(&db_path)
                .map_err(|e| eyre::eyre!("open store: {e}"))?;
            Ok(BlobStore::new(sqlite))
        }
        Some(path) => {
            // --store PATH: use explicit path
            let db_path = std::path::PathBuf::from(&path);
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

#[cfg(all(feature = "serve", not(target_family = "wasm")))]
fn cmd_serve(args: ServeArgs) -> eyre::Result<()> {
    let store = resolve_store(args.store)?;
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
