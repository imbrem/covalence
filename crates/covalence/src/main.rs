use clap::{Parser, Subcommand};

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
    }
}

fn init_tracing() {
    use tracing_subscriber::EnvFilter;

    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info,hyper=warn,tower=warn"));

    tracing_subscriber::fmt().with_env_filter(filter).init();
}

#[cfg(all(feature = "serve", not(target_family = "wasm")))]
fn cmd_serve(args: ServeArgs) -> eyre::Result<()> {
    let config = covalence_serve::ServeConfig {
        version: covalence::VERSION,
        target: covalence::TARGET,
        port: args.port,
        open: args.open,
        api_only: args.api,
    };

    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?
        .block_on(covalence_serve::run_serve(config))
}
