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
    Cog,

    /// Start the LSP server
    #[cfg(feature = "lsp")]
    Lsp(LspArgs),

    /// Start the web server
    #[cfg(feature = "serve")]
    Serve(ServeArgs),
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
}

fn main() {
    init_tracing();

    #[cfg(not(target_family = "wasm"))]
    color_eyre::install().expect("color-eyre");

    let cli = Cli::parse();

    match cli.command {
        None => println!("covalence {VERSION_LONG}"),

        #[cfg(feature = "cogit")]
        Some(Command::Cog) => {
            println!("cogit {} ({})", covalence_git::VERSION, covalence::TARGET);
        }

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
        Some(Command::Serve(args)) => {
            #[cfg(target_family = "wasm")]
            {
                eprintln!("cov serve: not available on WASM targets");
                std::process::exit(1);
            }
            #[cfg(not(target_family = "wasm"))]
            {
                if let Err(e) = cmd_serve(args) {
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
    };

    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?
        .block_on(covalence_serve::run_serve(config))
}
