use clap::Parser;

mod cmd;

#[cfg(all(feature = "repl", not(target_family = "wasm")))]
mod highlight;

const VERSION_LONG: &str = concat!(env!("CARGO_PKG_VERSION"), " (", env!("COV_TARGET"), ")");

#[derive(Parser)]
#[command(name = "cov", about = "Covalence theorem prover CLI", version = VERSION_LONG)]
struct Cli {
    #[command(subcommand)]
    command: Option<cmd::Command>,
}

fn main() {
    init_tracing();

    #[cfg(not(target_family = "wasm"))]
    color_eyre::install().expect("color-eyre");

    let cli = Cli::parse();

    match cli.command {
        None => println!("covalence {VERSION_LONG}"),

        #[cfg(all(feature = "cogit", not(target_family = "wasm")))]
        Some(cmd::Command::Cog(args)) => cmd::cog::run(args),

        #[cfg(all(feature = "hol", not(target_family = "wasm")))]
        Some(cmd::Command::Hol(args)) => cmd::hol::run(args),
        #[cfg(all(feature = "k", not(target_family = "wasm")))]
        Some(cmd::Command::K(args)) => cmd::k::run(args),

        #[cfg(feature = "lsp")]
        Some(cmd::Command::Lsp(args)) => cmd::lsp::run(args),

        #[cfg(feature = "serve")]
        Some(cmd::Command::Serve(_args)) => {
            #[cfg(target_family = "wasm")]
            {
                eprintln!("cov serve: not available on WASM targets");
                std::process::exit(1);
            }
            #[cfg(not(target_family = "wasm"))]
            cmd::run_or_exit(cmd::serve::run(_args));
        }

        #[cfg(feature = "repl")]
        Some(cmd::Command::Repl(_args)) => {
            #[cfg(target_family = "wasm")]
            {
                eprintln!("cov repl: not available on WASM targets");
                std::process::exit(1);
            }
            #[cfg(not(target_family = "wasm"))]
            cmd::run_or_exit(cmd::repl::run(_args));
        }
    }
}

fn init_tracing() {
    use tracing_subscriber::EnvFilter;

    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info,hyper=warn,tower=warn"));

    tracing_subscriber::fmt().with_env_filter(filter).init();
}
