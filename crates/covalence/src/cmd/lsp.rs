use crate::VERSION_LONG;

#[derive(clap::Args)]
pub struct LspArgs {
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

pub fn run(args: LspArgs) {
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
