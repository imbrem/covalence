fn main() {
    let args: Vec<String> = std::env::args().collect();

    // argv[0] detection: if invoked as "cog" (e.g. via symlink), act as `cov cog`
    let argv0 = args.first().map(|s| {
        std::path::Path::new(s)
            .file_name()
            .unwrap_or_default()
            .to_str()
            .unwrap_or_default()
            .to_owned()
    });

    #[cfg(feature = "cogit")]
    if argv0.as_deref() == Some("cog") {
        covalence_git::run_cog(&args[1..], covalence::TARGET);
        return;
    }

    match args.get(1).map(|s| s.as_str()) {
        Some("--version" | "-V") => {
            println!("cov {} ({})", covalence::VERSION, covalence::TARGET);
        }
        Some("--help" | "-h") => {
            println!("cov — Covalence theorem prover CLI");
            println!();
            println!("Usage: cov [COMMAND] [OPTIONS]");
            println!();
            println!("Commands:");
            println!("  cog  Cogit VCS");
            println!("  lsp  Start the Covalence LSP server");
            println!();
            println!("Options:");
            println!("  -h, --help     Print this help message");
            println!("  -V, --version  Print version");
        }
        #[cfg(feature = "cogit")]
        Some("cog") => {
            covalence_git::run_cog(&args[2..], covalence::TARGET);
        }
        #[cfg(feature = "lsp")]
        Some("lsp") => {
            let config = covalence_lsp::LspConfig {
                version: covalence::VERSION,
                target: covalence::TARGET,
            };
            covalence_lsp::run_lsp(&args[2..], &config);
        }
        None => {
            println!("covalence {} ({})", covalence::VERSION, covalence::TARGET);
        }
        Some(other) => {
            eprintln!("cov: unknown command '{other}'");
            eprintln!("Try 'cov --help' for more information.");
            std::process::exit(1);
        }
    }
}
