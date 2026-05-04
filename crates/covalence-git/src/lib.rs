pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub fn run_cog(args: &[String], target: &str) {
    match args.first().map(|s| s.as_str()) {
        Some("--version" | "-V") => {
            println!("cog {} ({})", VERSION, target);
        }
        Some("--help" | "-h") => {
            println!("cog — Cogit VCS");
            println!();
            println!("Usage: cog [OPTIONS]");
            println!();
            println!("Options:");
            println!("  -h, --help     Print this help message");
            println!("  -V, --version  Print version");
        }
        None => {
            println!("cogit {} ({})", VERSION, target);
        }
        Some(other) => {
            eprintln!("cog: unknown option '{other}'");
            eprintln!("Try 'cog --help' for more information.");
            std::process::exit(1);
        }
    }
}
