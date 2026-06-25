use std::path::PathBuf;

use clap::Subcommand;

#[derive(clap::Args)]
pub struct HolArgs {
    #[command(subcommand)]
    pub command: Option<HolCommand>,
}

#[derive(Subcommand)]
pub enum HolCommand {
    /// Check OpenTheory article files
    Check(CheckArgs),
}

#[derive(clap::Args)]
pub struct CheckArgs {
    /// Print each command as it executes
    #[arg(long)]
    verbose: bool,

    /// Print summary statistics
    #[arg(long)]
    stats: bool,

    /// Continue checking remaining files after the first failure.
    #[arg(long)]
    keep_going: bool,

    /// Article files to check (.art)
    files: Vec<PathBuf>,
}

pub fn run(args: HolArgs) {
    match args.command {
        None => println!("cov hol (HOL Light kernel)"),
        Some(HolCommand::Check(_args)) => {
            eprintln!(
                "cov hol check is not available yet — the OpenTheory article \
                 checker needs wiring to a HOL kernel over covalence-hol."
            );
            std::process::exit(2);
        }
    }
}
