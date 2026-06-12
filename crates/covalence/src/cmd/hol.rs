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
                "cov hol check is temporarily disabled while the PureHol kernel \
                 is being migrated to the HOL-Light primitive rule set. Track \
                 the kernel-design branch for the WASM-proof rewrite."
            );
            std::process::exit(2);
        }
    }
}

// The PureHol-backed `run_check` is gated while the PureHol
// adapter is being migrated to the HOL-Light primitive rule
// set (Pure→HOL collapse). Preserved in git history; reinstate
// once `covalence-hol::pure_hol` lands on the new kernel API.
