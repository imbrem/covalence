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
        Some(HolCommand::Check(args)) => {
            if let Err(e) = run_check(args) {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
    }
}

fn run_check(args: CheckArgs) -> eyre::Result<()> {
    use covalence_hol::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, PureHol};
    use covalence_opentheory::{ArticleInterp, NameTable};

    if args.files.is_empty() {
        eyre::bail!("no article files specified");
    }

    let mut kernel = PureHol::new(FUN_TYCON_ID, BOOL_TYCON_ID, EQ_CONST_ID);
    let mut names = NameTable::new();
    let mut failures = 0;

    for path in &args.files {
        let input =
            std::fs::read_to_string(path).map_err(|e| eyre::eyre!("{}: {e}", path.display()))?;

        let interp = ArticleInterp::new(&mut kernel, &mut names);
        match interp.interpret(&input) {
            Ok(result) => {
                let n_thm = result.theorems.len();
                let n_ax = result.assumptions.len();
                if args.stats || args.verbose {
                    println!(
                        "{}: {} theorem{}, {} axiom{}",
                        path.display(),
                        n_thm,
                        if n_thm == 1 { "" } else { "s" },
                        n_ax,
                        if n_ax == 1 { "" } else { "s" },
                    );
                } else {
                    println!("{}: ok ({n_thm} theorems)", path.display());
                }
            }
            Err(e) => {
                eprintln!("{}: error: {e}", path.display());
                failures += 1;
                if !args.keep_going {
                    std::process::exit(1);
                }
            }
        }
    }

    if failures > 0 {
        eyre::bail!("{failures} article(s) failed");
    }
    Ok(())
}
