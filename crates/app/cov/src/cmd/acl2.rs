//! `cov acl2` — untrusted corpus progress and fail-closed completeness gates.

use std::path::PathBuf;

use clap::{Args, Subcommand, ValueEnum};
use covalence_lisp::book::BookConfig;
use covalence_lisp::progress::{CompletenessRequirement, CorpusProgress, ProgressMode, run_corpus};

#[derive(Args)]
pub struct Acl2Args {
    #[command(subcommand)]
    command: Option<Acl2Command>,
}

#[derive(Subcommand)]
enum Acl2Command {
    /// Report deterministic import progress without enforcing completeness.
    Progress(CorpusArgs),
    /// Fail unless every target reaches the requested completeness level.
    Check(CheckArgs),
}

#[derive(Args)]
struct CorpusArgs {
    /// Traverse and classify books without checked replay.
    #[arg(long)]
    inventory: bool,

    /// Emit the canonical source/include/event manifest instead of the summary.
    #[arg(long)]
    manifest: bool,

    /// Root containing the selected ACL2 books.
    root: PathBuf,

    /// Caller-supplied pinned corpus revision.
    revision: String,

    /// Root-relative target books.
    #[arg(required = true)]
    books: Vec<String>,
}

#[derive(Args)]
struct CheckArgs {
    #[command(flatten)]
    corpus: CorpusArgs,

    /// Minimum completeness level required of every target.
    #[arg(long, value_enum, default_value_t = RequirementArg::SourceGreen)]
    require: RequirementArg,

    /// Require exact byte equality with a previously emitted canonical manifest.
    #[arg(long)]
    expected_manifest: Option<PathBuf>,
}

#[derive(Clone, Copy, ValueEnum)]
enum RequirementArg {
    EventCompatible,
    DefinitionsComplete,
    LogicalGreen,
    SourceGreen,
}

impl From<RequirementArg> for CompletenessRequirement {
    fn from(value: RequirementArg) -> Self {
        match value {
            RequirementArg::EventCompatible => Self::EventCompatible,
            RequirementArg::DefinitionsComplete => Self::DefinitionsComplete,
            RequirementArg::LogicalGreen => Self::LogicalGreen,
            RequirementArg::SourceGreen => Self::SourceGreen,
        }
    }
}

pub fn run(args: Acl2Args) -> eyre::Result<()> {
    match args.command {
        None => {
            println!("cov acl2 (ACL2 book progress and checked completeness gates)");
            Ok(())
        }
        Some(Acl2Command::Progress(args)) => {
            let progress = corpus_progress(&args);
            print_progress(&progress, args.manifest);
            Ok(())
        }
        Some(Acl2Command::Check(args)) => {
            let progress = corpus_progress(&args.corpus);
            print_progress(&progress, args.corpus.manifest);
            progress
                .check(args.require.into())
                .map_err(|error| eyre::eyre!("{error}"))?;
            if let Some(expected) = args.expected_manifest {
                let bytes = std::fs::read(&expected)
                    .map_err(|error| eyre::eyre!("manifest.read:{}:{error}", expected.display()))?;
                progress
                    .check_manifest(&bytes)
                    .map_err(|error| eyre::eyre!("{error}"))?;
            }
            Ok(())
        }
    }
}

fn corpus_progress(args: &CorpusArgs) -> CorpusProgress {
    let config = BookConfig::new(&args.root).with_dir_root("system", &args.root);
    let mode = if args.inventory {
        ProgressMode::Inventory
    } else {
        ProgressMode::Replay
    };
    run_corpus(config, args.revision.clone(), args.books.clone(), mode)
}

fn print_progress(progress: &CorpusProgress, manifest: bool) {
    if manifest {
        print!("{}", progress.to_manifest_tsv());
    } else {
        print!("{}", progress.to_tsv());
    }
}
