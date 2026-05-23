use clap::Subcommand;

#[derive(clap::Args)]
pub struct CogArgs {
    #[command(subcommand)]
    pub command: Option<CogCommand>,
}

#[derive(Subcommand)]
pub enum CogCommand {
    /// Hash file contents with one or more algorithms
    HashBlob(HashBlobArgs),
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
#[clap(rename_all = "snake_case")]
pub enum HashAlgo {
    Blake3,
    GitSha1,
    GitSha256,
    Sha256,
}

impl From<HashAlgo> for covalence_git::HashAlgo {
    fn from(a: HashAlgo) -> Self {
        match a {
            HashAlgo::Blake3 => Self::Blake3,
            HashAlgo::GitSha1 => Self::GitSha1,
            HashAlgo::GitSha256 => Self::GitSha256,
            HashAlgo::Sha256 => Self::Sha256,
        }
    }
}

#[derive(clap::Args)]
pub struct HashBlobArgs {
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

pub fn run(args: CogArgs) {
    match args.command {
        None => println!("cogit {} ({})", covalence_git::VERSION, covalence::TARGET),
        Some(CogCommand::HashBlob(args)) => {
            if let Err(e) = run_hash_blob(args) {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
    }
}

fn run_hash_blob(args: HashBlobArgs) -> std::io::Result<()> {
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
    let algos: Vec<covalence_git::HashAlgo> = algos.into_iter().map(Into::into).collect();
    covalence_git::hash_blob(&args.paths, &algos, args.json)
}
