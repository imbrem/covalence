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

    /// Clone a git repository into a covalence store
    Clone(CloneArgs),
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

#[derive(clap::Args)]
pub struct CloneArgs {
    /// Repository URL (HTTP/HTTPS)
    pub url: String,

    /// Shallow clone depth
    #[arg(long)]
    pub depth: Option<u32>,

    /// Partial clone filter (e.g. "blob:none")
    #[arg(long)]
    pub filter: Option<String>,

    /// Only fetch refs matching this branch name
    #[arg(long)]
    pub branch: Option<String>,

    /// SQLite store path (default: in-memory)
    #[arg(long)]
    pub store: Option<std::path::PathBuf>,
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
        Some(CogCommand::Clone(args)) => {
            if let Err(e) = run_clone(args) {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
    }
}

fn run_clone(args: CloneArgs) -> std::io::Result<()> {
    use covalence_git::clone::{CloneOptions, clone_into};
    use covalence_git::gix_hash;
    use covalence_git::store::GitStore;

    let store = match &args.store {
        Some(path) => GitStore::open(path, gix_hash::Kind::Sha1)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?,
        None => GitStore::memory(gix_hash::Kind::Sha1)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?,
    };

    let ref_prefixes = match &args.branch {
        Some(b) => vec![format!("refs/heads/{b}"), "HEAD".to_string()],
        None => vec![],
    };

    let opts = CloneOptions {
        url: args.url.clone(),
        depth: args.depth,
        filter: args.filter.clone(),
        ref_prefixes,
    };

    let result = clone_into(&opts, &store, |msg| {
        eprintln!("{msg}");
    })?;

    println!(
        "Cloned {} object(s) from {}",
        result.objects_stored, args.url
    );
    for r in &result.refs {
        if let Some(ref target) = r.symref_target {
            println!("  {} -> {} {}", r.name, target, r.oid);
        } else {
            println!("  {} {}", r.name, r.oid);
        }
    }
    if !result.cov_trees.is_empty() {
        println!("Trees (O256):");
        for (git_oid, cov_hash) in &result.cov_trees {
            println!("  {git_oid} -> {cov_hash}");
        }
    }
    if !result.shallow_boundaries.is_empty() {
        println!("Shallow boundaries: {}", result.shallow_boundaries.len());
    }
    if let Some(ref path) = args.store {
        println!("Store: {}", path.display());
    } else {
        println!("Store: in-memory (objects will be discarded)");
    }

    // Auto-discover a running covalence server and push objects to it
    // (skip when --store is used — the user wants local persistence only).
    #[cfg(not(target_family = "wasm"))]
    if args.store.is_none() {
        let cwd = std::env::current_dir().ok();
        let servers = covalence_proto::discovery::discover_servers(cwd.as_deref());
        if let Some(url) = servers.first().and_then(|(_, desc)| desc.url.as_ref()) {
            println!(
                "Pushing to server {} (pid {})...",
                servers[0].1.id, servers[0].1.pid
            );
            let backend = covalence_client::SyncHttpBackend::new(url.clone());
            push_to_server(&store, &backend)?;
        }
    }

    Ok(())
}

#[cfg(not(target_family = "wasm"))]
fn push_to_server(
    store: &covalence_git::store::GitStore,
    backend: &covalence_client::SyncHttpBackend,
) -> std::io::Result<()> {
    use covalence_kernel::SyncBackend;

    let blobs = store
        .all_blob_data()
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?;
    for data in &blobs {
        backend
            .store_blob(data)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?;
    }
    let trees = store
        .all_tree_data()
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?;
    for data in &trees {
        backend
            .store_tree(data)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?;
    }
    println!("Pushed {} blob(s) and {} tree(s)", blobs.len(), trees.len());
    Ok(())
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
