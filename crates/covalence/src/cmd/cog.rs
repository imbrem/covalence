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

    /// Mount a tree object (by O256 hash) as a read-only FUSE filesystem
    ///
    /// Linux-only scaffold. No range requests; reading a large file pulls
    /// the entire blob into memory per syscall. Intended for cog repos full
    /// of small text files and for agent/LLM-driven inspection.
    #[cfg(target_os = "linux")]
    Mount(MountArgs),
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

#[cfg(target_os = "linux")]
#[derive(clap::Args)]
pub struct MountArgs {
    /// Tree object hash (hex-encoded O256, 64 hex chars).
    pub hash: String,

    /// Mountpoint directory (must exist and be empty).
    pub mountpoint: std::path::PathBuf,

    /// SQLite store path. If omitted, attempts server auto-discovery and
    /// errors out if no running covalence server is found.
    #[arg(long)]
    pub store: Option<std::path::PathBuf>,

    /// Allow other users to access the mount (passes `allow_other` to FUSE).
    /// Requires `user_allow_other` in /etc/fuse.conf.
    #[arg(long)]
    pub allow_other: bool,
}

#[derive(clap::Args)]
pub struct CloneArgs {
    /// Repository URL (http/https), local path (`file://`, `/abs/path`,
    /// `./rel/path`, `~/path`), or `.` / omitted to discover and clone the
    /// repository enclosing the current working directory.
    pub url: Option<String>,

    /// Shallow clone depth (HTTP clones only)
    #[arg(long)]
    pub depth: Option<u32>,

    /// Partial clone filter (e.g. "blob:none") (HTTP clones only)
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
        #[cfg(target_os = "linux")]
        Some(CogCommand::Mount(args)) => {
            if let Err(e) = run_mount(args) {
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

    let url = resolve_clone_url(args.url.as_deref())?;

    let opts = CloneOptions {
        url: url.clone(),
        depth: args.depth,
        filter: args.filter.clone(),
        ref_prefixes,
    };

    let result = clone_into(&opts, &store, |msg| {
        eprintln!("{msg}");
    })?;

    println!("Cloned {} object(s) from {}", result.objects_stored, url);
    for r in &result.refs {
        if let Some(ref target) = r.symref_target {
            println!("  {} -> {} {}", r.name, target, r.oid);
        } else {
            println!("  {} {}", r.name, r.oid);
        }
    }
    if !result.cov_trees.is_empty() {
        println!("Registered {} covalence tree(s)", result.cov_trees.len());
    }
    if !result.shallow_boundaries.is_empty() {
        println!("Shallow boundaries: {}", result.shallow_boundaries.len());
    }
    if let Some(ref path) = args.store {
        println!("Store: {}", path.display());
        println!(
            "Query the SHA1 → O256 map with `cov repl --standalone --store {}` and `\"{}\" git-open`.",
            path.display(),
            path.display(),
        );
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

/// Resolve the `cov cog clone [URL]` argument:
/// - `None` or `"."` → discover the repository enclosing the current working
///   directory via [`covalence_proto::git::discover_from_cwd`].
/// - anything else → pass through unchanged.
///
/// Returns the string `clone_into` should classify (path or URL).
fn resolve_clone_url(arg: Option<&str>) -> std::io::Result<String> {
    let needs_discovery = matches!(arg, None | Some(".") | Some("./"));
    if needs_discovery {
        let repo = covalence_proto::git::discover_from_cwd().ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "no git repository found in the current directory or any ancestor",
            )
        })?;
        eprintln!(
            "Discovered {} repository at {}",
            if repo.bare { "bare" } else { "worktree" },
            repo.root.display(),
        );
        return Ok(repo.root.to_string_lossy().into_owned());
    }
    Ok(arg.unwrap().to_string())
}

#[cfg(not(target_family = "wasm"))]
fn push_to_server(
    store: &covalence_git::store::GitStore,
    backend: &covalence_client::SyncHttpBackend,
) -> std::io::Result<()> {
    use covalence_shell::SyncBackend;

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

// ---------------------------------------------------------------------------
// cov cog mount — Linux-only FUSE scaffold
// ---------------------------------------------------------------------------
//
// !!! TEMPORARY SCAFFOLD !!!
//
// The mount uses covalence-fuse's TreeFs, which has NO RANGE REQUESTS: every
// FUSE `read` pulls the full blob into memory and slices. That makes mounting
// large media catastrophic. The next major iteration introduces an
// async-range store trait in covalence-store; rewrite this command to use it
// then. See covalence-fuse's crate docs for the full rationale.

#[cfg(target_os = "linux")]
fn run_mount(args: MountArgs) -> std::io::Result<()> {
    use covalence_fuse::{TreeFsConfig, mount_tree};
    use covalence_hash::O256;

    let root: O256 = parse_o256(&args.hash).map_err(|e| {
        std::io::Error::new(std::io::ErrorKind::InvalidInput, format!("hash: {e}"))
    })?;

    let store = resolve_mount_store(args.store.as_deref())?;

    if !args.mountpoint.is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!(
                "mountpoint {} must exist and be a directory",
                args.mountpoint.display()
            ),
        ));
    }

    let cfg = TreeFsConfig {
        allow_other: args.allow_other,
        ..TreeFsConfig::default()
    };

    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;

    eprintln!(
        "Mounting {} at {} (read-only, no range requests).",
        args.hash,
        args.mountpoint.display(),
    );
    eprintln!("Ctrl-C to unmount.");

    rt.block_on(async move {
        tokio::select! {
            res = mount_tree(store, root, &args.mountpoint, cfg) => res,
            _ = tokio::signal::ctrl_c() => {
                eprintln!("\nunmounting...");
                Ok(())
            }
        }
    })?;

    Ok(())
}

#[cfg(target_os = "linux")]
fn parse_o256(s: &str) -> Result<covalence_hash::O256, String> {
    if s.len() != 64 {
        return Err(format!("expected 64 hex chars, got {}", s.len()));
    }
    let mut bytes = [0u8; 32];
    for i in 0..32 {
        let hi = hex_nibble(s.as_bytes()[i * 2])?;
        let lo = hex_nibble(s.as_bytes()[i * 2 + 1])?;
        bytes[i] = (hi << 4) | lo;
    }
    Ok(covalence_hash::O256::from_bytes(bytes))
}

#[cfg(target_os = "linux")]
fn hex_nibble(b: u8) -> Result<u8, String> {
    match b {
        b'0'..=b'9' => Ok(b - b'0'),
        b'a'..=b'f' => Ok(b - b'a' + 10),
        b'A'..=b'F' => Ok(b - b'A' + 10),
        _ => Err(format!("bad hex char: {:?}", b as char)),
    }
}

/// Pick a content store for the mount: explicit `--store` SQLite, else
/// auto-discover a running covalence server and wrap its sync HTTP backend.
#[cfg(target_os = "linux")]
fn resolve_mount_store(
    store: Option<&std::path::Path>,
) -> std::io::Result<covalence_store::BlobStore<covalence_hash::O256>> {
    use covalence_store::{BlobStore, SqliteStore};

    if let Some(path) = store {
        let sqlite = SqliteStore::open(path)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?;
        return Ok(BlobStore::new(sqlite));
    }

    let cwd = std::env::current_dir().ok();
    let servers = covalence_proto::discovery::discover_servers(cwd.as_deref());
    let url = servers
        .iter()
        .find_map(|(_, desc)| desc.url.clone())
        .ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "no --store path and no running covalence server discovered; \
                 pass --store <path> or start `cov serve` first",
            )
        })?;
    let backend = covalence_client::SyncHttpBackend::new(url);
    Ok(BlobStore::new(BackendContentStore(backend)))
}

/// Adapter that exposes a [`SyncHttpBackend`] as a [`ContentStore<O256>`].
///
/// Read-only: `put`/`insert` are wired to error because the tree mount never
/// writes. If we ever support a writable mount, plumb those through the
/// server's blob upload endpoint.
#[cfg(target_os = "linux")]
struct BackendContentStore(covalence_client::SyncHttpBackend);

#[cfg(target_os = "linux")]
impl covalence_store::ContentStore<covalence_hash::O256> for BackendContentStore {
    fn get(&self, key: &covalence_hash::O256) -> Option<Vec<u8>> {
        use covalence_shell::SyncBackend;
        self.0.get_blob(key).ok().flatten()
    }

    fn put(
        &self,
        _key: covalence_hash::O256,
        _data: &[u8],
    ) -> Result<(), covalence_store::StoreError> {
        Err(covalence_store::StoreError::Io(
            "BackendContentStore is read-only".to_string(),
        ))
    }

    fn insert(&self, _data: &[u8]) -> Result<covalence_hash::O256, covalence_store::StoreError> {
        Err(covalence_store::StoreError::Io(
            "BackendContentStore is read-only".to_string(),
        ))
    }

    fn contains(&self, key: &covalence_hash::O256) -> bool {
        use covalence_shell::SyncBackend;
        self.0.has_blob(key).unwrap_or(false)
    }
}

