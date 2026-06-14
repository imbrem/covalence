//! Per-repo cog store living inside an existing `.git` directory.
//!
//! A repository already carries a content-addressed object database under
//! `.git`. The cog store is a sibling database next to it — keyed by
//! BLAKE3 (`O256`) instead of git's SHA — anchored at the git
//! **commondir** so all linked worktrees share one cache. It is
//! auto-ignored (nothing under `.git` is tracked), travels with the
//! gitdir, and needs no global install.
//!
//! The directory is `.git/cog-<COG_STORE_UUID>/`; the trailing UUID is a
//! fixed, well-known marker that makes the directory unmistakable and
//! collision-proof against any future git feature or other tool named
//! "cog".
//!
//! Layout:
//! ```text
//! .git/cog-<uuid>/
//!   store.db    SQLite ContentStore<O256>  (small blobs)
//!   objects/    BLAKE3 loose store         (large blobs)
//!   sources.json  remote upstreams + url->hash cache   (later)
//! ```

mod loose;
pub use loose::Blake3LooseStore;

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use covalence_hash::O256;
use covalence_store::{BlobStore, SizeRouter, SqliteStore, StoreError};

/// The one well-known cog-store directory UUID. Never changes.
pub const COG_STORE_UUID: &str = "14169d9d-e25f-46dd-abc7-dd53b495cd06";

/// The cog-store directory name: `cog-<COG_STORE_UUID>`.
pub const COG_STORE_DIRNAME: &str = "cog-14169d9d-e25f-46dd-abc7-dd53b495cd06";

/// Handle to a cog-store directory inside a git repository.
///
/// Pure path logic plus thin opener helpers; constructing the handle
/// neither touches the filesystem nor creates anything until you call
/// [`create`](Self::create) or one of the `open_*` methods.
#[derive(Debug, Clone)]
pub struct CogStoreDir {
    dir: PathBuf,
}

impl CogStoreDir {
    /// Anchor the store at an already-resolved git common directory: the
    /// store lives at `<commondir>/cog-<uuid>/`.
    pub fn at_commondir(commondir: &Path) -> Self {
        Self {
            dir: commondir.join(COG_STORE_DIRNAME),
        }
    }

    /// Resolve the commondir for a repository root (a worktree root, a
    /// `.git` directory, or a bare gitdir) and anchor the store there.
    pub fn from_repo_root(repo_root: &Path) -> io::Result<Self> {
        Ok(Self::at_commondir(&resolve_commondir(repo_root)?))
    }

    /// Walk up from the current working directory to the enclosing
    /// repository and anchor the store at its commondir. Returns `None`
    /// if no git repository encloses the cwd.
    pub fn discover() -> io::Result<Option<Self>> {
        let cwd = std::env::current_dir()?;
        let start = fs::canonicalize(&cwd).unwrap_or(cwd);
        for dir in start.ancestors() {
            if is_repo_root(dir) {
                return Ok(Some(Self::from_repo_root(dir)?));
            }
        }
        Ok(None)
    }

    /// The store directory (`.git/cog-<uuid>/`).
    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// Path to the default SQLite blob store (`store.db`).
    pub fn db_path(&self) -> PathBuf {
        self.dir.join("store.db")
    }

    /// Path to the BLAKE3 loose-object directory (`objects/`).
    pub fn objects_dir(&self) -> PathBuf {
        self.dir.join("objects")
    }

    /// Path to the remote-source descriptor (`sources.json`).
    pub fn sources_path(&self) -> PathBuf {
        self.dir.join("sources.json")
    }

    /// Create the store directory (`mkdir -p`).
    pub fn create(&self) -> io::Result<()> {
        fs::create_dir_all(&self.dir)
    }

    /// Open (creating if absent) the SQLite blob store at `store.db`.
    pub fn open_sqlite(&self) -> Result<SqliteStore, StoreError> {
        self.create().map_err(|e| StoreError::Io(e.to_string()))?;
        SqliteStore::open(self.db_path()).map_err(|e| StoreError::Io(e.to_string()))
    }

    /// A BLAKE3 loose-object store over `objects/` (the directory is
    /// created lazily on first write).
    pub fn loose(&self) -> Blake3LooseStore {
        Blake3LooseStore::new(self.objects_dir())
    }

    /// The opinionated default store: a single SQLite `ContentStore<O256>`.
    pub fn open_default(&self) -> Result<BlobStore<O256>, StoreError> {
        Ok(BlobStore::new(self.open_sqlite()?))
    }

    /// A size-routed store: small blobs to SQLite, large blobs (`>=
    /// threshold` bytes) to the BLAKE3 loose store; reads consult both.
    pub fn open_routed(&self, threshold: u64) -> Result<BlobStore<O256>, StoreError> {
        let small = BlobStore::new(self.open_sqlite()?);
        let large = BlobStore::new(self.loose());
        Ok(BlobStore::new(SizeRouter::new(small, large, threshold)))
    }
}

/// True if `dir` looks like a repository root: it contains `.git`
/// (worktree, file or directory) or is itself a bare gitdir.
fn is_repo_root(dir: &Path) -> bool {
    if fs::symlink_metadata(dir.join(".git")).is_ok() {
        return true;
    }
    dir.join("objects").is_dir() && dir.join("HEAD").is_file()
}

/// Resolve the shared common directory for a repository root.
///
/// Handles worktree roots (`<root>/.git` directory), linked-worktree
/// gitlinks (`<root>/.git` is a `gitdir: <path>` file), and bare
/// repositories (the input is itself the gitdir). The commondir is the
/// gitdir unless a `commondir` pointer file redirects it (linked
/// worktrees), so every worktree shares one store.
fn resolve_commondir(repo_root: &Path) -> io::Result<PathBuf> {
    let gitdir = resolve_gitdir(repo_root)?;
    let commondir = match fs::read_to_string(gitdir.join("commondir")) {
        Ok(s) => {
            let joined = gitdir.join(s.trim());
            fs::canonicalize(&joined).unwrap_or(joined)
        }
        Err(_) => gitdir.clone(),
    };
    Ok(commondir)
}

/// Resolve a repository root to its (per-worktree) gitdir.
fn resolve_gitdir(repo_root: &Path) -> io::Result<PathBuf> {
    let dot_git = repo_root.join(".git");
    match fs::symlink_metadata(&dot_git) {
        Ok(m) if m.is_file() => {
            // Linked-worktree gitlink: `gitdir: <path>`.
            let content = fs::read_to_string(&dot_git)?;
            let rest = content
                .lines()
                .find_map(|l| l.strip_prefix("gitdir:"))
                .map(str::trim)
                .ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("{}: malformed gitlink", dot_git.display()),
                    )
                })?;
            let p = PathBuf::from(rest);
            let abs = if p.is_absolute() { p } else { repo_root.join(p) };
            Ok(fs::canonicalize(&abs).unwrap_or(abs))
        }
        Ok(_) => Ok(dot_git), // `.git` directory: ordinary worktree.
        Err(_) => {
            // Bare repository: the root is itself the gitdir.
            if repo_root.join("objects").is_dir() && repo_root.join("HEAD").is_file() {
                Ok(repo_root.to_path_buf())
            } else {
                Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    format!("not a git repository: {}", repo_root.display()),
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_store::ContentStore;

    fn fresh(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("cov_cog_dir_{name}_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn dirname_matches_uuid() {
        assert_eq!(COG_STORE_DIRNAME, format!("cog-{COG_STORE_UUID}"));
    }

    #[test]
    fn worktree_commondir_is_dot_git() {
        let root = fresh("worktree");
        fs::create_dir_all(root.join(".git")).unwrap();
        let cog = CogStoreDir::from_repo_root(&root).unwrap();
        assert_eq!(cog.dir(), root.join(".git").join(COG_STORE_DIRNAME));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn linked_worktree_follows_gitlink() {
        let root = fresh("linked");
        let common = root.join("main/.git");
        let wt_gitdir = common.join("worktrees/wt");
        fs::create_dir_all(&wt_gitdir).unwrap();
        fs::create_dir_all(common.join("objects")).unwrap();
        // The linked worktree's gitdir points back at the common dir.
        fs::write(wt_gitdir.join("commondir"), "../..\n").unwrap();
        let wt = root.join("wt");
        fs::create_dir_all(&wt).unwrap();
        fs::write(wt.join(".git"), format!("gitdir: {}\n", wt_gitdir.display())).unwrap();

        let cog = CogStoreDir::from_repo_root(&wt).unwrap();
        assert_eq!(cog.dir(), common.join(COG_STORE_DIRNAME));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn open_default_round_trips() {
        let root = fresh("default");
        fs::create_dir_all(root.join(".git")).unwrap();
        let cog = CogStoreDir::from_repo_root(&root).unwrap();
        let store = cog.open_default().unwrap();
        let key = store.insert(b"hello cog").unwrap();
        assert_eq!(store.get(&key).unwrap(), b"hello cog");
        assert!(cog.db_path().exists());
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn open_routed_splits_by_size() {
        let root = fresh("routed");
        fs::create_dir_all(root.join(".git")).unwrap();
        let cog = CogStoreDir::from_repo_root(&root).unwrap();
        let store = cog.open_routed(8).unwrap();

        let small = store.insert(b"tiny").unwrap();
        let large = store.insert(b"a clearly larger blob").unwrap();
        assert_eq!(store.get(&small).unwrap(), b"tiny");
        assert_eq!(store.get(&large).unwrap(), b"a clearly larger blob");

        // The large blob landed in the loose store, the small one did not.
        assert!(cog.loose().contains(&large));
        assert!(!cog.loose().contains(&small));
        let _ = fs::remove_dir_all(&root);
    }
}
