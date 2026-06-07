//! Clone a git repository into a covalence store.
//!
//! Implements the git smart HTTP protocol v2 with packfile parsing, storing
//! fetched objects directly into a [`GitStore`](crate::store::GitStore).

mod http;
pub mod local;
pub mod packfile;
pub mod pktline;

use std::io;
use std::path::PathBuf;

use covalence_hash::{O256, gix_hash};

use crate::store::GitStore;

pub use local::{LocalCloneOptions, clone_local_into};

/// Options for cloning a git repository.
pub struct CloneOptions {
    /// Repository URL (HTTP/HTTPS).
    pub url: String,
    /// Shallow clone depth (e.g. `Some(1)` for `--depth 1`).
    pub depth: Option<u32>,
    /// Partial clone filter (e.g. `"blob:none"`).
    pub filter: Option<String>,
    /// Only fetch refs matching these prefixes (e.g. `["refs/heads/main"]`).
    pub ref_prefixes: Vec<String>,
}

/// A remote reference discovered during clone.
#[derive(Debug, Clone)]
pub struct RemoteRef {
    /// Full ref name (e.g. `refs/heads/main`).
    pub name: String,
    /// Object ID the ref points to.
    pub oid: gix_hash::ObjectId,
    /// Symbolic ref target (e.g. `HEAD` → `refs/heads/main`).
    pub symref_target: Option<String>,
}

/// Result of a clone operation.
#[derive(Debug)]
pub struct CloneResult {
    /// Remote refs discovered.
    pub refs: Vec<RemoteRef>,
    /// Number of objects stored.
    pub objects_stored: usize,
    /// Shallow boundary OIDs (for shallow clones).
    pub shallow_boundaries: Vec<gix_hash::ObjectId>,
    /// Covalence tree hashes (O256) produced by converting git trees.
    /// Each entry maps a git tree OID to its covalence O256 keyed tree hash.
    pub cov_trees: Vec<(gix_hash::ObjectId, O256)>,
}

/// Source location for a clone.
pub enum CloneSource {
    /// An HTTP/HTTPS git remote (smart-protocol v2).
    Http(String),
    /// A local git repository on disk.
    Local(PathBuf),
}

/// Classify a clone URL.
///
/// `file://` URLs, paths starting with `/`, `./`, `../`, or `~/`, and `http(s)`
/// URLs are recognised. Anything else falls back to HTTP — preserving the
/// existing behaviour for bare hostnames or relative paths typed as URLs.
pub fn classify_url(url: &str) -> CloneSource {
    if let Some(rest) = url.strip_prefix("file://") {
        // Tolerate `file:///path` (empty host) and `file://path` (host == path).
        let path = rest.trim_start_matches('/');
        let mut out = PathBuf::from("/");
        out.push(path);
        return CloneSource::Local(out);
    }
    if url.starts_with("http://") || url.starts_with("https://") {
        return CloneSource::Http(url.to_string());
    }
    if url.starts_with('/')
        || url.starts_with("./")
        || url.starts_with("../")
        || url.starts_with("~/")
    {
        let expanded = if let Some(rest) = url.strip_prefix("~/") {
            match std::env::var_os("HOME") {
                Some(home) => {
                    let mut p = PathBuf::from(home);
                    p.push(rest);
                    p
                }
                None => PathBuf::from(url),
            }
        } else {
            PathBuf::from(url)
        };
        return CloneSource::Local(expanded);
    }
    CloneSource::Http(url.to_string())
}

/// Clone a git repository into a [`GitStore`].
///
/// Dispatches by URL: HTTP(S) remotes use the smart-protocol v2 transport,
/// local paths (and `file://` URLs) walk the source ODB directly via
/// [`clone_local_into`].
///
/// This is the synchronous entry point. To call from a tokio context — e.g.
/// from an axum handler in `covalence-serve` — enable the `clone-async`
/// feature and use [`async_clone_into`] instead.
pub fn clone_into(
    opts: &CloneOptions,
    store: &GitStore,
    mut progress: impl FnMut(&str),
) -> io::Result<CloneResult> {
    match classify_url(&opts.url) {
        CloneSource::Local(path) => clone_local_into(
            &LocalCloneOptions {
                path,
                ref_prefixes: opts.ref_prefixes.clone(),
            },
            store,
            progress,
        ),
        CloneSource::Http(http_url) => clone_http_into(&http_url, opts, store, &mut progress),
    }
}

/// Tokio-friendly wrapper around [`clone_into`].
///
/// The clone itself is fundamentally blocking — ureq + rustls drive the HTTP
/// transport, the packfile parser is CPU-bound, and `GitStore` writes hit
/// SQLite synchronously. Running it on tokio's blocking thread pool via
/// [`tokio::task::spawn_blocking`] keeps the runtime responsive without
/// rewriting any of that to be async.
///
/// `progress` runs on the blocking thread. To stream updates back to async
/// callers, push them into an mpsc channel:
///
/// ```ignore
/// let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<String>();
/// let handle = tokio::spawn(async_clone_into(opts, store, move |m| {
///     let _ = tx.send(m.to_string());
/// }));
/// while let Some(msg) = rx.recv().await { /* forward to client */ }
/// let result = handle.await??;
/// ```
#[cfg(feature = "clone-async")]
pub async fn async_clone_into<F>(
    opts: CloneOptions,
    store: GitStore,
    mut progress: F,
) -> io::Result<CloneResult>
where
    F: FnMut(&str) + Send + 'static,
{
    tokio::task::spawn_blocking(move || clone_into(&opts, &store, |m| progress(m)))
        .await
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("clone join: {e}")))?
}

fn clone_http_into(
    http_url: &str,
    opts: &CloneOptions,
    store: &GitStore,
    progress: &mut dyn FnMut(&str),
) -> io::Result<CloneResult> {
    let url = http::GitUrl::parse(http_url);
    let agent =
        ureq::Agent::new_with_config(ureq::config::Config::builder().https_only(false).build());

    // 1. Discover capabilities
    progress("Discovering server capabilities...");
    let caps = http::discover(&agent, &url)?;
    if caps.version < 2 {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            format!(
                "server does not support protocol v2 (got version {})",
                caps.version
            ),
        ));
    }

    // 2. List refs
    progress("Listing remote refs...");
    let remote_refs = http::ls_refs(&agent, &url, &opts.ref_prefixes)?;
    if remote_refs.is_empty() {
        return Ok(CloneResult {
            refs: Vec::new(),
            objects_stored: 0,
            shallow_boundaries: Vec::new(),
            cov_trees: Vec::new(),
        });
    }

    for r in &remote_refs {
        if let Some(ref target) = r.symref_target {
            progress(&format!("  {} -> {} ({})", r.name, target, r.oid));
        } else {
            progress(&format!("  {} {}", r.name, r.oid));
        }
    }

    // 3. Build want list (deduplicated)
    let mut wants: Vec<gix_hash::ObjectId> = remote_refs.iter().map(|r| r.oid).collect();
    wants.sort();
    wants.dedup();

    // 4. Fetch
    progress(&format!("Fetching {} object(s)...", wants.len()));
    let fetch_resp = http::fetch(&agent, &url, &wants, opts.depth, opts.filter.as_deref())?;

    // 5. Parse packfile
    progress("Parsing packfile...");
    let pack_result = if fetch_resp.pack_data.is_empty() {
        packfile::PackResult { objects_stored: 0 }
    } else {
        packfile::parse_pack(&fetch_resp.pack_data, store)?
    };

    progress(&format!(
        "Done: {} objects stored",
        pack_result.objects_stored
    ));

    // 6. Record shallow boundaries
    for oid in &fetch_resp.shallow_oids {
        store
            .insert_shallow(oid, None)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e.to_string()))?;
    }

    // 7. Convert git trees to covalence trees
    progress("Converting trees...");
    let cov_trees = store
        .convert_trees()
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e.to_string()))?;
    progress(&format!("Converted {} tree(s)", cov_trees.len()));

    // Convert refs
    let refs = remote_refs
        .into_iter()
        .map(|r| RemoteRef {
            name: r.name,
            oid: r.oid,
            symref_target: r.symref_target,
        })
        .collect();

    Ok(CloneResult {
        refs,
        objects_stored: pack_result.objects_stored,
        shallow_boundaries: fetch_resp.shallow_oids,
        cov_trees,
    })
}

#[cfg(test)]
mod url_tests {
    use super::*;

    #[test]
    fn classify_local_paths() {
        assert!(
            matches!(classify_url("/abs/path"), CloneSource::Local(p) if p.to_str() == Some("/abs/path"))
        );
        assert!(matches!(classify_url("./rel"), CloneSource::Local(_)));
        assert!(matches!(classify_url("../up"), CloneSource::Local(_)));
        assert!(matches!(
            classify_url("file:///abs/path"),
            CloneSource::Local(p) if p.to_str() == Some("/abs/path")
        ));
        assert!(matches!(
            classify_url("file://host/p"),
            CloneSource::Local(p) if p.to_str() == Some("/host/p")
        ));
    }

    #[test]
    fn classify_http_urls() {
        assert!(matches!(
            classify_url("https://github.com/foo/bar"),
            CloneSource::Http(s) if s == "https://github.com/foo/bar"
        ));
        assert!(matches!(
            classify_url("http://localhost:8080"),
            CloneSource::Http(_)
        ));
        // Bare hostname / scheme-less URL falls through to HTTP for back-compat.
        assert!(matches!(
            classify_url("github.com/foo"),
            CloneSource::Http(_)
        ));
    }
}

#[cfg(all(test, feature = "clone-async"))]
mod async_tests {
    use super::*;
    use crate::store::{GitBackend, GitObjectKind, LooseBackend};
    use covalence_hash::gix_hash;
    use std::fs;
    use std::path::PathBuf;
    use std::sync::{Arc, Mutex};

    fn fresh_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "cov_async_clone_{name}_{}_{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn build_repo(gitdir: &std::path::Path) -> gix_hash::ObjectId {
        let objects = gitdir.join("objects");
        fs::create_dir_all(&objects).unwrap();
        let loose = LooseBackend::new(&objects, gix_hash::Kind::Sha1);
        let blob = loose
            .write_object(GitObjectKind::Blob, b"async hello")
            .unwrap();
        let mut tree = Vec::new();
        tree.extend_from_slice(b"100644 hi\0");
        tree.extend_from_slice(blob.as_bytes());
        let tree_oid = loose.write_object(GitObjectKind::Tree, &tree).unwrap();
        let commit =
            format!("tree {tree_oid}\nauthor A <a@b> 0 +0000\ncommitter A <a@b> 0 +0000\n\nok\n");
        let commit_oid = loose
            .write_object(GitObjectKind::Commit, commit.as_bytes())
            .unwrap();
        let refs = gitdir.join("refs").join("heads");
        fs::create_dir_all(&refs).unwrap();
        fs::write(refs.join("main"), format!("{commit_oid}\n")).unwrap();
        fs::write(gitdir.join("HEAD"), "ref: refs/heads/main\n").unwrap();
        commit_oid
    }

    /// The async wrapper drives the clone on tokio's blocking pool and the
    /// `Send + 'static` progress callback fires from there.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn async_clone_local_collects_progress_and_objects() {
        let work = fresh_dir("local");
        let src = work.join("src.git");
        fs::create_dir_all(&src).unwrap();
        let commit_oid = build_repo(&src);

        let store = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
        let opts = CloneOptions {
            url: src.to_string_lossy().into_owned(),
            depth: None,
            filter: None,
            ref_prefixes: Vec::new(),
        };

        // Progress is captured via a Send + 'static closure (the same shape a
        // server would use to feed an mpsc::UnboundedSender<String>).
        let log: Arc<Mutex<Vec<String>>> = Arc::default();
        let log_for_cb = log.clone();
        let result = async_clone_into(opts, store.clone(), move |m| {
            log_for_cb.lock().unwrap().push(m.to_string());
        })
        .await
        .unwrap();

        assert_eq!(result.objects_stored, 3);
        assert!(store.contains_object(&commit_oid));
        let head = result.refs.iter().find(|r| r.name == "HEAD").unwrap();
        assert_eq!(head.oid, commit_oid);

        let log = log.lock().unwrap();
        assert!(
            log.iter().any(|m| m.contains("Iterating source objects")),
            "progress callback should have received transport messages, got {log:?}"
        );

        let _ = fs::remove_dir_all(&work);
    }

    /// `spawn_blocking` surfaces panics in the work as Err — make sure we wrap
    /// the JoinError into an io::Error rather than panicking the caller.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn async_clone_propagates_clone_errors() {
        let dir = fresh_dir("notrepo");
        let store = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
        let opts = CloneOptions {
            url: dir.to_string_lossy().into_owned(),
            depth: None,
            filter: None,
            ref_prefixes: Vec::new(),
        };
        let err = async_clone_into(opts, store, |_| {}).await.unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound);
        let _ = fs::remove_dir_all(&dir);
    }
}
