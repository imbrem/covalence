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
        assert!(matches!(classify_url("/abs/path"), CloneSource::Local(p) if p.to_str() == Some("/abs/path")));
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
        assert!(matches!(classify_url("github.com/foo"), CloneSource::Http(_)));
    }
}
