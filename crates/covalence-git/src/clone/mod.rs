//! Clone a git repository into a covalence store.
//!
//! Implements the git smart HTTP protocol v2 with packfile parsing, storing
//! fetched objects directly into a [`GitStore`](crate::store::GitStore).

mod http;
pub mod packfile;
pub mod pktline;

use std::io;

use covalence_hash::{O256, gix_hash};

use crate::store::GitStore;

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

/// Clone a remote git repository into a [`GitStore`].
///
/// Uses the git smart HTTP protocol v2 to:
/// 1. Discover server capabilities
/// 2. List remote refs (optionally filtered by prefix)
/// 3. Fetch objects (with optional depth/filter)
/// 4. Parse the packfile and store objects
pub fn clone_into(
    opts: &CloneOptions,
    store: &GitStore,
    mut progress: impl FnMut(&str),
) -> io::Result<CloneResult> {
    let url = http::GitUrl::parse(&opts.url);
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
