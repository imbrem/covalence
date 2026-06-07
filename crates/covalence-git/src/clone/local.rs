//! Clone from a local git repository on disk.
//!
//! Walks every reachable git object in a source repository's object database
//! (loose objects and pack files) and writes each into a [`GitStore`], then
//! enumerates the source's refs and finally runs the git-tree → covalence-tree
//! conversion. The clone is eager: every object in the source ODB is copied,
//! and the resulting store has full coverage independent of the source.

use std::collections::HashSet;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use covalence_hash::gix_hash;

use crate::store::{GitBackend, GitStore, OdbBackend};

use super::{CloneResult, RemoteRef};

/// Options for cloning a local git repository.
pub struct LocalCloneOptions {
    /// Path to a git repository: a worktree root containing `.git`, a bare
    /// gitdir containing `objects/`, or a `.git` directory itself.
    pub path: PathBuf,
    /// Only ingest refs whose names start with one of these prefixes. An
    /// empty list ingests every ref. `HEAD` is always reported.
    pub ref_prefixes: Vec<String>,
}

/// Clone a local git repository into a [`GitStore`].
///
/// 1. Resolves the gitdir (handling worktree-pointer `.git` files and
///    `commondir` indirection).
/// 2. Iterates every object in the source ODB and writes it into `store`.
/// 3. Reads `HEAD`, loose refs under `refs/`, and `packed-refs`.
/// 4. Calls [`GitStore::convert_trees`] to register covalence trees.
pub fn clone_local_into(
    opts: &LocalCloneOptions,
    store: &GitStore,
    mut progress: impl FnMut(&str),
) -> io::Result<CloneResult> {
    let layout = RepoLayout::resolve(&opts.path)?;
    progress(&format!(
        "Source gitdir: {} (commondir: {})",
        layout.gitdir.display(),
        layout.commondir.display(),
    ));

    let objects_dir = layout.commondir.join("objects");
    if !objects_dir.is_dir() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!(
                "not a git repository: {} has no objects/",
                layout.commondir.display()
            ),
        ));
    }

    let src = OdbBackend::open_auto(&objects_dir).map_err(store_err_to_io)?;

    progress("Iterating source objects...");
    let mut objects_stored = 0usize;
    let mut seen: HashSet<gix_hash::ObjectId> = HashSet::new();
    for oid in src.iter_oids().map_err(store_err_to_io)? {
        let oid = oid.map_err(store_err_to_io)?;
        if !seen.insert(oid) {
            continue;
        }
        let obj = src.read_object(&oid).map_err(store_err_to_io)?;
        let written = store
            .write_object(obj.kind, &obj.data)
            .map_err(store_err_to_io)?;
        if written != oid {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("hash mismatch on copy: src {oid}, dest {written}"),
            ));
        }
        objects_stored += 1;
    }
    progress(&format!("Copied {objects_stored} object(s)"));

    progress("Reading refs...");
    let refs = read_refs(&layout, &opts.ref_prefixes)?;
    for r in &refs {
        if let Some(ref target) = r.symref_target {
            progress(&format!("  {} -> {} ({})", r.name, target, r.oid));
        } else {
            progress(&format!("  {} {}", r.name, r.oid));
        }
    }

    progress("Converting trees...");
    let cov_trees = store.convert_trees().map_err(store_err_to_io)?;
    progress(&format!("Converted {} tree(s)", cov_trees.len()));

    Ok(CloneResult {
        refs,
        objects_stored,
        shallow_boundaries: Vec::new(),
        cov_trees,
    })
}

fn store_err_to_io(e: covalence_store::StoreError) -> io::Error {
    io::Error::new(io::ErrorKind::Other, e.to_string())
}

/// Layout of a git repository on disk.
struct RepoLayout {
    /// Per-worktree gitdir (where `HEAD` and worktree-local refs live).
    gitdir: PathBuf,
    /// Shared common dir (where `objects/`, `packed-refs`, and shared refs
    /// live). Equals `gitdir` for non-worktree repositories.
    commondir: PathBuf,
}

impl RepoLayout {
    fn resolve(input: &Path) -> io::Result<Self> {
        let gitdir = resolve_gitdir(input)?;
        let commondir = match fs::read_to_string(gitdir.join("commondir")) {
            Ok(s) => {
                let rel = s.trim();
                let joined = gitdir.join(rel);
                fs::canonicalize(&joined).unwrap_or(joined)
            }
            Err(_) => gitdir.clone(),
        };
        Ok(Self { gitdir, commondir })
    }
}

/// Resolve a user-supplied path to a gitdir.
fn resolve_gitdir(input: &Path) -> io::Result<PathBuf> {
    let meta = fs::metadata(input)
        .map_err(|e| io::Error::new(e.kind(), format!("{}: {e}", input.display())))?;

    if meta.is_file() {
        // Worktree gitlink: `gitdir: <path>`
        return parse_gitlink(input);
    }

    let dot_git = input.join(".git");
    if let Ok(m) = fs::metadata(&dot_git) {
        if m.is_dir() {
            return Ok(dot_git);
        }
        if m.is_file() {
            return parse_gitlink(&dot_git);
        }
    }

    // Treat `input` as a gitdir (bare repo or already-resolved gitdir).
    if input.join("objects").is_dir() || input.join("HEAD").is_file() {
        return Ok(input.to_path_buf());
    }

    Err(io::Error::new(
        io::ErrorKind::NotFound,
        format!("not a git repository: {}", input.display()),
    ))
}

fn parse_gitlink(file: &Path) -> io::Result<PathBuf> {
    let contents = fs::read_to_string(file)?;
    for line in contents.lines() {
        if let Some(rest) = line.strip_prefix("gitdir:") {
            let rel = rest.trim();
            let base = file.parent().unwrap_or(Path::new("."));
            let joined = base.join(rel);
            return Ok(fs::canonicalize(&joined).unwrap_or(joined));
        }
    }
    Err(io::Error::new(
        io::ErrorKind::InvalidData,
        format!("{}: no gitdir line", file.display()),
    ))
}

/// Read all refs from a repository layout.
fn read_refs(layout: &RepoLayout, prefixes: &[String]) -> io::Result<Vec<RemoteRef>> {
    use std::collections::HashMap;

    let mut by_name: HashMap<String, RemoteRef> = HashMap::new();
    let mut head_symref: Option<String> = None;

    // 1. HEAD lives in the worktree gitdir.
    let head_path = layout.gitdir.join("HEAD");
    if let Ok(contents) = fs::read_to_string(&head_path) {
        let trimmed = contents.trim();
        if let Some(target) = trimmed.strip_prefix("ref:") {
            head_symref = Some(target.trim().to_string());
        } else if let Ok(oid) = gix_hash::ObjectId::from_hex(trimmed.as_bytes()) {
            // Detached HEAD: report HEAD as a concrete ref.
            by_name.insert(
                "HEAD".to_string(),
                RemoteRef {
                    name: "HEAD".to_string(),
                    oid,
                    symref_target: None,
                },
            );
        }
    }

    // 2. Loose refs under <gitdir>/refs/ (worktree-local) and
    //    <commondir>/refs/ (shared). gitdir wins on collision.
    walk_loose_refs(&layout.commondir, "refs", &mut by_name)?;
    if layout.gitdir != layout.commondir {
        walk_loose_refs(&layout.gitdir, "refs", &mut by_name)?;
    }

    // 3. packed-refs lives in the commondir; loose refs override packed.
    let packed = layout.commondir.join("packed-refs");
    if let Ok(contents) = fs::read_to_string(&packed) {
        parse_packed_refs(&contents, &mut by_name);
    }

    // 4. Resolve HEAD symref to the corresponding concrete OID, if known.
    if let Some(target) = head_symref {
        if let Some(target_ref) = by_name.get(&target) {
            let oid = target_ref.oid;
            by_name.insert(
                "HEAD".to_string(),
                RemoteRef {
                    name: "HEAD".to_string(),
                    oid,
                    symref_target: Some(target),
                },
            );
        }
    }

    // 5. Apply prefix filter (HEAD is always kept).
    let mut refs: Vec<RemoteRef> = by_name
        .into_values()
        .filter(|r| {
            r.name == "HEAD"
                || prefixes.is_empty()
                || prefixes.iter().any(|p| r.name.starts_with(p))
        })
        .collect();
    refs.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(refs)
}

/// Recursively read loose refs from `<root>/<rel>`, where each file's contents
/// are an OID (or a symref the parent ref reading already handled). New entries
/// overwrite existing ones — call commondir-first, then gitdir.
fn walk_loose_refs(
    root: &Path,
    rel: &str,
    out: &mut std::collections::HashMap<String, RemoteRef>,
) -> io::Result<()> {
    let dir = root.join(rel);
    let entries = match fs::read_dir(&dir) {
        Ok(e) => e,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => return Err(e),
    };
    for entry in entries {
        let entry = entry?;
        let ty = entry.file_type()?;
        let name = entry.file_name();
        let name_str = match name.to_str() {
            Some(s) => s,
            None => continue,
        };
        let child_rel = format!("{rel}/{name_str}");
        if ty.is_dir() {
            walk_loose_refs(root, &child_rel, out)?;
            continue;
        }
        let contents = match fs::read_to_string(entry.path()) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let trimmed = contents.trim();
        // A loose ref may be a symref; we treat the OID form as authoritative
        // and ignore loose symrefs (rare outside HEAD).
        if trimmed.starts_with("ref:") {
            continue;
        }
        if let Ok(oid) = gix_hash::ObjectId::from_hex(trimmed.as_bytes()) {
            out.insert(
                child_rel.clone(),
                RemoteRef {
                    name: child_rel,
                    oid,
                    symref_target: None,
                },
            );
        }
    }
    Ok(())
}

/// Parse a `packed-refs` file. Only inserts refs not already present
/// (loose refs win).
fn parse_packed_refs(contents: &str, out: &mut std::collections::HashMap<String, RemoteRef>) {
    for line in contents.lines() {
        let line = line.trim_end();
        if line.is_empty() || line.starts_with('#') || line.starts_with('^') {
            // `^<oid>` peeled lines apply to the previous tag; we currently
            // drop them (the unpeeled OID is what callers iterate from).
            continue;
        }
        let mut parts = line.splitn(2, ' ');
        let oid_hex = match parts.next() {
            Some(s) => s,
            None => continue,
        };
        let name = match parts.next() {
            Some(s) => s,
            None => continue,
        };
        let oid = match gix_hash::ObjectId::from_hex(oid_hex.as_bytes()) {
            Ok(o) => o,
            Err(_) => continue,
        };
        out.entry(name.to_string()).or_insert(RemoteRef {
            name: name.to_string(),
            oid,
            symref_target: None,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::{GitObjectKind, LooseBackend};

    fn fresh_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "cov_local_clone_{name}_{}_{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// Build a minimal git repo at `gitdir` with one blob, one tree pointing at
    /// the blob, one commit pointing at the tree, and `refs/heads/main` →
    /// commit. Returns the commit OID and tree OID.
    fn build_repo(gitdir: &Path) -> (gix_hash::ObjectId, gix_hash::ObjectId) {
        let objects = gitdir.join("objects");
        fs::create_dir_all(&objects).unwrap();
        let loose = LooseBackend::new(&objects, gix_hash::Kind::Sha1);

        let blob_data = b"hello local clone";
        let blob_oid = loose.write_object(GitObjectKind::Blob, blob_data).unwrap();

        // Tree entry: "100644 hello\0<20-byte OID>"
        let mut tree_data = Vec::new();
        tree_data.extend_from_slice(b"100644 hello\0");
        tree_data.extend_from_slice(blob_oid.as_bytes());
        let tree_oid = loose.write_object(GitObjectKind::Tree, &tree_data).unwrap();

        let commit_data = format!(
            "tree {tree_oid}\nauthor A <a@b> 0 +0000\ncommitter A <a@b> 0 +0000\n\nfirst commit\n"
        );
        let commit_oid = loose
            .write_object(GitObjectKind::Commit, commit_data.as_bytes())
            .unwrap();

        // refs/heads/main → commit, HEAD → ref: refs/heads/main
        let refs_heads = gitdir.join("refs").join("heads");
        fs::create_dir_all(&refs_heads).unwrap();
        fs::write(refs_heads.join("main"), format!("{commit_oid}\n")).unwrap();
        fs::write(gitdir.join("HEAD"), "ref: refs/heads/main\n").unwrap();

        (commit_oid, tree_oid)
    }

    #[test]
    fn clone_bare_layout() {
        let work = fresh_dir("bare");
        let src = work.join("src.git");
        fs::create_dir_all(&src).unwrap();
        let (commit_oid, tree_oid) = build_repo(&src);

        let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
        let opts = LocalCloneOptions {
            path: src.clone(),
            ref_prefixes: Vec::new(),
        };
        let mut log = Vec::new();
        let result = clone_local_into(&opts, &dest, |m| log.push(m.to_string())).unwrap();

        assert_eq!(result.objects_stored, 3, "blob + tree + commit");
        assert!(dest.contains_object(&commit_oid));
        assert!(dest.contains_object(&tree_oid));

        // refs/heads/main and HEAD (symref-resolved to the same commit).
        let main = result
            .refs
            .iter()
            .find(|r| r.name == "refs/heads/main")
            .expect("refs/heads/main");
        assert_eq!(main.oid, commit_oid);
        let head = result.refs.iter().find(|r| r.name == "HEAD").expect("HEAD");
        assert_eq!(head.oid, commit_oid);
        assert_eq!(head.symref_target.as_deref(), Some("refs/heads/main"));

        // Tree conversion produced exactly one covalence tree.
        assert_eq!(result.cov_trees.len(), 1);
        assert_eq!(result.cov_trees[0].0, tree_oid);

        let _ = fs::remove_dir_all(&work);
    }

    #[test]
    fn clone_worktree_layout() {
        let work = fresh_dir("worktree");
        let repo = work.join("repo");
        let gitdir = repo.join(".git");
        fs::create_dir_all(&gitdir).unwrap();
        let (commit_oid, _tree_oid) = build_repo(&gitdir);

        let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
        let opts = LocalCloneOptions {
            path: repo.clone(),
            ref_prefixes: Vec::new(),
        };
        let result = clone_local_into(&opts, &dest, |_| {}).unwrap();

        assert_eq!(result.objects_stored, 3);
        let head = result.refs.iter().find(|r| r.name == "HEAD").unwrap();
        assert_eq!(head.oid, commit_oid);

        let _ = fs::remove_dir_all(&work);
    }

    #[test]
    fn clone_with_packed_refs_and_prefix_filter() {
        let work = fresh_dir("packed");
        let src = work.join("src.git");
        fs::create_dir_all(&src).unwrap();
        let (commit_oid, _) = build_repo(&src);

        // Move refs/heads/main into packed-refs and remove the loose copy.
        let loose_main = src.join("refs").join("heads").join("main");
        fs::remove_file(&loose_main).unwrap();
        let packed = format!(
            "# pack-refs with: peeled fully-peeled sorted \n{commit_oid} refs/heads/main\n{commit_oid} refs/tags/v1\n^{commit_oid}\n",
        );
        fs::write(src.join("packed-refs"), packed).unwrap();

        let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();

        // No filter → both refs visible (plus HEAD).
        let result = clone_local_into(
            &LocalCloneOptions {
                path: src.clone(),
                ref_prefixes: Vec::new(),
            },
            &dest,
            |_| {},
        )
        .unwrap();
        assert!(result.refs.iter().any(|r| r.name == "refs/heads/main"));
        assert!(result.refs.iter().any(|r| r.name == "refs/tags/v1"));
        assert!(result.refs.iter().any(|r| r.name == "HEAD"));

        // Filter to refs/heads/* — tags drop, HEAD kept.
        let dest2 = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
        let result = clone_local_into(
            &LocalCloneOptions {
                path: src.clone(),
                ref_prefixes: vec!["refs/heads/".to_string()],
            },
            &dest2,
            |_| {},
        )
        .unwrap();
        assert!(result.refs.iter().any(|r| r.name == "refs/heads/main"));
        assert!(!result.refs.iter().any(|r| r.name == "refs/tags/v1"));
        assert!(result.refs.iter().any(|r| r.name == "HEAD"));

        let _ = fs::remove_dir_all(&work);
    }

    #[test]
    fn detached_head() {
        let work = fresh_dir("detached");
        let src = work.join("src.git");
        fs::create_dir_all(&src).unwrap();
        let (commit_oid, _) = build_repo(&src);
        // Overwrite HEAD with a detached OID.
        fs::write(src.join("HEAD"), format!("{commit_oid}\n")).unwrap();
        // Drop refs/heads so HEAD is the only thing pointing at the commit.
        let _ = fs::remove_dir_all(src.join("refs").join("heads"));

        let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
        let result = clone_local_into(
            &LocalCloneOptions {
                path: src.clone(),
                ref_prefixes: Vec::new(),
            },
            &dest,
            |_| {},
        )
        .unwrap();
        let head = result.refs.iter().find(|r| r.name == "HEAD").unwrap();
        assert_eq!(head.oid, commit_oid);
        assert!(head.symref_target.is_none());

        let _ = fs::remove_dir_all(&work);
    }

    #[test]
    fn not_a_git_repo() {
        let dir = fresh_dir("nope");
        let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
        let err = clone_local_into(
            &LocalCloneOptions {
                path: dir.clone(),
                ref_prefixes: Vec::new(),
            },
            &dest,
            |_| {},
        )
        .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound);
        let _ = fs::remove_dir_all(&dir);
    }
}
