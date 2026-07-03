//! Discover the enclosing git repository for a path.
//!
//! Walks the ancestor chain of a starting directory looking for a worktree
//! root (`<dir>/.git` exists as a file or directory) or a bare gitdir
//! (`<dir>/objects/` and `<dir>/HEAD` both exist).
//!
//! This is independent of the server-discovery code in
//! [`crate::discovery`] — it has no platform deps and is always available.

use std::fs;
use std::path::{Path, PathBuf};

/// A git repository discovered on disk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiscoveredRepo {
    /// The path a clone/CLI would treat as the repository.
    ///
    /// For a worktree this is the worktree root (the directory containing
    /// `.git`). For a bare repository this is the gitdir itself.
    pub root: PathBuf,
    /// True if the repository has no working tree.
    pub bare: bool,
}

/// Walk up from `start` looking for a git repository.
///
/// Returns the closest enclosing repository, or `None` if none is found before
/// hitting the filesystem root. `start` is canonicalized when possible so
/// symlinks and relative paths like `.` resolve to the same location.
pub fn discover_git_repo(start: &Path) -> Option<DiscoveredRepo> {
    let canonical = fs::canonicalize(start).ok();
    let walk_from: &Path = canonical.as_deref().unwrap_or(start);
    for dir in walk_from.ancestors() {
        if let Some(repo) = classify_dir(dir) {
            return Some(repo);
        }
    }
    None
}

/// Walk up from the process's current working directory.
pub fn discover_from_cwd() -> Option<DiscoveredRepo> {
    let cwd = std::env::current_dir().ok()?;
    discover_git_repo(&cwd)
}

fn classify_dir(dir: &Path) -> Option<DiscoveredRepo> {
    let dot_git = dir.join(".git");
    if fs::symlink_metadata(&dot_git).is_ok() {
        return Some(DiscoveredRepo {
            root: dir.to_path_buf(),
            bare: false,
        });
    }
    // Bare-repo shape: `objects/` plus `HEAD`. Requiring both avoids
    // matching arbitrary directories named e.g. `objects/`.
    if dir.join("objects").is_dir() && dir.join("HEAD").is_file() {
        return Some(DiscoveredRepo {
            root: dir.to_path_buf(),
            bare: true,
        });
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "cov_repo_discover_{name}_{}_{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn finds_worktree_root_from_subdir() {
        let work = fresh_dir("worktree");
        let repo = work.join("repo");
        fs::create_dir_all(repo.join(".git")).unwrap();
        let nested = repo.join("a").join("b").join("c");
        fs::create_dir_all(&nested).unwrap();

        let found = discover_git_repo(&nested).expect("should find repo");
        assert_eq!(found.root, fs::canonicalize(&repo).unwrap());
        assert!(!found.bare);

        let _ = fs::remove_dir_all(&work);
    }

    #[test]
    fn finds_worktree_root_from_dot_git_file() {
        // `.git` may be a file (worktree gitlink, submodule). Discovery only
        // cares that *something* called `.git` exists — clone resolution
        // handles the gitlink itself.
        let work = fresh_dir("gitlink");
        let repo = work.join("repo");
        fs::create_dir_all(&repo).unwrap();
        fs::write(repo.join(".git"), "gitdir: /tmp/something\n").unwrap();
        let nested = repo.join("sub");
        fs::create_dir_all(&nested).unwrap();

        let found = discover_git_repo(&nested).expect("should find repo");
        assert_eq!(found.root, fs::canonicalize(&repo).unwrap());
        assert!(!found.bare);

        let _ = fs::remove_dir_all(&work);
    }

    #[test]
    fn finds_bare_repo() {
        let work = fresh_dir("bare");
        let bare = work.join("repo.git");
        fs::create_dir_all(bare.join("objects")).unwrap();
        fs::write(bare.join("HEAD"), "ref: refs/heads/main\n").unwrap();

        let found = discover_git_repo(&bare).expect("should find bare repo");
        assert_eq!(found.root, fs::canonicalize(&bare).unwrap());
        assert!(found.bare);

        let _ = fs::remove_dir_all(&work);
    }

    #[test]
    fn returns_none_when_nothing_to_find() {
        let dir = fresh_dir("none");
        // Hop up via a uniquely named sub-tree so we don't accidentally
        // discover the temp dir's own enclosing repository.
        let nested = dir.join("a").join("b");
        fs::create_dir_all(&nested).unwrap();
        // We can't guarantee /tmp itself isn't under a repo, so we only
        // assert: if a repo is found, it is NOT inside `dir`.
        if let Some(found) = discover_git_repo(&nested) {
            let canonical_dir = fs::canonicalize(&dir).unwrap();
            assert!(
                !found.root.starts_with(&canonical_dir),
                "discovered {:?} inside test dir {:?}",
                found.root,
                canonical_dir,
            );
        }
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn closest_ancestor_wins() {
        let work = fresh_dir("nested");
        let outer = work.join("outer");
        fs::create_dir_all(outer.join(".git")).unwrap();
        let inner = outer.join("inner");
        fs::create_dir_all(inner.join(".git")).unwrap();
        let leaf = inner.join("sub");
        fs::create_dir_all(&leaf).unwrap();

        let found = discover_git_repo(&leaf).expect("should find repo");
        assert_eq!(found.root, fs::canonicalize(&inner).unwrap());

        let _ = fs::remove_dir_all(&work);
    }
}
