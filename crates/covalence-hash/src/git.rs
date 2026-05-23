use crate::{HashCtx, O256};

/// Hash data as a git object with the given type prefix and hash algorithm.
fn object_hash(kind: gix_hash::Kind, object_type: &str, data: &[u8]) -> gix_hash::ObjectId {
    let mut hasher = gix_hash::hasher(kind);
    let header = format!("{object_type} {}\0", data.len());
    hasher.update(header.as_bytes());
    hasher.update(data);
    hasher.try_finalize().expect("git hash finalize")
}

/// Hash data as a git blob using SHA-1.
///
/// ```
/// // Matches `echo -n "hello" | git hash-object --stdin`
/// assert_eq!(
///     covalence_hash::git::blob_sha1("hello").to_string(),
///     "b6fc4c620b67d95f953a5c1c1230aaab5db5a1b0",
/// );
/// ```
pub fn blob_sha1(data: impl AsRef<[u8]>) -> gix_hash::ObjectId {
    object_hash(gix_hash::Kind::Sha1, "blob", data.as_ref())
}

/// Hash data as a git blob using SHA-256.
///
/// ```
/// // Matches `echo -n "hello" | git hash-object --stdin` in a SHA-256 repo
/// // (git init --object-format=sha256)
/// assert_eq!(
///     covalence_hash::git::blob_sha256("hello").to_string(),
///     "8aec4e4876f854f688d0ebfc8f37598f38e5fd6903cccc850ca36591175aeb60",
/// );
/// ```
pub fn blob_sha256(data: impl AsRef<[u8]>) -> gix_hash::ObjectId {
    object_hash(gix_hash::Kind::Sha256, "blob", data.as_ref())
}

/// Hash data as a git tree using SHA-1 (does not validate tree format).
pub fn tree_sha1(data: impl AsRef<[u8]>) -> gix_hash::ObjectId {
    object_hash(gix_hash::Kind::Sha1, "tree", data.as_ref())
}

/// Hash data as a git tree using SHA-256 (does not validate tree format).
pub fn tree_sha256(data: impl AsRef<[u8]>) -> gix_hash::ObjectId {
    object_hash(gix_hash::Kind::Sha256, "tree", data.as_ref())
}

/// Git SHA-1 blob hashing context.
pub struct GitSha1;

/// Git SHA-256 blob hashing context.
pub struct GitSha256;

/// Git blob hashing context, parametrized by hash algorithm.
pub enum Git {
    Sha1,
    Sha256,
}

impl HashCtx for GitSha1 {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        let oid = blob_sha1(data);
        let bytes = oid.as_bytes();
        let mut buf = [0u8; 32];
        buf[..bytes.len()].copy_from_slice(bytes);
        O256::from_bytes(buf)
    }
}

impl HashCtx for GitSha256 {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        let oid = blob_sha256(data);
        let mut buf = [0u8; 32];
        buf.copy_from_slice(oid.as_bytes());
        O256::from_bytes(buf)
    }
}

impl HashCtx for Git {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        match self {
            Git::Sha1 => GitSha1.tag(data),
            Git::Sha256 => GitSha256.tag(data),
        }
    }
}

// --- HashDir impls: hash a directory listing as a git tree ---

use crate::dir::{DirEntry, DirMode, HashDir};

/// Serialize entries in git tree format and hash with the given git hash function.
fn git_tree_bytes(entries: &[DirEntry<'_>], hash_len: usize) -> Vec<u8> {
    debug_assert!(
        entries.windows(2).all(|w| w[0].name < w[1].name),
        "entries must be sorted and unique by name",
    );

    let mut buf = Vec::new();
    for entry in entries {
        let mode_str = match entry.mode {
            DirMode::Blob => "100644",
            DirMode::Dir => "40000",
        };
        buf.extend_from_slice(mode_str.as_bytes());
        buf.push(b' ');
        buf.extend_from_slice(entry.name.as_bytes());
        buf.push(0);
        buf.extend_from_slice(&entry.hash.as_bytes()[..hash_len]);
    }
    buf
}

impl HashDir for GitSha1 {
    fn hash_dir(&self, entries: &[DirEntry<'_>]) -> O256 {
        let buf = git_tree_bytes(entries, 20);
        let oid = tree_sha1(&buf);
        let mut out = [0u8; 32];
        out[..oid.as_bytes().len()].copy_from_slice(oid.as_bytes());
        O256::from_bytes(out)
    }
}

impl HashDir for GitSha256 {
    fn hash_dir(&self, entries: &[DirEntry<'_>]) -> O256 {
        let buf = git_tree_bytes(entries, 32);
        let oid = tree_sha256(&buf);
        let mut out = [0u8; 32];
        out.copy_from_slice(oid.as_bytes());
        O256::from_bytes(out)
    }
}

impl HashDir for Git {
    fn hash_dir(&self, entries: &[DirEntry<'_>]) -> O256 {
        match self {
            Git::Sha1 => GitSha1.hash_dir(entries),
            Git::Sha256 => GitSha256.hash_dir(entries),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Reference: echo -n "hello" | git hash-object --stdin
    const GIT_SHA1_HELLO: &str = "b6fc4c620b67d95f953a5c1c1230aaab5db5a1b0";

    // Reference: echo -n "hello" | git hash-object --stdin  (in a --object-format=sha256 repo)
    const GIT_SHA256_HELLO: &str =
        "8aec4e4876f854f688d0ebfc8f37598f38e5fd6903cccc850ca36591175aeb60";

    #[test]
    fn blob_sha1_matches_git() {
        assert_eq!(blob_sha1("hello").to_string(), GIT_SHA1_HELLO);
    }

    #[test]
    fn blob_sha256_matches_git() {
        assert_eq!(blob_sha256("hello").to_string(), GIT_SHA256_HELLO);
    }

    #[test]
    fn git_sha1_ctx_matches_function() {
        let from_fn = blob_sha1("hello");
        let from_ctx = GitSha1.tag("hello");
        let mut expected = [0u8; 32];
        expected[..from_fn.as_bytes().len()].copy_from_slice(from_fn.as_bytes());
        assert_eq!(*from_ctx.as_bytes(), expected);
    }

    #[test]
    fn git_sha256_ctx_matches_function() {
        let from_fn = blob_sha256("hello");
        let from_ctx = GitSha256.tag("hello");
        assert_eq!(from_ctx.as_bytes().as_slice(), from_fn.as_bytes());
    }

    #[test]
    fn git_sha256_ctx_matches_blob_git256() {
        assert_eq!(GitSha256.tag("hello"), O256::blob_git256("hello"));
    }

    #[test]
    fn git_enum_dispatches() {
        assert_eq!(Git::Sha1.tag("hello"), GitSha1.tag("hello"));
        assert_eq!(Git::Sha256.tag("hello"), GitSha256.tag("hello"));
    }

    // --- HashDir (git tree) tests ---

    #[test]
    fn git_sha1_manual_format() {
        let hash = O256::blob("content");
        let entries = [DirEntry {
            name: "file.txt",
            mode: DirMode::Blob,
            hash,
        }];

        let mut expected_buf = Vec::new();
        expected_buf.extend_from_slice(b"100644 file.txt\0");
        expected_buf.extend_from_slice(&hash.as_bytes()[..20]);

        let oid = tree_sha1(&expected_buf);
        let mut expected = [0u8; 32];
        expected[..oid.as_bytes().len()].copy_from_slice(oid.as_bytes());

        assert_eq!(GitSha1.hash_dir(&entries), O256::from_bytes(expected));
    }

    #[test]
    fn git_sha256_manual_format() {
        let hash = O256::blob("content");
        let entries = [DirEntry {
            name: "file.txt",
            mode: DirMode::Blob,
            hash,
        }];

        let mut expected_buf = Vec::new();
        expected_buf.extend_from_slice(b"100644 file.txt\0");
        expected_buf.extend_from_slice(hash.as_bytes());

        let oid = tree_sha256(&expected_buf);
        let mut expected = [0u8; 32];
        expected.copy_from_slice(oid.as_bytes());

        assert_eq!(GitSha256.hash_dir(&entries), O256::from_bytes(expected));
    }

    #[test]
    fn git_dir_mode_format() {
        let hash = O256::blob("sub");
        let entries = [DirEntry {
            name: "subdir",
            mode: DirMode::Dir,
            hash,
        }];

        let mut expected_buf = Vec::new();
        expected_buf.extend_from_slice(b"40000 subdir\0");
        expected_buf.extend_from_slice(&hash.as_bytes()[..20]);

        let oid = tree_sha1(&expected_buf);
        let mut expected = [0u8; 32];
        expected[..oid.as_bytes().len()].copy_from_slice(oid.as_bytes());

        assert_eq!(GitSha1.hash_dir(&entries), O256::from_bytes(expected));
    }

    #[test]
    fn git_enum_dispatch() {
        let entries = [DirEntry {
            name: "test",
            mode: DirMode::Blob,
            hash: O256::blob("data"),
        }];
        assert_eq!(Git::Sha1.hash_dir(&entries), GitSha1.hash_dir(&entries));
        assert_eq!(Git::Sha256.hash_dir(&entries), GitSha256.hash_dir(&entries));
    }

    #[test]
    fn convenience_method_git256() {
        let entries = [DirEntry {
            name: "test",
            mode: DirMode::Blob,
            hash: O256::blob("data"),
        }];
        assert_eq!(O256::dir_git256(&entries), GitSha256.hash_dir(&entries));
    }
}
