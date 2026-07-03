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

/// Hash data as a git commit using SHA-1 (does not validate commit format).
pub fn commit_sha1(data: impl AsRef<[u8]>) -> gix_hash::ObjectId {
    object_hash(gix_hash::Kind::Sha1, "commit", data.as_ref())
}

/// Hash data as a git commit using SHA-256 (does not validate commit format).
pub fn commit_sha256(data: impl AsRef<[u8]>) -> gix_hash::ObjectId {
    object_hash(gix_hash::Kind::Sha256, "commit", data.as_ref())
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

    #[test]
    fn commit_sha1_matches_git() {
        // printf 'tree 4b82...\nauthor ...\ncommitter ...\n\ntest commit\n' | git hash-object -t commit --stdin
        let commit_bytes = b"tree 4b825dc642cb6eb9a060e54bf899d69f82597401\n\
            author Test User <test@example.com> 1000000000 +0000\n\
            committer Test User <test@example.com> 1000000000 +0000\n\
            \n\
            test commit\n";
        assert_eq!(
            commit_sha1(commit_bytes).to_string(),
            "e1db426cfe2e239b11128fb96eaeadba3d77af61",
        );
    }
}
