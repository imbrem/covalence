mod object;
mod util;

pub use object::O256;
pub use util::{IdentityBuildHasher, IdentityHasher};

pub use blake3;
pub use sha2;

#[cfg(feature = "git")]
pub use gix_hash;

// ---------------------------------------------------------------------------
// Git object hashing convenience functions
// ---------------------------------------------------------------------------

#[cfg(feature = "git")]
/// Hash data as a git object with the given type prefix and hash algorithm.
fn git_object_hash(kind: gix_hash::Kind, object_type: &str, data: &[u8]) -> gix_hash::ObjectId {
    let mut hasher = gix_hash::hasher(kind);
    let header = format!("{object_type} {}\0", data.len());
    hasher.update(header.as_bytes());
    hasher.update(data);
    hasher.try_finalize().expect("git hash finalize")
}

#[cfg(feature = "git")]
/// Hash data as a git blob using SHA-1.
pub fn git_blob_sha1(data: &[u8]) -> gix_hash::ObjectId {
    git_object_hash(gix_hash::Kind::Sha1, "blob", data)
}

#[cfg(feature = "git")]
/// Hash data as a git blob using SHA-256.
pub fn git_blob_sha256(data: &[u8]) -> gix_hash::ObjectId {
    git_object_hash(gix_hash::Kind::Sha256, "blob", data)
}

#[cfg(feature = "git")]
/// Hash data as a git tree using SHA-1 (does not validate tree format).
pub fn git_tree_sha1(data: &[u8]) -> gix_hash::ObjectId {
    git_object_hash(gix_hash::Kind::Sha1, "tree", data)
}

#[cfg(feature = "git")]
/// Hash data as a git tree using SHA-256 (does not validate tree format).
pub fn git_tree_sha256(data: &[u8]) -> gix_hash::ObjectId {
    git_object_hash(gix_hash::Kind::Sha256, "tree", data)
}
