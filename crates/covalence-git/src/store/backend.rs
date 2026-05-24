//! Core types and trait for git object backends.

use std::fmt;
use std::str::FromStr;

use covalence_hash::gix_hash;
use covalence_store::StoreError;

/// The type of a git object.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GitObjectKind {
    Blob,
    Tree,
    Commit,
    Tag,
}

impl GitObjectKind {
    /// The type string used in git object headers.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Blob => "blob",
            Self::Tree => "tree",
            Self::Commit => "commit",
            Self::Tag => "tag",
        }
    }
}

impl fmt::Display for GitObjectKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for GitObjectKind {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, ()> {
        match s {
            "blob" => Ok(Self::Blob),
            "tree" => Ok(Self::Tree),
            "commit" => Ok(Self::Commit),
            "tag" => Ok(Self::Tag),
            _ => Err(()),
        }
    }
}

/// A git object: type tag plus raw data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GitObject {
    pub kind: GitObjectKind,
    pub data: Vec<u8>,
}

/// Trait abstracting a git object database.
///
/// Implementations may read and write loose objects on disk, access pack files,
/// shell out to `git cat-file` / `git hash-object`, or delegate to a library
/// such as `gix`.
pub trait GitBackend: Send + Sync {
    /// Read an object by its hash.
    fn read_object(&self, id: &gix_hash::ObjectId) -> Result<GitObject, StoreError>;

    /// Write an object and return its content-addressed hash.
    fn write_object(
        &self,
        kind: GitObjectKind,
        data: &[u8],
    ) -> Result<gix_hash::ObjectId, StoreError>;

    /// Check whether an object exists in the store.
    fn contains_object(&self, id: &gix_hash::ObjectId) -> bool;

    /// The hash algorithm used by this backend.
    fn hash_kind(&self) -> gix_hash::Kind;
}
