use covalence_hash::O256;
use covalence_store::StoreError;
use fuse3::Errno;

/// Errors raised while serving a FUSE request.
///
/// Each variant maps to a POSIX errno that the FUSE kernel forwards to the
/// requesting process. The mapping aims to make `ls`, `cat`, and friends
/// produce sensible messages without lying about the failure mode:
///
/// - `NotFound`  → `ENOENT` (name absent from a directory listing)
/// - `BlobMissing` → `EIO` (name *is* in the listing, but the blob can't be
///   resolved — surfaces as "Input/output error", which is honest)
/// - `NotADir` → `ENOTDIR`
/// - `BadDirTable` / `Store` → `EIO`
#[derive(Debug, thiserror::Error)]
pub enum FuseError {
    #[error("name not found in directory")]
    NotFound,

    #[error("blob missing from store: {0:?}")]
    BlobMissing(O256),

    #[error("entry is not a directory: {0:?}")]
    NotADir(O256),

    #[error("bad dir table: {0}")]
    BadDirTable(String),

    #[error("store error: {0}")]
    Store(#[from] StoreError),

    #[error("table decode error: {0}")]
    Table(String),
}

impl From<FuseError> for Errno {
    fn from(err: FuseError) -> Self {
        match err {
            FuseError::NotFound => libc::ENOENT.into(),
            FuseError::BlobMissing(_) => libc::EIO.into(),
            FuseError::NotADir(_) => libc::ENOTDIR.into(),
            FuseError::BadDirTable(_) => libc::EIO.into(),
            FuseError::Store(_) => libc::EIO.into(),
            FuseError::Table(_) => libc::EIO.into(),
        }
    }
}
