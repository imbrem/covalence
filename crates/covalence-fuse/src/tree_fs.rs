//! Read-only FUSE mount over a [`covalence_object::Dir`] tree.

use std::ffi::{OsStr, OsString};
use std::num::NonZeroU32;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use bytes::Bytes;
use covalence_hash::O256;
use covalence_object::{Dir, DirMode, DirRow, Table};
use covalence_store::{BlobStore, ContentStore, StoreError};
use fuse3::MountOptions;
use fuse3::raw::prelude::*;
use fuse3::raw::{Request, Session};
use fuse3::{Errno, FileType, Result as FuseResult, Timestamp};
use futures_util::stream;
use tokio::task;

use crate::error::FuseError;
use crate::inode::InodeTable;

/// One second; FUSE attr/entry TTLs.
const TTL: Duration = Duration::from_secs(1);

/// Convert a [`DirMode`] into a FUSE file type + POSIX permission bits.
fn mode_to_fuse(mode: DirMode) -> (FileType, u32) {
    match mode {
        DirMode::DIR => (FileType::Directory, 0o755),
        DirMode::REGULAR => (FileType::RegularFile, 0o644),
        DirMode::EXECUTABLE => (FileType::RegularFile, 0o755),
        DirMode::SYMLINK => (FileType::Symlink, 0o777),
        // SUBMODULE has no good local representation; show as empty dir.
        DirMode::SUBMODULE => (FileType::Directory, 0o555),
        _ => (FileType::RegularFile, 0o644),
    }
}

fn now() -> Timestamp {
    Timestamp::new(0, 0)
}

/// Configuration for [`mount_tree`].
#[derive(Clone, Debug)]
pub struct TreeFsConfig {
    pub fs_name: String,
    pub allow_other: bool,
    pub uid: u32,
    pub gid: u32,
}

impl Default for TreeFsConfig {
    fn default() -> Self {
        // SAFETY: getuid/getgid are infallible.
        let uid = unsafe { libc::getuid() };
        let gid = unsafe { libc::getgid() };
        Self {
            fs_name: String::from("covfs"),
            allow_other: false,
            uid,
            gid,
        }
    }
}

/// Read-only FUSE filesystem that resolves `(parent_dir_hash, name)` lookups
/// against a content store on demand.
///
/// Lazy resolution is the explicit design point: opening a subfolder triggers
/// `store.get(child_hash)`; if the blob is missing we reply `EIO`, leaving
/// `ls` of the parent intact. No prefetch pass walks the tree at mount time.
pub struct TreeFs {
    store: BlobStore<O256>,
    inodes: Arc<InodeTable>,
    cfg: TreeFsConfig,
}

impl TreeFs {
    pub fn new(store: BlobStore<O256>, root: O256, cfg: TreeFsConfig) -> Self {
        Self {
            inodes: Arc::new(InodeTable::new(root, DirMode::DIR)),
            store,
            cfg,
        }
    }

    /// Fetch a whole blob from the store via a blocking worker. Used for
    /// small payloads where ranging doesn't help — directory tables and
    /// symlink targets.
    async fn fetch_blob(&self, hash: O256) -> Result<Vec<u8>, FuseError> {
        let store = self.store.clone();
        let blob = task::spawn_blocking(move || store.get(&hash))
            .await
            .map_err(|e| FuseError::BadDirTable(format!("join: {e}")))?;
        blob.ok_or(FuseError::BlobMissing(hash))
    }

    /// Fetch a byte range via the sync trait's [`ContentStore::get_slice`]
    /// — backends with native partial reads (sqlite `substr`) only
    /// transfer those bytes from storage. Past-EOF reads return empty per
    /// POSIX `read(2)` semantics.
    async fn fetch_range(&self, hash: O256, start: u64, end: u64) -> Result<Bytes, FuseError> {
        let store = self.store.clone();
        let result = task::spawn_blocking(move || store.get_slice(&hash, start..end))
            .await
            .map_err(|e| FuseError::BadDirTable(format!("join: {e}")))?;
        match result {
            Ok(v) => Ok(Bytes::from(v)),
            // POSIX: read past EOF returns 0 bytes, not an error.
            Err(StoreError::RangeNotSatisfiable { .. }) => Ok(Bytes::new()),
            Err(StoreError::NotFound) => Err(FuseError::BlobMissing(hash)),
            Err(e) => Err(FuseError::BadDirTable(format!("store: {e}"))),
        }
    }

    /// Cheap size lookup via [`ContentStore::head`] — sqlite answers from
    /// the row header without reading the body.
    async fn head_blob(&self, hash: O256) -> Result<u64, FuseError> {
        let store = self.store.clone();
        let info = task::spawn_blocking(move || store.head(&hash))
            .await
            .map_err(|e| FuseError::BadDirTable(format!("join: {e}")))?;
        info.map(|i| i.size).ok_or(FuseError::BlobMissing(hash))
    }

    /// Load and parse a directory table.
    async fn load_dir(&self, hash: O256) -> Result<Table<Dir>, FuseError> {
        let blob = self.fetch_blob(hash).await?;
        Table::parse(blob, Dir).map_err(|e| FuseError::Table(e.to_string()))
    }

    /// Resolve the on-disk size of a file inode, asking the store via
    /// `head` if we don't already have it cached.
    async fn realize_size(&self, ino: u64, hash: O256) -> Result<u64, FuseError> {
        if let Some(entry) = self.inodes.get(ino) {
            if let Some(size) = entry.size {
                return Ok(size);
            }
        }
        let size = self.head_blob(hash).await?;
        self.inodes.set_size(ino, size);
        Ok(size)
    }

    async fn size_for(&self, ino: u64, mode: DirMode, hash: O256) -> Result<u64, FuseError> {
        if mode.is_dir() || mode == DirMode::SUBMODULE {
            Ok(0)
        } else {
            self.realize_size(ino, hash).await
        }
    }

    fn file_attr(&self, ino: u64, mode: DirMode, size: u64) -> FileAttr {
        let (kind, perm) = mode_to_fuse(mode);
        FileAttr {
            ino,
            size,
            blocks: size.div_ceil(512),
            atime: now(),
            mtime: now(),
            ctime: now(),
            kind,
            perm: perm as u16,
            nlink: if kind == FileType::Directory { 2 } else { 1 },
            uid: self.cfg.uid,
            gid: self.cfg.gid,
            rdev: 0,
            blksize: 4096,
        }
    }
}

impl Filesystem for TreeFs {
    type DirEntryStream<'a>
        = stream::Iter<std::vec::IntoIter<FuseResult<DirectoryEntry>>>
    where
        Self: 'a;
    type DirEntryPlusStream<'a>
        = stream::Iter<std::vec::IntoIter<FuseResult<DirectoryEntryPlus>>>
    where
        Self: 'a;

    async fn init(&self, _req: Request) -> FuseResult<ReplyInit> {
        Ok(ReplyInit {
            max_write: NonZeroU32::new(16 * 1024 * 1024).expect("16 MiB is nonzero"),
        })
    }

    async fn destroy(&self, _req: Request) {}

    async fn lookup(&self, _req: Request, parent: u64, name: &OsStr) -> FuseResult<ReplyEntry> {
        let parent_entry = self.inodes.get(parent).ok_or(Errno::from(libc::ENOENT))?;
        if !parent_entry.mode.is_dir() {
            return Err(FuseError::NotADir(parent_entry.hash).into());
        }

        let table = self.load_dir(parent_entry.hash).await?;
        let name_bytes = name.as_encoded_bytes();
        let row: Option<DirRow<&[u8]>> = table
            .get(name_bytes)
            .map_err(|e| FuseError::Table(e.to_string()))?;
        let row = row.ok_or(FuseError::NotFound)?;

        let ino = self.inodes.intern(row.child, row.mode);
        // Files need a real size so the kernel will issue `read(2)` calls;
        // directories don't, and SUBMODULE is shown as an empty dir. Anything
        // else (symlink target length, etc.) is realized on demand.
        let size = self.size_for(ino, row.mode, row.child).await?;
        let attr = self.file_attr(ino, row.mode, size);

        Ok(ReplyEntry {
            ttl: TTL,
            attr,
            generation: 0,
        })
    }

    async fn getattr(
        &self,
        _req: Request,
        inode: u64,
        _fh: Option<u64>,
        _flags: u32,
    ) -> FuseResult<ReplyAttr> {
        let entry = self.inodes.get(inode).ok_or(Errno::from(libc::ENOENT))?;
        let size = self.size_for(inode, entry.mode, entry.hash).await?;
        Ok(ReplyAttr {
            ttl: TTL,
            attr: self.file_attr(inode, entry.mode, size),
        })
    }

    async fn open(&self, _req: Request, inode: u64, _flags: u32) -> FuseResult<ReplyOpen> {
        // Stateless — fh is unused.
        let _ = self.inodes.get(inode).ok_or(Errno::from(libc::ENOENT))?;
        Ok(ReplyOpen { fh: 0, flags: 0 })
    }

    async fn read(
        &self,
        _req: Request,
        inode: u64,
        _fh: u64,
        offset: u64,
        size: u32,
    ) -> FuseResult<ReplyData> {
        let entry = self.inodes.get(inode).ok_or(Errno::from(libc::ENOENT))?;
        // One ranged fetch sized to this syscall (capped by FUSE at
        // ~16 MiB via `max_write`). `get_slice` clamps `end` to the
        // blob's actual length; past-EOF lands in `fetch_range` as empty.
        let end = offset.saturating_add(size as u64);
        let data = self.fetch_range(entry.hash, offset, end).await?;
        Ok(ReplyData { data })
    }

    async fn readdir(
        &self,
        _req: Request,
        parent: u64,
        _fh: u64,
        offset: i64,
    ) -> FuseResult<ReplyDirectory<Self::DirEntryStream<'_>>> {
        tracing::debug!("readdir ino={parent} offset={offset}");
        let parent_entry = self.inodes.get(parent).ok_or(Errno::from(libc::ENOENT))?;
        if !parent_entry.mode.is_dir() {
            return Err(FuseError::NotADir(parent_entry.hash).into());
        }
        let table = self.load_dir(parent_entry.hash).await?;

        let mut entries: Vec<FuseResult<DirectoryEntry>> = Vec::new();
        // FUSE wants `.` and `..` from us; the kernel doesn't synthesize them.
        entries.push(Ok(DirectoryEntry {
            inode: parent,
            kind: FileType::Directory,
            name: OsString::from("."),
            offset: 1,
        }));
        entries.push(Ok(DirectoryEntry {
            inode: parent, // we don't track parent ptrs; "." == ".." is harmless
            kind: FileType::Directory,
            name: OsString::from(".."),
            offset: 2,
        }));

        let n = table.num_entries();
        for i in 0..n {
            let row = table.row(i).map_err(|e| FuseError::Table(e.to_string()))?;
            let ino = self.inodes.intern(row.child, row.mode);
            let (kind, _perm) = mode_to_fuse(row.mode);
            entries.push(Ok(DirectoryEntry {
                inode: ino,
                kind,
                name: OsStr::from_bytes(row.name).to_os_string(),
                offset: (i as i64) + 3,
            }));
        }

        // Skip already-served entries.
        let skip = offset.max(0) as usize;
        let tail: Vec<_> = entries.into_iter().skip(skip).collect();
        Ok(ReplyDirectory {
            entries: stream::iter(tail),
        })
    }

    /// `readdirplus` — readdir + per-entry lookup attrs in one round trip.
    ///
    /// Modern Linux kernels enable `FUSE_DO_READDIRPLUS` in the init handshake,
    /// after which `getdents64` on a FUSE directory routes here instead of to
    /// [`Self::readdir`]. If we left the default `ENOSYS` impl in place, the
    /// kernel returns empty listings on every `ls` until it gives up and falls
    /// back, which manifests as silently-empty directories.
    async fn readdirplus(
        &self,
        _req: Request,
        parent: u64,
        _fh: u64,
        offset: u64,
        _lock_owner: u64,
    ) -> FuseResult<ReplyDirectoryPlus<Self::DirEntryPlusStream<'_>>> {
        tracing::debug!("readdirplus ino={parent} offset={offset}");
        let parent_entry = self.inodes.get(parent).ok_or(Errno::from(libc::ENOENT))?;
        if !parent_entry.mode.is_dir() {
            return Err(FuseError::NotADir(parent_entry.hash).into());
        }
        let table = self.load_dir(parent_entry.hash).await?;

        let parent_attr = self.file_attr(parent, parent_entry.mode, 0);
        let mut entries: Vec<FuseResult<DirectoryEntryPlus>> = Vec::new();
        entries.push(Ok(DirectoryEntryPlus {
            inode: parent,
            generation: 0,
            kind: FileType::Directory,
            name: OsString::from("."),
            offset: 1,
            attr: parent_attr,
            entry_ttl: TTL,
            attr_ttl: TTL,
        }));
        entries.push(Ok(DirectoryEntryPlus {
            inode: parent,
            generation: 0,
            kind: FileType::Directory,
            name: OsString::from(".."),
            offset: 2,
            attr: parent_attr,
            entry_ttl: TTL,
            attr_ttl: TTL,
        }));

        let n = table.num_entries();
        for i in 0..n {
            let row = table.row(i).map_err(|e| FuseError::Table(e.to_string()))?;
            let ino = self.inodes.intern(row.child, row.mode);
            let (kind, _perm) = mode_to_fuse(row.mode);
            let size = self.size_for(ino, row.mode, row.child).await?;
            let attr = self.file_attr(ino, row.mode, size);
            entries.push(Ok(DirectoryEntryPlus {
                inode: ino,
                generation: 0,
                kind,
                name: OsStr::from_bytes(row.name).to_os_string(),
                offset: (i as i64) + 3,
                attr,
                entry_ttl: TTL,
                attr_ttl: TTL,
            }));
        }

        let skip = offset as usize;
        let tail: Vec<_> = entries.into_iter().skip(skip).collect();
        Ok(ReplyDirectoryPlus {
            entries: stream::iter(tail),
        })
    }

    async fn readlink(&self, _req: Request, inode: u64) -> FuseResult<ReplyData> {
        let entry = self.inodes.get(inode).ok_or(Errno::from(libc::ENOENT))?;
        if entry.mode != DirMode::SYMLINK {
            return Err(libc::EINVAL.into());
        }
        let target = self.fetch_blob(entry.hash).await?;
        Ok(ReplyData {
            data: Bytes::from(target),
        })
    }

    async fn access(&self, _req: Request, inode: u64, _mask: u32) -> FuseResult<()> {
        let _ = self.inodes.get(inode).ok_or(Errno::from(libc::ENOENT))?;
        Ok(())
    }

    async fn opendir(&self, _req: Request, inode: u64, _flags: u32) -> FuseResult<ReplyOpen> {
        let entry = self.inodes.get(inode).ok_or(Errno::from(libc::ENOENT))?;
        if !entry.mode.is_dir() {
            return Err(FuseError::NotADir(entry.hash).into());
        }
        Ok(ReplyOpen { fh: 0, flags: 0 })
    }
}

/// Mount a tree object at `mountpoint` and run until the session ends.
///
/// The session ends when:
/// - The mount is externally unmounted (`fusermount -u`).
/// - The returned future is dropped (because the caller hit Ctrl-C, etc.).
pub async fn mount_tree(
    store: BlobStore<O256>,
    root: O256,
    mountpoint: &Path,
    cfg: TreeFsConfig,
) -> Result<(), std::io::Error> {
    let mut opts = MountOptions::default();
    opts.fs_name(cfg.fs_name.clone())
        .uid(cfg.uid)
        .gid(cfg.gid)
        .read_only(true)
        .allow_other(cfg.allow_other)
        .default_permissions(true);

    let fs = TreeFs::new(store, root, cfg);

    let session = Session::new(opts);
    let mount = session.mount_with_unprivileged(fs, mountpoint).await?;

    tracing::info!("mounted tree {root:?} at {}", mountpoint.display());
    mount.await?;
    Ok(())
}
