//! FUSE mounts for covalence content stores.
//!
//! Read-only mount of a [`covalence_object::Dir`] tree backed by any
//! [`covalence_store::ContentStore<O256>`]. Each `read(off, size)` calls
//! [`ContentStore::get_slice`](covalence_store::ContentStore::get_slice) for just the requested range — backends
//! with native partial reads (sqlite `substr`) only transfer those bytes
//! from disk. Size lookups use [`ContentStore::head`](covalence_store::ContentStore::head).
//!
//! The store is sync; FUSE runs in tokio. Calls go through
//! [`tokio::task::spawn_blocking`] so a slow backend (sqlite, disk, future
//! HTTP via the layered kernel cache) doesn't stall the tokio reactor.

#![cfg_attr(not(target_os = "linux"), allow(dead_code))]

#[cfg(target_os = "linux")]
mod error;
#[cfg(target_os = "linux")]
mod inode;
#[cfg(target_os = "linux")]
mod tree_fs;

#[cfg(target_os = "linux")]
pub use error::FuseError;
#[cfg(target_os = "linux")]
pub use tree_fs::{TreeFs, TreeFsConfig, mount_tree};
