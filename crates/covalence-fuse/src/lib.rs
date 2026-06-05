//! FUSE mounts for covalence content stores.
//!
//! # Status: temporary scaffold
//!
//! This crate is a **v1 prototype**. It is intentionally minimal so we can
//! start using FUSE mounts for cog repos and agent/LLM workflows. The major
//! known limitation is documented loudly throughout the code:
//!
//! ## NO RANGE REQUESTS
//!
//! Every FUSE `read(off, size)` currently fetches the **entire** backing blob
//! via `ContentStore::get` and slices it. This is fine for small files (source
//! code, configs, kernel-emitted JSON) but **catastrophic** for large blobs:
//! a `cat` of a 4 GiB file will pull 4 GiB into memory per read syscall.
//!
//! The next major version of this crate will introduce an
//! `AsyncRangeContentStore` trait alongside `ContentStore`, designed so that
//! S3, git-LFS, and SQLite blob storage can all serve byte ranges natively.
//! That trait will live in `covalence-store`. Until then: **do not mount trees
//! containing large blobs**.
//!
//! ## NO ASYNC STORE EITHER
//!
//! The existing `ContentStore` trait is sync. FUSE ops here call into it from
//! tokio tasks via `spawn_blocking`. This works but blocks a worker thread per
//! in-flight op. Async-native storage is part of the same v2 follow-up as
//! range requests — both will land together because they touch the same trait
//! surface.

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
