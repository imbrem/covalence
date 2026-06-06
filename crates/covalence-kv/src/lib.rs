//! Async key-value store traits and backends.
//!
//! The canonical [`KvStore`] trait is async and fallible — designed for
//! remote, untrusted, network-attached backends (S3, GCS, Azure, HTTP).
//! A synchronous variant [`sync::KvStore`] is provided for fast/trusted
//! local cases.
//!
//! Keys are slash-separated `&str`; backends sanitize at the boundary.
//! Values are `bytes::Bytes` (cheaply cloneable, slice-friendly).
//!
//! The [`aws`] module wraps `object_store`'s S3 backend with builder
//! helpers for AWS S3 and S3-compatible providers (Wasabi, Backblaze B2,
//! Cloudflare R2, MinIO, etc.) via endpoint override.

pub use bytes::Bytes;

mod error;
pub use error::Error;

mod meta;
pub use meta::Meta;

mod store;
pub use store::KvStore;

pub mod sync;

mod memory;
pub use memory::MemoryKv;

#[cfg(feature = "blocking")]
mod blocking;
#[cfg(feature = "blocking")]
pub use blocking::BlockingKv;

#[cfg(feature = "aws")]
pub mod aws;

#[cfg(feature = "aws")]
pub use object_store;

/// Result alias for kv-store operations.
pub type Result<T, E = Error> = std::result::Result<T, E>;
