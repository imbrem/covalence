//! Synchronous variant of [`KvStore`](super::KvStore).
//!
//! For fast, trusted, in-process backends where async overhead isn't justified.
//! Shape mirrors the existing `covalence_store::KvStore` so future unification
//! is a straightforward move.

use std::sync::Arc;

/// Hierarchical synchronous key-value store with interior mutability.
///
/// Object-safe for use behind `Arc<dyn KvStore>`.
pub trait KvStore: Send + Sync {
    /// Insert or overwrite a value.
    fn set(&self, key: &str, value: &[u8]);

    /// Look up a value by key.
    fn get(&self, key: &str) -> Option<Vec<u8>>;

    /// Mark a key as touched.
    fn touch(&self, key: &str);

    /// Check whether a key has been touched.
    fn touched(&self, key: &str) -> bool;

    /// Navigate to a child namespace.
    ///
    /// Returns the same child on repeated calls with the same key (shared state).
    fn ns(&self, key: &str) -> Arc<dyn KvStore>;

    /// Duplicate this handle (same underlying data).
    fn dup(&self) -> Arc<dyn KvStore>;
}
