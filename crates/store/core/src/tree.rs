use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use crate::TreeStore;

/// Internal data for a [`MemoryTreeStore`] node.
struct TreeStoreData {
    values: HashMap<Vec<u8>, Vec<u8>>,
    children: HashMap<Vec<u8>, Arc<MemoryTreeStore>>,
    touched: HashSet<Vec<u8>>,
}

impl TreeStoreData {
    fn new() -> Self {
        TreeStoreData {
            values: HashMap::new(),
            children: HashMap::new(),
            touched: HashSet::new(),
        }
    }
}

/// In-memory hierarchical tree store.
///
/// Clone-friendly (shares the underlying data via `Arc<Mutex<…>>`).
/// Implements [`TreeStore`] with interior mutability.
#[derive(Clone)]
pub struct MemoryTreeStore {
    data: Arc<Mutex<TreeStoreData>>,
}

impl MemoryTreeStore {
    /// Create a new, empty in-memory tree store.
    pub fn new() -> Self {
        MemoryTreeStore {
            data: Arc::new(Mutex::new(TreeStoreData::new())),
        }
    }
}

impl Default for MemoryTreeStore {
    fn default() -> Self {
        Self::new()
    }
}

impl TreeStore for MemoryTreeStore {
    fn set(&self, key: &[u8], value: &[u8]) {
        self.data
            .lock()
            .unwrap()
            .values
            .insert(key.to_vec(), value.to_vec());
    }

    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.data.lock().unwrap().values.get(key).cloned()
    }

    fn touch(&self, key: &[u8]) {
        self.data.lock().unwrap().touched.insert(key.to_vec());
    }

    fn touched(&self, key: &[u8]) -> bool {
        self.data.lock().unwrap().touched.contains(key)
    }

    fn ns(&self, key: &[u8]) -> Arc<dyn TreeStore> {
        let mut data = self.data.lock().unwrap();

        (data
            .children
            .entry(key.to_vec())
            .or_insert_with(|| Arc::new(MemoryTreeStore::new()))
            .clone()) as _
    }

    fn dup(&self) -> Arc<dyn TreeStore> {
        Arc::new(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_get() {
        let store = MemoryTreeStore::new();
        store.set(b"key", b"value");
        assert_eq!(store.get(b"key"), Some(b"value".to_vec()));
    }

    #[test]
    fn get_missing() {
        let store = MemoryTreeStore::new();
        assert_eq!(store.get(b"nope"), None);
    }

    #[test]
    fn overwrite() {
        let store = MemoryTreeStore::new();
        store.set(b"k", b"v1");
        store.set(b"k", b"v2");
        assert_eq!(store.get(b"k"), Some(b"v2".to_vec()));
    }

    #[test]
    fn touch_touched() {
        let store = MemoryTreeStore::new();
        assert!(!store.touched(b"x"));
        store.touch(b"x");
        assert!(store.touched(b"x"));
    }

    #[test]
    fn ns_isolation() {
        let store = MemoryTreeStore::new();
        store.set(b"k", b"root");
        let child = store.ns(b"child");
        child.set(b"k", b"nested");
        assert_eq!(store.get(b"k"), Some(b"root".to_vec()));
        assert_eq!(child.get(b"k"), Some(b"nested".to_vec()));
    }

    #[test]
    fn ns_sharing() {
        let store = MemoryTreeStore::new();
        let c1 = store.ns(b"x");
        c1.set(b"a", b"1");
        let c2 = store.ns(b"x");
        assert_eq!(c2.get(b"a"), Some(b"1".to_vec()));
    }

    #[test]
    fn dup_shares_data() {
        let store = MemoryTreeStore::new();
        store.set(b"k", b"v");
        let duped = store.dup();
        assert_eq!(duped.get(b"k"), Some(b"v".to_vec()));
        duped.set(b"k2", b"v2");
        assert_eq!(store.get(b"k2"), Some(b"v2".to_vec()));
    }
}
