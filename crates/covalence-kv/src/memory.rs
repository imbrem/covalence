//! In-memory [`KvStore`] backend. Trivial; useful for tests and as a baseline.

use std::collections::HashMap;
use std::sync::Mutex;

use async_trait::async_trait;
use bytes::Bytes;

use crate::{Error, KvStore, Meta, Result};

/// In-memory async key-value store. Internal `Mutex` for interior mutability.
#[derive(Default)]
pub struct MemoryKv {
    data: Mutex<HashMap<String, Bytes>>,
}

impl MemoryKv {
    pub fn new() -> Self {
        Self::default()
    }
}

#[async_trait]
impl KvStore for MemoryKv {
    async fn get(&self, key: &str) -> Result<Bytes> {
        self.data
            .lock()
            .unwrap()
            .get(key)
            .cloned()
            .ok_or_else(|| Error::NotFound {
                key: key.to_string(),
            })
    }

    async fn put(&self, key: &str, value: Bytes) -> Result<()> {
        self.data.lock().unwrap().insert(key.to_string(), value);
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<()> {
        self.data.lock().unwrap().remove(key);
        Ok(())
    }

    async fn head(&self, key: &str) -> Result<Meta> {
        let data = self.data.lock().unwrap();
        let v = data.get(key).ok_or_else(|| Error::NotFound {
            key: key.to_string(),
        })?;
        Ok(Meta {
            size: v.len() as u64,
            modified: None,
            etag: None,
        })
    }
}
