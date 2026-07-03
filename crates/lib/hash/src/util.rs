use std::hash::{BuildHasherDefault, Hasher};

/// A [`Hasher`] that uses the first 8 bytes of the input directly.
///
/// Valid only for keys that are already well-distributed hashes
/// (e.g. BLAKE3 output stored in [`O256`](crate::O256)), where re-hashing
/// is pure overhead.
#[derive(Default)]
pub struct IdentityHasher(u64);

impl Hasher for IdentityHasher {
    fn write(&mut self, bytes: &[u8]) {
        if bytes.len() >= 8 {
            self.0 = u64::from_ne_bytes(bytes[..8].try_into().unwrap());
        }
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

pub type IdentityBuildHasher = BuildHasherDefault<IdentityHasher>;
