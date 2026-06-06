pub mod names;
mod object;
mod util;

pub use names::{SAT, UNSAT};
pub use object::{
    Blake3Ctx, COV_ROOT, CovRoot, HashCtx, O256, Sha256, blake3_derive_key, blake3_keyed_hash,
    sha256,
};
#[cfg(feature = "sha1")]
pub use object::{Sha1Ctx, sha1};
#[cfg(feature = "sha512")]
pub use object::sha512;
pub use util::{IdentityBuildHasher, IdentityHasher};

pub use blake3;
pub use sha2;

#[cfg(feature = "git")]
pub use gix_hash;

#[cfg(feature = "git")]
pub mod git;

/// Expensive: compute the BLAKE3 content hash of some bytes.
///
/// Blanket-implemented for anything that implements `AsRef<[u8]>`, so it works
/// on `&[u8]`, `Vec<u8>`, `String`, `&str`, `bytes::Bytes`, etc.
///
/// ```
/// use covalence_hash::{ContentHash, O256};
///
/// let id = "hello world".to_id();
/// assert_eq!(id, O256::blob("hello world"));
/// assert_eq!(b"hello world".to_id(), "hello world".to_id());
/// assert_eq!(vec![1u8, 2, 3].to_id(), [1u8, 2, 3].as_slice().to_id());
/// ```
pub trait ContentHash {
    fn to_id(&self) -> O256;
}

impl<T: AsRef<[u8]>> ContentHash for T {
    fn to_id(&self) -> O256 {
        O256::blob(self.as_ref())
    }
}

/// Cheap: return a previously computed [`O256`] content identifier.
///
/// Implement this on types that already know their hash (e.g. blob handles,
/// store entries, the `O256` type itself).
///
/// ```
/// use covalence_hash::{ContentId, O256};
///
/// let h = O256::blob("hello");
/// assert_eq!(h.id(), h);
/// ```
pub trait ContentId {
    fn id(&self) -> O256;
}

impl ContentId for O256 {
    fn id(&self) -> O256 {
        *self
    }
}

#[cfg(test)]
mod trait_tests {
    use super::*;

    #[test]
    fn to_id_str() {
        assert_eq!("hello".to_id(), O256::blob("hello"));
    }

    #[test]
    fn to_id_string() {
        assert_eq!(String::from("hello").to_id(), O256::blob("hello"));
    }

    #[test]
    fn to_id_bytes() {
        assert_eq!(b"hello".to_id(), O256::blob("hello"));
    }

    #[test]
    fn to_id_vec() {
        assert_eq!(vec![1u8, 2, 3].to_id(), O256::blob(&[1, 2, 3]));
    }

    #[test]
    fn to_id_slice() {
        let data: &[u8] = &[1, 2, 3];
        assert_eq!(data.to_id(), O256::blob(&[1, 2, 3]));
    }

    #[test]
    fn to_id_consistent() {
        // Same content, different types → same hash.
        let s = "hello world";
        assert_eq!(s.to_id(), s.as_bytes().to_id());
        assert_eq!(s.to_id(), s.to_owned().to_id());
        assert_eq!(s.to_id(), Vec::from(s.as_bytes()).to_id());
    }

    #[test]
    fn content_id_o256_identity() {
        let h = O256::blob("test");
        assert_eq!(h.id(), h);
    }

    #[test]
    fn to_id_empty() {
        // Empty data still produces a valid (non-zero) hash.
        let h = "".to_id();
        assert_ne!(h, O256::default());
        assert_eq!(h, b"".to_id());
    }
}
