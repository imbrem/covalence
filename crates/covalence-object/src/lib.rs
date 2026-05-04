use std::fmt;

pub use gix_hash;

/// A 256-bit value — either a content-addressed hash or a random identifier.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct O256([u8; 32]);

impl O256 {
    /// Create an O256 from the BLAKE3 hash of the given bytes.
    pub fn blob(data: &[u8]) -> Self {
        Self(*blake3::hash(data).as_bytes())
    }

    /// Create an O256 from the SHA-256 hash of the given bytes.
    pub fn blob_sha256(data: &[u8]) -> Self {
        use sha2::Digest;
        Self(sha2::Sha256::digest(data).into())
    }

    /// Create an O256 from a git blob SHA-256 (header + content).
    pub fn blob_git256(data: &[u8]) -> Self {
        use gix_hash::Kind;
        let mut hasher = gix_hash::hasher(Kind::Sha256);
        let header = format!("blob {}\0", data.len());
        hasher.update(header.as_bytes());
        hasher.update(data);
        let oid = hasher.try_finalize().expect("git SHA-256 finalize");
        let mut buf = [0u8; 32];
        buf.copy_from_slice(oid.as_bytes());
        Self(buf)
    }

    /// Create an O256 from a random 256-bit value.
    pub fn random(rng: &mut impl rand::Rng) -> Self {
        Self(rng.random())
    }

    /// Return the raw 32-byte array.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl fmt::Display for O256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in &self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

impl fmt::Debug for O256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "O256({self})")
    }
}
