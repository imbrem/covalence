use std::fmt;
use std::hash;

/// A 256-bit value — either a content-addressed hash or a random identifier.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct O256([u8; 32]);

impl hash::Hash for O256 {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write(&self.0);
    }
}

impl Default for O256 {
    fn default() -> Self {
        Self([0u8; 32])
    }
}

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
    #[cfg(feature = "git")]
    pub fn blob_git256(data: &[u8]) -> Self {
        let oid = crate::git_blob_sha256(data);
        let mut buf = [0u8; 32];
        buf.copy_from_slice(oid.as_bytes());
        Self(buf)
    }

    /// Create an O256 from a random 256-bit value.
    pub fn random(rng: &mut impl rand::Rng) -> Self {
        Self(rng.random())
    }

    /// Create an O256 from a raw 32-byte array.
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Parse an O256 from a 64-character hex string.
    pub fn from_hex(hex: &str) -> Option<Self> {
        if hex.len() != 64 {
            return None;
        }
        let mut bytes = [0u8; 32];
        for i in 0..32 {
            bytes[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
        }
        Some(Self(bytes))
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
