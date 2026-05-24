use std::fmt;
use std::hash;

use covalence_rand::RngExt;

/// A hashing context that tags data to produce [`O256`] values.
///
/// Each implementor defines an independent hash function. BLAKE3's three
/// modes — plain hash (`()`), keyed hash ([`O256`]), and key derivation
/// ([`Blake3Ctx`]) — use different internal domains and are guaranteed to
/// produce disjoint outputs, even for identical inputs with null keys or
/// empty context strings.
///
/// ```
/// use covalence_hash::{HashCtx, O256, Blake3Ctx, Sha256};
///
/// // () is the null context — plain BLAKE3:
/// assert_eq!(().tag("hello"), O256::blob("hello"));
///
/// // O256 uses itself as a BLAKE3 keyed-hash key:
/// let key = O256::blob("hello");
/// assert_eq!(key.tag("world"), HashCtx::tag(&key, "world"));
///
/// // Blake3Ctx uses BLAKE3 key-derivation mode:
/// let ctx = Blake3Ctx::new("my-app v1");
/// let derived = ctx.tag(b"some data");
///
/// // Sha256 does plain SHA-256:
/// assert_eq!(Sha256.tag("hello"), O256::blob_sha256("hello"));
///
/// // All three BLAKE3 modes are domain-separated, even on the same input:
/// let blob  = O256::blob("hello");
/// let keyed = blob.tag("hello");         // key = blake3("hello")
/// let derived = ctx.tag("hello");
/// assert_ne!(blob, keyed);
/// assert_ne!(blob, derived);
/// assert_ne!(keyed, derived);
/// ```
pub trait HashCtx {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256;
}

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

impl HashCtx for () {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        O256::from_bytes(*blake3::hash(data.as_ref()).as_bytes())
    }
}

impl HashCtx for O256 {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        Self::from_bytes(*blake3::keyed_hash(&self.0, data.as_ref()).as_bytes())
    }
}

/// A context string that defines a BLAKE3 key-derivation hashing scheme.
///
/// Different context strings produce independent hash functions, providing
/// domain separation. Equivalent to `b3sum --derive-key "context"`.
///
/// ```
/// use covalence_hash::{Blake3Ctx, HashCtx, O256};
///
/// // Matches `echo -n "hello" | b3sum --derive-key "covalence test"`
/// let ctx = Blake3Ctx::new("covalence test");
/// assert_eq!(
///     ctx.tag("hello").to_string(),
///     "dbebf5103aedc920c405537138558c171a6ae79ec591b5875029e2186951ea35",
/// );
///
/// // Same result via the O256 convenience method:
/// assert_eq!(ctx.tag("hello"), O256::context("covalence test", "hello"));
/// ```
pub struct Blake3Ctx([u8; 32]);

impl Blake3Ctx {
    /// Create a new hashing context from a context string.
    pub fn new(ctx: &str) -> Self {
        Self(blake3::hazmat::hash_derive_key_context(ctx))
    }

    /// Create a hashing context from a pre-computed context key.
    pub const fn from_context_key(key: [u8; 32]) -> Self {
        Self(key)
    }
}

impl HashCtx for Blake3Ctx {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        use blake3::hazmat::HasherExt;
        let mut hasher = blake3::Hasher::new_from_context_key(&self.0);
        hasher.update(data.as_ref());
        O256::from_bytes(*hasher.finalize().as_bytes())
    }
}

/// SHA-256 hashing context.
pub struct Sha256;

impl HashCtx for Sha256 {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        use sha2::Digest;
        O256::from_bytes(sha2::Sha256::digest(data.as_ref()).into())
    }
}

/// The root Covalence hashing context.
///
/// All Covalence content hashes are derived under this context, ensuring
/// domain separation from any other BLAKE3 usage.
///
/// ```
/// use covalence_hash::{HashCtx, COV_ROOT};
///
/// let h = COV_ROOT.tag("hello");
/// assert_eq!(
///     h.to_string(),
///     covalence_hash::Blake3Ctx::new("covalence development").tag("hello").to_string(),
/// );
/// ```
pub struct CovRoot(Blake3Ctx);

impl CovRoot {
    /// Pre-computed context key for "covalence development".
    const CONTEXT_KEY: [u8; 32] = [
        0x5e, 0x04, 0xe0, 0xd7, 0x3f, 0x7a, 0x7e, 0x63, 0xa2, 0x0d, 0xf4, 0x15, 0xf8, 0x15, 0x24,
        0x48, 0x0a, 0xd9, 0xcd, 0xc8, 0x0d, 0x0c, 0x7c, 0x94, 0xc4, 0x33, 0xc1, 0x96, 0x6d, 0xa7,
        0xc9, 0x14,
    ];

    pub const fn new() -> Self {
        Self(Blake3Ctx::from_context_key(Self::CONTEXT_KEY))
    }
}

impl HashCtx for CovRoot {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        self.0.tag(data)
    }
}

/// The global Covalence root hashing context.
pub const COV_ROOT: CovRoot = CovRoot::new();

impl O256 {
    /// Create an O256 from the BLAKE3 hash of the given bytes.
    pub fn blob(data: impl AsRef<[u8]>) -> Self {
        ().tag(data)
    }

    /// BLAKE3 keyed hash: hash `data` with `self` as the 32-byte key.
    pub fn tag(&self, data: impl AsRef<[u8]>) -> Self {
        <Self as HashCtx>::tag(self, data)
    }

    /// BLAKE3 key derivation via Blake3Ctx.
    pub fn context(ctx: &str, data: impl AsRef<[u8]>) -> Self {
        Blake3Ctx::new(ctx).tag(data)
    }

    /// Create an O256 from the SHA-256 hash of the given bytes.
    pub fn blob_sha256(data: impl AsRef<[u8]>) -> Self {
        Sha256.tag(data)
    }

    /// Create an O256 from a git blob SHA-256 (header + content).
    #[cfg(feature = "git")]
    pub fn blob_git256(data: impl AsRef<[u8]>) -> Self {
        crate::git::GitSha256.tag(data)
    }

    /// Hash a sorted, unique directory listing using BLAKE3 keyed mode.
    pub fn dir(entries: &[crate::DirEntry<'_>]) -> Self {
        use crate::HashDir;
        ().hash_dir(entries)
    }

    /// Hash a sorted, unique directory listing using git SHA-256 tree format.
    #[cfg(feature = "git")]
    pub fn dir_git256(entries: &[crate::DirEntry<'_>]) -> Self {
        use crate::HashDir;
        crate::git::GitSha256.hash_dir(entries)
    }

    /// Create an O256 from a random 256-bit value.
    pub fn random(rng: &mut impl covalence_rand::Rng) -> Self {
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

#[cfg(test)]
mod tests {
    use super::*;

    // Reference: echo -n "hello" | b3sum
    const BLAKE3_HELLO: &str = "ea8f163db38682925e4491c5e58d4bb3506ef8c14eb78a86e908c5624a67200f";

    // Reference: echo -n "hello" | sha256sum
    const SHA256_HELLO: &str = "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824";

    // Reference: echo -n "world" | b3sum --keyed < <(echo -n "hello" | b3sum --raw)
    const KEYED_HELLO_WORLD: &str =
        "3cc37778d40bea3cc1de2563ec424204b0916e2d5b870d7e61f4dcb5830fa69f";

    // Reference: echo -n "hello" | b3sum --derive-key "covalence test"
    const DERIVE_COV_HELLO: &str =
        "dbebf5103aedc920c405537138558c171a6ae79ec591b5875029e2186951ea35";

    #[test]
    fn blob_matches_b3sum() {
        assert_eq!(O256::blob("hello").to_string(), BLAKE3_HELLO);
    }

    #[test]
    fn unit_ctx_is_blake3() {
        assert_eq!(().tag("hello"), O256::blob("hello"));
    }

    #[test]
    fn sha256_matches_sha256sum() {
        assert_eq!(O256::blob_sha256("hello").to_string(), SHA256_HELLO);
    }

    #[test]
    fn sha256_ctx_matches_convenience() {
        assert_eq!(Sha256.tag("hello"), O256::blob_sha256("hello"));
    }

    #[test]
    fn keyed_hash_matches_b3sum_keyed() {
        let key = O256::blob("hello");
        assert_eq!(key.tag("world").to_string(), KEYED_HELLO_WORLD);
    }

    #[test]
    fn derive_key_matches_b3sum_derive() {
        let ctx = Blake3Ctx::new("covalence test");
        assert_eq!(ctx.tag("hello").to_string(), DERIVE_COV_HELLO);
    }

    #[test]
    fn context_convenience_matches_blake3ctx() {
        let ctx = Blake3Ctx::new("covalence test");
        assert_eq!(ctx.tag("hello"), O256::context("covalence test", "hello"));
    }

    #[test]
    fn asref_accepts_str_and_bytes() {
        assert_eq!(O256::blob("hello"), O256::blob(b"hello" as &[u8]));
        assert_eq!(Sha256.tag("hello"), Sha256.tag(b"hello" as &[u8]));
    }

    // Domain separation: BLAKE3's three modes (hash, keyed hash, derive key)
    // use different internal IVs, so they never collide — even when the key
    // is the hash of the data, or the context/key is empty.

    #[test]
    fn keyed_hash_disjoint_from_blob() {
        // Use the hash of the input as the key — still distinct from plain hash.
        let h = O256::blob("hello");
        assert_ne!(h, h.tag("hello"));
    }

    #[test]
    fn derive_key_disjoint_from_blob() {
        assert_ne!(O256::blob("hello"), Blake3Ctx::new("hello").tag("hello"));
    }

    #[test]
    fn derive_key_disjoint_from_keyed_hash() {
        let h = O256::blob("hello");
        assert_ne!(h.tag("hello"), Blake3Ctx::new("hello").tag("hello"));
    }

    #[test]
    fn modes_disjoint_at_null_key_and_empty_context() {
        // Even with a zero key and an empty context string, all three modes
        // produce different results for the same data.
        let data = b"test";
        let blob = O256::blob(data);
        let keyed = O256::default().tag(data); // all-zero key
        let derived = Blake3Ctx::new("").tag(data); // empty context
        assert_ne!(blob, keyed);
        assert_ne!(blob, derived);
        assert_ne!(keyed, derived);
    }

    #[test]
    fn cov_root_context_key_matches_runtime() {
        // Verify the pre-computed const key matches what blake3 computes at runtime.
        let runtime = Blake3Ctx::new("covalence development");
        assert_eq!(COV_ROOT.tag("hello"), runtime.tag("hello"));
    }

    #[test]
    fn cov_root_is_const() {
        // COV_ROOT is usable in const position.
        const _: CovRoot = COV_ROOT;
    }
}
