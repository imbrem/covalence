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
pub struct O256(pub(crate) [u8; 32]);

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

/// One-shot raw SHA-256 of `data`, returning the 32-byte digest.
///
/// Equivalent to `Sha256.tag(data).as_bytes()`, but exposes the raw
/// fixed-width array used for differential testing of WASM SHA-256
/// reference components.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    use sha2::Digest;
    sha2::Sha256::digest(data).into()
}

/// One-shot raw SHA-512 of `data`, returning the 64-byte digest.
///
/// SHA-512 has a 512-bit (64-byte) output, which does not fit in the
/// 32-byte [`O256`], so this is exposed as a free function only — there
/// is no `Sha512Ctx: HashCtx` impl.
#[cfg(feature = "sha512")]
pub fn sha512(data: &[u8]) -> [u8; 64] {
    use sha2::Digest;
    sha2::Sha512::digest(data).into()
}

/// One-shot BLAKE3 keyed hash of `data` with a 32-byte `key`,
/// returning the 32-byte digest.
///
/// This is the raw-bytes mirror of `O256::tag` / `HashCtx::tag` on
/// `O256`, exposed for differential testing where callers want
/// `[u8; 32]` rather than [`O256`].
pub fn blake3_keyed_hash(key: &[u8; 32], data: &[u8]) -> [u8; 32] {
    *blake3::keyed_hash(key, data).as_bytes()
}

/// One-shot BLAKE3 key derivation: derive a 32-byte subkey from
/// `key_material` under the application-specific UTF-8 context string
/// `ctx`.
///
/// This is the raw-bytes mirror of [`Blake3Ctx::new(ctx).tag(key_material)`],
/// exposed for differential testing where callers want `[u8; 32]` rather
/// than [`O256`].
pub fn blake3_derive_key(ctx: &str, key_material: &[u8]) -> [u8; 32] {
    blake3::derive_key(ctx, key_material)
}

/// Raw SHA-1 hashing context (FIPS PUB 180-4 §6.1) — 20-byte output.
///
/// This is the bare SHA-1 primitive, NOT git-flavoured blob-framed SHA-1
/// (which is `git::GitSha1`). It is used by `covalence-wasm-spec` to
/// differentially test WASM SHA-1 components against a trusted Rust impl.
///
/// We use the `sha1` crate directly (rather than `gix-hash`'s
/// collision-detected `sha1_checked`) because the collision detection
/// changes the digest on prepared collision attacks — the spec WASM
/// implements plain SHA-1, so the reference must match plain SHA-1 too.
#[cfg(feature = "sha1")]
pub struct Sha1Ctx;

#[cfg(feature = "sha1")]
impl HashCtx for Sha1Ctx {
    fn tag(&self, data: impl AsRef<[u8]>) -> O256 {
        let digest = sha1(data.as_ref());
        let mut buf = [0u8; 32];
        buf[..20].copy_from_slice(&digest);
        O256::from_bytes(buf)
    }
}

/// One-shot raw SHA-1 of `data`, returning the 20-byte digest.
#[cfg(feature = "sha1")]
pub fn sha1(data: &[u8]) -> [u8; 20] {
    use sha1::Digest;
    sha1::Sha1::digest(data).into()
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

    /// Create an O256 from a random 256-bit value.
    pub fn random(rng: &mut impl covalence_rand::Rng) -> Self {
        Self(rng.random())
    }

    /// Create an O256 from a raw 32-byte array.
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
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

    #[test]
    fn sha256_free_fn_matches_sha256sum() {
        // Reference: echo -n "abc" | sha256sum
        const SHA256_ABC: &str =
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
        let digest = sha256(b"abc");
        let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, SHA256_ABC);
    }

    #[test]
    fn sha256_free_fn_matches_ctx() {
        // The free function and the Sha256 HashCtx tag must agree on the
        // first 32 bytes.
        let raw = sha256(b"hello");
        assert_eq!(&raw[..], Sha256.tag(b"hello").as_bytes());
    }

    #[cfg(feature = "sha512")]
    #[test]
    fn sha512_empty_matches_sha512sum() {
        // Reference: printf '' | sha512sum
        const SHA512_EMPTY: &str = "\
            cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce\
            47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e";
        let digest = sha512(b"");
        let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, SHA512_EMPTY);
    }

    #[cfg(feature = "sha512")]
    #[test]
    fn sha512_abc_matches_sha512sum() {
        // Reference: echo -n "abc" | sha512sum
        const SHA512_ABC: &str = "\
            ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
            2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f";
        let digest = sha512(b"abc");
        let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, SHA512_ABC);
    }

    #[test]
    fn blake3_keyed_hash_free_fn_matches_ctx() {
        // Mirror of `keyed_hash_matches_b3sum_keyed` using the free fn.
        let key = O256::blob("hello");
        let raw = blake3_keyed_hash(key.as_bytes(), b"world");
        assert_eq!(&raw, key.tag("world").as_bytes());
        // And matches the published reference.
        let hex: String = raw.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, KEYED_HELLO_WORLD);
    }

    #[test]
    fn blake3_derive_key_free_fn_matches_ctx() {
        // Mirror of `derive_key_matches_b3sum_derive` using the free fn.
        let raw = blake3_derive_key("covalence test", b"hello");
        let hex: String = raw.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, DERIVE_COV_HELLO);
        // And matches the Blake3Ctx tag.
        let ctx = Blake3Ctx::new("covalence test");
        assert_eq!(&raw, ctx.tag("hello").as_bytes());
    }

    // BLAKE3 official test-vector context string. Pins the derive-key
    // mode against the canonical BLAKE3 test vectors so downstream
    // crates can rely on a matching context when consuming
    // `BLAKE3-team/BLAKE3/test_vectors/test_vectors.json`.
    #[test]
    fn blake3_derive_key_matches_official_test_vectors() {
        const TV_CTX: &str = "BLAKE3 2019-12-27 16:29:52 test vectors context";
        // derive_0: empty key_material.
        let derived = blake3_derive_key(TV_CTX, b"");
        let hex: String = derived.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex, "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d",
            "BLAKE3 official derive-key vector with empty input failed",
        );
    }

    // Reference: printf '' | sha1sum
    #[cfg(feature = "sha1")]
    const SHA1_EMPTY: &str = "da39a3ee5e6b4b0d3255bfef95601890afd80709";

    // Reference: echo -n "abc" | sha1sum
    #[cfg(feature = "sha1")]
    const SHA1_ABC: &str = "a9993e364706816aba3e25717850c26c9cd0d89d";

    #[cfg(feature = "sha1")]
    #[test]
    fn sha1_empty_matches_fips() {
        let digest = sha1(b"");
        let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, SHA1_EMPTY);
    }

    #[cfg(feature = "sha1")]
    #[test]
    fn sha1_abc_matches_fips() {
        let digest = sha1(b"abc");
        let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, SHA1_ABC);
    }

    #[cfg(feature = "sha1")]
    #[test]
    fn sha1_ctx_matches_raw() {
        let raw = sha1(b"hello");
        let ctx = Sha1Ctx.tag(b"hello");
        assert_eq!(&ctx.as_bytes()[..20], &raw[..]);
        // Trailing 12 bytes are zero-padded.
        assert_eq!(&ctx.as_bytes()[20..], &[0u8; 12]);
    }
}

#[cfg(all(test, feature = "sha1"))]
mod sha1_extra_tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        let mut s = String::with_capacity(bytes.len() * 2);
        for b in bytes {
            s.push_str(&format!("{b:02x}"));
        }
        s
    }

    // FIPS 180-4 §A.2 — two-block vector (56 bytes, crosses the boundary).
    #[test]
    fn fips_two_block() {
        let m = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        assert_eq!(hex(&sha1(m)), "84983e441c3bd26ebaae4aa1f95129e5e54670f1");
    }

    // FIPS 180-4 §A.3 — long-message vector (1,000,000 'a's).
    #[test]
    fn fips_million_a() {
        let m = vec![b'a'; 1_000_000];
        assert_eq!(hex(&sha1(&m)), "34aa973cd4c4daa4f61eeb2bdbad27316534016f");
    }

    // Block-boundary lengths — common implementation bug sites for SHA-1 padding.
    // SHA-1's 512-bit block + 64-bit length field means L mod 64 ∈ {55, 56, 63, 0}
    // hit distinct padding paths. Just confirms the surface is stable across lengths.
    #[test]
    fn stable_across_block_boundaries() {
        for &len in &[0usize, 1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129] {
            let m = vec![0xa5u8; len];
            assert_eq!(sha1(&m).len(), 20, "len={len}");
            assert_eq!(Sha1Ctx.tag(&m).as_bytes()[..20], sha1(&m)[..]);
        }
    }

    // Pin domain separation against the other hashes in this crate, so an
    // accidental swap in downstream code shows up here.
    #[test]
    fn disjoint_from_sha256_and_blake3() {
        let m = b"hello";
        assert_ne!(&Sha1Ctx.tag(m).as_bytes()[..20], &Sha256.tag(m).as_bytes()[..20]);
        assert_ne!(&Sha1Ctx.tag(m).as_bytes()[..20], &().tag(m).as_bytes()[..20]);
    }
}
