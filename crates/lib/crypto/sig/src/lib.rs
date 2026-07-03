//! Wrapper crate for Ed25519 digital signatures.
//!
//! All signature and PKI imports should go through this crate.
//! Currently wraps `ed25519-dalek` for EdDSA key generation, signing,
//! and verification.

pub use ed25519_dalek::{
    self, KEYPAIR_LENGTH, PUBLIC_KEY_LENGTH, SECRET_KEY_LENGTH, SIGNATURE_LENGTH, Signature,
    SignatureError, SigningKey, VerifyingKey,
};

pub use ed25519_dalek::{Signer, Verifier};

/// Re-export of `rand_core` at the version compatible with `ed25519-dalek`.
/// Use this for key generation (e.g. `OsRng`, `CryptoRngCore`) to avoid
/// version mismatches with the latest `rand`/`rand_core`.
///
/// This is a deliberate exception to the `covalence-rand` wrapper rule —
/// `ed25519-dalek` 2.x requires `rand_core` 0.6, which is incompatible
/// with the latest `rand` 0.10.
pub use rand_core as dalek_rand_core;
