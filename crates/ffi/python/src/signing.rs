use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use covalence_hash::O256;

/// An authenticated entity (wraps an Ed25519 public key).
#[pyclass(frozen)]
pub struct Principal {
    key: covalence_crypto_sig::VerifyingKey,
}

#[pymethods]
impl Principal {
    /// Construct from 32-byte public key.
    #[new]
    fn new(bytes: &[u8]) -> PyResult<Self> {
        let arr: [u8; 32] = bytes
            .try_into()
            .map_err(|_| PyValueError::new_err("expected exactly 32 bytes"))?;
        let key = covalence_crypto_sig::VerifyingKey::from_bytes(&arr)
            .map_err(|e| PyValueError::new_err(format!("invalid public key: {e}")))?;
        Ok(Principal { key })
    }

    /// Serialize to 32-byte public key.
    fn bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.key.to_bytes())
    }

    fn __eq__(&self, other: &Principal) -> bool {
        self.key == other.key
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.key.to_bytes().hash(&mut h);
        h.finish()
    }

    fn __repr__(&self) -> String {
        let bytes = self.key.to_bytes();
        let hex: String = bytes.iter().take(8).map(|b| format!("{b:02x}")).collect();
        format!("Principal({hex}...)")
    }
}

/// An opaque detached signature over some data.
#[pyclass]
pub struct Signature {
    sig: covalence_crypto_sig::Signature,
}

#[pymethods]
impl Signature {
    /// Verify this signature against a principal and data.
    fn verify(&self, principal: &Principal, data: &[u8]) -> bool {
        let hash = O256::blob(data);
        covalence_crypto_sig::Verifier::verify(&principal.key, hash.as_bytes(), &self.sig).is_ok()
    }

    fn __repr__(&self) -> String {
        let bytes = self.sig.to_bytes();
        let hex: String = bytes.iter().take(8).map(|b| format!("{b:02x}")).collect();
        format!("Signature({hex}...)")
    }
}

/// A signing capability (wraps an Ed25519 keypair).
#[pyclass]
pub struct Signer {
    key: covalence_crypto_sig::SigningKey,
}

#[pymethods]
impl Signer {
    /// Generate a fresh keypair.
    #[staticmethod]
    fn generate() -> Self {
        let key = covalence_crypto_sig::SigningKey::generate(
            &mut covalence_crypto_sig::dalek_rand_core::OsRng,
        );
        Signer { key }
    }

    /// Get the principal (public key) for this signer.
    fn principal(&self) -> Principal {
        Principal {
            key: self.key.verifying_key(),
        }
    }

    /// Sign data, returning an opaque Signature.
    fn sign(&self, data: &[u8]) -> Signature {
        let hash = O256::blob(data);
        let sig = covalence_crypto_sig::Signer::sign(&self.key, hash.as_bytes());
        Signature { sig }
    }

    fn __repr__(&self) -> String {
        let bytes = self.key.verifying_key().to_bytes();
        let hex: String = bytes.iter().take(8).map(|b| format!("{b:02x}")).collect();
        format!("Signer(pub={hex}...)")
    }
}
