use std::io;
use std::path::Path;

pub use covalence_hash;
pub use covalence_hash::gix_hash;

#[cfg(feature = "object-store")]
pub use covalence_store;

#[cfg(feature = "object-store")]
pub mod store;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Hash algorithm for `hash_blob`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum HashAlgo {
    Blake3,
    GitSha1,
    GitSha256,
    Sha256,
}

impl HashAlgo {
    /// Key name used in output columns and JSON fields.
    pub fn key(self) -> &'static str {
        match self {
            HashAlgo::Blake3 => "blake3",
            HashAlgo::GitSha1 => "git_sha1",
            HashAlgo::GitSha256 => "git_sha256",
            HashAlgo::Sha256 => "sha256",
        }
    }
}

fn compute_hash(algo: HashAlgo, data: &[u8]) -> String {
    match algo {
        HashAlgo::Blake3 => covalence_hash::O256::blob(data).to_string(),
        HashAlgo::Sha256 => covalence_hash::O256::blob_sha256(data).to_string(),
        HashAlgo::GitSha256 => covalence_hash::O256::blob_git256(data).to_string(),
        HashAlgo::GitSha1 => covalence_hash::git::blob_sha1(data).to_string(),
    }
}

/// Hash each file with the requested algorithms and print results.
///
/// When `json` is true, outputs one JSON object per file (JSONL).
/// Otherwise outputs space-separated hex digests per line.
pub fn hash_blob(paths: &[impl AsRef<Path>], algos: &[HashAlgo], json: bool) -> io::Result<()> {
    for path in paths {
        let path = path.as_ref();
        let meta = std::fs::metadata(path)
            .map_err(|e| io::Error::new(e.kind(), format!("{}: {e}", path.display())))?;
        if !meta.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("{}: not a regular file", path.display()),
            ));
        }
        let data = std::fs::read(path)?;

        if json {
            let mut obj = serde_json::Map::new();
            for &algo in algos {
                obj.insert(
                    algo.key().to_string(),
                    serde_json::Value::String(compute_hash(algo, &data)),
                );
            }
            obj.insert(
                "path".to_string(),
                serde_json::Value::String(path.display().to_string()),
            );
            println!("{}", serde_json::Value::Object(obj));
        } else {
            let hashes: Vec<String> = algos.iter().map(|&a| compute_hash(a, &data)).collect();
            println!("{}", hashes.join("  "));
        }
    }
    Ok(())
}
