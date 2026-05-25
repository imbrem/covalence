use std::path::PathBuf;

use pyo3::exceptions::{PyRuntimeError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyList};

use covalence_hash::gix_hash;
use covalence_store::{ContentStore, Object, ObjectKind, ObjectStore};

use crate::hash::O256;

/// Parse a Python kind string into an ObjectKind.
fn parse_object_kind(kind: &str) -> PyResult<ObjectKind> {
    match kind {
        "blob" => Ok(ObjectKind::Blob),
        "tree" => Ok(ObjectKind::Tree),
        "commit" => Ok(ObjectKind::Commit),
        "tag" => Ok(ObjectKind::Tag),
        _ => Err(PyValueError::new_err(format!(
            "unknown object kind {kind:?}, expected \"blob\", \"tree\", \"commit\", or \"tag\""
        ))),
    }
}

/// Convert an ObjectKind to its string name.
fn object_kind_str(kind: ObjectKind) -> &'static str {
    match kind {
        ObjectKind::Blob => "blob",
        ObjectKind::Tree => "tree",
        ObjectKind::Commit => "commit",
        ObjectKind::Tag => "tag",
    }
}

/// Git object hash (SHA-1 or SHA-256).
#[pyclass(frozen, from_py_object)]
#[derive(Clone)]
pub struct GitObject {
    hex: String,
    kind: &'static str,
    raw: Vec<u8>,
}

#[pymethods]
impl GitObject {
    #[getter]
    fn hex(&self) -> &str {
        &self.hex
    }

    #[getter]
    fn kind(&self) -> &str {
        self.kind
    }

    /// Convert to O256 using identity mapping (SHA-256 only).
    ///
    /// Only valid for SHA-256 git objects (32 bytes). For SHA-1, you must
    /// provide a hash mapping (e.g. via `git_tree_to_dir_rows`).
    fn to_o256(&self) -> PyResult<O256> {
        if self.raw.len() == 32 {
            let bytes: [u8; 32] = self.raw[..].try_into().unwrap();
            Ok(O256(covalence_hash::O256::from_bytes(bytes)))
        } else {
            Err(PyValueError::new_err(format!(
                "to_o256() only supports SHA-256 (32 bytes) via identity mapping; \
                 this GitObject is {} ({} bytes). Provide a hash_map for SHA-1.",
                self.kind,
                self.raw.len()
            )))
        }
    }

    fn __str__(&self) -> &str {
        &self.hex
    }

    fn __repr__(&self) -> String {
        format!("GitObject({}, {})", self.kind, self.hex)
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.raw)
    }

    fn __eq__(&self, other: &GitObject) -> bool {
        self.raw == other.raw
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.raw.hash(&mut h);
        h.finish()
    }
}

pub(crate) fn oid_to_git_object(oid: gix_hash::ObjectId) -> GitObject {
    let kind = match oid.kind() {
        gix_hash::Kind::Sha1 => "sha1",
        gix_hash::Kind::Sha256 => "sha256",
        _ => "unknown",
    };
    GitObject {
        hex: oid.to_string(),
        kind,
        raw: oid.as_bytes().to_vec(),
    }
}

/// Parse a Python object as a git ObjectId.
/// Accepts GitObject or hex string (40 for SHA-1, 64 for SHA-256).
fn parse_git_hash(obj: &Bound<'_, PyAny>) -> PyResult<gix_hash::ObjectId> {
    if let Ok(g) = obj.extract::<PyRef<GitObject>>() {
        return gix_hash::ObjectId::try_from(&g.raw[..])
            .map_err(|e| PyValueError::new_err(e.to_string()));
    }
    if let Ok(hex) = obj.extract::<String>() {
        return gix_hash::ObjectId::from_hex(hex.as_bytes())
            .map_err(|e| PyValueError::new_err(e.to_string()));
    }
    Err(PyTypeError::new_err("expected GitObject or hex string"))
}

/// Parse an algo name into a gix_hash::Kind.
fn parse_algo(algo: &str) -> PyResult<gix_hash::Kind> {
    match algo {
        "sha1" => Ok(gix_hash::Kind::Sha1),
        "sha256" => Ok(gix_hash::Kind::Sha256),
        _ => Err(PyValueError::new_err(format!(
            "unknown algo {algo:?}, expected \"sha1\" or \"sha256\""
        ))),
    }
}

fn kind_to_str(kind: gix_hash::Kind) -> &'static str {
    match kind {
        gix_hash::Kind::Sha1 => "sha1",
        gix_hash::Kind::Sha256 => "sha256",
        _ => "unknown",
    }
}

// ---------------------------------------------------------------------------
// GitStore — content-addressed git loose object store
// ---------------------------------------------------------------------------

use covalence_git::store::{GitObjectStore, LooseBackend};

/// Content-addressed git object store (loose objects).
#[pyclass]
pub struct GitStore {
    inner: GitObjectStore<LooseBackend>,
    path: PathBuf,
    algo: &'static str,
}

#[pymethods]
impl GitStore {
    /// Create a GitStore backed by a loose object directory.
    #[new]
    #[pyo3(signature = (path, algo="sha1"))]
    fn new(path: &str, algo: &str) -> PyResult<Self> {
        let kind = parse_algo(algo)?;
        let path_buf = PathBuf::from(path);
        let backend = LooseBackend::new(&path_buf, kind);
        Ok(Self {
            inner: GitObjectStore::new(backend),
            path: path_buf,
            algo: kind_to_str(kind),
        })
    }

    /// Create a GitStore from a repository root (uses .git/objects).
    #[staticmethod]
    #[pyo3(signature = (path, algo="sha1"))]
    fn from_repo(path: &str, algo: &str) -> PyResult<Self> {
        let kind = parse_algo(algo)?;
        let repo_path = PathBuf::from(path);
        let objects_path = repo_path.join(".git").join("objects");
        let backend = LooseBackend::from_repo(&repo_path, kind);
        Ok(Self {
            inner: GitObjectStore::new(backend),
            path: objects_path,
            algo: kind_to_str(kind),
        })
    }

    /// Hash and store data as a blob, returning its GitObject key.
    fn insert(&self, data: &[u8]) -> PyResult<GitObject> {
        ContentStore::insert(&self.inner, data)
            .map(oid_to_git_object)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Retrieve data by key. Returns bytes or None.
    fn get<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        let oid = parse_git_hash(key)?;
        Ok(ContentStore::get(&self.inner, &oid).map(|data| PyBytes::new(py, &data)))
    }

    /// Store data under the given key.
    fn put(&self, key: &Bound<'_, PyAny>, data: &[u8]) -> PyResult<()> {
        let oid = parse_git_hash(key)?;
        ContentStore::put(&self.inner, oid, data)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Check whether a key exists in the store.
    fn contains(&self, key: &Bound<'_, PyAny>) -> PyResult<bool> {
        let oid = parse_git_hash(key)?;
        Ok(ContentStore::contains(&self.inner, &oid))
    }

    fn __contains__(&self, key: &Bound<'_, PyAny>) -> PyResult<bool> {
        self.contains(key)
    }

    /// The hash algorithm used by this store.
    #[getter]
    fn algo(&self) -> &str {
        self.algo
    }

    fn __repr__(&self) -> String {
        format!("GitStore({}, {})", self.algo, self.path.display())
    }

    // -- Typed object store API -----------------------------------------------

    /// Insert a typed object. `kind` is one of "blob", "tree", "commit", "tag".
    fn insert_object(&self, kind: &str, data: &[u8]) -> PyResult<GitObject> {
        let obj_kind = parse_object_kind(kind)?;
        let typed_data = data.to_vec();
        let oid = match obj_kind {
            ObjectKind::Blob => {
                ObjectStore::insert(&self.inner, &covalence_store::Blob(typed_data))
            }
            ObjectKind::Tree => {
                ObjectStore::insert(&self.inner, &covalence_store::Tree(typed_data))
            }
            ObjectKind::Commit => {
                ObjectStore::insert(&self.inner, &covalence_store::Commit(typed_data))
            }
            ObjectKind::Tag => ObjectStore::insert(&self.inner, &covalence_store::Tag(typed_data)),
        };
        oid.map(oid_to_git_object)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Get a typed object. Returns `(kind, data)` tuple or None if not found.
    fn get_object<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<(String, Bound<'py, PyBytes>)>> {
        let oid = parse_git_hash(key)?;
        match self.inner.get_any(&oid) {
            Ok(Some(obj)) => {
                let kind_str = object_kind_str(obj.kind);
                Ok(Some((kind_str.to_owned(), PyBytes::new(py, &obj.data))))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(PyRuntimeError::new_err(e.to_string())),
        }
    }

    /// Get object data with type checking. Returns bytes or None.
    /// Raises TypeError if the stored object has a different kind.
    fn get_typed<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
        kind: &str,
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        let oid = parse_git_hash(key)?;
        let obj_kind = parse_object_kind(kind)?;
        let result = match obj_kind {
            ObjectKind::Blob => ObjectStore::<_, covalence_store::Blob>::get(&self.inner, &oid)
                .map(|opt| opt.map(|b| b.into_data())),
            ObjectKind::Tree => ObjectStore::<_, covalence_store::Tree>::get(&self.inner, &oid)
                .map(|opt| opt.map(|t| t.into_data())),
            ObjectKind::Commit => ObjectStore::<_, covalence_store::Commit>::get(&self.inner, &oid)
                .map(|opt| opt.map(|c| c.into_data())),
            ObjectKind::Tag => ObjectStore::<_, covalence_store::Tag>::get(&self.inner, &oid)
                .map(|opt| opt.map(|t| t.into_data())),
        };
        match result {
            Ok(Some(data)) => Ok(Some(PyBytes::new(py, &data))),
            Ok(None) => Ok(None),
            Err(covalence_store::StoreError::KindMismatch { expected, got }) => {
                Err(PyTypeError::new_err(format!(
                    "type mismatch: expected {}, got {}",
                    object_kind_str(expected),
                    object_kind_str(got),
                )))
            }
            Err(e) => Err(PyRuntimeError::new_err(e.to_string())),
        }
    }
}

// ---------------------------------------------------------------------------
// GitHasher
// ---------------------------------------------------------------------------

/// Git hashing strategy that produces GitObject values.
#[pyclass]
pub struct GitHasher {
    kind: gix_hash::Kind,
}

#[pymethods]
impl GitHasher {
    fn hash_blob(&self, data: &[u8]) -> GitObject {
        let oid = match self.kind {
            gix_hash::Kind::Sha1 => covalence_hash::git::blob_sha1(data),
            gix_hash::Kind::Sha256 => covalence_hash::git::blob_sha256(data),
            _ => unreachable!("only sha1 and sha256 are supported"),
        };
        oid_to_git_object(oid)
    }

    fn hash_blob_file(&self, path: &str) -> PyResult<GitObject> {
        let data = std::fs::read(path).map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        Ok(self.hash_blob(&data))
    }

    fn hash_tree(&self, data: &[u8]) -> GitObject {
        let oid = match self.kind {
            gix_hash::Kind::Sha1 => covalence_hash::git::tree_sha1(data),
            gix_hash::Kind::Sha256 => covalence_hash::git::tree_sha256(data),
            _ => unreachable!("only sha1 and sha256 are supported"),
        };
        oid_to_git_object(oid)
    }
}

/// Git SHA-1 blob/tree hasher.
#[pyfunction]
pub fn git_sha1() -> GitHasher {
    GitHasher {
        kind: gix_hash::Kind::Sha1,
    }
}

/// Git SHA-256 blob/tree hasher.
#[pyfunction]
pub fn git_sha256() -> GitHasher {
    GitHasher {
        kind: gix_hash::Kind::Sha256,
    }
}

/// Parse raw git tree bytes and convert to directory rows.
///
/// - `data`: raw git tree body bytes
/// - `hash_map`: `dict[bytes, O256]` mapping raw git hash bytes → O256.
///   Required for SHA-1 (`hash_len=20`). Optional for SHA-256 (`hash_len=32`),
///   where `None` means identity mapping (git SHA-256 IS the O256).
/// - `hash_len`: hash length in bytes (20 for SHA-1, 32 for SHA-256)
///
/// Returns a list of dicts with "name" (bytes), "mode" (str), "child" (O256).
/// Raises `ValueError` if a hash key is missing from `hash_map`.
#[pyfunction]
#[pyo3(signature = (data, hash_map=None, hash_len=20))]
pub fn git_tree_to_dir_rows<'py>(
    py: Python<'py>,
    data: &[u8],
    hash_map: Option<&Bound<'py, PyDict>>,
    hash_len: usize,
) -> PyResult<Bound<'py, PyList>> {
    if hash_map.is_none() && hash_len != 32 {
        return Err(PyValueError::new_err(format!(
            "hash_map is required for hash_len={hash_len} (only hash_len=32 supports identity mapping)"
        )));
    }

    let entries = covalence_object::parse_git_tree(data, hash_len)
        .map_err(|e| PyValueError::new_err(e.to_string()))?;

    let result = PyList::empty(py);
    for entry in &entries {
        let mode = covalence_object::DirMode::from_git_mode(entry.mode)
            .map_err(|e| PyValueError::new_err(e.to_string()))?;

        let child = if let Some(map) = hash_map {
            let key = PyBytes::new(py, entry.hash);
            let val = map.get_item(&key)?.ok_or_else(|| {
                let hex: String = entry.hash.iter().map(|b| format!("{b:02x}")).collect();
                PyValueError::new_err(format!("hash not found in hash_map: {hex}"))
            })?;
            val.extract::<crate::hash::O256>()?
        } else {
            // Identity mapping: hash_len=32, use git SHA-256 directly as O256.
            let bytes: [u8; 32] = entry.hash.try_into().map_err(|_| {
                PyValueError::new_err("identity mapping requires exactly 32-byte hashes")
            })?;
            crate::hash::O256(covalence_hash::O256::from_bytes(bytes))
        };

        let row_dict = PyDict::new(py);
        row_dict.set_item("name", PyBytes::new(py, entry.name))?;
        row_dict.set_item("mode", mode.name())?;
        row_dict.set_item("child", child.into_pyobject(py)?)?;
        result.append(row_dict)?;
    }
    Ok(result)
}
