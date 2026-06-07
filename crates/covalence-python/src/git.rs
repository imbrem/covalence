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

// ---------------------------------------------------------------------------
// GitImport — sqlite-backed `cov cog clone` store, exposed for Python
// ---------------------------------------------------------------------------

use covalence_git::clone::{CloneOptions, CloneResult, CloneSource, classify_url, clone_into};
use covalence_git::store::{GitBackend, GitObjectKind, GitStore as CoreGitStore};

/// One discovered ref from a clone.
#[pyclass(frozen, skip_from_py_object)]
#[derive(Clone)]
pub struct GitRef {
    #[pyo3(get)]
    name: String,
    #[pyo3(get)]
    oid: String,
    #[pyo3(get)]
    symref_target: Option<String>,
}

#[pymethods]
impl GitRef {
    fn __repr__(&self) -> String {
        match &self.symref_target {
            Some(t) => format!("GitRef({} -> {} {})", self.name, t, self.oid),
            None => format!("GitRef({} {})", self.name, self.oid),
        }
    }
}

/// Sqlite-backed git store: holds the SHA1 → O256 map produced by cloning a
/// git repository. Wraps [`covalence_git::store::GitStore`].
#[pyclass]
pub struct GitImport {
    inner: CoreGitStore,
}

#[pymethods]
impl GitImport {
    /// Open an existing sqlite GitStore at `path`. With no `path`, creates a
    /// fresh in-memory store.
    #[staticmethod]
    #[pyo3(signature = (path=None, algo="sha1"))]
    fn open(path: Option<&str>, algo: &str) -> PyResult<Self> {
        let kind = parse_algo(algo)?;
        let inner = match path {
            Some(p) => CoreGitStore::open(p, kind)
                .map_err(|e| PyRuntimeError::new_err(format!("open: {e}")))?,
            None => CoreGitStore::memory(kind)
                .map_err(|e| PyRuntimeError::new_err(format!("memory: {e}")))?,
        };
        Ok(Self { inner })
    }

    /// Clone a git repository — HTTP(S) URL or local path — into a sqlite
    /// store at `store` (or an in-memory one if `store` is None). Returns a
    /// `GitCloneResult` exposing the freshly-populated `GitImport` plus the
    /// refs and counts the underlying clone surfaced.
    #[staticmethod]
    #[pyo3(signature = (url, store=None, branch=None, depth=None, filter=None, algo="sha1"))]
    fn clone(
        py: Python<'_>,
        url: &str,
        store: Option<&str>,
        branch: Option<&str>,
        depth: Option<u32>,
        filter: Option<&str>,
        algo: &str,
    ) -> PyResult<GitCloneResult> {
        let kind = parse_algo(algo)?;
        let core = match store {
            Some(p) => CoreGitStore::open(p, kind)
                .map_err(|e| PyRuntimeError::new_err(format!("open: {e}")))?,
            None => CoreGitStore::memory(kind)
                .map_err(|e| PyRuntimeError::new_err(format!("memory: {e}")))?,
        };
        let ref_prefixes = match branch {
            Some(b) => vec![format!("refs/heads/{b}"), "HEAD".to_string()],
            None => Vec::new(),
        };
        let opts = CloneOptions {
            url: url.to_string(),
            depth,
            filter: filter.map(|s| s.to_string()),
            ref_prefixes,
        };

        // Release the GIL while we do network/disk I/O — clones routinely
        // run for many seconds and would otherwise block any other Python
        // thread.
        let result: CloneResult = py
            .detach(|| clone_into(&opts, &core, |_| {}))
            .map_err(|e| PyRuntimeError::new_err(format!("clone: {e}")))?;

        // Build the Python `GitImport` Py<> that the result owns.
        let import = Py::new(py, GitImport { inner: core })?;

        let refs: Vec<GitRef> = result
            .refs
            .into_iter()
            .map(|r| GitRef {
                name: r.name,
                oid: r.oid.to_string(),
                symref_target: r.symref_target,
            })
            .collect();
        let cov_trees: Vec<(String, O256)> = result
            .cov_trees
            .into_iter()
            .map(|(oid, h)| (oid.to_string(), O256(h)))
            .collect();
        Ok(GitCloneResult {
            store: import,
            objects_stored: result.objects_stored,
            refs,
            cov_trees,
            url: url.to_string(),
        })
    }

    /// Classify a URL into "http" or "local" — useful when callers want to
    /// branch on the transport before calling `clone`.
    #[staticmethod]
    fn classify(url: &str) -> &'static str {
        match classify_url(url) {
            CloneSource::Http(_) => "http",
            CloneSource::Local(_) => "local",
        }
    }

    /// Count of registered git objects (full + shallow).
    #[getter]
    fn count(&self) -> usize {
        self.inner.len()
    }

    /// Count of registered covalence trees (from `convert_trees`).
    #[getter]
    fn cov_tree_count(&self) -> usize {
        self.inner.cov_tree_hashes().len()
    }

    /// Look up a SHA-1/256 OID (hex or [`GitObject`]); return the O256 the
    /// git blob payload hashes to.
    fn resolve(&self, oid: &Bound<'_, PyAny>) -> PyResult<O256> {
        let parsed = parse_git_hash(oid)?;
        let obj = self
            .inner
            .read_object(&parsed)
            .map_err(|e| PyValueError::new_err(format!("not resolvable: {e}")))?;
        Ok(O256(covalence_hash::O256::blob(&obj.data)))
    }

    /// Reverse lookup: given an O256, find the git OID whose blob hashes to
    /// it (lexicographically smallest, deterministic). Returns `None` if no
    /// such mapping is registered.
    fn reverse(&self, target: O256) -> PyResult<Option<GitObject>> {
        let found = self
            .inner
            .git_oid_for_blob_hash(&target.0)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        Ok(found.map(oid_to_git_object))
    }

    /// Write `data` as a git blob into the store; return the git OID. The
    /// O256 → git-OID mapping is updated implicitly (the GitStore records
    /// `O256::blob(data)` as `blob_hash`), so subsequent `resolve` /
    /// `reverse` calls see the new entry.
    fn store_blob(&self, data: &[u8]) -> PyResult<GitObject> {
        self.inner
            .write_object(GitObjectKind::Blob, data)
            .map(oid_to_git_object)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Check whether a git OID is registered (including shallow entries).
    fn contains(&self, oid: &Bound<'_, PyAny>) -> PyResult<bool> {
        let parsed = parse_git_hash(oid)?;
        Ok(self.inner.contains_oid(&parsed))
    }

    fn __contains__(&self, oid: &Bound<'_, PyAny>) -> PyResult<bool> {
        self.contains(oid)
    }

    fn __repr__(&self) -> String {
        format!(
            "GitImport(objects={}, cov_trees={})",
            self.inner.len(),
            self.inner.cov_tree_hashes().len(),
        )
    }
}

/// Result of [`GitImport::clone`].
#[pyclass(frozen)]
pub struct GitCloneResult {
    #[pyo3(get)]
    store: Py<GitImport>,
    #[pyo3(get)]
    objects_stored: usize,
    refs: Vec<GitRef>,
    cov_trees: Vec<(String, O256)>,
    #[pyo3(get)]
    url: String,
}

#[pymethods]
impl GitCloneResult {
    /// Refs discovered during the clone.
    #[getter]
    fn refs(&self) -> Vec<GitRef> {
        self.refs.clone()
    }

    /// Number of covalence trees converted from git trees.
    #[getter]
    fn cov_trees_count(&self) -> usize {
        self.cov_trees.len()
    }

    /// Iterate the git tree OID → covalence O256 mapping. Returns a list of
    /// `(oid_hex, O256)` tuples, *only* materialised when explicitly asked —
    /// avoids dumping thousands of entries by default.
    fn cov_trees(&self) -> Vec<(String, O256)> {
        self.cov_trees.clone()
    }

    fn __repr__(&self) -> String {
        format!(
            "GitCloneResult(url={:?}, objects_stored={}, refs={}, cov_trees={})",
            self.url,
            self.objects_stored,
            self.refs.len(),
            self.cov_trees.len(),
        )
    }
}

/// Module-level convenience: `covalence.git_clone(url, store=None, ...)` is
/// equivalent to `covalence.GitImport.clone(url, store=None, ...)`.
#[pyfunction]
#[pyo3(signature = (url, store=None, branch=None, depth=None, filter=None, algo="sha1"))]
pub fn git_clone(
    py: Python<'_>,
    url: &str,
    store: Option<&str>,
    branch: Option<&str>,
    depth: Option<u32>,
    filter: Option<&str>,
    algo: &str,
) -> PyResult<GitCloneResult> {
    GitImport::clone(py, url, store, branch, depth, filter, algo)
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
