//! URL-based OpenTheory package resolvers.
//!
//! [`UrlResolver`] fetches packages over HTTP from an OpenTheory repo server.
//! [`CachingUrlResolver`] wraps it with an on-disk cache so packages are
//! downloaded at most once.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::error::OtError;
use crate::resolve::{TheoryResolver, strip_version};

/// Default OpenTheory repo URL.
pub const OPENTHEORY_REPO: &str = "https://opentheory.gilith.com/opentheory/packages";

// -----------------------------------------------------------------------
// UrlResolver — fetch packages over HTTP
// -----------------------------------------------------------------------

/// Resolves OpenTheory packages by fetching from an HTTP repository.
///
/// The repository layout is:
/// ```text
/// {base_url}/{name}-{version}/{name}.thy
/// {base_url}/{name}-{version}/{name}.art
/// ```
pub struct UrlResolver {
    base_url: String,
    versions: RefCell<HashMap<String, String>>,
}

impl UrlResolver {
    pub fn new(base_url: impl Into<String>) -> Self {
        let mut url = base_url.into();
        // Strip trailing slash for consistent URL construction.
        while url.ends_with('/') {
            url.pop();
        }
        UrlResolver {
            base_url: url,
            versions: RefCell::new(HashMap::new()),
        }
    }

    /// Resolve a package name to its versioned form.
    ///
    /// If the name already contains a version suffix (e.g. `"bool-def-1.11"`),
    /// returns it as-is. Otherwise looks up the version registered by umbrella
    /// `.thy` processing.
    fn resolve_versioned<'a>(&'a self, package: &'a str) -> Result<Cow<'a, str>, OtError> {
        // Already versioned?
        if has_version_suffix(package) {
            return Ok(Cow::Borrowed(package));
        }
        // Look up in registered versions.
        let versions = self.versions.borrow();
        if let Some(versioned) = versions.get(package) {
            return Ok(Cow::Owned(versioned.clone()));
        }
        Err(OtError::ParseError(format!(
            "no version known for package: {package} (umbrella must be processed first)"
        )))
    }

    fn fetch_url(&self, url: &str) -> Result<String, OtError> {
        let body = ureq::get(url)
            .call()
            .map_err(|e| OtError::ParseError(format!("HTTP fetch failed for {url}: {e}")))?
            .body_mut()
            .read_to_string()
            .map_err(|e| OtError::ParseError(format!("failed to read body from {url}: {e}")))?;
        Ok(body)
    }
}

impl TheoryResolver for UrlResolver {
    fn load_theory_file(&self, package: &str) -> Result<String, OtError> {
        let versioned = self.resolve_versioned(package)?;
        let base_name = strip_version(&versioned).unwrap_or(&versioned);
        let url = format!("{}/{versioned}/{base_name}.thy", self.base_url);
        self.fetch_url(&url)
    }

    fn load_file(&self, package: &str, path: &str) -> Result<String, OtError> {
        let versioned = self.resolve_versioned(package)?;
        let url = format!("{}/{versioned}/{path}", self.base_url);
        self.fetch_url(&url)
    }

    fn register_version(&self, unversioned: &str, versioned: &str) {
        self.versions
            .borrow_mut()
            .insert(unversioned.to_string(), versioned.to_string());
    }
}

// -----------------------------------------------------------------------
// CachingUrlResolver — disk-cached URL resolver
// -----------------------------------------------------------------------

/// Wraps a [`UrlResolver`] with an on-disk cache.
///
/// On every load:
/// 1. Check `{cache_dir}/{versioned}/{filename}` on disk — return if found.
/// 2. Fetch via the inner [`UrlResolver`].
/// 3. Write to disk for future use.
///
/// The on-disk layout matches [`crate::resolve::FileResolver`] expectations,
/// so after populating via `CachingUrlResolver`, a `FileResolver` can be used
/// for offline access.
pub struct CachingUrlResolver {
    inner: UrlResolver,
    cache_dir: PathBuf,
}

impl CachingUrlResolver {
    pub fn new(cache_dir: impl AsRef<Path>, base_url: impl Into<String>) -> Self {
        CachingUrlResolver {
            inner: UrlResolver::new(base_url),
            cache_dir: cache_dir.as_ref().to_path_buf(),
        }
    }

    /// Try to read from cache, falling back to network fetch + cache write.
    fn cached_load(&self, versioned: &str, filename: &str) -> Result<String, OtError> {
        let dir = self.cache_dir.join(versioned);
        let path = dir.join(filename);

        // Cache hit?
        if path.exists() {
            return std::fs::read_to_string(&path).map_err(|e| {
                OtError::ParseError(format!("cannot read cached {}: {e}", path.display()))
            });
        }

        // Cache miss — fetch from network.
        let url = format!("{}/{versioned}/{filename}", self.inner.base_url);
        let content = self.inner.fetch_url(&url)?;

        // Write to cache.
        std::fs::create_dir_all(&dir).map_err(|e| {
            OtError::ParseError(format!("cannot create cache dir {}: {e}", dir.display()))
        })?;
        std::fs::write(&path, &content).map_err(|e| {
            OtError::ParseError(format!("cannot write cache {}: {e}", path.display()))
        })?;

        Ok(content)
    }
}

impl TheoryResolver for CachingUrlResolver {
    fn load_theory_file(&self, package: &str) -> Result<String, OtError> {
        let versioned = self.inner.resolve_versioned(package)?;
        let base_name = strip_version(&versioned).unwrap_or(&versioned);
        let filename = format!("{base_name}.thy");
        self.cached_load(&versioned, &filename)
    }

    fn load_file(&self, package: &str, path: &str) -> Result<String, OtError> {
        let versioned = self.inner.resolve_versioned(package)?;
        self.cached_load(&versioned, path)
    }

    fn register_version(&self, unversioned: &str, versioned: &str) {
        self.inner.register_version(unversioned, versioned);
    }
}

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

/// Check whether a name already has a version suffix (ends with `-DIGIT...`).
fn has_version_suffix(name: &str) -> bool {
    strip_version(name).is_some()
}
