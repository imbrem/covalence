//! URL-based OpenTheory package resolvers.
//!
//! [`UrlResolver`] fetches packages over HTTP from an OpenTheory repo server.
//! [`CachingUrlResolver`] wraps it with an on-disk cache so packages are
//! downloaded at most once.

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
    /// Site origin (`scheme://host[:port]`) hosting the `?pkg=` package-info
    /// interface used to resolve a bare name to its latest version.
    site_origin: String,
    versions: RefCell<HashMap<String, String>>,
}

impl UrlResolver {
    pub fn new(base_url: impl Into<String>) -> Self {
        let mut url = base_url.into();
        // Strip trailing slash for consistent URL construction.
        while url.ends_with('/') {
            url.pop();
        }
        let site_origin = site_origin_of(&url);
        UrlResolver {
            base_url: url,
            site_origin,
            versions: RefCell::new(HashMap::new()),
        }
    }

    /// Resolve a package name to its versioned form (`"bool"` → `"bool-1.37"`).
    ///
    /// A name that already carries a version suffix is returned as-is; a name
    /// registered by umbrella `.thy` processing uses that version; otherwise
    /// the repo's `?pkg=<name>` package-info page is queried for the latest
    /// version (memoised for the rest of the run).
    pub(crate) fn resolve_versioned(&self, package: &str) -> Result<String, OtError> {
        if has_version_suffix(package) {
            return Ok(package.to_string());
        }
        if let Some(versioned) = self.versions.borrow().get(package) {
            return Ok(versioned.clone());
        }
        let versioned = self.query_version(package)?;
        self.versions
            .borrow_mut()
            .insert(package.to_string(), versioned.clone());
        Ok(versioned)
    }

    /// Query the repo's `?pkg=<name>` page and extract the latest version.
    fn query_version(&self, package: &str) -> Result<String, OtError> {
        let url = format!("{}/?pkg={package}", self.site_origin);
        let html = self.fetch_url(&url)?;
        extract_latest_version(&html, package).ok_or_else(|| {
            OtError::ParseError(format!(
                "could not resolve a version for package `{package}` from {url}"
            ))
        })
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
        let base_name = strip_version(&versioned).unwrap_or(versioned.as_str());
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

    /// Resolve a package name to its versioned form, reusing a
    /// previously-cached version (offline) before querying the network. This
    /// lets a populated cache be re-used without re-hitting the `?pkg=` index.
    fn resolve_versioned(&self, package: &str) -> Result<String, OtError> {
        if has_version_suffix(package) {
            return Ok(package.to_string());
        }
        if let Some(versioned) = scan_cache_for_version(&self.cache_dir, package) {
            // Memoise so the inner resolver reuses it for sibling files.
            self.inner.register_version(package, &versioned);
            return Ok(versioned);
        }
        self.inner.resolve_versioned(package)
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
        let versioned = self.resolve_versioned(package)?;
        let base_name = strip_version(&versioned).unwrap_or(versioned.as_str());
        let filename = format!("{base_name}.thy");
        self.cached_load(&versioned, &filename)
    }

    fn load_file(&self, package: &str, path: &str) -> Result<String, OtError> {
        let versioned = self.resolve_versioned(package)?;
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

/// The site origin (`scheme://host[:port]`) of a repo URL — everything up to
/// the first path segment. Used to reach the sibling `?pkg=` interface.
fn site_origin_of(url: &str) -> String {
    if let Some(scheme_end) = url.find("://") {
        let after = scheme_end + 3;
        if let Some(slash) = url[after..].find('/') {
            return url[..after + slash].to_string();
        }
    }
    url.to_string()
}

/// Extract the latest version of `name` from a repo `?pkg=<name>` page. The
/// page's title and heading read `Package <name>-<version>` (the version being
/// the newest), so we read the version token immediately following the first
/// `Package <name>-`.
fn extract_latest_version(html: &str, name: &str) -> Option<String> {
    let needle = format!("Package {name}-");
    let start = html.find(&needle)? + needle.len();
    let ver: String = html[start..]
        .chars()
        .take_while(|c| c.is_ascii_digit() || *c == '.')
        .collect();
    // A real version has at least one dot (e.g. `1.37`, `1.107`).
    if ver.contains('.') {
        Some(format!("{name}-{ver}"))
    } else {
        None
    }
}

/// Find a cached `{name}-{version}` directory under `cache_dir`, if any.
fn scan_cache_for_version(cache_dir: &Path, package: &str) -> Option<String> {
    for entry in std::fs::read_dir(cache_dir).ok()?.flatten() {
        let dir_name = entry.file_name().to_string_lossy().into_owned();
        if strip_version(&dir_name) == Some(package) && entry.path().is_dir() {
            return Some(dir_name);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn origin_strips_path() {
        assert_eq!(
            site_origin_of("https://opentheory.gilith.com/opentheory/packages"),
            "https://opentheory.gilith.com"
        );
        assert_eq!(
            site_origin_of("http://localhost:8080/repo"),
            "http://localhost:8080"
        );
        assert_eq!(site_origin_of("https://example.com"), "https://example.com");
    }

    #[test]
    fn extract_version_from_pkg_page() {
        // Shape of the real `?pkg=bool` page (title + heading carry the latest).
        let html = "<title>Gilith OpenTheory Repo - Package bool-1.37</title>\
                    <h2>Package bool-1.37</h2><td>versions</td>\
                    <a href=\"?pkg=bool-def-1.11\">bool-def-1.11</a>";
        assert_eq!(
            extract_latest_version(html, "bool").as_deref(),
            Some("bool-1.37")
        );
        // A hyphenated name with a multi-part version.
        let html2 = "<h2>Package natural-order-def-1.63</h2>";
        assert_eq!(
            extract_latest_version(html2, "natural-order-def").as_deref(),
            Some("natural-order-def-1.63")
        );
        // No version present → None.
        assert_eq!(
            extract_latest_version("<h2>nothing here</h2>", "bool"),
            None
        );
    }
}
