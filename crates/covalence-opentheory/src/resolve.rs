//! Theory dependency resolution and package checking.
//!
//! [`TheoryResolver`] is the trait that abstracts how packages are located and
//! loaded.  [`check_theory`] walks the dependency graph, processes each
//! package's article against a shared kernel, and returns the resulting theory.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use covalence_hol::traits::HolLightKernel;

use crate::error::OtError;
use crate::interp::ArticleInterp;
use crate::name::NameTable;
use crate::theory::{TheoryFile, parse_theory_file};

// -----------------------------------------------------------------------
// Theory — the result of checking a package
// -----------------------------------------------------------------------

/// A checked theory: assumptions (unsatisfied axioms) and exported theorems.
#[derive(Debug)]
pub struct Theory<K: HolLightKernel> {
    /// Assumptions introduced by `axiom` commands that are not satisfied by
    /// imported theorems.
    pub assumptions: Vec<K::Thm>,
    /// Theorems exported by `thm` commands.
    pub theorems: Vec<K::Thm>,
}

// -----------------------------------------------------------------------
// TheoryResolver trait
// -----------------------------------------------------------------------

/// Trait for locating and loading OpenTheory packages.
///
/// Implementors resolve package names to their `.thy` metadata and article
/// content.  This is intentionally minimal so that callers can back it with
/// the filesystem, an in-memory map, a database, a network fetch, etc.
pub trait TheoryResolver {
    /// Load the raw `.thy` file text for a package.
    fn load_theory_file(&self, package: &str) -> Result<String, OtError>;

    /// Load the raw article text for a package's article.
    ///
    /// `package` is the package name, `article_path` is the relative path
    /// from the `.thy` file (e.g. `"bool-def-true.art"`).
    fn load_article(&self, package: &str, article_path: &str) -> Result<String, OtError>;
}

// -----------------------------------------------------------------------
// TheoryCache — persistent cache across multiple check_theory calls
// -----------------------------------------------------------------------

/// Cache of already-checked theories. Reuse across multiple [`check_theory`]
/// calls to avoid re-processing (and re-defining constants in) the kernel.
pub type TheoryCache<K> = HashMap<String, Theory<K>>;

// -----------------------------------------------------------------------
// check_theory — the main entry point
// -----------------------------------------------------------------------

/// Check a package and all its (transitive) dependencies.
///
/// Processes packages in dependency order against the shared `kernel`,
/// caching results so each package is checked at most once.  Returns a
/// reference to the [`Theory`] inside `cache` for the requested package.
///
/// Pass the same `cache` across multiple calls to avoid re-processing
/// shared dependencies.
pub fn check_theory<'c, K, R>(
    kernel: &mut K,
    names: &mut NameTable,
    resolver: &R,
    package: &str,
    cache: &'c mut TheoryCache<K>,
) -> Result<&'c Theory<K>, OtError>
where
    K: HolLightKernel,
    R: TheoryResolver,
{
    let mut in_progress: HashSet<String> = HashSet::new();
    check_theory_inner(kernel, names, resolver, package, cache, &mut in_progress)?;
    cache
        .get(package)
        .ok_or_else(|| OtError::ParseError(format!("package not found: {package}")))
}

fn check_theory_inner<K, R>(
    kernel: &mut K,
    names: &mut NameTable,
    resolver: &R,
    package: &str,
    cache: &mut HashMap<String, Theory<K>>,
    in_progress: &mut HashSet<String>,
) -> Result<(), OtError>
where
    K: HolLightKernel,
    R: TheoryResolver,
{
    if cache.contains_key(package) {
        return Ok(());
    }
    if !in_progress.insert(package.to_string()) {
        return Err(OtError::ParseError(format!(
            "circular dependency: {package}"
        )));
    }

    // 1. Load and parse the theory file.
    let thy_text = resolver.load_theory_file(package)?;
    let thy: TheoryFile = parse_theory_file(&thy_text)?;

    // 2. Recursively check all dependencies first.
    for req in &thy.requires {
        check_theory_inner(kernel, names, resolver, req, cache, in_progress)?;
    }

    // 3. Gather imported theorems from dependencies.
    let mut imported_theorems: Vec<K::Thm> = Vec::new();
    for req in &thy.requires {
        if let Some(dep) = cache.get(req) {
            imported_theorems.extend(dep.theorems.iter().cloned());
        }
    }

    // 4. Process the article.
    let article_text = resolver.load_article(package, &thy.article)?;
    let interp = ArticleInterp::new(kernel, names);
    let result = interp.interpret(&article_text)?;

    // 5. Filter assumptions: remove any that are alpha-equivalent to an
    //    imported theorem's conclusion.
    let unsatisfied: Vec<K::Thm> = result
        .assumptions
        .into_iter()
        .filter(|ax| {
            let ax_concl = kernel.concl(*ax);
            !imported_theorems
                .iter()
                .any(|imp| kernel.aconv(kernel.concl(*imp), ax_concl))
        })
        .collect();

    in_progress.remove(package);
    cache.insert(
        package.to_string(),
        Theory {
            assumptions: unsatisfied,
            theorems: result.theorems,
        },
    );
    Ok(())
}

// -----------------------------------------------------------------------
// register_select — register the `select` primitive constant
// -----------------------------------------------------------------------

/// Register the `select` (Hilbert choice) primitive constant in the kernel.
///
/// In the OpenTheory standard, `select` has type `(A -> bool) -> A` and is
/// a primitive constant (not defined by any package).  This must be called
/// before processing any package that references `Data.Bool.select`.
pub fn register_select<K: HolLightKernel>(kernel: &mut K, names: &mut NameTable) {
    let select_id = names.intern_str("Data.Bool.select");
    // select : (A -> bool) -> A
    let a = kernel.mk_tyvar(names.intern_str("A"));
    let bool_ty = kernel.bool_type();
    let pred_ty = kernel.fun_type(a, bool_ty); // A -> bool
    let select_ty = kernel.fun_type(pred_ty, a); // (A -> bool) -> A
    let _ = kernel.new_constant(select_id, select_ty);
}

// -----------------------------------------------------------------------
// FileResolver — loads packages from a directory on disk
// -----------------------------------------------------------------------

/// Resolves OpenTheory packages from a directory tree.
///
/// Expects the layout:
/// ```text
/// base_dir/
///   {name}-{version}/
///     {name}.thy
///     {name}.art
/// ```
pub struct FileResolver {
    base_dir: PathBuf,
}

impl FileResolver {
    pub fn new(base_dir: impl AsRef<Path>) -> Self {
        FileResolver {
            base_dir: base_dir.as_ref().to_path_buf(),
        }
    }

    /// Find the package directory. Tries `{name}-{version}/` patterns.
    fn find_package_dir(&self, package: &str) -> Result<PathBuf, OtError> {
        // Try exact directory name with version suffixes.
        for entry in std::fs::read_dir(&self.base_dir)
            .map_err(|e| OtError::ParseError(format!("cannot read base dir: {e}")))?
        {
            let entry =
                entry.map_err(|e| OtError::ParseError(format!("cannot read entry: {e}")))?;
            let dir_name = entry.file_name().to_string_lossy().into_owned();
            // Match: "package-X.Y" where the prefix before the last "-X.Y" is the package name.
            if dir_name == package || strip_version(&dir_name) == Some(package) {
                let path = entry.path();
                if path.is_dir() {
                    return Ok(path);
                }
            }
        }
        Err(OtError::ParseError(format!(
            "package directory not found for: {package}"
        )))
    }
}

/// Strip a trailing `-X.Y` version suffix, returning the package name.
fn strip_version(dir_name: &str) -> Option<&str> {
    // Find the last '-' that's followed by a digit.
    for (i, _) in dir_name.rmatch_indices('-') {
        let rest = &dir_name[i + 1..];
        if rest.chars().next().is_some_and(|c| c.is_ascii_digit()) {
            return Some(&dir_name[..i]);
        }
    }
    None
}

impl TheoryResolver for FileResolver {
    fn load_theory_file(&self, package: &str) -> Result<String, OtError> {
        let dir = self.find_package_dir(package)?;
        // Look for any .thy file in the directory.
        for entry in std::fs::read_dir(&dir)
            .map_err(|e| OtError::ParseError(format!("cannot read dir: {e}")))?
        {
            let entry =
                entry.map_err(|e| OtError::ParseError(format!("cannot read entry: {e}")))?;
            let path = entry.path();
            if path.extension().is_some_and(|e| e == "thy") {
                return std::fs::read_to_string(&path).map_err(|e| {
                    OtError::ParseError(format!("cannot read {}: {e}", path.display()))
                });
            }
        }
        Err(OtError::ParseError(format!(
            "no .thy file found in: {}",
            dir.display()
        )))
    }

    fn load_article(&self, package: &str, article_path: &str) -> Result<String, OtError> {
        let dir = self.find_package_dir(package)?;
        let path = dir.join(article_path);
        std::fs::read_to_string(&path)
            .map_err(|e| OtError::ParseError(format!("cannot read {}: {e}", path.display())))
    }
}
