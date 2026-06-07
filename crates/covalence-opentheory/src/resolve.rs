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
use crate::theory::{TheoryBlock, TheoryFile, parse_theory_file};

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

    /// Load a file from a package directory (article, interpretation, etc.).
    ///
    /// `package` is the package name, `path` is the relative path
    /// from the package directory (e.g. `"bool-def-true.art"`, `"word.int"`).
    fn load_file(&self, package: &str, path: &str) -> Result<String, OtError>;

    /// BinderHint that `unversioned` maps to `versioned` (e.g. `"bool-def"` → `"bool-def-1.11"`).
    ///
    /// Called when umbrella blocks reveal version info. Default no-op.
    fn register_version(&self, _unversioned: &str, _versioned: &str) {}
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

    // 2. Recursively check all top-level dependencies first.
    for req in &thy.requires {
        check_theory_inner(kernel, names, resolver, req, cache, in_progress)?;
    }

    // 3. Process the package based on its structure.
    if let Some(article_path) = thy.main_article() {
        // LEAF: single main block with an article.
        let article_path = article_path.to_string();
        check_leaf_package(kernel, names, resolver, package, &thy, &article_path, cache)?;
    } else {
        // UMBRELLA/MIXED: named blocks referencing sub-packages or local articles.
        check_umbrella_package(kernel, names, resolver, package, &thy, cache, in_progress)?;
    }

    in_progress.remove(package);
    Ok(())
}

/// Process a leaf package: single article, filter assumptions against imports.
fn check_leaf_package<K, R>(
    kernel: &mut K,
    names: &mut NameTable,
    resolver: &R,
    package: &str,
    thy: &TheoryFile,
    article_path: &str,
    cache: &mut HashMap<String, Theory<K>>,
) -> Result<(), OtError>
where
    K: HolLightKernel,
    R: TheoryResolver,
{
    // Gather imported theorems from top-level requires.
    let imported_theorems = gather_requires_theorems(kernel, &thy.requires, cache);

    // Process the article.
    let article_text = resolver.load_file(package, article_path)?;
    let interp = ArticleInterp::new(kernel, names);
    let result = interp.interpret(&article_text)?;

    // Filter assumptions.
    let unsatisfied = filter_assumptions(kernel, result.assumptions, &imported_theorems);

    cache.insert(
        package.to_string(),
        Theory {
            assumptions: unsatisfied,
            theorems: result.theorems,
        },
    );
    Ok(())
}

/// Process an umbrella/mixed package: topo-sort blocks, resolve sub-packages.
fn check_umbrella_package<K, R>(
    kernel: &mut K,
    names: &mut NameTable,
    resolver: &R,
    package: &str,
    thy: &TheoryFile,
    cache: &mut HashMap<String, Theory<K>>,
    in_progress: &mut HashSet<String>,
) -> Result<(), OtError>
where
    K: HolLightKernel,
    R: TheoryResolver,
{
    let sorted = topo_sort_blocks(&thy.blocks)?;

    // Map block name -> its theorems (accumulated during processing).
    let mut block_theorems: HashMap<String, Vec<K::Thm>> = HashMap::new();
    let mut all_assumptions: Vec<K::Thm> = Vec::new();

    for block in &sorted {
        if block.name == "main" {
            // Main block just aggregates imports.
            let mut thms = Vec::new();
            for imp in &block.imports {
                if let Some(imp_thms) = block_theorems.get(imp.as_str()) {
                    thms.extend(imp_thms.iter().cloned());
                }
            }
            block_theorems.insert("main".to_string(), thms);
            continue;
        }

        if let Some(ref pkg_ref) = block.package {
            // Block references an external sub-package.
            let pkg_name = strip_version(pkg_ref).unwrap_or(pkg_ref);
            resolver.register_version(pkg_name, pkg_ref);
            check_theory_inner(kernel, names, resolver, pkg_name, cache, in_progress)?;

            if let Some(sub_theory) = cache.get(pkg_name) {
                let mut thms = sub_theory.theorems.clone();

                // Apply interpretation if present.
                if let Some(ref int_path) = block.interpretation {
                    let int_text = resolver.load_file(package, int_path)?;
                    let int_map = parse_interpretation(&int_text);
                    apply_interpretation(kernel, names, &int_map, &mut thms);
                }

                block_theorems.insert(block.name.clone(), thms);
                all_assumptions.extend(sub_theory.assumptions.iter().cloned());
            }
        } else if let Some(ref article_path) = block.article {
            // Block has a local article.
            let mut available = Vec::new();
            // Theorems from imported blocks.
            for imp in &block.imports {
                if let Some(imp_thms) = block_theorems.get(imp.as_str()) {
                    available.extend(imp_thms.iter().cloned());
                }
            }
            // Theorems from top-level requires.
            let req_thms = gather_requires_theorems(kernel, &thy.requires, cache);
            available.extend(req_thms);

            let article_text = resolver.load_file(package, article_path)?;
            let interp = ArticleInterp::new(kernel, names);
            let result = interp.interpret(&article_text)?;

            let unsatisfied = filter_assumptions(kernel, result.assumptions, &available);
            all_assumptions.extend(unsatisfied);
            block_theorems.insert(block.name.clone(), result.theorems);
        }
        // Blocks with only imports and no package/article are pure aggregators
        // (handled like main above).
        else if !block.imports.is_empty() {
            let mut thms = Vec::new();
            for imp in &block.imports {
                if let Some(imp_thms) = block_theorems.get(imp.as_str()) {
                    thms.extend(imp_thms.iter().cloned());
                }
            }
            block_theorems.insert(block.name.clone(), thms);
        }
    }

    let main_thms = block_theorems.remove("main").unwrap_or_default();

    cache.insert(
        package.to_string(),
        Theory {
            assumptions: all_assumptions,
            theorems: main_thms,
        },
    );
    Ok(())
}

/// Gather theorems from all top-level `requires:` dependencies.
fn gather_requires_theorems<K: HolLightKernel>(
    _kernel: &K,
    requires: &[String],
    cache: &HashMap<String, Theory<K>>,
) -> Vec<K::Thm> {
    let mut theorems = Vec::new();
    for req in requires {
        if let Some(dep) = cache.get(req.as_str()) {
            theorems.extend(dep.theorems.iter().cloned());
        }
    }
    theorems
}

/// Filter assumptions: remove any alpha-equivalent to an imported theorem.
fn filter_assumptions<K: HolLightKernel>(
    kernel: &K,
    assumptions: Vec<K::Thm>,
    imported: &[K::Thm],
) -> Vec<K::Thm> {
    assumptions
        .into_iter()
        .filter(|ax| {
            let ax_concl = kernel.concl(*ax);
            !imported
                .iter()
                .any(|imp| kernel.aconv(kernel.concl(*imp), ax_concl))
        })
        .collect()
}

/// Topological sort of theory blocks by their `import:` edges.
fn topo_sort_blocks(blocks: &[TheoryBlock]) -> Result<Vec<&TheoryBlock>, OtError> {
    let name_to_idx: HashMap<&str, usize> = blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.name.as_str(), i))
        .collect();

    let n = blocks.len();
    let mut in_degree = vec![0u32; n];
    let mut adj: Vec<Vec<usize>> = vec![vec![]; n];

    for (i, block) in blocks.iter().enumerate() {
        for imp in &block.imports {
            if let Some(&j) = name_to_idx.get(imp.as_str()) {
                adj[j].push(i);
                in_degree[i] += 1;
            }
            // Imports referencing unknown blocks are silently ignored.
        }
    }

    let mut queue: Vec<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();
    let mut sorted = Vec::with_capacity(n);

    while let Some(idx) = queue.pop() {
        sorted.push(&blocks[idx]);
        for &dep in &adj[idx] {
            in_degree[dep] -= 1;
            if in_degree[dep] == 0 {
                queue.push(dep);
            }
        }
    }

    if sorted.len() != n {
        return Err(OtError::ParseError(
            "circular import dependency among blocks".into(),
        ));
    }
    Ok(sorted)
}

// -----------------------------------------------------------------------
// Interpretation files (.int)
// -----------------------------------------------------------------------

/// A parsed interpretation: maps old names to new names.
#[derive(Debug)]
pub struct Interpretation {
    /// Type renamings: `old_name -> new_name`.
    pub types: Vec<(String, String)>,
    /// Constant renamings: `old_name -> new_name`.
    pub consts: Vec<(String, String)>,
}

/// Parse an interpretation file.
///
/// Format:
/// ```text
/// type "Data.Word.word" as "Data.Byte.byte"
/// const "Data.Word.+" as "Data.Byte.+"
/// ```
pub fn parse_interpretation(input: &str) -> Interpretation {
    let mut types = Vec::new();
    let mut consts = Vec::new();

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        let (kind, rest) = if let Some(rest) = line.strip_prefix("type ") {
            ("type", rest)
        } else if let Some(rest) = line.strip_prefix("const ") {
            ("const", rest)
        } else {
            continue;
        };

        // Parse: "old.name" as "new.name"
        if let Some((old, new)) = parse_as_pair(rest) {
            match kind {
                "type" => types.push((old, new)),
                "const" => consts.push((old, new)),
                _ => {}
            }
        }
    }

    Interpretation { types, consts }
}

/// Parse `"Foo.Bar" as "Baz.Qux"` → `("Foo.Bar", "Baz.Qux")`.
fn parse_as_pair(s: &str) -> Option<(String, String)> {
    let s = s.trim();
    // Find first quoted string.
    let (old, rest) = parse_quoted(s)?;
    let rest = rest.trim();
    let rest = rest.strip_prefix("as")?.trim();
    let (new, _) = parse_quoted(rest)?;
    Some((old, new))
}

/// Parse a `"quoted string"`, returning the content and remaining input.
fn parse_quoted(s: &str) -> Option<(String, &str)> {
    let s = s.strip_prefix('"')?;
    let end = s.find('"')?;
    Some((s[..end].to_string(), &s[end + 1..]))
}

/// Apply an interpretation (renaming) to a set of theorems.
///
/// This creates new constants/types in the kernel with the new names, mirroring
/// the originals. For now this is a placeholder that logs but doesn't deeply
/// rename theorem internals — full deep renaming requires kernel support.
fn apply_interpretation<K: HolLightKernel>(
    _kernel: &mut K,
    _names: &mut NameTable,
    _interp: &Interpretation,
    _theorems: &mut Vec<K::Thm>,
) {
    // TODO: Deep renaming of types/constants within theorems.
    // For now, interpretations are parsed but not applied. Sub-packages
    // define their own types/constants under their original names, and
    // the interpretation mapping is recorded for future use.
    //
    // Full implementation requires walking each theorem's term/type tree
    // and replacing NameIds according to the interpretation map.
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
///
/// Supports searching multiple base directories. The first directory
/// is searched first, allowing overrides (e.g. custom packages before std).
pub struct FileResolver {
    base_dirs: Vec<PathBuf>,
}

impl FileResolver {
    pub fn new(base_dir: impl AsRef<Path>) -> Self {
        FileResolver {
            base_dirs: vec![base_dir.as_ref().to_path_buf()],
        }
    }

    /// Create a resolver that searches multiple directories in order.
    pub fn with_dirs(dirs: Vec<PathBuf>) -> Self {
        FileResolver { base_dirs: dirs }
    }

    /// Find the package directory. Tries `{name}-{version}/` patterns.
    fn find_package_dir(&self, package: &str) -> Result<PathBuf, OtError> {
        for base_dir in &self.base_dirs {
            if let Ok(entries) = std::fs::read_dir(base_dir) {
                for entry in entries {
                    let entry = entry
                        .map_err(|e| OtError::ParseError(format!("cannot read entry: {e}")))?;
                    let dir_name = entry.file_name().to_string_lossy().into_owned();
                    if dir_name == package || strip_version(&dir_name) == Some(package) {
                        let path = entry.path();
                        if path.is_dir() {
                            return Ok(path);
                        }
                    }
                }
            }
        }
        Err(OtError::ParseError(format!(
            "package directory not found for: {package}"
        )))
    }
}

/// Strip a trailing `-X.Y` version suffix, returning the package name.
pub(crate) fn strip_version(dir_name: &str) -> Option<&str> {
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

    fn load_file(&self, package: &str, path: &str) -> Result<String, OtError> {
        let dir = self.find_package_dir(package)?;
        let full_path = dir.join(path);
        std::fs::read_to_string(&full_path)
            .map_err(|e| OtError::ParseError(format!("cannot read {}: {e}", full_path.display())))
    }
}
