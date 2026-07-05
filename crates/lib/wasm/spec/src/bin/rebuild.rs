//! Walk `assets/wasm/<algo>/<variant>/`, regenerate each `<variant>.wasm`
//! from its committed source, and overwrite the `.wasm` so it can be
//! committed.
//!
//! Variant → WIT mapping convention:
//!
//! - Variants whose directory name ends in `-stateful` target
//!   `<algo>-stateful.wit` (single-instance world).
//! - All other variants target `<algo>.wit` (resource world).
//!
//! Two source shapes are supported:
//!
//! ## `.wat` (default path)
//!
//! For each variant dir containing `<variant>.wat`:
//!   1. Read `<variant>.wat` and the chosen WIT.
//!   2. If the WAT is missing the canonical-ABI `hash` export, run
//!      `compose_one_shot_with` to inject the one-shot wrapper.
//!   3. `compile_wat` → core wasm.
//!   4. `encode_core_as_component` against the chosen WIT → component.
//!   5. Write `<variant>.wasm`.
//!
//! ## `.c` (`--features rebuild-c`)
//!
//! For each variant dir containing `<variant>.c` (single-file) or
//! `<variant>/*.c` (multi-file), and only when this binary is built
//! with `--features rebuild-c`:
//!
//!   1. Discover the C sources.
//!   2. Invoke `clang` with the canonical wasm32-unknown-unknown
//!      freestanding flag set:
//!
//!          clang --target=wasm32-unknown-unknown
//!                -nostdlib -nostartfiles
//!                -Wl,--no-entry -Wl,--export-dynamic
//!                -O2 -fno-builtin
//!                -mbulk-memory
//!                -o <variant>.core.wasm
//!                <c_sources>
//!
//!   3. Read the produced core wasm.
//!   4. If the core wasm exports
//!      `covalence:hash/api@0.1.0#hash` directly we skip the WAT-level
//!      compose step (C sources are expected to emit `hash`, since
//!      the WAT-level wrapper relies on `$init_impl` / `$update_impl` /
//!      `$finalize_impl` local aliases that only exist in our hand-
//!      written `.wat` files). If the export is missing, surface a
//!      clear error — the C source is expected to emit the one-shot
//!      itself.
//!   5. `encode_core_as_component` against the chosen WIT → component.
//!   6. Write `<variant>.wasm`.
//!
//! When `rebuild-c` is OFF and a `.c` source is present, the variant is
//! skipped with a warning. The default rebuild path stays toolchain-free.
//!
//! ## Export naming
//!
//! The canonical-ABI Legacy mangling requires every interface export
//! to land under `covalence:hash/api@0.1.0#<kebab-name>`. For C
//! sources we use clang's `__attribute__((export_name("...")))` on
//! each canonical-ABI function — no out-of-band `exports.json` map is
//! needed. The required export list for a `*-stateful` C variant is:
//!
//! ```text
//! covalence:hash/api@0.1.0#init       — ()           → ()
//! covalence:hash/api@0.1.0#update     — (i32 i32)    → ()
//! covalence:hash/api@0.1.0#finalize   — ()           → i32 (return area)
//! covalence:hash/api@0.1.0#compress   — (i32 i32 i32 i32) → i32
//! covalence:hash/api@0.1.0#hash       — (i32 i32)    → i32
//! cabi_realloc                         — bump allocator
//! memory                               — exported linear memory
//! ```
//!
//! For non-stateful (`resource`) C variants the required exports
//! match `<algo>.wit`'s resource shape; we don't currently ship any
//! such variant, but the rebuild path is shape-agnostic.

use std::fs;
use std::path::{Path, PathBuf};
use std::process;

use covalence_hash::{HashCtx, Sha256};
use covalence_wasm::{compile_wat, encode_core_as_component};
use covalence_wasm_spec::{Shape, compose_one_shot_with};
use thiserror::Error;

/// Per-variant build errors. We use `thiserror` rather than ad-hoc
/// strings so the C-toolchain path can surface clang failures cleanly.
#[derive(Debug, Error)]
enum BuildError {
    #[error("read {0}: {1}")]
    Read(String, std::io::Error),
    #[error("write {0}: {1}")]
    Write(String, std::io::Error),
    #[error("compose: {0}")]
    Compose(#[from] covalence_wasm_spec::ComposeError),
    #[error("compile_wat: {0}")]
    Wat(#[from] CompileWatError),
    #[error("encode_core_as_component: {0}")]
    Encode(#[from] EncodeError),
    #[cfg(feature = "rebuild-c")]
    #[error(transparent)]
    Clang(#[from] ClangError),
    #[cfg(feature = "rebuild-c")]
    #[error(
        "c-sourced variant {variant} does not export a recognised \
         canonical-ABI entry point (`covalence:hash/api@0.1.0#hash` for \
         hash specs or `covalence:sign/api@0.1.0#verify` for sign specs); \
         the C source must emit the wrapper itself"
    )]
    CMissingEntryExport { variant: String },
}

// Tiny `From` shims so `?` works across crates without leaking foreign
// error types into our public surface (rebuild is a binary anyway, so
// the surface here is internal).
#[derive(Debug, Error)]
#[error("{0}")]
struct CompileWatError(String);

#[derive(Debug, Error)]
#[error("{0}")]
struct EncodeError(String);

impl From<covalence_wasm::WasmError> for CompileWatError {
    fn from(e: covalence_wasm::WasmError) -> Self {
        Self(e.to_string())
    }
}

impl From<covalence_wasm::WasmError> for EncodeError {
    fn from(e: covalence_wasm::WasmError) -> Self {
        Self(e.to_string())
    }
}

#[cfg(feature = "rebuild-c")]
#[derive(Debug, Error)]
enum ClangError {
    #[error("`clang` not found in PATH (`rebuild-c` requires a wasm-capable clang)")]
    NotFound(std::io::Error),
    #[error("clang exited with status {status}:\n{stderr}")]
    NonZero { status: String, stderr: String },
    #[error("no .c sources found for variant `{0}`")]
    NoSources(String),
}

fn main() {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let assets = crate_dir.join("assets/wasm");
    let mut any_err = false;

    let algos = match fs::read_dir(&assets) {
        Ok(rd) => rd.flatten().collect::<Vec<_>>(),
        Err(e) => {
            eprintln!("cannot read assets dir {}: {e}", assets.display());
            process::exit(1);
        }
    };
    for algo_entry in algos {
        if !algo_entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
            continue;
        }
        let algo_dir = algo_entry.path();
        let algo = algo_entry.file_name().to_string_lossy().into_owned();
        let resource_wit_path = algo_dir.join(format!("{algo}.wit"));
        let stateful_wit_path = algo_dir.join(format!("{algo}-stateful.wit"));

        let variants = match fs::read_dir(&algo_dir) {
            Ok(rd) => rd.flatten().collect::<Vec<_>>(),
            Err(_) => continue,
        };
        for var_entry in variants {
            if !var_entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
                continue;
            }
            let var_dir = var_entry.path();
            let variant = var_entry.file_name().to_string_lossy().into_owned();
            let wat_path = var_dir.join(format!("{variant}.wat"));
            let wasm_path = var_dir.join(format!("{variant}.wasm"));

            let source = classify_source(&var_dir, &variant, &wat_path);
            let source = match source {
                Some(s) => s,
                None => continue,
            };

            let (target_wit_path, shape) = if variant.ends_with("-stateful") {
                (&stateful_wit_path, Shape::Stateful)
            } else {
                (&resource_wit_path, Shape::Resource)
            };
            if !target_wit_path.exists() {
                eprintln!(
                    "[{algo}/{variant}] FAILED: WIT {} missing",
                    target_wit_path.display()
                );
                any_err = true;
                continue;
            }
            let wit = match fs::read_to_string(target_wit_path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!(
                        "[{algo}/{variant}] FAILED: read {}: {e}",
                        target_wit_path.display()
                    );
                    any_err = true;
                    continue;
                }
            };

            let result = match source {
                Source::Wat => build_wat_variant(&wit, &wat_path, &wasm_path, shape),
                #[cfg(feature = "rebuild-c")]
                Source::C(c_sources) => {
                    build_c_variant(&wit, &c_sources, &var_dir, &variant, &wasm_path)
                }
            };
            match result {
                Ok(bytes) => report(&algo, &variant, &bytes),
                Err(e) => {
                    eprintln!("[{algo}/{variant}] FAILED: {e}");
                    any_err = true;
                }
            }
        }
    }
    if any_err {
        process::exit(1);
    }
}

/// What source shape does the variant ship?
enum Source {
    Wat,
    /// One or more `.c` files. Only constructed when this binary is
    /// built with `--features rebuild-c`; otherwise C-source variants
    /// are skipped at classification time with a warning.
    #[cfg(feature = "rebuild-c")]
    C(Vec<PathBuf>),
}

fn classify_source(var_dir: &Path, variant: &str, wat_path: &Path) -> Option<Source> {
    let _ = variant; // only used by the rebuild-c branch
    if wat_path.exists() {
        return Some(Source::Wat);
    }
    // Collect every .c file in the variant directory.
    let mut c_sources: Vec<PathBuf> = Vec::new();
    if let Ok(rd) = fs::read_dir(var_dir) {
        for entry in rd.flatten() {
            let p = entry.path();
            if p.extension().map(|e| e == "c").unwrap_or(false) {
                c_sources.push(p);
            }
        }
    }
    if c_sources.is_empty() {
        return None;
    }
    c_sources.sort();
    #[cfg(feature = "rebuild-c")]
    {
        Some(Source::C(c_sources))
    }
    #[cfg(not(feature = "rebuild-c"))]
    {
        eprintln!(
            "[{variant}] WARNING: c-source variant {variant} requires \
             --features rebuild-c; skipping ({} files found)",
            c_sources.len()
        );
        None
    }
}

fn build_wat_variant(
    wit: &str,
    wat_path: &Path,
    wasm_path: &Path,
    shape: Shape,
) -> Result<Vec<u8>, BuildError> {
    let wat_src = fs::read_to_string(wat_path)
        .map_err(|e| BuildError::Read(wat_path.display().to_string(), e))?;
    let effective_wat = if needs_one_shot_wrapper(&wat_src) {
        compose_one_shot_with(&wat_src, shape)?
    } else {
        wat_src
    };
    let core = compile_wat(&effective_wat).map_err(CompileWatError::from)?;
    let comp = encode_core_as_component(&core, wit).map_err(EncodeError::from)?;
    fs::write(wasm_path, &comp)
        .map_err(|e| BuildError::Write(wasm_path.display().to_string(), e))?;
    Ok(comp)
}

#[cfg(feature = "rebuild-c")]
fn build_c_variant(
    wit: &str,
    c_sources: &[PathBuf],
    var_dir: &Path,
    variant: &str,
    wasm_path: &Path,
) -> Result<Vec<u8>, BuildError> {
    if c_sources.is_empty() {
        return Err(ClangError::NoSources(variant.to_string()).into());
    }
    let core_path = var_dir.join(format!("{variant}.core.wasm"));
    invoke_clang(c_sources, &core_path)?;
    let core =
        fs::read(&core_path).map_err(|e| BuildError::Read(core_path.display().to_string(), e))?;
    // Discard the intermediate .core.wasm — we only commit the final
    // component .wasm. (Keep this side-effect last so that if encode
    // fails, the user can inspect .core.wasm to debug.)
    let cleanup_core = core_path.clone();

    // C variants are expected to emit the canonical-ABI entry point
    // themselves; double-check before handing off to the component
    // encoder. Hash specs export `hash`, sign specs export `verify`.
    if !core_exports_known_entry(&core) {
        return Err(BuildError::CMissingEntryExport {
            variant: variant.to_string(),
        });
    }

    let comp = encode_core_as_component(&core, wit).map_err(EncodeError::from)?;
    fs::write(wasm_path, &comp)
        .map_err(|e| BuildError::Write(wasm_path.display().to_string(), e))?;
    // Tidy up only on success — leave .core.wasm around on failure for
    // post-mortem inspection.
    let _ = fs::remove_file(&cleanup_core);
    Ok(comp)
}

#[cfg(feature = "rebuild-c")]
fn invoke_clang(c_sources: &[PathBuf], out_path: &Path) -> Result<(), ClangError> {
    use std::process::Command;

    let mut cmd = Command::new("clang");
    cmd.arg("--target=wasm32-unknown-unknown")
        .arg("-nostdlib")
        .arg("-nostartfiles")
        .arg("-Wl,--no-entry")
        .arg("-Wl,--export-dynamic")
        .arg("-O2")
        .arg("-fno-builtin")
        .arg("-mbulk-memory")
        .arg("-o")
        .arg(out_path);
    for src in c_sources {
        cmd.arg(src);
    }
    let output = cmd.output().map_err(ClangError::NotFound)?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        return Err(ClangError::NonZero {
            status: output.status.to_string(),
            stderr,
        });
    }
    Ok(())
}

#[cfg(feature = "rebuild-c")]
fn core_exports_known_entry(core: &[u8]) -> bool {
    // Cheap check: look for either canonical-ABI entry point name in
    // the raw bytes. The export section stores names as UTF-8 strings
    // so a straight byte-window scan is reliable. We accept either
    // `hash` (for hash specs) or `verify` (for sign specs) — both
    // shapes are valid; the rebuild path is shape-agnostic beyond
    // requiring that the C source emit *some* canonical-ABI export.
    const HASH_NEEDLE: &[u8] = b"covalence:hash/api@0.1.0#hash";
    const VERIFY_NEEDLE: &[u8] = b"covalence:sign/api@0.1.0#verify";
    core.windows(HASH_NEEDLE.len()).any(|w| w == HASH_NEEDLE)
        || core
            .windows(VERIFY_NEEDLE.len())
            .any(|w| w == VERIFY_NEEDLE)
}

fn report(algo: &str, variant: &str, bytes: &[u8]) {
    let b3 = ().tag(bytes);
    let s256 = Sha256.tag(bytes);
    println!(
        "[{algo}/{variant}] {} bytes, BLAKE3={}, SHA-256={}",
        bytes.len(),
        b3,
        s256
    );
}

fn needs_one_shot_wrapper(wat: &str) -> bool {
    !wat.contains("covalence:hash/api@0.1.0#hash\"")
}
