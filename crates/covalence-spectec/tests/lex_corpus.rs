//! Lex every vendored `.spectec` source file from upstream without error.
//!
//! Sources live in `assets/spectec/`:
//! - `wasm-3.0/*.spectec` — the full WebAssembly 3.0 specification (36 files)
//! - `test-frontend/test.spectec` — upstream's focused parser/elaborator unit cases
//! - `test-middlend/test.spectec` — upstream's middle-end unit cases
//!
//! See `assets/spectec/README.md` for the pinned upstream commit.

use std::path::{Path, PathBuf};

use covalence_spectec::{lex::lex, source::SourceMap};

fn assets_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("assets/spectec")
}

fn list_spectec_files(dir: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("spectec"))
        .collect();
    out.sort();
    out
}

fn lex_file(path: &Path) -> Result<usize, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("read {}: {e}", path.display()))?;
    let mut map = SourceMap::new();
    let id = map.add(path, &text);
    match lex(id, &text) {
        Ok(tokens) => Ok(tokens.len()),
        Err(diag) => {
            let (line, col) = map.line_col(diag.primary.file, diag.primary.start);
            Err(format!(
                "{}:{line}:{col}: {}",
                path.display(),
                diag.message
            ))
        }
    }
}

#[test]
fn lex_all_wasm_3_0_files() {
    let dir = assets_dir().join("wasm-3.0");
    let files = list_spectec_files(&dir);
    assert!(
        !files.is_empty(),
        "no .spectec files found in {} — vendor missing?",
        dir.display()
    );

    let mut errors = Vec::new();
    let mut total_tokens = 0usize;
    for f in &files {
        match lex_file(f) {
            Ok(n) => total_tokens += n,
            Err(e) => errors.push(e),
        }
    }

    if !errors.is_empty() {
        panic!("lex errors:\n{}", errors.join("\n"));
    }
    // Sanity check: each file produces tokens.
    assert!(total_tokens > 0, "no tokens produced for any file");
    eprintln!(
        "lex_all_wasm_3_0_files: {} files, {} tokens",
        files.len(),
        total_tokens
    );
}

#[test]
fn lex_frontend_test_file() {
    let path = assets_dir().join("test-frontend/test.spectec");
    let n = lex_file(&path).expect("lex frontend test corpus");
    assert!(n > 100, "expected nontrivial token count, got {n}");
}

#[test]
fn lex_middlend_test_file() {
    let path = assets_dir().join("test-middlend/test.spectec");
    let n = lex_file(&path).expect("lex middlend test corpus");
    assert!(n > 10, "expected nontrivial token count, got {n}");
}
