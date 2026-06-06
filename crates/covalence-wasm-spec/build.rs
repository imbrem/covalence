//! READ-ONLY build script.
//!
//! Walks `assets/wasm/<algo>/<variant>/` and emits three generated files
//! into `$OUT_DIR`:
//!   - `hashes.rs`   — `pub const <ALGO>_<VARIANT>_BLAKE3: O256 = ...; ...`
//!   - `bytes.rs`    — `include_str!`/`include_bytes!` constants for the
//!                     committed `.wat`, `.wasm`, and `.wit` files. For
//!                     C-sourced variants (which have no `.wat`) the
//!                     `WAT` constant is the empty string.
//!   - `registry.rs` — `pub const ALL_SPECS: &[&Spec<'static>] = &[...]`
//!
//! Hashes (BLAKE3 + SHA-256) are computed from the committed `.wasm`
//! bytes. The build script never parses `.wat`, never invokes a
//! compiler. If a `.wasm` is missing (fresh checkout, asset added
//! without regen) we simply omit it from the registry — the friendly
//! remediation is to run `cargo run -p covalence-wasm-spec --bin rebuild`.
//!
//! Variant → WIT convention: variants whose dir name ends in `-stateful`
//! target `<algo>-stateful.wit`; all other variants target `<algo>.wit`.
//!
//! Vectors and metadata may live at variant level (preferred for
//! variant-specific test cases like streaming-cut KATs) or at algo
//! level (`<algo>/vectors.json`, `<algo>/description.md`,
//! `<algo>/metadata.toml`). When both exist, variant-level wins.
//!
//! `metadata.toml` shape:
//! ```toml
//! [[spec_doc]]
//! title = "FIPS PUB 180-4"
//! url = "https://..."
//! # optional: local_path = "spec.pdf"
//!
//! [hash]
//! output_bits = 160
//! block_bits = 512
//! state_bits = 160
//! length_extendable = true
//! keyed = false
//! xof = false
//! modes = ["hash", "keyed-hash", "derive-key"]
//! ```
//! Variant-level entries override algo-level entries section-by-section
//! (an entire `[hash]` block in a variant replaces the algo-level
//! `[hash]`; same for `[[spec_doc]]`).

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use covalence_hash::{HashCtx, O256, Sha256};
use toml::Value as TomlValue;

fn main() {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let assets_root = crate_dir.join("assets/wasm");
    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").expect("OUT_DIR"));

    println!("cargo:rerun-if-changed=assets/wasm");

    let variants = scan_variants(&assets_root);

    write_hashes(&out_dir, &variants);
    write_bytes(&out_dir, &assets_root, &variants);
    write_registry(&out_dir, &variants);
}

#[derive(Debug)]
#[allow(dead_code)]
struct Variant {
    algo: String,
    variant: String,
    /// `None` for C-sourced variants — they have no auditable WAT
    /// surface; the embedded `WAT` constant will be the empty string.
    wat_path: Option<PathBuf>,
    wasm_path: PathBuf,
    wit_path: PathBuf,
    description_path: Option<PathBuf>,
    vectors_path: Option<PathBuf>,
    /// Merged metadata: variant-level sections override algo-level
    /// sections (entire `[hash]` block / entire `[[spec_doc]]` array
    /// replaces the algo-level one when present in the variant file).
    metadata: HashMetadata,
    wasm_exists: bool,
    blake3: Option<O256>,
    sha256: Option<[u8; 32]>,
}

#[derive(Debug, Default, Clone)]
struct HashMetadata {
    hash_props: Option<HashPropsData>,
    sign_props: Option<SignPropsData>,
    spec_docs: Vec<SpecDocData>,
}

#[derive(Debug, Clone)]
struct HashPropsData {
    output_bits: u32,
    block_bits: u32,
    state_bits: u32,
    length_extendable: bool,
    keyed: bool,
    xof: bool,
    modes: Vec<String>,
}

#[derive(Debug, Clone)]
struct SignPropsData {
    public_key_bytes: u32,
    signature_bytes: u32,
    deterministic_verify: bool,
    deterministic_sign: bool,
}

#[derive(Debug, Clone)]
struct SpecDocData {
    title: String,
    url: String,
    local_path: Option<String>,
}

fn scan_variants(root: &Path) -> Vec<Variant> {
    let mut out = Vec::new();
    if !root.exists() {
        return out;
    }
    let algos = match fs::read_dir(root) {
        Ok(rd) => rd,
        Err(_) => return out,
    };
    for algo_entry in algos.flatten() {
        if !algo_entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
            continue;
        }
        let algo_dir = algo_entry.path();
        let algo = algo_entry.file_name().to_string_lossy().into_owned();
        let resource_wit = algo_dir.join(format!("{algo}.wit"));
        let stateful_wit = algo_dir.join(format!("{algo}-stateful.wit"));

        let algo_vectors = {
            let p = algo_dir.join("vectors.json");
            p.exists().then_some(p)
        };
        let algo_description = {
            let p = algo_dir.join("description.md");
            p.exists().then_some(p)
        };
        let algo_metadata = {
            let p = algo_dir.join("metadata.toml");
            p.exists().then_some(p)
        };

        println!("cargo:rerun-if-changed={}", resource_wit.display());
        println!("cargo:rerun-if-changed={}", stateful_wit.display());
        if let Some(p) = &algo_vectors {
            println!("cargo:rerun-if-changed={}", p.display());
        }
        if let Some(p) = &algo_description {
            println!("cargo:rerun-if-changed={}", p.display());
        }
        if let Some(p) = &algo_metadata {
            println!("cargo:rerun-if-changed={}", p.display());
        }

        let variants_iter = match fs::read_dir(&algo_dir) {
            Ok(rd) => rd,
            Err(_) => continue,
        };
        for var_entry in variants_iter.flatten() {
            if !var_entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
                continue;
            }
            let var_dir = var_entry.path();
            let variant = var_entry.file_name().to_string_lossy().into_owned();
            let wat_path = var_dir.join(format!("{variant}.wat"));
            let wasm_path = var_dir.join(format!("{variant}.wasm"));
            let var_description = {
                let p = var_dir.join("description.md");
                p.exists().then_some(p)
            };
            let var_vectors = {
                let p = var_dir.join("vectors.json");
                p.exists().then_some(p)
            };
            let var_metadata = {
                let p = var_dir.join("metadata.toml");
                p.exists().then_some(p)
            };
            let description_path = var_description.or_else(|| algo_description.clone());
            let vectors_path = var_vectors.or_else(|| algo_vectors.clone());
            if let Some(p) = &var_metadata {
                println!("cargo:rerun-if-changed={}", p.display());
            }
            let algo_md = algo_metadata
                .as_deref()
                .map(parse_metadata_file)
                .unwrap_or_default();
            let var_md = var_metadata
                .as_deref()
                .map(parse_metadata_file)
                .unwrap_or_default();
            let metadata = merge_metadata(algo_md, var_md);
            // Either a hand-written WAT or one or more `.c` files must
            // exist. C-sourced variants have no `.wat` to embed —
            // `bytes.rs` will emit an empty `WAT` string for them.
            let has_c_source = !c_source_paths(&var_dir).is_empty();
            if !wat_path.exists() && !has_c_source {
                continue;
            }
            let wit_path = if variant.ends_with("-stateful") {
                stateful_wit.clone()
            } else {
                resource_wit.clone()
            };
            let (blake3, sha256, wasm_exists) = if wasm_path.exists() {
                match fs::read(&wasm_path) {
                    Ok(bytes) => {
                        let b3 = ().tag(&bytes);
                        let s256 = *Sha256.tag(&bytes).as_bytes();
                        (Some(b3), Some(s256), true)
                    }
                    Err(_) => (None, None, false),
                }
            } else {
                (None, None, false)
            };
            println!("cargo:rerun-if-changed={}", wasm_path.display());
            println!("cargo:rerun-if-changed={}", wat_path.display());
            // Rerun on any .c source change too, so adding/removing C
            // files re-triggers the registry generation.
            for c in c_source_paths(&var_dir) {
                println!("cargo:rerun-if-changed={}", c.display());
            }

            let wat_path_opt = if wat_path.exists() {
                Some(wat_path)
            } else {
                None
            };
            out.push(Variant {
                algo: algo.clone(),
                variant,
                wat_path: wat_path_opt,
                wasm_path,
                wit_path,
                description_path,
                vectors_path,
                metadata,
                wasm_exists,
                blake3,
                sha256,
            });
        }
    }
    out
}

/// Enumerate every `.c` file directly inside the variant directory.
/// Sorted for determinism — `cargo:rerun-if-changed` directives are
/// order-sensitive and we want the same list on every build.
fn c_source_paths(var_dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let Ok(rd) = fs::read_dir(var_dir) else {
        return out;
    };
    for entry in rd.flatten() {
        let p = entry.path();
        if p.extension().map(|e| e == "c").unwrap_or(false) {
            out.push(p);
        }
    }
    out.sort();
    out
}

fn const_name(algo: &str, variant: &str, suffix: &str) -> String {
    format!(
        "{}_{}_{}",
        algo.to_uppercase().replace('-', "_"),
        variant.to_uppercase().replace('-', "_"),
        suffix
    )
}

fn write_hashes(out_dir: &Path, variants: &[Variant]) {
    let path = out_dir.join("hashes.rs");
    let mut f = fs::File::create(&path).expect("create hashes.rs");
    writeln!(
        f,
        "// AUTO-GENERATED by covalence-wasm-spec/build.rs. Do not edit."
    )
    .unwrap();
    let has_any = variants.iter().any(|v| v.wasm_exists);
    if has_any {
        writeln!(f, "use covalence_hash::O256;").unwrap();
    }
    for v in variants {
        if !v.wasm_exists {
            continue;
        }
        let b3 = v.blake3.unwrap();
        let s256 = v.sha256.unwrap();
        writeln!(
            f,
            "/// BLAKE3 content hash of the committed `{}.wasm` for `{}`.",
            v.variant, v.algo
        )
        .unwrap();
        write!(
            f,
            "pub const {}: O256 = O256::from_bytes([",
            const_name(&v.algo, &v.variant, "BLAKE3"),
        )
        .unwrap();
        for (i, b) in b3.as_bytes().iter().enumerate() {
            if i > 0 {
                write!(f, ", ").unwrap();
            }
            write!(f, "0x{b:02x}").unwrap();
        }
        writeln!(f, "]);").unwrap();
        writeln!(
            f,
            "/// SHA-256 hash of the committed `{}.wasm` for `{}`.",
            v.variant, v.algo
        )
        .unwrap();
        write!(
            f,
            "pub const {}: [u8; 32] = [",
            const_name(&v.algo, &v.variant, "SHA256")
        )
        .unwrap();
        for (i, b) in s256.iter().enumerate() {
            if i > 0 {
                write!(f, ", ").unwrap();
            }
            write!(f, "0x{b:02x}").unwrap();
        }
        writeln!(f, "];").unwrap();
    }
}

fn write_bytes(out_dir: &Path, _assets_root: &Path, variants: &[Variant]) {
    let path = out_dir.join("bytes.rs");
    let mut f = fs::File::create(&path).expect("create bytes.rs");
    writeln!(
        f,
        "// AUTO-GENERATED by covalence-wasm-spec/build.rs. Do not edit."
    )
    .unwrap();
    for v in variants {
        if !v.wasm_exists {
            writeln!(
                f,
                "// Asset `{}` is not yet built. Run `cargo run -p covalence-wasm-spec --bin rebuild`.",
                v.wasm_path.display()
            )
            .unwrap();
            continue;
        }
        let wasm_p = v.wasm_path.to_string_lossy();
        let wit_p = v.wit_path.to_string_lossy();
        // C-sourced variants have no WAT — emit an empty constant so
        // downstream `Spec.wat` field can stay non-optional. Existing
        // WAT-based variants keep their auditable `.wat` source.
        if let Some(wat_path) = &v.wat_path {
            writeln!(
                f,
                "pub const {}: &str = include_str!(\"{}\");",
                const_name(&v.algo, &v.variant, "WAT"),
                wat_path.to_string_lossy()
            )
            .unwrap();
        } else {
            writeln!(
                f,
                "pub const {}: &str = \"\";",
                const_name(&v.algo, &v.variant, "WAT"),
            )
            .unwrap();
        }
        writeln!(
            f,
            "pub const {}: &[u8] = include_bytes!(\"{}\");",
            const_name(&v.algo, &v.variant, "WASM"),
            wasm_p
        )
        .unwrap();
        writeln!(
            f,
            "pub const {}: &str = include_str!(\"{}\");",
            const_name(&v.algo, &v.variant, "WIT"),
            wit_p
        )
        .unwrap();
        if let Some(desc) = &v.description_path {
            writeln!(
                f,
                "pub const {}: &str = include_str!(\"{}\");",
                const_name(&v.algo, &v.variant, "DESCRIPTION"),
                desc.to_string_lossy()
            )
            .unwrap();
        } else {
            writeln!(
                f,
                "pub const {}: &str = \"\";",
                const_name(&v.algo, &v.variant, "DESCRIPTION"),
            )
            .unwrap();
        }
    }
}

fn write_registry(out_dir: &Path, variants: &[Variant]) {
    let path = out_dir.join("registry.rs");
    let mut f = fs::File::create(&path).expect("create registry.rs");
    writeln!(
        f,
        "// AUTO-GENERATED by covalence-wasm-spec/build.rs. Do not edit."
    )
    .unwrap();
    let has_any = variants.iter().any(|v| v.wasm_exists);
    if has_any {
        writeln!(f, "use super::hashes;").unwrap();
        writeln!(f, "use super::bytes;").unwrap();
    }

    for v in variants {
        if !v.wasm_exists {
            continue;
        }
        let var_const = format!(
            "SPEC_{}_{}",
            v.algo.to_uppercase().replace('-', "_"),
            v.variant.to_uppercase().replace('-', "_")
        );

        let kats = parse_vectors(v.vectors_path.as_deref());
        let kats_const = format!("KATS_{var_const}");
        writeln!(f, "static {kats_const}: &[Kat<'static>] = &[").unwrap();
        for k in &kats {
            writeln!(
                f,
                "    Kat {{ name: \"{}\", mode: KatMode::{}, input: {}, key: {}, expected: {}, expected_result: {} }},",
                k.name,
                k.mode_enum,
                bytes_literal(&k.input),
                match &k.key {
                    Some(b) => format!("Some({})", bytes_literal(b)),
                    None => "None".into(),
                },
                bytes_literal(&k.expected),
                k.expected_result,
            )
            .unwrap();
        }
        writeln!(f, "];").unwrap();

        // Build SpecKind::{Hash,Sign}(...) from the parsed metadata.
        // A `[sign]` block in metadata.toml selects `SpecKind::Sign`;
        // otherwise we default to `SpecKind::Hash` (preserving the
        // previous behaviour: variants with no metadata fall back to
        // an all-zero `HashProperties` + single `Hash` mode).
        let kind_expr = kind_expr(&v.metadata);

        let docs_const = format!("SPEC_DOCS_{var_const}");
        writeln!(f, "static {docs_const}: &[SpecDoc<'static>] = &[").unwrap();
        for doc in &v.metadata.spec_docs {
            let local_path_expr = match &doc.local_path {
                Some(p) => format!("Some(\"{}\")", escape_str(p)),
                None => "None".into(),
            };
            writeln!(
                f,
                "    SpecDoc {{ title: \"{}\", url: \"{}\", local_path: {local_path_expr} }},",
                escape_str(&doc.title),
                escape_str(&doc.url),
            )
            .unwrap();
        }
        writeln!(f, "];").unwrap();

        let linked_const = format!("LINKED_{var_const}");
        writeln!(
            f,
            "static {linked_const}: &[&Spec<'static>] = &[];"
        )
        .unwrap();

        writeln!(f, "pub static {var_const}: Spec<'static> = Spec {{").unwrap();
        writeln!(f, "    name: \"{}\",", v.algo).unwrap();
        writeln!(f, "    variant: \"{}\",", v.variant).unwrap();
        writeln!(
            f,
            "    blake3: hashes::{},",
            const_name(&v.algo, &v.variant, "BLAKE3")
        )
        .unwrap();
        writeln!(
            f,
            "    sha256: hashes::{},",
            const_name(&v.algo, &v.variant, "SHA256")
        )
        .unwrap();
        writeln!(f, "    kind: {kind_expr},").unwrap();
        writeln!(
            f,
            "    meta: Metadata {{ description: bytes::{}, spec_docs: {docs_const} }},",
            const_name(&v.algo, &v.variant, "DESCRIPTION")
        )
        .unwrap();
        writeln!(f, "    wit: bytes::{},", const_name(&v.algo, &v.variant, "WIT")).unwrap();
        writeln!(f, "    wat: bytes::{},", const_name(&v.algo, &v.variant, "WAT")).unwrap();
        writeln!(
            f,
            "    wasm: bytes::{},",
            const_name(&v.algo, &v.variant, "WASM")
        )
        .unwrap();
        writeln!(f, "    kats: {kats_const},").unwrap();
        writeln!(f, "    linked: {linked_const},").unwrap();
        writeln!(f, "}};").unwrap();
    }

    write!(f, "pub static ALL_SPECS: &[&Spec<'static>] = &[").unwrap();
    let mut first = true;
    for v in variants {
        if !v.wasm_exists {
            continue;
        }
        let var_const = format!(
            "SPEC_{}_{}",
            v.algo.to_uppercase().replace('-', "_"),
            v.variant.to_uppercase().replace('-', "_")
        );
        if !first {
            write!(f, ", ").unwrap();
        }
        first = false;
        write!(f, "&{var_const}").unwrap();
    }
    writeln!(f, "];").unwrap();
}

/// Minimal `vectors.json` shape: a JSON array of objects with fields
/// `name`, `mode` ("one-shot" | "streaming" | "compress"), `input`
/// (hex), optional `key` (hex), and `expected` (hex). We use a very
/// small ad-hoc parser to avoid adding `serde_json` as a build dep.
struct ParsedKat {
    name: String,
    mode_enum: &'static str,
    input: Vec<u8>,
    key: Option<Vec<u8>>,
    expected: Vec<u8>,
    /// Defaults to `true` for accept vectors / hash KATs. Verify KATs
    /// can override via the `expected_result` JSON field to specify a
    /// reject vector.
    expected_result: bool,
}

fn parse_vectors(path: Option<&Path>) -> Vec<ParsedKat> {
    let Some(path) = path else { return Vec::new() };
    let Ok(text) = fs::read_to_string(path) else { return Vec::new() };
    let mut out = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'{' {
            i += 1;
            continue;
        }
        let start = i;
        let mut depth = 0;
        let mut end = i;
        while end < bytes.len() {
            match bytes[end] {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            end += 1;
        }
        if end >= bytes.len() {
            break;
        }
        let obj = &text[start..=end];
        if let Some(kat) = parse_one_kat(obj) {
            out.push(kat);
        }
        i = end + 1;
    }
    out
}

fn parse_one_kat(obj: &str) -> Option<ParsedKat> {
    let name = extract_string(obj, "name")?.to_string();
    let mode = extract_string(obj, "mode")?;
    let mode_enum = match mode.as_str() {
        "one-shot" | "oneshot" => "OneShot",
        "streaming" | "stream" => "Streaming",
        "compress" => "Compress",
        "keyed-hash" | "keyed" => "KeyedHash",
        "derive-key" | "derive" => "DeriveKey",
        "verify" => "Verify",
        _ => return None,
    };
    // Verify KATs carry pk/msg/sig: `key` = pk (hex), `input` =
    // message (hex), `expected` = signature (hex). All other modes
    // reuse the original (input, key, expected) shape.
    let input = hex_to_bytes(&extract_string(obj, "input")?)?;
    let key = if mode_enum == "DeriveKey" {
        extract_string(obj, "context").map(|s| s.into_bytes())
    } else {
        extract_string(obj, "key").and_then(|s| hex_to_bytes(&s))
    };
    let expected = hex_to_bytes(&extract_string(obj, "expected")?)?;
    // `expected_result` only meaningful for Verify; defaults to `true`
    // (an accept vector / a hash KAT where the field is ignored).
    let expected_result = extract_bool(obj, "expected_result").unwrap_or(true);
    Some(ParsedKat {
        name,
        mode_enum,
        input,
        key,
        expected,
        expected_result,
    })
}

/// Extract a `"<key>": true|false` literal. Returns `None` if absent
/// or malformed. Tiny ad-hoc parser to avoid adding `serde_json` as a
/// build dependency, matching the rest of this file's style.
fn extract_bool(obj: &str, key: &str) -> Option<bool> {
    let needle = format!("\"{key}\"");
    let i = obj.find(&needle)?;
    let after = &obj[i + needle.len()..];
    let colon = after.find(':')?;
    let after = after[colon + 1..].trim_start();
    if after.starts_with("true") {
        Some(true)
    } else if after.starts_with("false") {
        Some(false)
    } else {
        None
    }
}

fn extract_string(obj: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\"");
    let i = obj.find(&needle)?;
    let after = &obj[i + needle.len()..];
    let colon = after.find(':')?;
    let after = &after[colon + 1..];
    let q = after.find('"')?;
    let after = &after[q + 1..];
    let end_q = after.find('"')?;
    Some(after[..end_q].to_string())
}

fn hex_to_bytes(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    let bytes = s.as_bytes();
    for chunk in bytes.chunks(2) {
        let hi = hex_digit(chunk[0])?;
        let lo = hex_digit(chunk[1])?;
        out.push((hi << 4) | lo);
    }
    Some(out)
}

fn hex_digit(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

fn bytes_literal(b: &[u8]) -> String {
    if b.is_empty() {
        return "&[]".into();
    }
    let mut out = String::from("&[");
    for (i, x) in b.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&format!("0x{x:02x}"));
    }
    out.push(']');
    out
}

fn parse_metadata_file(path: &Path) -> HashMetadata {
    let Ok(text) = fs::read_to_string(path) else {
        return HashMetadata::default();
    };
    let Ok(value) = text.parse::<TomlValue>() else {
        return HashMetadata::default();
    };
    let table = match value {
        TomlValue::Table(t) => t,
        _ => return HashMetadata::default(),
    };
    let hash_props = table.get("hash").and_then(parse_hash_props_table);
    let sign_props = table.get("sign").and_then(parse_sign_props_table);
    let mut spec_docs = Vec::new();
    if let Some(TomlValue::Array(arr)) = table.get("spec_doc") {
        for entry in arr {
            if let Some(doc) = parse_spec_doc_table(entry) {
                spec_docs.push(doc);
            }
        }
    }
    HashMetadata {
        hash_props,
        sign_props,
        spec_docs,
    }
}

fn parse_hash_props_table(v: &TomlValue) -> Option<HashPropsData> {
    let t = v.as_table()?;
    let get_u32 = |k: &str| t.get(k).and_then(|x| x.as_integer()).map(|x| x as u32);
    let get_bool = |k: &str| t.get(k).and_then(|x| x.as_bool());
    let output_bits = get_u32("output_bits").unwrap_or(0);
    let block_bits = get_u32("block_bits").unwrap_or(0);
    let state_bits = get_u32("state_bits").unwrap_or(0);
    let length_extendable = get_bool("length_extendable").unwrap_or(false);
    let keyed = get_bool("keyed").unwrap_or(false);
    let xof = get_bool("xof").unwrap_or(false);
    let mut modes = Vec::new();
    if let Some(TomlValue::Array(arr)) = t.get("modes") {
        for m in arr {
            if let Some(s) = m.as_str() {
                modes.push(s.to_string());
            }
        }
    }
    Some(HashPropsData {
        output_bits,
        block_bits,
        state_bits,
        length_extendable,
        keyed,
        xof,
        modes,
    })
}

fn parse_sign_props_table(v: &TomlValue) -> Option<SignPropsData> {
    let t = v.as_table()?;
    let get_u32 = |k: &str| t.get(k).and_then(|x| x.as_integer()).map(|x| x as u32);
    let get_bool = |k: &str| t.get(k).and_then(|x| x.as_bool());
    let public_key_bytes = get_u32("public_key_bytes").unwrap_or(0);
    let signature_bytes = get_u32("signature_bytes").unwrap_or(0);
    let deterministic_verify = get_bool("deterministic_verify").unwrap_or(false);
    let deterministic_sign = get_bool("deterministic_sign").unwrap_or(false);
    Some(SignPropsData {
        public_key_bytes,
        signature_bytes,
        deterministic_verify,
        deterministic_sign,
    })
}

fn parse_spec_doc_table(v: &TomlValue) -> Option<SpecDocData> {
    let t = v.as_table()?;
    let title = t.get("title").and_then(|x| x.as_str())?.to_string();
    let url = t.get("url").and_then(|x| x.as_str())?.to_string();
    let local_path = t
        .get("local_path")
        .and_then(|x| x.as_str())
        .map(|s| s.to_string());
    Some(SpecDocData {
        title,
        url,
        local_path,
    })
}

fn merge_metadata(algo: HashMetadata, var: HashMetadata) -> HashMetadata {
    // Variant-level sections wholesale-replace algo-level sections.
    HashMetadata {
        hash_props: var.hash_props.or(algo.hash_props),
        sign_props: var.sign_props.or(algo.sign_props),
        spec_docs: if !var.spec_docs.is_empty() {
            var.spec_docs
        } else {
            algo.spec_docs
        },
    }
}

fn kind_expr(md: &HashMetadata) -> String {
    // A `[sign]` table wins over `[hash]`: a metadata.toml that
    // declares sign properties is unambiguously a sign spec. For
    // ed25519 v0 we always emit `message_hashing: None` — cross-
    // linking the verify spec to a sha512 spec via WIT composition
    // is a planned follow-up.
    if let Some(s) = &md.sign_props {
        return format!(
            "SpecKind::Sign(SignProperties {{ public_key_bytes: {}, signature_bytes: {}, \
             deterministic_verify: {}, deterministic_sign: {}, message_hashing: None }})",
            s.public_key_bytes, s.signature_bytes, s.deterministic_verify, s.deterministic_sign,
        );
    }
    hash_kind_expr(md)
}

fn hash_kind_expr(md: &HashMetadata) -> String {
    let props = md.hash_props.clone().unwrap_or(HashPropsData {
        output_bits: 0,
        block_bits: 0,
        state_bits: 0,
        length_extendable: false,
        keyed: false,
        xof: false,
        modes: vec!["hash".into()],
    });
    let mut modes_lit = String::from("&[");
    let mut first = true;
    for m in &props.modes {
        let mapped = match m.to_ascii_lowercase().as_str() {
            "hash" => "HashMode::Hash",
            "keyed-hash" | "keyedhash" => "HashMode::KeyedHash",
            "derive-key" | "derivekey" => "HashMode::DeriveKey",
            "hmac" => "HashMode::Hmac",
            _ => continue,
        };
        if !first {
            modes_lit.push_str(", ");
        }
        first = false;
        modes_lit.push_str(mapped);
    }
    // Always have at least one mode, default to `Hash`.
    if first {
        modes_lit.push_str("HashMode::Hash");
    }
    modes_lit.push(']');
    format!(
        "SpecKind::Hash(HashProperties {{ output_bits: {}, block_bits: {}, state_bits: {}, \
         length_extendable: {}, keyed: {}, xof: {}, modes: {modes_lit} }})",
        props.output_bits,
        props.block_bits,
        props.state_bits,
        props.length_extendable,
        props.keyed,
        props.xof,
    )
}

fn escape_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str(r"\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out
}
