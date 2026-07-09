//! # `covalence-tcb-db` — dump the TCB *shape* to SQLite (zero-TCB tooling)
//!
//! Proof of concept for the maintainer's "dump a TCB to SQLite" payoff of the
//! base relations refactor (`notes/vibes/base-abstraction.md` §5): once every
//! computation is an untrusted relation and every axiom a simple proposition,
//! the whole TCB is *data* — and data can live in a database. Today the
//! closest machine-readable image of the TCB is the checked-in `docs/deps/`
//! artifacts; this crate ingests them and round-trips them through SQLite:
//!
//! - **languages + admitted rules** from the golden manifests
//!   (`docs/deps/{core,eval,builtins}-manifest.txt` — the `Manifest`s of
//!   `CoreLang`/`CoreEval`/`Builtins`, pinned by each crate's
//!   `manifest_matches_golden` test);
//! - **audit configs** (mint sites, non-test LoC, public-surface leaf counts
//!   `fn`/`struct`/`enum`/`trait`/`macro`, defs coupling) and **mint-site
//!   locations** from `docs/deps/tcb-audit.json` (`scripts/tcb-audit.mjs`).
//!
//! ## Placement (justification)
//!
//! `crates/app/` — this is an *application-side tool over repo artifacts*,
//! not kernel code: it must depend on the SQLite wrapper (`covalence-sqlite`,
//! dependency discipline: never raw `rusqlite`) and the JSON wrapper
//! (`covalence-json`), neither of which may enter the kernel dependency
//! closure (the base must stay portable/wasm-clean, and nothing trusted may
//! grow deps). No kernel crate depends on this crate, and this crate depends
//! on no kernel crate — it reads the *golden files*, which the kernel's own
//! tests pin against the real `Manifest`s. Zero TCB delta by construction.
//!
//! ## Trust story
//!
//! The dump is a projection of already-untrusted, machine-generated artifacts.
//! Nothing here mints, checks, or attests anything: a `.db` row is not a
//! theorem (the R3 "reload returns bytes, not theorems" discipline of
//! `notes/vibes/tcb-holomega-roadmap.md` Front D applies verbatim).

#![forbid(unsafe_code)]

use std::fs;
use std::path::Path;

use covalence_json::Value;
use covalence_sqlite::{Connection, params};

/// Errors from reading the docs/deps artifacts or the database.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
    #[error("json: {0}")]
    Json(#[from] covalence_json::Error),
    #[error("sqlite: {0}")]
    Sqlite(#[from] covalence_sqlite::Error),
    #[error("malformed artifact: {0}")]
    Malformed(String),
}

/// A language and its admitted-rule list, in manifest order (order is part of
/// the golden file, so it round-trips).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LanguageRules {
    /// Language name (e.g. `CoreLang`).
    pub language: String,
    /// The golden manifest file this was read from (repo-relative).
    pub manifest_path: String,
    /// Admitted rule names, in manifest order.
    pub rules: Vec<String>,
}

/// One audit configuration row from `tcb-audit.json` (a trust tier), with its
/// public-surface leaf counts per item kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigRow {
    pub name: String,
    pub files: i64,
    pub non_test_loc: i64,
    pub unsafe_count: i64,
    pub mint_sites: i64,
    pub pub_fn: i64,
    pub pub_struct: i64,
    pub pub_enum: i64,
    pub pub_trait: i64,
    pub pub_macro: i64,
    pub pub_total: i64,
    pub defs_coupling: i64,
}

/// One audited `Thm::new` mint site (per config).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MintSite {
    pub config: String,
    pub file: String,
    pub line: i64,
    pub snippet: String,
}

/// The TCB shape: everything the dump persists (and the round-trip reloads).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TcbShape {
    pub languages: Vec<LanguageRules>,
    pub configs: Vec<ConfigRow>,
    pub mint_sites: Vec<MintSite>,
}

/// The `(language, golden manifest)` pairs the repo pins today. The names are
/// the untrusted display overlay — identity in the kernel is the `TypeId`;
/// the golden files are what the kernel's `manifest_matches_golden` tests pin.
pub const MANIFESTS: &[(&str, &str)] = &[
    ("CoreLang", "docs/deps/core-manifest.txt"),
    ("CoreEval", "docs/deps/eval-manifest.txt"),
    ("Builtins", "docs/deps/builtins-manifest.txt"),
];

/// Read the TCB shape from a repo checkout (its `docs/deps/` artifacts).
pub fn read_shape(repo_root: &Path) -> Result<TcbShape, Error> {
    let mut languages = Vec::new();
    for &(language, rel) in MANIFESTS {
        let text = fs::read_to_string(repo_root.join(rel))?;
        let rules = text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(str::to_owned)
            .collect();
        languages.push(LanguageRules {
            language: language.to_owned(),
            manifest_path: rel.to_owned(),
            rules,
        });
    }

    let audit: Value = covalence_json::from_str(&fs::read_to_string(
        repo_root.join("docs/deps/tcb-audit.json"),
    )?)?;
    let configs_obj = audit
        .get("configs")
        .and_then(Value::as_object)
        .ok_or_else(|| Error::Malformed("tcb-audit.json: no `configs` object".into()))?;

    let mut configs = Vec::new();
    let mut mint_sites = Vec::new();
    for (name, cfg) in configs_obj {
        let n = |key: &str| -> Result<i64, Error> {
            cfg.get(key)
                .and_then(Value::as_i64)
                .ok_or_else(|| Error::Malformed(format!("config `{name}`: missing count `{key}`")))
        };
        let surface = |key: &str| -> Result<i64, Error> {
            cfg.get("publicSurface")
                .and_then(|s| s.get(key))
                .and_then(Value::as_i64)
                .ok_or_else(|| {
                    Error::Malformed(format!("config `{name}`: missing publicSurface.{key}"))
                })
        };
        configs.push(ConfigRow {
            name: name.clone(),
            files: n("files")?,
            non_test_loc: n("nonTestLoc")?,
            unsafe_count: n("unsafe")?,
            mint_sites: n("mintSites")?,
            pub_fn: surface("fn")?,
            pub_struct: surface("struct")?,
            pub_enum: surface("enum")?,
            pub_trait: surface("trait")?,
            pub_macro: surface("macro")?,
            pub_total: n("publicSurfaceTotal")?,
            defs_coupling: n("defsCoupling")?,
        });
        for loc in cfg
            .get("mintSiteLocations")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let s = loc.as_str().ok_or_else(|| {
                Error::Malformed(format!("config `{name}`: non-string mint site"))
            })?;
            mint_sites.push(parse_mint_site(name, s)?);
        }
    }
    Ok(TcbShape {
        languages,
        configs,
        mint_sites,
    })
}

/// Parse a `path:line: snippet` mint-site location string.
fn parse_mint_site(config: &str, s: &str) -> Result<MintSite, Error> {
    let bad = || Error::Malformed(format!("mint site `{s}`: expected `path:line: snippet`"));
    let (file, rest) = s.split_once(':').ok_or_else(bad)?;
    let (line, snippet) = rest.split_once(':').ok_or_else(bad)?;
    Ok(MintSite {
        config: config.to_owned(),
        file: file.to_owned(),
        line: line.parse().map_err(|_| bad())?,
        snippet: snippet.trim().to_owned(),
    })
}

/// The schema. `language_rules.position` preserves manifest order; mint sites
/// key on `(config, file, line)`.
const SCHEMA: &str = "
CREATE TABLE languages (
    name          TEXT PRIMARY KEY,
    manifest_path TEXT NOT NULL
) STRICT;
CREATE TABLE language_rules (
    language TEXT    NOT NULL REFERENCES languages(name),
    position INTEGER NOT NULL,
    rule     TEXT    NOT NULL,
    PRIMARY KEY (language, position)
) STRICT;
CREATE TABLE configs (
    name          TEXT PRIMARY KEY,
    files         INTEGER NOT NULL,
    non_test_loc  INTEGER NOT NULL,
    unsafe_count  INTEGER NOT NULL,
    mint_sites    INTEGER NOT NULL,
    pub_fn        INTEGER NOT NULL,
    pub_struct    INTEGER NOT NULL,
    pub_enum      INTEGER NOT NULL,
    pub_trait     INTEGER NOT NULL,
    pub_macro     INTEGER NOT NULL,
    pub_total     INTEGER NOT NULL,
    defs_coupling INTEGER NOT NULL
) STRICT;
CREATE TABLE mint_sites (
    config  TEXT    NOT NULL REFERENCES configs(name),
    file    TEXT    NOT NULL,
    line    INTEGER NOT NULL,
    snippet TEXT    NOT NULL,
    PRIMARY KEY (config, file, line)
) STRICT;
";

/// Create the schema and dump the shape into `conn` (one transaction).
pub fn dump(shape: &TcbShape, conn: &mut Connection) -> Result<(), Error> {
    let tx = conn.transaction()?;
    tx.execute_batch(SCHEMA)?;
    for lang in &shape.languages {
        tx.execute(
            "INSERT INTO languages (name, manifest_path) VALUES (?1, ?2)",
            params![lang.language, lang.manifest_path],
        )?;
        for (i, rule) in lang.rules.iter().enumerate() {
            tx.execute(
                "INSERT INTO language_rules (language, position, rule) VALUES (?1, ?2, ?3)",
                params![lang.language, i as i64, rule],
            )?;
        }
    }
    for c in &shape.configs {
        tx.execute(
            "INSERT INTO configs (name, files, non_test_loc, unsafe_count, mint_sites,
                pub_fn, pub_struct, pub_enum, pub_trait, pub_macro, pub_total, defs_coupling)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
            params![
                c.name,
                c.files,
                c.non_test_loc,
                c.unsafe_count,
                c.mint_sites,
                c.pub_fn,
                c.pub_struct,
                c.pub_enum,
                c.pub_trait,
                c.pub_macro,
                c.pub_total,
                c.defs_coupling
            ],
        )?;
    }
    for m in &shape.mint_sites {
        tx.execute(
            "INSERT INTO mint_sites (config, file, line, snippet) VALUES (?1, ?2, ?3, ?4)",
            params![m.config, m.file, m.line, m.snippet],
        )?;
    }
    tx.commit()?;
    Ok(())
}

/// Reload the full shape from `conn` — the round-trip inverse of [`dump`]
/// (ordering matches [`read_shape`]: manifest order for rules, insertion
/// order preserved via rowid for configs and mint sites).
pub fn load(conn: &Connection) -> Result<TcbShape, Error> {
    let mut languages = Vec::new();
    let mut lang_stmt = conn.prepare("SELECT name, manifest_path FROM languages ORDER BY rowid")?;
    let mut rule_stmt =
        conn.prepare("SELECT rule FROM language_rules WHERE language = ?1 ORDER BY position")?;
    let lang_rows: Vec<(String, String)> = lang_stmt
        .query_map([], |r| Ok((r.get(0)?, r.get(1)?)))?
        .collect::<Result<_, _>>()?;
    for (language, manifest_path) in lang_rows {
        let rules = rule_stmt
            .query_map(params![language], |r| r.get(0))?
            .collect::<Result<_, _>>()?;
        languages.push(LanguageRules {
            language,
            manifest_path,
            rules,
        });
    }

    let mut cfg_stmt = conn.prepare(
        "SELECT name, files, non_test_loc, unsafe_count, mint_sites, pub_fn, pub_struct,
                pub_enum, pub_trait, pub_macro, pub_total, defs_coupling
         FROM configs ORDER BY rowid",
    )?;
    let configs = cfg_stmt
        .query_map([], |r| {
            Ok(ConfigRow {
                name: r.get(0)?,
                files: r.get(1)?,
                non_test_loc: r.get(2)?,
                unsafe_count: r.get(3)?,
                mint_sites: r.get(4)?,
                pub_fn: r.get(5)?,
                pub_struct: r.get(6)?,
                pub_enum: r.get(7)?,
                pub_trait: r.get(8)?,
                pub_macro: r.get(9)?,
                pub_total: r.get(10)?,
                defs_coupling: r.get(11)?,
            })
        })?
        .collect::<Result<_, _>>()?;

    let mut mint_stmt =
        conn.prepare("SELECT config, file, line, snippet FROM mint_sites ORDER BY rowid")?;
    let mint_sites = mint_stmt
        .query_map([], |r| {
            Ok(MintSite {
                config: r.get(0)?,
                file: r.get(1)?,
                line: r.get(2)?,
                snippet: r.get(3)?,
            })
        })?
        .collect::<Result<_, _>>()?;

    Ok(TcbShape {
        languages,
        configs,
        mint_sites,
    })
}
