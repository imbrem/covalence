//! TEMPORARY / THROWAWAY DEMO SURFACE — the `/metamath` web page's backend.
//!
//! Clean REST for data + a thin WebSocket for live status only. The server is
//! **stateful**: a `.mm` source is parsed once into a cached [`MmSession`]
//! (keyed by content hash + optional user), then:
//!
//!   - graph + per-theorem data are served by **REST** (cacheable, immutable
//!     for a given session),
//!   - the parallel kernel import is kicked off by a **REST** `POST /prove`,
//!   - and live per-theorem status is forwarded over a **thin status WS** that
//!     only carries `snapshot`/`proving`/`proved`/`done` frames.
//!
//! This is NOT part of the stable API surface — it powers a throwaway UX
//! experiment (a "task view" of a covalence proof DB) and is expected to be
//! deleted/rewritten wholesale.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock, RwLock};

use axum::Json;
use axum::extract::ws::{Message, WebSocket, WebSocketUpgrade};
use axum::extract::{Path, Query, State};
use axum::http::{StatusCode, header};
use axum::response::{IntoResponse, Response};
use covalence_hash::O256;
use serde::Deserialize;
use serde_json::{Value, json};

use crate::AppState;

/// All TEMPORARY `/metamath` demo routes, grouped in one router so the whole
/// demo is a single removable/refactorable unit. Nest at `/api/metamath`:
///   - `POST /upload`                        — cache a `.mm` source → `{file,total,origin}`
///   - `GET  /sessions`                      — list cached sessions
///   - `GET  /session/{hash}`                — session info / attach-by-hash probe
///   - `GET  /session/{hash}/graph`          — the static declaration graph
///   - `GET  /session/{hash}/theorem/{name}` — one theorem's full detail
///   - `POST /session/{hash}/prove`          — start the parallel prove
///   - `GET  /session/{hash}/status`         — live status WebSocket
pub fn router() -> axum::Router<AppState> {
    use axum::extract::DefaultBodyLimit;
    use axum::routing::{get, post};
    axum::Router::new()
        // set.mm is ~48 MB — lift axum's default 2 MB request-body cap here.
        .route(
            "/upload",
            post(create_db).layer(DefaultBodyLimit::max(256 * 1024 * 1024)),
        )
        .route("/sessions", get(list_dbs))
        .route("/stats", get(server_stats))
        .route("/session/{hash}", get(db_info))
        .route("/session/{hash}/graph", get(graph))
        .route("/session/{hash}/symbols", get(symbols))
        .route("/session/{hash}/hol", get(hol))
        .route("/session/{hash}/hol/terms", get(hol_terms))
        .route("/session/{hash}/theorem/{name}", get(theorem))
        .route("/session/{hash}/prove", post(prove))
        .route("/session/{hash}/status", get(status_ws))
}

// ---------------------------------------------------------------------------
// Session registry
// ---------------------------------------------------------------------------

/// `(file-hash-hex, optional-user-key)` — sessions are cached per source per
/// user, so re-POSTing the same `.mm` reuses the parsed database.
pub type SessionKey = (String, Option<String>);

/// All live Metamath demo sessions. Lives in [`AppState`] as an `Arc`.
pub type MmSessions = Mutex<HashMap<SessionKey, Arc<MmSession>>>;

/// One parsed-and-cached Metamath database, ready to serve.
pub struct MmSession {
    /// The parsed database, shared read-only across the prove threads.
    pub db: Arc<covalence_hol::metamath::Database>,
    /// Logical (`|-`) `$p` theorem count.
    pub total: usize,
    /// Provenance: where this `.mm` came from (a URL or label). `None` if it was
    /// uploaded without a `?from=` hint. Filled in on a later cache-hit if a
    /// `from` is supplied and it was previously `None`.
    pub origin: RwLock<Option<String>>,
    /// Cached graph JSON (computed once on first GET `/graph`).
    pub graph: OnceLock<String>,
    /// label → proved-result JSON (filled as the prove task completes).
    pub results: RwLock<HashMap<String, Value>>,
    /// Broadcast channel for live status frames.
    pub status_tx: tokio::sync::broadcast::Sender<String>,
    /// CAS guard so the prove task is launched at most once per session.
    pub proving: AtomicBool,
    /// Token → Unicode typeset symbol, decoded from the database's `$t`
    /// `althtmldef` section (empty if the `.mm` has no typesetting). Served by
    /// `/symbols` so the page can typeset formulas like the Proof Explorer.
    pub symbols: HashMap<String, String>,
    /// **Pass 1** of the two-pass import: every theorem's HOL conclusion term,
    /// hash-consed into one shared DAG and pretty-printed (folding the most-reused
    /// sub-formulas to named definitions). Computed once, lazily, off-runtime.
    pub hol: OnceLock<HolSurface>,
}

/// The pass-1 result: the interned HOL surface of the whole database.
pub struct HolSurface {
    /// label → pretty-printed HOL conclusion (folding any sub-formula that is an
    /// exact instance of a named Metamath definition).
    pub terms: HashMap<String, String>,
    /// The Metamath **definitions** (syntactic formers + `df-*`) — each already
    /// has a name; this is the `name ↔ HOL term` reference, the bidirectional map
    /// used to fold/explain the symbols appearing in theorem terms.
    pub defs: Vec<DefEntry>,
    /// Total statement-tree nodes summed over all conclusions (un-interned).
    pub surface_nodes: usize,
    /// Distinct nodes after interning (the shared DAG) — `surface_nodes / dag_nodes`
    /// is the dedup factor.
    pub dag_nodes: usize,
}

/// One named Metamath definition and its HOL encoding.
pub struct DefEntry {
    /// The Metamath label (the definition's name).
    pub label: String,
    /// `"former"` (a `wff`/`class`/… syntax constructor) or `"def"` (a `df-*`).
    pub kind: &'static str,
    /// The rendered Metamath statement.
    pub mm: String,
    /// The rendered HOL term (the encoded conclusion).
    pub hol: String,
}

/// `?user=<opt>` query for every endpoint.
#[derive(Deserialize, Default)]
pub struct UserQ {
    pub user: Option<String>,
}

/// `?user=<opt>&from=<string>` query for the create endpoint. `from` records
/// provenance (a URL or label) of the uploaded `.mm`.
#[derive(Deserialize, Default)]
pub struct CreateQ {
    pub user: Option<String>,
    pub from: Option<String>,
}

/// `?user=<opt>&workers=N` query for the prove endpoint.
#[derive(Deserialize, Default)]
pub struct ProveQ {
    pub user: Option<String>,
    pub workers: Option<usize>,
}

fn lookup(state: &AppState, hash: &str, user: &Option<String>) -> Option<Arc<MmSession>> {
    let key: SessionKey = (hash.to_string(), user.clone());
    state.mm.lock().unwrap().get(&key).cloned()
}

// ---------------------------------------------------------------------------
// Rendering helpers (static per-theorem data from the database)
// ---------------------------------------------------------------------------

/// Render one theorem's proof code (Normal labels joined, or Compressed
/// `( labels ) letters`).
fn render_proof(a: &covalence_metamath::database::Assertion) -> String {
    use covalence_metamath::database::Proof;
    match &a.proof {
        Some(Proof::Normal(labels)) => labels.join(" "),
        Some(Proof::Compressed { labels, letters }) => {
            format!("( {} ) {}", labels.join(" "), String::from_utf8_lossy(letters))
        }
        None => String::new(),
    }
}

/// The deduped (first-seen order) logical (`|-`) dependency list of a proof:
/// `[{label, kind}]` with kind axiom/def/thm (thm if the dep has its own proof,
/// else `df*` → def, else axiom).
fn render_deps(db: &covalence_hol::metamath::Database, a: &covalence_metamath::database::Assertion) -> Vec<Value> {
    use covalence_metamath::database::Statement;
    use covalence_metamath::{ProofStep, proof_steps};

    let mut deps: Vec<Value> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    if let Ok(steps) = proof_steps(db, a) {
        for step in &steps {
            let ProofStep::Label(l) = step else { continue };
            if seen.contains(l) {
                continue;
            }
            let Some(Statement::Assert(dep)) = db.statement_by_label(l) else {
                continue;
            };
            if dep.conclusion.typecode() != "|-" {
                continue;
            }
            seen.insert(l.clone());
            let kind = if dep.proof.is_some() {
                "thm"
            } else if l.starts_with("df") {
                "def"
            } else {
                "axiom"
            };
            deps.push(json!({ "label": l, "kind": kind }));
        }
    }
    deps
}

/// The graph-phase item for one theorem: `{label, mm, deps}`.
fn graph_item(db: &covalence_hol::metamath::Database, label: &str) -> Value {
    use covalence_metamath::database::Statement;
    match db.statement_by_label(label) {
        Some(Statement::Assert(a)) => json!({
            "label": label,
            "mm": a.conclusion.render(),
            "deps": render_deps(db, a),
        }),
        _ => json!({ "label": label, "mm": "", "deps": [] }),
    }
}

/// Build the proved-result JSON for one finished theorem (stored in `results`
/// and broadcast over the status WS).
fn proved_result(
    result: &covalence_core::Result<covalence_core::Thm>,
    import_ms: f64,
) -> Value {
    match result {
        Ok(thm) => {
            let full = format!("{}", thm.concl());
            let hol_preview: String = full.chars().take(400).collect();
            json!({
                "status": "proved",
                "ok": true,
                "hyps": thm.hyps().len(),
                "genuine": thm.has_no_obs(),
                "holPreview": hol_preview,
                "importMs": import_ms,
            })
        }
        Err(e) => json!({
            "status": "error",
            "ok": false,
            "error": e.to_string(),
            "importMs": import_ms,
        }),
    }
}

// ---------------------------------------------------------------------------
// Typesetting: $t althtmldef → token → Unicode map
// ---------------------------------------------------------------------------

/// Build the `token → Unicode` map from a `.mm` source's `$t` `althtmldef`
/// section (the Unicode/HTML typesetting; `htmldef` is GIFs, `latexdef` is TeX).
/// Identity and empty mappings are dropped (the page passes unmapped tokens
/// through unchanged).
fn symbol_map(source: &str) -> HashMap<String, String> {
    let mut map = HashMap::new();
    for d in covalence_metamath::parse_typesetting(source) {
        if d.kind != "althtmldef" {
            continue;
        }
        let uni = decode_html_text(&d.value);
        if uni.is_empty() || uni == d.token {
            continue;
        }
        map.insert(d.token, uni);
    }
    map
}

/// Decode an `althtmldef` HTML fragment to display text: drop tags, then decode
/// entities (numeric `&#x1D711;` + the full HTML5 named table via `html-escape`),
/// and collapse whitespace.
fn decode_html_text(raw: &str) -> String {
    // html-escape decodes entities but not markup, so strip `<...>` tags first.
    let mut stripped = String::with_capacity(raw.len());
    let mut chars = raw.chars();
    while let Some(c) = chars.next() {
        if c == '<' {
            for d in chars.by_ref() {
                if d == '>' {
                    break;
                }
            }
        } else {
            stripped.push(c);
        }
    }
    let decoded = html_escape::decode_html_entities(&stripped);
    decoded.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// GET `/api/metamath/session/{hash}/symbols` — the database's token → Unicode
/// typeset map (from its `$t` `althtmldef` section). Empty if it has none.
pub async fn symbols(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    Json(sess.symbols.clone()).into_response()
}

// ---------------------------------------------------------------------------
// Pass 1: the interned HOL surface (terms + a definitions fold)
// ---------------------------------------------------------------------------

use covalence_core::Term;
use covalence_core::term::TermKind;

/// `Some((a, b))` if `t` is `mm$concat a b` (the encoding's uninterpreted binary
/// former — a `Free`, see `mm_database::concat_fn`).
fn concat_parts(t: &Term) -> Option<(&Term, &Term)> {
    let (inner, b) = t.as_app()?;
    let (cf, a) = inner.as_app()?;
    (cf.as_free()?.name() == "mm$concat").then_some((a, b))
}

/// One encoding leaf → its display token (`mm$c$<tok>`/`mm$v$<tok>` stripped).
fn hol_atom(t: &Term) -> String {
    match t.as_free() {
        Some(v) => {
            let name = v.name();
            name.strip_prefix("mm$c$")
                .or_else(|| name.strip_prefix("mm$v$"))
                .unwrap_or(name)
                .to_string()
        }
        None => format!("{t}"),
    }
}

/// Pretty-print a HOL conclusion: flatten the `mm$concat` token sequence and
/// strip the encoding prefixes. Sub-formulas present in `names` are folded to
/// their definition name; the root term itself is never folded.
fn render_hol(t: &Term, names: &HashMap<Term, String>) -> String {
    let mut out = Vec::new();
    hol_children(t, names, &mut out);
    out.join(" ")
}

fn hol_flatten(t: &Term, names: &HashMap<Term, String>, out: &mut Vec<String>) {
    if let Some(n) = names.get(t) {
        out.push(n.clone());
        return;
    }
    hol_children(t, names, out);
}

fn hol_children(t: &Term, names: &HashMap<Term, String>, out: &mut Vec<String>) {
    match concat_parts(t) {
        Some((a, b)) => {
            hol_flatten(a, names, out);
            hol_flatten(b, names, out);
        }
        None => out.push(hol_atom(t)),
    }
}

fn tree_size(t: &Term) -> usize {
    1 + match t.kind() {
        TermKind::App(f, x) => tree_size(f) + tree_size(x),
        TermKind::Abs(_, b) => tree_size(b),
        _ => 0,
    }
}

/// Flattened token length of a concat chain (1 for a leaf).
fn token_len(t: &Term) -> usize {
    match concat_parts(t) {
        Some((a, b)) => token_len(a) + token_len(b),
        None => 1,
    }
}

/// **Pass 1.** Build the whole database's interned HOL surface on a single
/// thread: encode every theorem conclusion + every Metamath definition into one
/// shared interner, then pretty-print each — folding any sub-formula that is an
/// exact instance of a named definition back to that definition's label.
/// Blocking (run off the async runtime).
///
/// The definitions are the database's *own* named assertions — the syntactic
/// formers (`wff`/`class`/… constructors) and the `df-*` definitions — so the
/// `name ↔ HOL term` map uses real Metamath names, not synthetic ones.
fn build_hol_surface(db: &covalence_hol::metamath::Database) -> HolSurface {
    use covalence_hol::metalogic::mm_database::{Parser, intern_surface};
    use covalence_hol::metalogic::mm_import::theorem_labels;
    use covalence_metamath::database::Statement;

    let parser = Parser::new(db);
    let thm_labels = theorem_labels(db);
    let mut cons = covalence_core::HashCons::new();

    // Interned theorem conclusions (pass-1 proper). `intern_surface` also seeds
    // the cons with their shared structure.
    let decls = intern_surface(db, &parser, &thm_labels, &mut cons).unwrap_or_default();

    // The Metamath definitions, interned into the SAME cons (so they share the
    // theorems' constants). `name ↔ interned encoded conclusion`.
    let mut names: HashMap<Term, String> = HashMap::new();
    let mut def_terms: Vec<(String, &'static str, Term)> = Vec::new();
    for a in db.assertions() {
        let kind = if a.conclusion.typecode() != "|-" {
            "former" // a wff/class/setvar syntax constructor
        } else if a.label.starts_with("df") {
            "def" // a df-* definition
        } else {
            continue;
        };
        let Ok(enc) = parser.encode_expr(&a.conclusion) else {
            continue;
        };
        let enc = enc.cons_with(&mut cons);
        // Only fold *compound* definitions (≥3 tokens): folding an atomic symbol
        // (`T.`, `bool`) to its constructor label would make terms *less*
        // readable. Atomic definitions still appear in the reference panel.
        if token_len(&enc) >= 3 {
            names.entry(enc.clone()).or_insert_with(|| a.label.clone());
        }
        def_terms.push((a.label.clone(), kind, enc));
    }

    // Render the definitions (folding nested definitions, never the root itself).
    let defs: Vec<DefEntry> = def_terms
        .iter()
        .filter_map(|(label, kind, enc)| {
            let Some(Statement::Assert(a)) = db.statement_by_label(label) else {
                return None;
            };
            Some(DefEntry {
                label: label.clone(),
                kind,
                mm: a.conclusion.render(),
                hol: render_hol(enc, &names),
            })
        })
        .collect();

    // Render each theorem conclusion, folding definition instances.
    let mut terms = HashMap::with_capacity(decls.len());
    let mut surface_nodes = 0usize;
    for d in &decls {
        surface_nodes += tree_size(&d.concl) + d.hyps.iter().map(tree_size).sum::<usize>();
        terms.insert(d.label.clone(), render_hol(&d.concl, &names));
    }

    HolSurface {
        terms,
        defs,
        surface_nodes,
        dag_nodes: cons.len(),
    }
}

/// Compute the pass-1 surface once (off the runtime) and cache it on the session.
async fn ensure_hol(sess: &Arc<MmSession>) {
    if sess.hol.get().is_some() {
        return;
    }
    let s2 = sess.clone();
    if let Ok(surface) = tokio::task::spawn_blocking(move || build_hol_surface(&s2.db)).await {
        let _ = sess.hol.set(surface);
    }
}

/// GET `/api/metamath/session/{hash}/hol` — pass-1 stats + the definitions fold:
/// `{surfaceNodes, dagNodes, dedup, defs:[{name, term}]}`. Triggers pass 1.
pub async fn hol(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    ensure_hol(&sess).await;
    let Some(s) = sess.hol.get() else {
        return (StatusCode::INTERNAL_SERVER_ERROR, "hol surface unavailable").into_response();
    };
    Json(json!({
        "surfaceNodes": s.surface_nodes,
        "dagNodes": s.dag_nodes,
        "dedup": s.surface_nodes as f64 / s.dag_nodes.max(1) as f64,
        "defs": s.defs.iter().map(|d| json!({
            "label": d.label,
            "kind": d.kind,
            "mm": d.mm,
            "hol": d.hol,
        })).collect::<Vec<_>>(),
    }))
    .into_response()
}

/// GET `/api/metamath/session/{hash}/hol/terms` — the whole `label → HOL term`
/// map (pass 1). One fetch; the page caches it for the list/detail. Triggers
/// pass 1.
pub async fn hol_terms(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    ensure_hol(&sess).await;
    let Some(s) = sess.hol.get() else {
        return (StatusCode::INTERNAL_SERVER_ERROR, "hol surface unavailable").into_response();
    };
    Json(&s.terms).into_response()
}

// ---------------------------------------------------------------------------
// POST /api/metamath/db — parse (or reuse) a session
// ---------------------------------------------------------------------------

/// POST `/api/metamath/db?user=<opt>&from=<string>` — body = raw `.mm` source.
/// Computes the content hash; if `(hash, user)` is not already cached, parses the
/// database (off the async runtime) and inserts a new [`MmSession`], recording
/// `from` as the session's `origin` (provenance). On a cache-hit the existing
/// origin is kept, but back-filled if it was `None` and `from` is now supplied.
/// Returns `{"file": <hash>, "total": N, "origin": <string|null>}`.
pub async fn create_db(
    State(state): State<AppState>,
    Query(q): Query<CreateQ>,
    body: axum::body::Bytes,
) -> Response {
    let hash = O256::blob(&body).to_string();
    let key: SessionKey = (hash.clone(), q.user.clone());

    if let Some(sess) = state.mm.lock().unwrap().get(&key).cloned() {
        // Cache-hit: keep the existing origin, but fill it if it was unknown.
        let mut origin = sess.origin.write().unwrap();
        if origin.is_none() {
            if let Some(from) = &q.from {
                *origin = Some(from.clone());
            }
        }
        return Json(json!({ "file": hash, "total": sess.total, "origin": *origin }))
            .into_response();
    }

    // Parse off the async runtime (set.mm parse is ~1s).
    let source = match String::from_utf8(body.to_vec()) {
        Ok(s) => s,
        Err(_) => return (StatusCode::BAD_REQUEST, "source is not valid UTF-8").into_response(),
    };
    let (parsed, symbols) = tokio::task::spawn_blocking(move || {
        let db = covalence_hol::metamath::parse(&source);
        let symbols = symbol_map(&source);
        (db, symbols)
    })
    .await
    .unwrap_or_else(|e| panic!("parse task panicked: {e}"));

    let db = match parsed {
        Ok(db) => db,
        Err(e) => return (StatusCode::BAD_REQUEST, format!("parse error: {e}")).into_response(),
    };

    let total = covalence_hol::metalogic::mm_import::theorem_labels(&db).len();
    // Generous capacity so the per-theorem frame stream rarely overruns a
    // briefly-busy client (a Lagged overrun self-heals via a re-sent snapshot).
    let (status_tx, _rx) = tokio::sync::broadcast::channel::<String>(16384);
    let origin = q.from.clone();
    let session = Arc::new(MmSession {
        db: Arc::new(db),
        total,
        origin: RwLock::new(origin.clone()),
        graph: OnceLock::new(),
        results: RwLock::new(HashMap::new()),
        status_tx,
        proving: AtomicBool::new(false),
        symbols,
        hol: OnceLock::new(),
    });

    state.mm.lock().unwrap().insert(key, session);
    Json(json!({ "file": hash, "total": total, "origin": origin })).into_response()
}

// ---------------------------------------------------------------------------
// GET /api/metamath/db/{hash} — session info / attach-by-hash probe
// ---------------------------------------------------------------------------

/// GET `/api/metamath/db/{hash}?user=<opt>` — lightweight session metadata
/// (distinct from `/graph`, which is the bulk data). Used by the page to probe
/// whether a hash is already loaded on the server *without downloading*:
/// `{"file", "total", "origin", "proving": bool, "proved": N, "errors": N}`.
/// 404 if no such session.
pub async fn db_info(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    let (proved, errors) = count_results(&sess);
    Json(json!({
        "file": hash,
        "total": sess.total,
        "origin": *sess.origin.read().unwrap(),
        "proving": sess.proving.load(Ordering::SeqCst),
        "proved": proved,
        "errors": errors,
    }))
    .into_response()
}

/// Count `(proved, errors)` from a session's `results` cache (`ok == true` is a
/// proved theorem, `ok == false` an import error).
fn count_results(sess: &MmSession) -> (usize, usize) {
    let results = sess.results.read().unwrap();
    let mut proved = 0;
    let mut errors = 0;
    for v in results.values() {
        match v.get("ok").and_then(Value::as_bool) {
            Some(true) => proved += 1,
            _ => errors += 1,
        }
    }
    (proved, errors)
}

// ---------------------------------------------------------------------------
// GET /api/metamath/stats — instantaneous server metrics (RAM etc.)
// ---------------------------------------------------------------------------

/// GET `/api/metamath/stats` — a point sample of process/server metrics:
/// `{rssBytes, peakRssBytes, sessions, theoremsCached, uptimeSecs}`. The page
/// polls this on an interval and plots the time series client-side (so the
/// server stays stateless). `rssBytes`/`peakRssBytes` are `null` off Linux.
pub async fn server_stats(State(state): State<AppState>) -> Response {
    let (rss, peak) = read_proc_rss();
    let sessions = state.mm.lock().unwrap();
    let n = sessions.len();
    let cached: usize = sessions
        .values()
        .map(|s| s.results.read().unwrap().len())
        .sum();
    drop(sessions);
    Json(json!({
        "rssBytes": rss,
        "peakRssBytes": peak,
        "sessions": n,
        "theoremsCached": cached,
        "uptimeSecs": state.started.elapsed().as_secs(),
    }))
    .into_response()
}

/// Resident-set / peak-RSS in bytes, read from `/proc/self/status` (Linux).
/// Returns `(None, None)` elsewhere or on read failure.
#[cfg(target_os = "linux")]
fn read_proc_rss() -> (Option<u64>, Option<u64>) {
    let Ok(s) = std::fs::read_to_string("/proc/self/status") else {
        return (None, None);
    };
    let parse_kb = |v: &str| v.split_whitespace().next()?.parse::<u64>().ok().map(|kb| kb * 1024);
    let mut rss = None;
    let mut peak = None;
    for line in s.lines() {
        if let Some(v) = line.strip_prefix("VmRSS:") {
            rss = parse_kb(v);
        } else if let Some(v) = line.strip_prefix("VmHWM:") {
            peak = parse_kb(v);
        }
    }
    (rss, peak)
}

#[cfg(not(target_os = "linux"))]
fn read_proc_rss() -> (Option<u64>, Option<u64>) {
    (None, None)
}

// ---------------------------------------------------------------------------
// GET /api/metamath/dbs — all cached sessions (for the "loaded on server" list)
// ---------------------------------------------------------------------------

/// GET `/api/metamath/dbs` — a JSON array of every cached session:
/// `[{file, user, origin, total, proved}]`. Powers the page's "loaded on
/// server" picker so a previously-imported set.mm can be reattached without
/// re-downloading 48 MB.
pub async fn list_dbs(State(state): State<AppState>) -> Response {
    let sessions = state.mm.lock().unwrap();
    let mut out: Vec<Value> = sessions
        .iter()
        .map(|((hash, user), sess)| {
            let (proved, _errors) = count_results(sess);
            json!({
                "file": hash,
                "user": user,
                "origin": *sess.origin.read().unwrap(),
                "total": sess.total,
                "proved": proved,
            })
        })
        .collect();
    // Stable-ish ordering for the UI (by origin then hash).
    out.sort_by(|a, b| {
        let ka = a.get("origin").and_then(Value::as_str).unwrap_or("");
        let kb = b.get("origin").and_then(Value::as_str).unwrap_or("");
        ka.cmp(kb)
            .then_with(|| a.get("file").and_then(Value::as_str).cmp(&b.get("file").and_then(Value::as_str)))
    });
    Json(out).into_response()
}

// ---------------------------------------------------------------------------
// GET /api/metamath/db/{hash}/graph — the cached static graph
// ---------------------------------------------------------------------------

/// GET `/api/metamath/db/{hash}/graph?user=<opt>` — the whole static
/// declaration graph: `{"total": N, "theorems": [{label, mm, deps}]}`. Computed
/// once into the session's `graph` `OnceLock`, then served verbatim. The graph
/// is immutable for a given session, so it is served with strong-caching
/// headers (`ETag` = the file hash, long `Cache-Control`).
pub async fn graph(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };

    let body = sess
        .graph
        .get_or_init(|| {
            let labels = covalence_hol::metalogic::mm_import::theorem_labels(&sess.db);
            let theorems: Vec<Value> = labels.iter().map(|l| graph_item(&sess.db, l)).collect();
            json!({ "total": sess.total, "theorems": theorems }).to_string()
        })
        .clone();

    let etag = format!("\"{hash}\"");
    (
        [
            (header::CONTENT_TYPE, "application/json".to_string()),
            (header::CACHE_CONTROL, "public, max-age=31536000, immutable".to_string()),
            (header::ETAG, etag),
        ],
        body,
    )
        .into_response()
}

// ---------------------------------------------------------------------------
// GET /api/metamath/db/{hash}/theorem/{name} — one theorem's full detail
// ---------------------------------------------------------------------------

/// GET `/api/metamath/db/{hash}/theorem/{name}?user=<opt>` — full per-theorem
/// detail: `{label, mm, ess, deps, proof, status, ok?, hyps?, genuine?,
/// holPreview?, importMs?, error?}`. Static fields render from the db; dynamic
/// fields come from the `results` cache (`status:"pending"` if not yet proved).
pub async fn theorem(
    State(state): State<AppState>,
    Path((hash, name)): Path<(String, String)>,
    Query(q): Query<UserQ>,
) -> Response {
    use covalence_metamath::database::Statement;

    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };

    let Some(Statement::Assert(a)) = sess.db.statement_by_label(&name) else {
        return (StatusCode::NOT_FOUND, "no such theorem").into_response();
    };
    if a.conclusion.typecode() != "|-" {
        return (StatusCode::NOT_FOUND, "not a logical theorem").into_response();
    }

    let ess: Vec<String> = a.frame.essentials.iter().map(|h| h.expr.render()).collect();
    let mut out = json!({
        "label": name,
        "mm": a.conclusion.render(),
        "ess": ess,
        "deps": render_deps(&sess.db, a),
        "proof": render_proof(a),
        "status": "pending",
    });
    // The HOL term. Prefer the cached pass-1 surface (folded to definition
    // names); but if it is not built yet (a big database still interning), encode
    // *just this one* conclusion on demand — `Parser::new` + one `encode_expr` is
    // a few ms — so the term shows immediately instead of "interning…".
    let hol_term = match sess.hol.get() {
        Some(s) => s.terms.get(&name).cloned(),
        None => {
            use covalence_hol::metalogic::mm_database::Parser;
            let parser = Parser::new(&sess.db);
            parser
                .encode_expr(&a.conclusion)
                .ok()
                .map(|enc| render_hol(&enc, &HashMap::new()))
        }
    };
    if let (Value::Object(o), Some(t)) = (&mut out, hol_term) {
        o.insert("holTerm".into(), Value::String(t));
    }

    if let Some(res) = sess.results.read().unwrap().get(&name) {
        if let (Value::Object(base), Value::Object(extra)) = (&mut out, res) {
            for (k, v) in extra {
                base.insert(k.clone(), v.clone());
            }
        }
    }

    Json(out).into_response()
}

// ---------------------------------------------------------------------------
// POST /api/metamath/db/{hash}/prove — kick off the parallel import
// ---------------------------------------------------------------------------

/// POST `/api/metamath/db/{hash}/prove?user=<opt>&workers=N` — start the
/// parallel kernel import (idempotent via a CAS on `proving`). Returns 202
/// `{"started": true|false}`. `workers` 0/absent = auto. Results are stored in
/// the session's `results` cache and broadcast over the status WS.
pub async fn prove(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<ProveQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };

    // CAS: only the first caller wins and spawns the prove thread.
    if sess
        .proving
        .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
        .is_err()
    {
        return (StatusCode::ACCEPTED, Json(json!({ "started": false }))).into_response();
    }

    let workers = q.workers.unwrap_or(0);
    let sess2 = sess.clone();
    std::thread::spawn(move || prove_worker(sess2, workers));

    (StatusCode::ACCEPTED, Json(json!({ "started": true }))).into_response()
}

/// The blocking prove worker: derive every logical theorem in parallel, storing
/// each result in `results` and broadcasting `proving`/`proved`/`done` frames.
fn prove_worker(sess: Arc<MmSession>, workers: usize) {
    use covalence_hol::metalogic::mm_import::import_theorems_parallel;

    let started = std::time::Instant::now();
    let n_ok = AtomicUsize::new(0);
    let grand_total = AtomicUsize::new(0);
    let tx = &sess.status_tx;

    import_theorems_parallel(
        &sess.db,
        workers,
        |total| {
            grand_total.store(total, Ordering::Relaxed);
        },
        |label| {
            let _ = tx.send(json!({ "type": "proving", "label": label }).to_string());
        },
        |done, total, label, result, elapsed| {
            let import_ms = elapsed.as_micros() as f64 / 1000.0;
            let res_json = proved_result(result, import_ms);
            if result.is_ok() {
                n_ok.fetch_add(1, Ordering::Relaxed);
            }
            // Store the result for late REST GETs / WS snapshots.
            sess.results
                .write()
                .unwrap()
                .insert(label.to_string(), res_json.clone());
            // Broadcast the live frame.
            let mut frame = json!({
                "type": "proved",
                "done": done,
                "total": total,
                "label": label,
            });
            if let (Value::Object(f), Value::Object(r)) = (&mut frame, &res_json) {
                for (k, v) in r {
                    if k == "status" {
                        continue; // the frame `type` already carries this
                    }
                    f.insert(k.clone(), v.clone());
                }
            }
            let _ = tx.send(frame.to_string());
        },
    );

    let _ = tx.send(
        json!({
            "type": "done",
            "ok": n_ok.load(Ordering::Relaxed),
            "total": grand_total.load(Ordering::Relaxed),
            "elapsedMs": started.elapsed().as_millis() as u64,
        })
        .to_string(),
    );
}

// ---------------------------------------------------------------------------
// WS /api/metamath/db/{hash}/status — thin live status forwarder
// ---------------------------------------------------------------------------

/// WS `/api/metamath/db/{hash}/status?user=<opt>` — on connect, send a snapshot
/// of already-proved results (so a late joiner is current), then subscribe to
/// the session's broadcast channel and forward each frame verbatim.
pub async fn status_ws(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
    ws: WebSocketUpgrade,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    ws.on_upgrade(move |socket| handle_status_ws(socket, sess))
}

async fn handle_status_ws(mut socket: WebSocket, sess: Arc<MmSession>) {
    // Subscribe BEFORE building the snapshot, so no frame between the snapshot
    // and the first forwarded message is lost.
    let mut rx = sess.status_tx.subscribe();

    // A `snapshot` frame: label+ok for every already-proved theorem. Built from
    // the authoritative `results` cache, so it fully re-syncs the client's
    // statuses — used both on connect and to *recover from a broadcast lag*.
    let snapshot = || {
        let results = sess.results.read().unwrap();
        let entries: Vec<Value> = results
            .iter()
            .map(|(label, v)| json!({ "label": label, "ok": v.get("ok").and_then(Value::as_bool).unwrap_or(false) }))
            .collect();
        json!({ "type": "snapshot", "total": sess.total, "results": entries }).to_string()
    };
    if socket.send(Message::Text(snapshot().into())).await.is_err() {
        return;
    }

    loop {
        match rx.recv().await {
            Ok(msg) => {
                if socket.send(Message::Text(msg.into())).await.is_err() {
                    break;
                }
            }
            // Lagged: the client briefly fell behind and the bounded broadcast
            // ring dropped frames. Re-send a full snapshot so no theorem is left
            // stuck (the `results` cache is authoritative), then keep streaming.
            Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => {
                if socket.send(Message::Text(snapshot().into())).await.is_err() {
                    break;
                }
            }
            Err(tokio::sync::broadcast::error::RecvError::Closed) => break,
        }
    }
    let _ = socket.send(Message::Close(None)).await;
}
