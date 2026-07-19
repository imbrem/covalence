//! TEMPORARY / THROWAWAY DEMO SURFACE — the `/metamath` web page's backend.
//!
//! Clean REST for data + a thin WebSocket for live status only. The server is
//! **stateful**: a `.mm` source is parsed once into a cached `MmSession`
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
///   - `POST /upload`                              — cache a `.mm` source → `{file,total,origin}`
///   - `GET  /sessions`                            — list cached sessions
///   - `GET  /stats`                               — instantaneous server metrics
///   - `GET  /session/{hash}`                      — session info / attach-by-hash probe
///   - `GET  /session/{hash}/graph`                — the static declaration graph
///   - `GET  /session/{hash}/symbols`              — the `$t` token → Unicode map
///   - `GET  /session/{hash}/hol`                  — the interned HOL surface (pass 1)
///   - `GET  /session/{hash}/hol/terms`            — `label → HOL term` map
///   - `GET  /session/{hash}/theorem/{name}`       — one theorem's full detail
///   - `GET  /session/{hash}/theorem/{name}/steps` — the verifying proof trace
///   - `GET  /session/{hash}/search`               — assertion search (label + statement)
///   - `POST /session/{hash}/apply`                — one backward step against an assertion
///   - `POST /session/{hash}/verify`               — check a user-assembled proof
///   - `POST /session/{hash}/prove`                — start the parallel prove
///   - `GET  /session/{hash}/status`               — live status WebSocket
///
/// The last four are the **proof-assistant** surface (a LAMP-style step/search/
/// apply/verify loop). `apply` and `verify` are the only places a client can
/// learn that something is proved: both run the real `covalence-metamath`
/// checker, and neither has an admit path.
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
        .route("/session/{hash}/theorem/{name}/steps", get(theorem_steps))
        .route("/session/{hash}/search", get(search))
        .route("/session/{hash}/apply", post(apply))
        .route("/session/{hash}/verify", post(verify_proof))
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
    pub db: Arc<covalence_init::metamath::Database>,
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
    /// CAS guard so the pass-1 interner is launched at most once.
    pub interning: AtomicBool,
    /// Live pass-1 progress (theorems interned, total, distinct DAG nodes so
    /// far) — read by `/hol` and broadcast as `interning` status frames.
    pub intern_done: AtomicUsize,
    pub intern_total: AtomicUsize,
    pub intern_nodes: AtomicUsize,
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
            format!(
                "( {} ) {}",
                labels.join(" "),
                String::from_utf8_lossy(letters)
            )
        }
        None => String::new(),
    }
}

/// The deduped (first-seen order) logical (`|-`) dependency list of a proof:
/// `[{label, kind}]` with kind axiom/def/thm (thm if the dep has its own proof,
/// else `df*` → def, else axiom).
fn render_deps(
    db: &covalence_init::metamath::Database,
    a: &covalence_metamath::database::Assertion,
) -> Vec<Value> {
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
fn graph_item(db: &covalence_init::metamath::Database, label: &str) -> Value {
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
fn proved_result(result: &covalence_core::Result<covalence_init::Thm>, import_ms: f64) -> Value {
    match result {
        Ok(thm) => {
            let full = format!("{}", thm.concl());
            let hol_preview: String = full.chars().take(400).collect();
            json!({
                "status": "proved",
                "ok": true,
                "hyps": thm.hyps().len(),
                // Every kernel Thm is oracle-free since the observer system was
                // deleted (toHOL purge); kept as a hardcoded field for JSON API
                // compatibility until an admits-manifest provenance story lands.
                "genuine": true,
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
fn build_hol_surface(
    db: &covalence_init::metamath::Database,
    progress: &dyn Fn(usize, usize, usize),
) -> HolSurface {
    use covalence_init::metalogic::mm_database::Parser;
    use covalence_init::metalogic::mm_import::theorem_labels;
    use covalence_metamath::database::Statement;

    let parser = Parser::new(db);
    let thm_labels = theorem_labels(db);
    let total = thm_labels.len();
    let mut cons = covalence_core::HashCons::new();

    // Interned theorem conclusions (pass-1 proper), reporting progress as the
    // shared DAG grows (every ~512 theorems, plus once at the end).
    struct Decl {
        label: String,
        concl: Term,
        hyps: Vec<Term>,
    }
    let mut decls: Vec<Decl> = Vec::with_capacity(total);
    for (i, label) in thm_labels.iter().enumerate() {
        if let Some(Statement::Assert(a)) = db.statement_by_label(label)
            && let Ok(c) = parser.encode_expr(&a.conclusion)
        {
            let concl = c.cons_with(&mut cons);
            let hyps: Vec<Term> = a
                .frame
                .essentials
                .iter()
                .filter_map(|h| {
                    parser
                        .encode_expr(&h.expr)
                        .ok()
                        .map(|e| e.cons_with(&mut cons))
                })
                .collect();
            decls.push(Decl {
                label: label.clone(),
                concl,
                hyps,
            });
        }
        if i % 512 == 0 {
            progress(i, total, cons.len());
        }
    }
    progress(total, total, cons.len());

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

/// Launch pass 1 in the background (at most once per session). It interns the
/// whole surface on one thread, broadcasting `interning` progress frames and a
/// final `interned` frame over the session's status WS, and caches the result in
/// `sess.hol`. Returns immediately. Idempotent: a no-op once started/done.
fn start_hol(sess: Arc<MmSession>) {
    if sess.hol.get().is_some() {
        return;
    }
    if sess
        .interning
        .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
        .is_err()
    {
        return; // already running
    }
    std::thread::spawn(move || {
        let tx = sess.status_tx.clone();
        let surface = build_hol_surface(&sess.db, &|done, total, nodes| {
            sess.intern_done.store(done, Ordering::Relaxed);
            sess.intern_total.store(total, Ordering::Relaxed);
            sess.intern_nodes.store(nodes, Ordering::Relaxed);
            let _ = tx.send(
                json!({ "type": "interning", "done": done, "total": total, "nodes": nodes })
                    .to_string(),
            );
        });
        let frame = json!({
            "type": "interned",
            "surfaceNodes": surface.surface_nodes,
            "dagNodes": surface.dag_nodes,
            "dedup": surface.surface_nodes as f64 / surface.dag_nodes.max(1) as f64,
            "defs": surface.defs.len(),
        });
        let _ = sess.hol.set(surface);
        let _ = tx.send(frame.to_string());
    });
}

/// GET `/api/metamath/session/{hash}/hol` — **non-blocking**: triggers pass 1 in
/// the background and returns either the finished surface
/// (`{ready:true, surfaceNodes, dagNodes, dedup, defs:[…]}`) or the current
/// interning progress (`{ready:false, done, total, nodes}`). Live updates also
/// stream as `interning`/`interned` frames on the status WS.
pub async fn hol(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    start_hol(sess.clone());
    match sess.hol.get() {
        Some(s) => Json(json!({
            "ready": true,
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
        .into_response(),
        None => Json(json!({
            "ready": false,
            "done": sess.intern_done.load(Ordering::Relaxed),
            "total": sess.intern_total.load(Ordering::Relaxed),
            "nodes": sess.intern_nodes.load(Ordering::Relaxed),
        }))
        .into_response(),
    }
}

/// GET `/api/metamath/session/{hash}/hol/terms` — the whole `label → HOL term`
/// map once pass 1 is done (else `{}`; the page falls back to the per-theorem
/// on-demand encoding in the meantime). Triggers pass 1.
pub async fn hol_terms(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    start_hol(sess.clone());
    match sess.hol.get() {
        Some(s) => Json(&s.terms).into_response(),
        None => Json(json!({})).into_response(),
    }
}

// ---------------------------------------------------------------------------
// POST /api/metamath/upload — parse (or reuse) a session
// ---------------------------------------------------------------------------

/// POST `/api/metamath/upload?user=<opt>&from=<string>` — body = raw `.mm` source.
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
        if origin.is_none()
            && let Some(from) = &q.from
        {
            *origin = Some(from.clone());
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
        let db = covalence_init::metamath::parse(&source);
        let symbols = symbol_map(&source);
        (db, symbols)
    })
    .await
    .unwrap_or_else(|e| panic!("parse task panicked: {e}"));

    let db = match parsed {
        Ok(db) => db,
        Err(e) => return (StatusCode::BAD_REQUEST, format!("parse error: {e}")).into_response(),
    };

    let total = covalence_init::metalogic::mm_import::theorem_labels(&db).len();
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
        interning: AtomicBool::new(false),
        intern_done: AtomicUsize::new(0),
        intern_total: AtomicUsize::new(0),
        intern_nodes: AtomicUsize::new(0),
    });

    state.mm.lock().unwrap().insert(key, session);
    Json(json!({ "file": hash, "total": total, "origin": origin })).into_response()
}

// ---------------------------------------------------------------------------
// GET /api/metamath/session/{hash} — session info / attach-by-hash probe
// ---------------------------------------------------------------------------

/// GET `/api/metamath/session/{hash}?user=<opt>` — lightweight session metadata
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
    let parse_kb = |v: &str| {
        v.split_whitespace()
            .next()?
            .parse::<u64>()
            .ok()
            .map(|kb| kb * 1024)
    };
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
// GET /api/metamath/sessions — all cached sessions (for the "loaded on server" list)
// ---------------------------------------------------------------------------

/// GET `/api/metamath/sessions` — a JSON array of every cached session:
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
        ka.cmp(kb).then_with(|| {
            a.get("file")
                .and_then(Value::as_str)
                .cmp(&b.get("file").and_then(Value::as_str))
        })
    });
    Json(out).into_response()
}

// ---------------------------------------------------------------------------
// GET /api/metamath/session/{hash}/graph — the cached static graph
// ---------------------------------------------------------------------------

/// GET `/api/metamath/session/{hash}/graph?user=<opt>` — the whole static
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
            let labels = covalence_init::metalogic::mm_import::theorem_labels(&sess.db);
            let theorems: Vec<Value> = labels.iter().map(|l| graph_item(&sess.db, l)).collect();
            json!({ "total": sess.total, "theorems": theorems }).to_string()
        })
        .clone();

    let etag = format!("\"{hash}\"");
    (
        [
            (header::CONTENT_TYPE, "application/json".to_string()),
            (
                header::CACHE_CONTROL,
                "public, max-age=31536000, immutable".to_string(),
            ),
            (header::ETAG, etag),
        ],
        body,
    )
        .into_response()
}

// ---------------------------------------------------------------------------
// GET /api/metamath/session/{hash}/theorem/{name} — one theorem's full detail
// ---------------------------------------------------------------------------

/// GET `/api/metamath/session/{hash}/theorem/{name}?user=<opt>` — full per-theorem
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
            use covalence_init::metalogic::mm_database::Parser;
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

    if let Some(res) = sess.results.read().unwrap().get(&name)
        && let (Value::Object(base), Value::Object(extra)) = (&mut out, res)
    {
        for (k, v) in extra {
            base.insert(k.clone(), v.clone());
        }
    }

    Json(out).into_response()
}

// ---------------------------------------------------------------------------
// The proof-assistant surface: steps / search / apply / verify
// ---------------------------------------------------------------------------

/// Classify an assertion for the UI: `thm` if it has a proof, else `def` for a
/// `df*` definition, else `axiom`. (Shared with [`render_deps`]' rule so the
/// search pane and the dependency list agree.)
fn assertion_kind(a: &covalence_metamath::database::Assertion) -> &'static str {
    if a.proof.is_some() {
        "thm"
    } else if a.label.starts_with("df") {
        "def"
    } else {
        "axiom"
    }
}

/// Render an expression into an existing buffer (clearing it first), so a scan
/// over the whole database reuses one allocation instead of one per assertion.
fn render_into(e: &covalence_metamath::Expr, buf: &mut String) {
    buf.clear();
    buf.push_str(e.typecode());
    for s in e.body() {
        buf.push(' ');
        buf.push_str(s.as_str());
    }
}

/// One [`covalence_metamath::TraceStep`] as wire JSON. `args`/`subst`/`hyps` are
/// present only on `assertion` steps; `heapIndex` only on `heapRef`.
fn trace_step_json(s: &covalence_metamath::TraceStep) -> Value {
    let mut o = json!({
        "i": s.index,
        "label": s.label,
        "kind": s.kind.tag(),
        "expr": s.expr,
        "stackDepth": s.stack_depth,
    });
    let Value::Object(m) = &mut o else {
        unreachable!("json! built an object")
    };
    if s.kind == covalence_metamath::TraceKind::Assertion {
        m.insert("args".into(), json!(s.args));
        m.insert(
            "subst".into(),
            Value::Array(
                s.subst
                    .iter()
                    .map(|(v, e)| json!({ "var": v, "expr": e }))
                    .collect(),
            ),
        );
        m.insert(
            "hyps".into(),
            Value::Array(
                s.hyps
                    .iter()
                    .map(|h| json!({ "label": h.label, "before": h.before, "after": h.after }))
                    .collect(),
            ),
        );
    }
    if let Some(idx) = s.heap_index {
        m.insert("heapIndex".into(), json!(idx));
    }
    o
}

/// GET `/api/metamath/session/{hash}/theorem/{name}/steps?user=<opt>` — the
/// theorem's proof as a **verifying replay trace**:
/// `{label, kind, conclusion, axiom, steps:[{i,label,kind,expr,stackDepth,…}]}`.
///
/// The trace comes from `covalence_metamath::proof_trace`, i.e. from actually
/// re-running the checker: every reported substitution is the one the verifier
/// derived, not a reconstruction. A theorem whose proof does not verify returns
/// `{ok:false, error}` with the checker's message rather than a partial trace.
/// `$a` axioms have no proof and report `axiom:true` with an empty step list.
/// 404 on an unknown session or a label that is not an assertion.
pub async fn theorem_steps(
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

    match covalence_metamath::proof_trace(&sess.db, a) {
        Ok(steps) => Json(json!({
            "ok": true,
            "label": name,
            "kind": assertion_kind(a),
            "axiom": a.proof.is_none(),
            "conclusion": a.conclusion.render(),
            "hyps": a.frame.essentials.iter()
                .map(|h| json!({ "label": h.label, "expr": h.expr.render() }))
                .collect::<Vec<_>>(),
            "steps": steps.iter().map(trace_step_json).collect::<Vec<_>>(),
        }))
        .into_response(),
        // The proof is in the database but does not check out. Say so — never
        // serve a half-trace that could read as a valid proof.
        Err(e) => Json(json!({
            "ok": false,
            "label": name,
            "error": e.to_string(),
        }))
        .into_response(),
    }
}

/// `?user=<opt>&q=<needle>&limit=N` for the search endpoint.
#[derive(Deserialize, Default)]
pub struct SearchQ {
    pub user: Option<String>,
    pub q: Option<String>,
    pub limit: Option<usize>,
}

/// Hard cap on `/search` results, whatever `limit` asks for.
const SEARCH_LIMIT_MAX: usize = 200;

/// Case-insensitive substring test against an already-lowercased `needle`,
/// without allocating. Case folding is ASCII-only: Metamath labels and math
/// symbols are ASCII by construction, so a non-ASCII byte simply compares
/// exactly, which is the behaviour we want for typeset tokens.
fn contains_ignore_case(haystack: &str, needle: &str) -> bool {
    if needle.is_empty() {
        return true;
    }
    let (h, n) = (haystack.as_bytes(), needle.as_bytes());
    if h.len() < n.len() {
        return false;
    }
    // `eq_ignore_ascii_case` folds only ASCII letters, so non-ASCII bytes are
    // compared exactly — no allocation, and no lossy Unicode folding.
    h.windows(n.len()).any(|w| w.eq_ignore_ascii_case(n))
}

/// GET `/api/metamath/session/{hash}/search?q=&limit=&user=` — assertion search
/// for the "find a theorem to apply" pane. Case-insensitive substring match on
/// the label **or** on the rendered statement; returns
/// `{q, total, truncated, results:[{label, kind, mm, hypCount}]}` in database
/// order. `limit` defaults to 50 and is capped at [`SEARCH_LIMIT_MAX`]; an empty
/// `q` returns the first page of the database.
///
/// A linear scan with an early exit at the limit. Statements render into one
/// reused buffer and are matched in place, so a query allocates per *result*,
/// not per assertion.
///
/// Measured on `set.mm` (~47k assertions), release build: **~25 ms** for the
/// worst case (a needle that matches nothing, so the scan runs to the end) and
/// **<1 ms** for a typical query that fills its page early and exits. A debug
/// build is roughly 4× slower (~105 ms worst case).
pub async fn search(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<SearchQ>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    let needle = q.q.unwrap_or_default().to_lowercase();
    let limit = q.limit.unwrap_or(50).min(SEARCH_LIMIT_MAX);

    let mut results: Vec<Value> = Vec::new();
    let mut buf = String::new();
    let mut truncated = false;
    for a in sess.db.assertions() {
        if results.len() >= limit {
            truncated = true;
            break;
        }
        // The statement is needed either way — to match against, and to return
        // on a hit — so render first, then test label before statement.
        render_into(&a.conclusion, &mut buf);
        if !needle.is_empty()
            && !contains_ignore_case(&a.label, &needle)
            && !contains_ignore_case(&buf, &needle)
        {
            continue;
        }
        results.push(json!({
            "label": a.label,
            "kind": assertion_kind(a),
            "mm": buf,
            "hypCount": a.frame.essentials.len(),
        }));
    }

    Json(json!({
        "q": needle,
        "total": results.len(),
        "truncated": truncated,
        "results": results,
    }))
    .into_response()
}

// PERF(cov:server.mm.search-linear-scan, minor): `/search` re-renders every
// assertion per request. Measured on set.mm (~47k assertions): ~25 ms release /
// ~105 ms debug for a needle that matches nothing and so scans to the end;
// sub-millisecond when the page fills early. Fine for a click-to-search pane,
// but a debounced type-ahead over set.mm will feel the worst case — a prebuilt
// per-session rendered-statement index is the fix.

/// Parse a rendered statement (`"|- ( ph -> ph )"`) into an [`Expr`] against the
/// database's symbol table. Every token must be a declared symbol, so a typo
/// fails here rather than silently becoming an unmatchable goal.
fn parse_goal(
    db: &covalence_init::metamath::Database,
    text: &str,
) -> Result<covalence_metamath::Expr, String> {
    let toks: Vec<&str> = text.split_whitespace().collect();
    let Some((tc, body)) = toks.split_first() else {
        return Err("goal is empty".into());
    };
    for t in &toks {
        if !db.is_symbol(t) {
            return Err(format!("`{t}` is not a symbol of this database"));
        }
    }
    if db.is_variable(tc) {
        return Err(format!("`{tc}` is a variable, not a typecode"));
    }
    Ok(covalence_metamath::Expr::new(
        *tc,
        body.iter().map(|s| (*s).into()).collect(),
    ))
}

/// POST `/api/metamath/session/{hash}/apply?user=<opt>` body
/// `{"goal": "<rendered statement>", "label": "<assertion>"}`.
#[derive(Deserialize)]
pub struct ApplyReq {
    pub goal: String,
    pub label: String,
}

/// POST `/api/metamath/session/{hash}/apply` — **one backward step**: match
/// `goal` against `label`'s conclusion and report what remains to prove.
///
/// On success: `{ok:true, label, kind, goal, subst:[{var,expr}],
/// subgoals:[{label, expr}], floats:[{var, typecode, expr|null}], unsolved:[var]}`
/// — `subgoals` are `label`'s essential hypotheses under the substitution (what
/// you must now prove), `floats` its mandatory floating hypotheses, and
/// `unsolved` the frame variables the goal does not determine (they occur only
/// in the hypotheses, so their `expr` is `null` and the corresponding subgoals
/// still mention them).
///
/// On a non-match: HTTP 200 with `{ok:false, error}`, following the
/// `/api/lisp` convention — non-2xx is reserved for session/route problems.
///
/// The returned substitution is guaranteed to rebuild the goal exactly (see
/// `covalence_metamath::match_conclusion`), but it is a *suggestion*, not a
/// proof: nothing here is proved until `/verify` replays a real proof.
pub async fn apply(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
    Json(req): Json<ApplyReq>,
) -> Response {
    use covalence_metamath::database::Statement;
    use covalence_metamath::{apply_subst, match_conclusion};

    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    let Some(Statement::Assert(target)) = sess.db.statement_by_label(&req.label) else {
        return Json(json!({
            "ok": false,
            "error": format!("`{}` is not an assertion of this database", req.label),
        }))
        .into_response();
    };
    let goal = match parse_goal(&sess.db, &req.goal) {
        Ok(g) => g,
        Err(e) => return Json(json!({ "ok": false, "error": e })).into_response(),
    };

    let Some(subst) = match_conclusion(&sess.db, target, &goal) else {
        return Json(json!({
            "ok": false,
            "error": format!(
                "`{}` does not match the goal (its conclusion is `{}`)",
                req.label,
                target.conclusion.render(),
            ),
        }))
        .into_response();
    };

    let render_body = |body: &[covalence_metamath::Symbol]| {
        body.iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join(" ")
    };
    let floats: Vec<Value> = target
        .frame
        .floats
        .iter()
        .map(|f| {
            json!({
                "var": f.var,
                "typecode": f.typecode,
                "expr": subst.get(&f.var).map(|b| render_body(b)),
            })
        })
        .collect();
    let unsolved: Vec<&str> = target
        .frame
        .floats
        .iter()
        .filter(|f| !subst.contains_key(&f.var))
        .map(|f| f.var.as_str())
        .collect();

    Json(json!({
        "ok": true,
        "label": req.label,
        "kind": assertion_kind(target),
        "goal": goal.render(),
        "subst": subst.iter()
            .map(|(v, b)| json!({ "var": v, "expr": render_body(b) }))
            .collect::<Vec<_>>(),
        "subgoals": target.frame.essentials.iter()
            .map(|h| json!({
                "label": h.label,
                "expr": apply_subst(&h.expr, &subst).render(),
            }))
            .collect::<Vec<_>>(),
        "floats": floats,
        "unsolved": unsolved,
    }))
    .into_response()
}

/// POST `/api/metamath/session/{hash}/verify?user=<opt>` body
/// `{"steps": ["label", …], "goal": "<rendered statement>", "theorem": "<opt>"}`.
#[derive(Deserialize)]
pub struct VerifyReq {
    pub steps: Vec<String>,
    pub goal: String,
    /// Optional: an existing theorem whose frame this proof is being written in.
    /// Supplying it makes that theorem's `$e` hypotheses citable and its `$d`
    /// declarations available to discharge distinct-variable obligations.
    pub theorem: Option<String>,
}

/// POST `/api/metamath/session/{hash}/verify` — run the **real checker** over a
/// user-assembled normal proof, then **re-derive it in the kernel**. Returns
/// `{ok, error?, conclusion?, steps?, hol?}`.
///
/// This is the honesty anchor of the proof assistant: a client cannot conclude
/// "proved" from its own bookkeeping, only from this endpoint returning
/// `ok:true`. It builds a synthetic `Assertion` carrying `Proof::Normal(steps)`
/// and hands it to `covalence_metamath::proof_trace`, which *is*
/// `verify_assertion` with a recording observer — the same stack discipline,
/// typecode checks, hypothesis checks, and `$d` checks, with no admit path. A
/// proof that does not replay to exactly the stated goal fails.
///
/// **Two independent claims, two fields.** `ok` is the *Metamath* verdict (the
/// Rust stack verifier). `hol` is the *kernel* verdict: the same synthetic
/// assertion replayed through
/// [`covalence_init::metalogic::mm_database::replay_assertion_scoped`], which
/// re-derives every step through the kernel and returns a genuine
/// `E ⊢ Derivable_L' ⌜S⌝`. The Metamath verifier's say-so is **not** trusted for
/// the kernel claim (thin-waist doctrine: *construct*, don't trust) — `hol.ok`
/// is true only when a real `Thm` came back, and the rendered theorem is a
/// projection of that `Thm`'s own term, never a reconstruction of what it ought
/// to have been. `hol.ok:false` with `skipped:true` means the kernel path was
/// not attempted at all.
///
/// Scoping: `$f` floating hypotheses may be cited freely (they only push
/// `typecode var`, and the `$d` machinery guards the rest), but `$e` essential
/// hypotheses are restricted to those of the named `theorem`'s frame. Without
/// that restriction any `$e` anywhere in the database could be cited out of its
/// scope, which would let a "proof" assume an arbitrary premise.
///
/// Failures of the proof itself are HTTP 200 with `ok:false` (the `/api/lisp`
/// convention); non-2xx is reserved for session/route problems.
pub async fn verify_proof(
    State(state): State<AppState>,
    Path(hash): Path<String>,
    Query(q): Query<UserQ>,
    Json(req): Json<VerifyReq>,
) -> Response {
    let Some(sess) = lookup(&state, &hash, &q.user) else {
        return (StatusCode::NOT_FOUND, "no such session").into_response();
    };
    let (conclusion, steps, synthetic) = match check_user_proof(&sess.db, &req) {
        Ok(v) => v,
        Err(e) => return Json(json!({ "ok": false, "error": e })).into_response(),
    };
    let steps_json: Vec<Value> = steps.iter().map(trace_step_json).collect();

    // The Metamath check passed. Now *independently* construct the kernel
    // theorem. This is CPU-bound (term construction + kernel re-checking), so it
    // runs off the async runtime. A join failure (panic/cancel) is reported as a
    // kernel failure, never as a success.
    let db = sess.db.clone();
    let hol = tokio::task::spawn_blocking(move || kernel_derive(&db, &synthetic))
        .await
        .unwrap_or_else(
            |e| json!({ "ok": false, "error": format!("kernel derivation task failed: {e}") }),
        );

    Json(json!({
        "ok": true,
        "conclusion": conclusion,
        "steps": steps_json,
        "hol": hol,
    }))
    .into_response()
}

/// Cap on submitted proof length before the kernel path is attempted. The
/// kernel replay is O(steps × cited-clauses) of real term construction; an
/// interactive proof is tens of steps, so anything past this is a paste of a
/// machine-generated proof and is *reported as skipped* rather than tying up a
/// blocking thread. The Metamath check still runs and is still reported.
const KERNEL_STEP_LIMIT: usize = 4096;

/// Re-derive a verified synthetic assertion **in the kernel** and render the
/// result. Returns the `hol` object of `/verify`'s response.
///
/// Honesty contract, enforced here:
/// - success (`ok:true`) is returned **only** when `replay_assertion_scoped`
///   handed back an actual `Thm`;
/// - `thm`/`statement`/`hyps` are *projections of that `Thm`'s own conclusion
///   and hypothesis terms* (see [`derivable_stmt`]), so they cannot drift from
///   what was proved; if the projection does not recognise the term shape the
///   literal kernel term is printed instead;
/// - the theorem's hypotheses are always rendered — a hypothesis-carrying
///   theorem is never displayed as a closed `⊢ concl`;
/// - "not attempted" is a distinct outcome (`ok:false, skipped:true`) from
///   "attempted and failed" (`ok:false` with `error`).
fn kernel_derive(
    db: &covalence_init::metamath::Database,
    assertion: &covalence_metamath::database::Assertion,
) -> Value {
    let n_steps = match &assertion.proof {
        Some(covalence_metamath::database::Proof::Normal(s)) => s.len(),
        _ => 0,
    };
    if n_steps > KERNEL_STEP_LIMIT {
        return json!({
            "ok": false,
            "skipped": true,
            "reason": format!(
                "proof has {n_steps} steps (limit {KERNEL_STEP_LIMIT}); the kernel \
                 derivation was not attempted"
            ),
        });
    }

    let t0 = std::time::Instant::now();
    let result = covalence_init::metalogic::mm_database::replay_assertion_scoped(db, assertion);
    let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;

    match result {
        Ok(thm) => {
            let hyps: Vec<String> = thm.hyps().iter().map(|h| render_derivable(h)).collect();
            let concl = render_derivable(thm.concl());
            let thm_line = if hyps.is_empty() {
                format!("⊢ {concl}")
            } else {
                format!("{} ⊢ {concl}", hyps.join(", "))
            };
            let raw: String = format!("{}", thm.concl()).chars().take(400).collect();
            json!({
                "ok": true,
                "thm": thm_line,
                "statement": concl,
                "hyps": hyps,
                "hypCount": thm.hyps().len(),
                // The rule set the theorem's `Derivable_L'` ranges over: the `|-`
                // assertions this proof cites, a sub-rule-set of the database's
                // logic (`Derivable_L' ⟹ Derivable_L` by monotonicity).
                "ruleSet": "proof-cited",
                "raw": raw,
                "elapsedMs": elapsed_ms,
            })
        }
        Err(e) => json!({
            "ok": false,
            "error": e.to_string(),
            "elapsedMs": elapsed_ms,
        }),
    }
}

/// Peel a `Derivable_L ⌜A⌝` term — literally `∀d. Closed_L d ⟹ d A` — back to
/// its encoded statement `A`. A pure structural projection of a kernel term:
/// it reads `A` out of the theorem, it does not rebuild it from the request.
/// `None` if the term is not of that shape (then the caller prints the term
/// literally rather than guessing).
fn derivable_stmt(t: &Term) -> Option<&Term> {
    let (_all, abs) = t.as_app()?; // `∀` applied to an abstraction
    let (_ty, body) = abs.as_abs()?; // `Closed_L #0 ⟹ #0 A`
    let (imp_lhs, rhs) = body.as_app()?; // `(⟹ Closed_L #0)` and `#0 A`
    imp_lhs.as_app()?; // the implication must indeed be binary
    let (d, a) = rhs.as_app()?; // `#0 A`
    matches!(d.kind(), TermKind::Bound(0)).then_some(a)
}

/// Render one `Derivable_L ⌜A⌝` term for display, folding the `mm$concat`
/// encoding back to its Metamath token sequence. Falls back to the literal
/// kernel term (truncated) when the shape is unrecognised — an unrecognised
/// term is shown as-is, never as a guessed statement.
fn render_derivable(t: &Term) -> String {
    match derivable_stmt(t) {
        Some(a) => format!("Derivable ⌜{}⌝", render_hol(a, &HashMap::new())),
        None => format!("{t}").chars().take(400).collect(),
    }
}

/// The whole of `/verify`'s Metamath logic, separated from the HTTP shell so it
/// is directly testable: build the synthetic assertion and run the real checker.
/// `Ok((rendered conclusion, trace, the synthetic assertion))` iff the proof
/// genuinely replays to the goal; `Err(message)` for every kind of failure, with
/// no path that reports success without a completed replay.
///
/// The returned assertion is the *same object* the checker accepted — the kernel
/// path ([`kernel_derive`]) replays exactly it, so the two claims are about one
/// proof, and the `$e`-scope rejection above guards both.
#[allow(clippy::type_complexity)]
fn check_user_proof(
    db: &covalence_init::metamath::Database,
    req: &VerifyReq,
) -> Result<
    (
        String,
        Vec<covalence_metamath::TraceStep>,
        covalence_metamath::database::Assertion,
    ),
    String,
> {
    use covalence_metamath::database::{Assertion, Frame, Proof, Statement};

    let goal = parse_goal(db, &req.goal)?;

    // The frame the proof is written in. Without a named theorem the proof gets
    // an empty frame: no citable `$e`, and no `$d` to discharge obligations
    // with — so anything needing either is (correctly) rejected.
    let (frame, scope_disjoints) = match &req.theorem {
        Some(name) => match db.statement_by_label(name) {
            Some(Statement::Assert(a)) => (a.frame.clone(), a.scope_disjoints.clone()),
            _ => return Err(format!("`{name}` is not an assertion of this database")),
        },
        None => (Frame::default(), Vec::new()),
    };

    // Reject out-of-scope `$e` citations before replaying (see the doc comment
    // on `verify_proof`).
    for label in &req.steps {
        if let Some(Statement::Essential(h)) = db.statement_by_label(label)
            && !frame.essentials.iter().any(|e| e.label == h.label)
        {
            return Err(format!(
                "`{label}` is a hypothesis of another theorem and may not be cited here"
            ));
        }
    }

    let synthetic = Assertion {
        label: req.theorem.clone().unwrap_or_else(|| "<goal>".to_string()),
        conclusion: goal,
        frame,
        proof: Some(Proof::Normal(req.steps.clone())),
        scope_disjoints,
    };

    let steps = covalence_metamath::proof_trace(db, &synthetic).map_err(|e| e.to_string())?;
    Ok((synthetic.conclusion.render(), steps, synthetic))
}

// TODO(cov:server.mm.verify-hol-transport, major): `/verify`'s `hol` theorem is
// `Derivable_L' ⌜S⌝` over the *proof-cited* sub-rule-set `L'`, not the whole
// database's `L`. `metalogic::transport_db` discharges `Derivable_L' ⟹
// Derivable_L`; run it (or expose the clause labels of `L'`) so the response can
// state the full-database claim rather than leaving the frontend to say
// "derivable from the rules this proof cites".
//
// TODO(cov:server.mm.verify-hol-cache, minor): every `/verify` rebuilds the
// database `Parser` (O(database size); ~5 ms on set.mm) and recompiles the cited
// clauses. Cache a `Parser` + `ClauseCache` per `MmSession` (both are read-only /
// per-worker) so an interactive step-by-step session pays it once.
//
// TODO(cov:server.mm.proof-session-state, major): `/apply` and `/verify` are
// stateless one-shots — the server keeps no proof tree, so a client assembles the
// step list itself and re-submits it whole. A server-side proof session (goal
// tree, undo, partial proofs) is the next layer.

// ---------------------------------------------------------------------------
// POST /api/metamath/session/{hash}/prove — kick off the parallel import
// ---------------------------------------------------------------------------

/// POST `/api/metamath/session/{hash}/prove?user=<opt>&workers=N` — start the
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

    // Kick off pass 1 (interning) alongside proving — independent work, and the
    // single-threaded interner overlaps the parallel prove rather than idling
    // cores ahead of it.
    start_hol(sess.clone());

    let workers = q.workers.unwrap_or(0);
    let sess2 = sess.clone();
    std::thread::spawn(move || prove_worker(sess2, workers));

    (StatusCode::ACCEPTED, Json(json!({ "started": true }))).into_response()
}

/// The blocking prove worker: derive every logical theorem in parallel, storing
/// each result in `results` and broadcasting `proving`/`proved`/`done` frames.
fn prove_worker(sess: Arc<MmSession>, workers: usize) {
    use covalence_init::metalogic::mm_import::import_theorems_parallel;

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
// WS /api/metamath/session/{hash}/status — thin live status forwarder
// ---------------------------------------------------------------------------

/// WS `/api/metamath/session/{hash}/status?user=<opt>` — on connect, send a snapshot
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The Metamath book's "demo0", minus `th1`'s proof — the proof is what the
    /// tests below submit through `/verify`.
    const DEMO0: &str = "\
        $c 0 + = -> ( ) term wff |- $.\n\
        $v t r s P Q $.\n\
        tt $f term t $.\n\
        tr $f term r $.\n\
        ts $f term s $.\n\
        wp $f wff P $.\n\
        wq $f wff Q $.\n\
        tze $a term 0 $.\n\
        tpl $a term ( t + r ) $.\n\
        weq $a wff t = r $.\n\
        wim $a wff ( P -> Q ) $.\n\
        a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
        a2 $a |- ( t + 0 ) = t $.\n\
        ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
            mp $a |- Q $.\n\
        $}\n\
    ";

    /// `th1`'s proof of `|- t = t`, as the step list a client would assemble.
    const TH1_STEPS: &str = "tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
        tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp";

    fn db() -> covalence_init::metamath::Database {
        covalence_init::metamath::parse(DEMO0).unwrap()
    }

    fn req(steps: &str, goal: &str) -> VerifyReq {
        VerifyReq {
            steps: steps.split_whitespace().map(str::to_string).collect(),
            goal: goal.to_string(),
            theorem: None,
        }
    }

    #[test]
    fn verify_accepts_a_genuine_proof() {
        let (concl, steps, _) = check_user_proof(&db(), &req(TH1_STEPS, "|- t = t"))
            .expect("demo0's own proof of th1 must verify");
        assert_eq!(concl, "|- t = t");
        // The trace is the replay, so it has one step per submitted label.
        assert_eq!(steps.len(), TH1_STEPS.split_whitespace().count());
        assert_eq!(steps.last().unwrap().expr, "|- t = t");
    }

    #[test]
    fn verify_rejects_a_bogus_proof() {
        let db = db();

        // Truncated: leaves residue on the stack instead of one result.
        let e = check_user_proof(&db, &req("tt tze tpl tt weq", "|- t = t")).unwrap_err();
        assert!(!e.is_empty(), "a rejection must explain itself");

        // Empty: proves nothing.
        assert!(check_user_proof(&db, &req("", "|- t = t")).is_err());

        // A real proof, but of a *different* statement than the one claimed.
        // This is the case that matters most: the replay succeeds, and the
        // result-vs-goal check is what must reject it.
        assert!(
            check_user_proof(&db, &req(TH1_STEPS, "|- 0 = 0")).is_err(),
            "a proof of `t = t` must not be accepted as a proof of `0 = 0`"
        );

        // An unknown label is not silently skipped.
        assert!(check_user_proof(&db, &req("tt bogus", "|- t = t")).is_err());

        // A goal token that is not a symbol of this database.
        assert!(check_user_proof(&db, &req(TH1_STEPS, "|- t ~ t")).is_err());
    }

    #[test]
    fn verify_refuses_out_of_scope_hypotheses() {
        // `min` is `mp`'s essential hypothesis `|- P`. Citing it without being
        // inside `mp`'s frame would assume an arbitrary premise, so it must be
        // refused — with and without a named theorem.
        let db = db();
        assert!(check_user_proof(&db, &req("wp min", "|- P")).is_err());

        let mut r = req("wp min", "|- P");
        r.theorem = Some("a1".to_string());
        assert!(check_user_proof(&db, &r).is_err());

        // Inside `mp`'s own frame it is legitimately citable (the resulting
        // one-step "proof" of `|- P` is exactly `mp`'s hypothesis).
        let mut r = req("min", "|- P");
        r.theorem = Some("mp".to_string());
        assert!(check_user_proof(&db, &r).is_ok());
    }

    /// Run the whole `/verify` pipeline (Metamath check → kernel derivation) and
    /// return the `hol` object, exactly as the handler assembles it.
    fn hol_of(db: &covalence_init::metamath::Database, r: &VerifyReq) -> Value {
        let (_, _, synthetic) = check_user_proof(db, r).expect("metamath check must pass");
        kernel_derive(db, &synthetic)
    }

    /// **The point of the endpoint**: a user-assembled proof becomes a real
    /// in-HOL derivation, not merely a Rust-checked Metamath one.
    #[test]
    fn verify_produces_a_real_kernel_theorem() {
        let db = db();
        let hol = hol_of(&db, &req("tt a2", "|- ( t + 0 ) = t"));
        assert_eq!(hol["ok"], json!(true));
        assert_eq!(hol["hypCount"], json!(0));
        // The rendered theorem is a projection of the kernel term, so it must
        // name the statement actually derived.
        assert_eq!(hol["thm"], json!("⊢ Derivable ⌜( t + 0 ) = t⌝"));
        // `raw` is the literal kernel conclusion — it really is a `∀d.` term.
        assert!(hol["raw"].as_str().unwrap().contains("mm$"));

        // demo0's own `th1` proof, assembled by the client, also derives.
        let hol = hol_of(&db, &req(TH1_STEPS, "|- t = t"));
        assert_eq!(hol["ok"], json!(true));
        assert_eq!(hol["thm"], json!("⊢ Derivable ⌜t = t⌝"));
    }

    /// A hypothesis-carrying result surfaces its hypotheses. Displaying this as
    /// `⊢ Q` would be a false claim, so the rendered `thm` must carry them.
    #[test]
    fn verify_kernel_surfaces_hypotheses() {
        let db = db();
        let mut r = req("wp wq min maj mp", "|- Q");
        r.theorem = Some("mp".to_string());
        let hol = hol_of(&db, &r);
        assert_eq!(hol["ok"], json!(true));
        assert_eq!(hol["hypCount"], json!(2));
        let thm = hol["thm"].as_str().unwrap();
        assert!(thm.contains('⊢') && thm.starts_with("Derivable ⌜"));
        assert!(thm.ends_with("⊢ Derivable ⌜Q⌝"));
        let hyps: Vec<&str> = hol["hyps"]
            .as_array()
            .unwrap()
            .iter()
            .map(|h| h.as_str().unwrap())
            .collect();
        assert!(hyps.contains(&"Derivable ⌜P⌝"));
        assert!(hyps.contains(&"Derivable ⌜( P -> Q )⌝"));
    }

    /// A bogus proof fails the Metamath check, so the kernel path is never even
    /// reached — and when handed the bad assertion directly the kernel refuses
    /// it too. There is no route on which a bogus proof reports `hol.ok:true`.
    #[test]
    fn verify_kernel_rejects_a_bogus_proof() {
        use covalence_metamath::database::{Assertion, Frame, Proof};
        let db = db();

        // 1. The Metamath check rejects it first (so `/verify` returns ok:false
        //    and no `hol` field is produced at all).
        assert!(check_user_proof(&db, &req("tt tze tpl tt weq", "|- t = t")).is_err());

        // 2. Belt and braces: hand the kernel the same bad assertion directly.
        let bogus = Assertion {
            label: "<goal>".into(),
            conclusion: covalence_metamath::Expr::new(
                "|-",
                vec!["t".into(), "=".into(), "t".into()],
            ),
            frame: Frame::default(),
            proof: Some(Proof::Normal(
                "tt tze tpl tt weq".split(' ').map(str::to_string).collect(),
            )),
            scope_disjoints: Vec::new(),
        };
        let hol = kernel_derive(&db, &bogus);
        assert_eq!(hol["ok"], json!(false));
        assert!(hol["error"].as_str().unwrap().len() > 0);

        // 3. A proof of a *different* statement than the goal: the kernel's own
        //    final conclusion check rejects it, independently of Metamath.
        let mismatched = Assertion {
            conclusion: covalence_metamath::Expr::new(
                "|-",
                vec!["0".into(), "=".into(), "0".into()],
            ),
            proof: Some(Proof::Normal(
                "tt a2".split(' ').map(str::to_string).collect(),
            )),
            ..bogus.clone()
        };
        assert_eq!(kernel_derive(&db, &mismatched)["ok"], json!(false));
    }

    /// The `$e`-scope restriction guards the **kernel** path too: an out-of-scope
    /// `$e` citation is rejected before any assertion is built, so the kernel is
    /// never asked to assume another theorem's premise.
    #[test]
    fn verify_scope_restriction_guards_the_kernel_path() {
        let db = db();
        // Out of scope: rejected before an assertion exists, so `kernel_derive`
        // is unreachable for this request.
        assert!(check_user_proof(&db, &req("wp min", "|- P")).is_err());
        let mut r = req("wp min", "|- P");
        r.theorem = Some("a1".to_string());
        assert!(check_user_proof(&db, &r).is_err());

        // In scope (inside `mp`'s own frame): allowed, and the kernel result is
        // honest about it — the "proof" of `|- P` assumes `|- P`.
        let mut r = req("min", "|- P");
        r.theorem = Some("mp".to_string());
        let hol = hol_of(&db, &r);
        assert_eq!(hol["ok"], json!(true));
        assert_eq!(hol["hypCount"], json!(1));
        assert_eq!(hol["thm"], json!("Derivable ⌜P⌝ ⊢ Derivable ⌜P⌝"));
    }

    /// An over-long proof is reported as *skipped*, a third outcome distinct
    /// from both success and failure.
    #[test]
    fn kernel_derivation_skips_over_long_proofs() {
        use covalence_metamath::database::{Assertion, Frame, Proof};
        let db = db();
        let huge = Assertion {
            label: "<goal>".into(),
            conclusion: covalence_metamath::Expr::new(
                "|-",
                vec!["t".into(), "=".into(), "t".into()],
            ),
            frame: Frame::default(),
            proof: Some(Proof::Normal(vec!["tt".to_string(); KERNEL_STEP_LIMIT + 1])),
            scope_disjoints: Vec::new(),
        };
        let hol = kernel_derive(&db, &huge);
        assert_eq!(hol["ok"], json!(false));
        assert_eq!(hol["skipped"], json!(true));
        assert!(hol["reason"].as_str().unwrap().contains("limit"));
    }

    #[test]
    fn search_matching_is_case_insensitive() {
        // The needle arrives already lowercased by the handler.
        assert!(contains_ignore_case("syl2anc", "syl"));
        assert!(contains_ignore_case("SYL2ANC", "syl"));
        assert!(contains_ignore_case("|- ( ph -> ps )", "ph ->"));
        assert!(!contains_ignore_case("syl", "syl2anc"), "needle too long");
        assert!(!contains_ignore_case("ax-mp", "syl"));
        // An empty needle matches everything (the "first page" case).
        assert!(contains_ignore_case("", ""));
        // Non-ASCII is compared exactly rather than folded.
        assert!(contains_ignore_case("|- 𝜑", "𝜑"));
    }

    #[test]
    fn parse_goal_validates_symbols() {
        let db = db();
        assert!(parse_goal(&db, "|- ( t + 0 ) = t").is_ok());
        assert!(parse_goal(&db, "").is_err(), "empty goal");
        assert!(parse_goal(&db, "|- nope").is_err(), "undeclared symbol");
        assert!(parse_goal(&db, "t = t").is_err(), "typecode is a variable");
    }

    #[test]
    fn apply_matches_and_reports_subgoals() {
        use covalence_metamath::database::Statement;
        use covalence_metamath::{apply_subst, match_conclusion};

        let db = db();
        let Some(Statement::Assert(mp)) = db.statement_by_label("mp") else {
            panic!("mp");
        };
        // Backward step: to prove `|- t = t` by `mp`, `Q := t = t`, and `min`
        // and `maj` become the subgoals — with `P` left unsolved, since the
        // conclusion `|- Q` does not mention it.
        let goal = parse_goal(&db, "|- t = t").unwrap();
        let s = match_conclusion(&db, mp, &goal).expect("mp's conclusion is just `|- Q`");
        assert_eq!(s.get("Q").map(|b| b.len()), Some(3));
        assert!(!s.contains_key("P"), "`P` is not determined by the goal");
        let maj = &mp.frame.essentials[1];
        assert_eq!(apply_subst(&maj.expr, &s).render(), "|- ( P -> t = t )");
    }
}
