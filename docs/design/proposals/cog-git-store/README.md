# Cog Git Store — dogfooding cog to serve test assets

> **STATUS: IN PROGRESS — foundation landed.** The §0 default
> (`CogStoreDir` + SQLite store under `.git/cog-<uuid>/`), the §1.1
> `OverlayStore`/`SizeRouter` combinators, and the §2 BLAKE3
> `Blake3LooseStore` are implemented and tested, wired through
> `cov cog store {info,add,cat} [--routed]`. Still to do: §1.2–1.3 git
> indexing, §3 `cov cog fetch`, §4 the `set.mm` test. A staged plan for a
> zero-install,
> per-repo content store that lives *inside* an existing `.git`
> directory, indexes the surrounding git repo, spills large blobs to a
> BLAKE3 loose-object store, and lazily fetches missing hashes from
> remote URLs (file or git) — caching them on the way through. The
> first consumer is the test suite: dogfood cog to serve fixtures, and
> eventually fetch large corpora like `set.mm` and check them with
> `covalence-metamath`.
>
> This is the **native, hard-wired precursor** to
> [`../wasm-store-composition/`](../wasm-store-composition/): the
> combined store here is exactly a `wraps`/`depends_on` graph (see
> [`StoreManifest`][manifest]), assembled in Rust instead of out of WASM
> components. It also makes concrete the "store sits outside the kernel
> TCB as an oracle" stance from
> [`../layered-framework/04-store.md`](../layered-framework/04-store.md).

## 0. The one idea

A repo already carries a content-addressed object database under
`.git`. We add a **sibling** database next to it — keyed by BLAKE3
(`O256`) instead of git's SHA — and teach cog to read through both as a
single store, falling back to remote sources and caching what it pulls.
Nothing is installed globally; nothing lands in the working tree;
deleting the directory loses only cache, never source of truth.

```
worktree/
  .git/
    objects/                         ← git's own ODB (SHA-1 / SHA-256)
    cog-14169d9d-e25f-46dd-abc7-dd53b495cd06/   ← THE cog store dir
      store.db        SQLite ContentStore<O256>      (small blobs)   [§1]
      objects/        BLAKE3 loose store  ab/cdef…   (large blobs)   [§3]
      index.db        git-OID ⇄ O256 index            (or in store.db)[§2]
      sources.json    remote upstreams + url→hash cache             [§4]
      manifest.json   StoreManifest describing the combined graph   [opt]
```

### Why under `.git`, and why a UUID suffix

- **Auto-ignored.** Git never tracks anything under `.git`, so the
  store never shows in `git status`, never gets committed, never
  pollutes the working tree. No `.gitignore` edit required.
- **Travels with the gitdir.** It rides along with the repository's
  real git directory and is naturally shared across linked worktrees
  (we anchor it at the **commondir**, §0.1).
- **Zero install.** No global state, no daemon required, no XDG
  directory to provision. The store's lifetime is the repo's.
- **The UUID is the well-known marker.** A bare `.git/cog` risks
  colliding with some future git feature or another tool named "cog".
  A fixed UUID suffix makes the directory an unmistakable, greppable,
  collision-proof signature that *this* is a covalence cog store:

  ```rust
  /// The one well-known cog-store directory UUID. Never changes.
  pub const COG_STORE_UUID: &str = "14169d9d-e25f-46dd-abc7-dd53b495cd06";
  pub const COG_STORE_DIRNAME: &str = "cog-14169d9d-e25f-46dd-abc7-dd53b495cd06";
  ```

### 0.1 Locating the directory

Discovery reuses the existing, dependency-free walker
[`covalence_proto::git::discover_git_repo`][discover] →
`DiscoveredRepo { root, bare }`. The store dir is anchored at the
**commondir**, not the per-worktree gitdir, so every linked worktree
shares one cache:

- **Worktree:** `.git` is a directory → store at
  `<root>/.git/cog-<uuid>/`. `.git` is a *file* (linked worktree
  pointer `gitdir: …`) → resolve to the commondir and put the store
  there. The gitdir/commondir resolution already exists in
  [`covalence-git/src/clone/local.rs`][local] (it handles
  worktree-pointer `.git` files and `commondir`); factor that out and
  reuse it.
- **Bare repo:** `root` *is* the gitdir → `<root>/cog-<uuid>/`.

```rust
/// Handle to a cog store directory inside a git repo. Pure path logic;
/// opening backends is separate so callers pick which layers they want.
pub struct CogStoreDir { dir: PathBuf }

impl CogStoreDir {
    /// Walk up from `cwd`, resolve the commondir, return the store dir
    /// (does not create it).
    pub fn discover() -> io::Result<Option<Self>>;
    /// Anchor at an already-resolved git common directory.
    pub fn at_commondir(commondir: &Path) -> Self;
    pub fn create(&self) -> io::Result<()>;        // mkdir -p
    pub fn db_path(&self) -> PathBuf;              // dir/store.db
    pub fn objects_dir(&self) -> PathBuf;          // dir/objects
    pub fn sources_path(&self) -> PathBuf;         // dir/sources.json
}
```

**Where the code lives.** Recommend a new `cog` module in
**`covalence-git`** behind a `cog` feature (`cog = ["sqlite",
"object-store"]`) — it already owns git layout, `GitStore`,
`LooseBackend`, and `LfsStore`. Repo discovery stays the caller's job
(the CLI already depends on `covalence-proto`), so `covalence-git` need
not gain a `covalence-proto` edge: pass a resolved path in. If the
module outgrows that home, extract a `covalence-cog` crate later.

### 0.2 The opinionated default (start here)

The minimum viable store is **just `store.db`** — a
[`SqliteStore`][sqlite] opened at `db_path()`, wrapped in a
`BlobStore<O256>`. This is the foundation everything else layers onto,
and it is a one-function helper:

```rust
impl CogStoreDir {
    /// Open (creating if absent) the default cog store: a single SQLite
    /// ContentStore<O256> at `store.db`.
    pub fn open_sqlite(&self) -> Result<SqliteStore, StoreError>;
    pub fn open_default(&self) -> Result<BlobStore<O256>, StoreError> {
        self.create()?;
        Ok(BlobStore::new(self.open_sqlite()?))
    }
}
```

CLI wiring mirrors the existing [`resolve_store`][resolve] in
`cmd/mod.rs`: when no explicit `--store` is given, a new cog-aware
default discovers the repo and opens `.git/cog-<uuid>/store.db` instead
of falling back to in-memory. (`cov serve --store` already resolves a
default DB path via [`default_store_path()`][cfg] — the cog store is
the *repo-scoped* analogue.)

Everything below is additive: each step wraps the previous store in one
more layer of the read-fallback / write-routing graph.

---

## 1. Step 1 — index the git repo into a combined store

**Goal.** Read a blob by its BLAKE3 hash and have it served from *either*
the cog SQLite DB *or* the surrounding git ODB, transparently.

### 1.1 The missing primitive: an overlay/fallback combinator

`covalence-store` has wrappers (`BlobStore`, `GitPrefixStore`,
`KeyedObjectStore`) but **no read-fallback / write-routing combinator**.
Add one — it is the generic shape the rest of this proposal assembles:

```rust
/// Reads try each layer in order; the first hit wins. Writes go to the
/// single writable `primary`. Mirrors StoreManifest `depends_on`: the
/// store can ride out a missing upstream.
pub struct OverlayStore<K> {
    primary: BlobStore<K>,        // writable, checked first
    fallbacks: Vec<BlobStore<K>>, // read-only, checked in order
}

impl<K: Send + Sync + Clone> ContentStore<K> for OverlayStore<K> {
    fn get(&self, k: &K) -> Option<Vec<u8>> { /* primary, then fallbacks */ }
    fn get_slice(&self, k: &K, r: Range<u64>) -> Result<Vec<u8>, StoreError> { /* first hit */ }
    fn head(&self, k: &K) -> Option<BlobInfo> { /* first hit */ }
    fn contains(&self, k: &K) -> bool { /* any layer */ }
    fn insert(&self, d: &[u8]) -> Result<K, StoreError> { self.primary.insert(d) }
    fn put(&self, k: K, d: &[u8]) -> Result<(), StoreError> { self.primary.put(k, d) }
}
```

`get_slice`/`head` range-fallthrough composes cleanly with SQLite's
native `substr` reads and (later) the loose store's `pread`. This type
belongs in `covalence-store` (behind no extra feature) so every consumer
gets it.

### 1.2 Indexing: git OID ⇄ O256

Git objects are keyed by SHA; the cog store is keyed by BLAKE3. To read
a git-stored file *by its content hash*, we need a mapping. The
machinery already exists in [`covalence-git`'s `GitStore`][gitstore]
(`git_objects: git_oid → blob_hash`, `blobs: o256 → data`,
`cov_trees`) — but that copies data into SQLite. For indexing an
*existing* repo we want a **lazy** index that maps without copying:

```sql
-- in store.db (or a sibling index.db)
CREATE TABLE IF NOT EXISTS git_index (
    o256    BLOB PRIMARY KEY,   -- O256::blob(raw_content)
    git_oid BLOB NOT NULL,      -- git object id (read lazily from ODB)
    kind    TEXT NOT NULL       -- "blob" | "tree" | "commit" | "tag"
) WITHOUT ROWID;
```

**Indexer.** Enumerate git objects via
[`OdbBackend::iter_oids`][odb] (loose **and** packed), read each, and
for **blobs** record `O256::blob(raw_content) → oid`. Asset serving is
about file *content*, so we key blobs by the BLAKE3 of their raw bytes —
the same hash `cov cog hash-blob --blake3` and `SqliteStore::insert`
produce, so a file's identity is stable across cog and git. (Trees and
commits are git-structured; indexing them is a later extension and is
not needed for serving assets.)

```rust
pub fn index_git_repo(store: &CogStoreDir, repo: &Path) -> Result<IndexStats, StoreError>;
```

`--global` may target the XDG store ([`default_store_path()`][cfg])
instead of the repo-local DB, and the overlay can even chain repo-local
over global.

### 1.3 The combined store

```rust
/// Reads:  cog SQLite  →  git ODB (via git_index)
/// Writes: cog SQLite
pub fn combined_store(dir: &CogStoreDir, repo: &Path)
    -> Result<BlobStore<O256>, StoreError>;
```

The git layer is an `OdbBackend` wrapped in a small
`ContentStore<O256>` adapter that, on `get(o256)`, looks up `git_index`
→ `oid` → reads the object bytes from the ODB. Misses fall through (to
§3's loose store, then §4's remote fetch).

**Deliverables:** `OverlayStore` in `covalence-store`; `git_index`
table + indexer + ODB-by-O256 adapter in `covalence-git`;
`cov cog index [--global]` CLI command.

---

## 2. Step 2 — BLAKE3 loose object store for large blobs

**Goal.** Keep SQLite lean: small blobs in the DB, large blobs as loose
files. Big goes to the loose store, small to SQLite — now a **triple**
combined store (SQLite + loose + git-ODB).

### 2.1 The loose store

[`LfsStore`][lfs] is *already* a `ContentStore<O256>` that writes raw,
uncompressed bytes into a git-style fanout (`aa/bb/<full>`) keyed by a
256-bit hash — it just uses SHA-256 (`O256::blob_sha256`). Step 2 is
"`LfsStore`, but keyed by BLAKE3 (`O256::blob`)". Two ways:

- **(Recommended) Generalize the loose store over its hash function.**
  Parameterize the existing fanout store by a `HashCtx` / hash-fn so
  the same code backs both the SHA-256 LFS store and a BLAKE3 cog loose
  store. One fanout level (`ab/<rest>`, git-style) keeps it familiar;
  raw bytes (no zlib) keep `pread` range reads cheap.
- Or add a sibling `Blake3LooseStore` if generalizing churns LFS too
  much.

```rust
pub struct Blake3LooseStore { dir: PathBuf }   // dir/ab/cdef… raw bytes
impl ContentStore<O256> for Blake3LooseStore {
    // get_slice via pread; head via file length; insert hashes with O256::blob
}
```

### 2.2 Size-routing writes

```rust
/// Routes inserts by size; reads check both. Default threshold 1 MiB.
pub struct SizeRouter<K> { small: BlobStore<K>, large: BlobStore<K>, threshold: u64 }
```

`insert(data)`: `data.len() >= threshold` → loose (`large`), else SQLite
(`small`). Reads consult both. The full read order becomes:

```
cog SQLite  →  cog BLAKE3 loose  →  git ODB (index)   [→ §4 remote]
```

**Rationale.** SQLite (`WITHOUT ROWID`, `substr` ranges) is excellent
for many small blobs but bloats and slows under large BLOBs and fat WAL
frames; loose files get OS page-cache, cheap `pread`, and drop-in LFS
compatibility. Threshold is config (`sources.json` / `manifest.json`).

**Deliverables:** generalized loose store (BLAKE3 variant) + `SizeRouter`
in `covalence-store`; wire both into `combined_store`.

---

## 3. Step 3 — fetch hash-first, URL-second, cache the result

**Goal.** `cov cog fetch` resolves a hash from the cog store first; on a
miss, fetches from a URL (file or git), verifies, and **caches into the
cog store** so the next lookup is local.

```rust
/// Resolution order:
///   1. combined cog store (SQLite → loose → git index)
///   2. each configured URL source, in order
/// On a remote hit: verify (if an expected hash was given), then insert
/// into the cog store (size-routed) and record provenance.
pub fn fetch(store: &CombinedStore, want: FetchRequest) -> Result<O256, FetchError>;

pub struct FetchRequest {
    pub hash: Option<O256>,   // content address to satisfy
    pub url: Option<String>,  // where to get it if missing
    pub expect: Option<O256>, // verify fetched bytes against this
}
```

CLI:

```sh
cov cog fetch <hash>                       # cog store only; error if absent
cov cog fetch <url>                        # fetch+cache; print the O256
cov cog fetch <url> --expect <hash>        # fetch, verify, cache
cov cog fetch <hash> --from <url>          # try local; fall back to url
```

### 3.1 Caching = the store is the cache

The cog store *is* the cache (`depends_on` upstreams, per
[`StoreManifest`][manifest]). `sources.json` records provenance so
re-fetching is cheap and auditable:

```jsonc
{
  "threshold_bytes": 1048576,
  "sources": [ { "name": "metamath", "url": "https://…", "kind": "file" } ],
  "url_cache": { "https://…/set.mm": "<o256-hex>" }   // url → content hash
}
```

### 3.2 Stages

| Stage | Scope | Builds on |
|-------|-------|-----------|
| **3a** | Plain file URLs (`http`/`https`/`file`) via `ureq`, content-addressed cache, optional `--expect` verify. *Smallest slice; unblocks `set.mm`.* | [`covalence-opentheory::fetch_url`][otfetch] template |
| **3b** | Provenance + `url_cache` tables; conditional GET (ETag / `Last-Modified`) so a known URL revalidates instead of re-downloading. | 3a |
| **3c** | **Git repo URLs** (`<repo>@<ref>:<path>`): use the existing smart-HTTP-v2 clone ([`covalence-git::clone`][clone], `CloneSource::Http`/`Local`) into the cog `GitStore`, then resolve `path@ref` → blob `O256`. Partial clone (`blob:none`) to fetch a single blob. | §1 index, clone |
| **3d** | Federated sources: multiple upstreams / mirrors with ordered fallback + retry (the `depends_on` list). | 3a–3c |

"The URL can be a git repo or just a regular file URL" → **3a** (file) +
**3c** (git). Plain files cover `set.mm` directly; the git path gives
reproducible, ref-pinned fetches.

**Deliverables:** `cov cog fetch` command + `fetch()` function;
`sources.json` read/write; gate outbound HTTP behind a `fetch` feature
(matching `covalence-repl` / `covalence-opentheory`).

---

## 4. Step 4 — `set.mm` fetch-and-check test

**Goal.** An integration test that fetches `set.mm` from a URL into a
cog store and checks it with [`covalence-metamath`][mm] — opt-in, so
default CI stays fast.

### 4.1 Shape

`crates/covalence-metamath/tests/setmm_fetch.rs`:

1. Create a cog store in a temp dir (or a stable, reused cache dir so CI
   downloads once).
2. `fetch()` `set.mm` from a pinned source (§3a file URL, or §3c git
   ref for reproducibility) into the store.
3. Parse with `covalence_metamath::parse` (its `FileResolver` already
   handles `$[ … $]` includes), then `verify_all` / a bounded subset of
   `verify_proof`.

### 4.2 Make it disableable — two layers (house pattern)

The codebase gates optional tests by **feature flag** (compile-time) +
**env var** (runtime); it does **not** use `#[ignore]`.

- **Compile gate:** `#![cfg(feature = "fetch")]` on the test (no
  outbound HTTP in a default build).
- **Runtime gate:** require `COV_TEST_SETMM=1` to run; otherwise return
  early (skip). Mirrors `covalence-llm`'s `COV_LLM_MODEL` env reads.
- **Knobs:** `COV_TEST_SETMM_URL` (override source),
  `COV_TEST_SETMM_FULL=1` (full `verify_all` vs. a bounded prefix —
  full set.mm verification is minutes-long and tens of MB).
- **Reproducibility:** pin a specific `metamath/set.mm` commit/tag (via
  §3c) and/or an `--expect` BLAKE3, so the test is deterministic. The
  cog store doubles as the download cache across runs.

```rust
#![cfg(feature = "fetch")]
#[test]
fn setmm_fetch_and_verify() {
    if std::env::var("COV_TEST_SETMM").is_err() { return; } // opt-in
    // … open temp cog store, fetch set.mm, parse, verify (bounded unless _FULL)
}
```

### 4.3 Forward hook

"We'll be adding metamath import support to `covalence-core` shortly."
The test starts against `covalence-metamath`'s own `verify_all`; once
core import lands, add a second assertion that the imported terms
type-check in the kernel. Keep both behind the same gates.

**Deliverables:** opt-in `setmm_fetch` test; `fetch` feature on
`covalence-metamath` (dev-dependency on the cog/fetch path); a note in
the [PR checklist][claude] that `COV_TEST_SETMM` is off by default.

---

## 5. Build order

1. **[done] §0.2** `CogStoreDir` + `open_default()` — the SQLite-only
   default under `.git/cog-<uuid>/` (commondir-anchored), exposed as
   `cov cog store`.
2. **[done] §1.1** `OverlayStore` + `SizeRouter` in `covalence-store`
   (generic, reusable).
3. **[done] §2** `Blake3LooseStore` + `SizeRouter` wiring →
   `cov cog store --routed` (SQLite + loose). *(BLAKE3 loose store added
   as a sibling to `LfsStore` rather than generalizing it; revisit if a
   shared generic loose store proves worthwhile.)*
4. **[next] §1.2–1.3** `git_index` + indexer + ODB-by-O256 adapter +
   `cov cog index`; fold the git layer into the overlay → triple store.
5. **§3a** `cov cog fetch` for file URLs + content-addressed cache.
6. **§3b–3d** provenance/url-cache, conditional GET, git-URL fetch,
   federation — as needed.
7. **§4** opt-in `set.mm` test.

Steps 1–2 are independently useful (faster, repo-local test fixtures)
before any network code exists.

## 6. Open questions

1. **Code home.** `cog` module in `covalence-git` (recommended) vs. a
   new `covalence-cog` crate. Start in-crate; extract if it grows.
2. **Keyspace.** Blobs keyed by raw-content BLAKE3 (asset model,
   recommended) vs. git-framed bytes. Keep `GitStore.git_objects` for
   git-native lookups; `git_index` for content lookups.
3. **Overlay placement.** `OverlayStore`/`SizeRouter` as first-class
   `covalence-store` combinators (recommended) vs. ad-hoc in
   `covalence-git`. The former benefits every consumer and matches the
   `StoreManifest` graph.
4. **Concurrency.** Multiple `cov` processes / worktrees sharing one
   store. SQLite WAL + busy-timeout (already in `covalence-sqlite`) and
   atomic temp+rename in the loose store (already in `LooseBackend`)
   cover most of it; document the contract.
5. **GC / pruning.** The cache grows unbounded. A `cov cog gc`
   (size-capped LRU over the loose store + url_cache) is a later add.
6. **Manifest.** Emit a `manifest.json` ([`StoreManifest`][manifest])
   describing the assembled graph, so the store self-describes and the
   future WASM-component composition
   ([`../wasm-store-composition/`](../wasm-store-composition/)) can adopt
   it unchanged.

---

[manifest]: ../../../../crates/covalence-store/src/metadata.rs
[sqlite]: ../../../../crates/covalence-store/src/sqlite.rs
[resolve]: ../../../../crates/covalence/src/cmd/mod.rs
[cfg]: ../../../../crates/covalence-proto/src/config.rs
[discover]: ../../../../crates/covalence-proto/src/git.rs
[local]: ../../../../crates/covalence-git/src/clone/local.rs
[gitstore]: ../../../../crates/covalence-git/src/store/sqlite_store.rs
[odb]: ../../../../crates/covalence-git/src/store/odb.rs
[lfs]: ../../../../crates/covalence-git/src/lfs.rs
[clone]: ../../../../crates/covalence-git/src/clone/mod.rs
[otfetch]: ../../../../crates/covalence-opentheory/src/fetch.rs
[mm]: ../../../../crates/covalence-metamath/src/lib.rs
[claude]: ../../../../CLAUDE.md
