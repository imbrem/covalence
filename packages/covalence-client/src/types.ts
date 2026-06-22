/** 64-character lowercase hex string (blake3 hash). */
export type Hash = string;

/** SAT decision result. */
export type Decision = 'sat' | 'unknown' | 'unsat';

/** GET /api/info */
export interface InfoResponse {
  version: string;
  cog_version: string;
  target: string;
  cwd: string;
}

/** GET /api/health */
export interface HealthResponse {
  status: string;
  version: string;
  cog_version: string;
  target: string;
  uptime_secs: number;
}

/** POST /api/blobs, POST /api/blobs/url, POST /api/blobs/file */
export interface HashResponse {
  hash: Hash;
}

/** GET /api/blobs */
export interface BlobStatsResponse {
  count: number | null;
}

/** GET /api/decide/:hash */
export interface DecideResponse {
  result: Decision;
  proved: Hash[];
}

/** Object kinds returned by the object store. */
export type ObjectKind = 'blob' | 'tree' | 'commit' | 'tag' | 'tagged';

/** GET /api/objects/info/:hash
 *
 * When the requested hash is a *keyed identity* registered in the
 * kernel's tag registry, `kind` is `'tagged'` and `tag` /
 * `contentHash` carry the BLAKE3 derivation context and the
 * underlying content blob's hash, respectively.
 */
export interface ObjectInfoResponse {
  kind: ObjectKind;
  size: number;
  tag?: string;
  contentHash?: Hash;
}

/** Entry in a tree listing. */
export interface TreeEntry {
  name: string;
  mode: string;
  hash: Hash;
}

// ---------------------------------------------------------------------------
// TEMPORARY / THROWAWAY DEMO: Metamath sessions (the `/metamath` page).
//
// Clean REST for data + a thin WebSocket for live status only. A `.mm` source
// is POSTed once into a cached session (keyed by content hash); graph + theorem
// data are then served by REST, the kernel import is kicked off by REST, and
// live per-theorem status is forwarded over a thin status WS. See
// CovalenceClient.{createMmDb,mmDbInfo,mmDbList,mmGraph,mmTheorem,startMmProve,
// connectMmStatus}.
// ---------------------------------------------------------------------------

/** A logical (`|-`) assertion referenced by a theorem's proof. */
export interface ImportDep {
  label: string;
  kind: 'axiom' | 'def' | 'thm';
}

/** POST /api/metamath/db → the session handle. */
export interface MmDbResponse {
  /** Content hash of the `.mm` source (the session id). */
  file: Hash;
  /** Logical (`|-`) `$p` theorem count. */
  total: number;
  /** Provenance (a URL or label) recorded via `?from=`, if any. */
  origin?: string | null;
}

/** GET /api/metamath/db/{hash} → lightweight session metadata (the
 * "attach by hash" probe — existence + counts, no bulk download). */
export interface MmDbInfo {
  file: Hash;
  total: number;
  /** Provenance (a URL or label), if known. */
  origin?: string | null;
  /** Whether a prove run is currently underway. */
  proving: boolean;
  /** Theorems proved so far (from the results cache). */
  proved: number;
  /** Theorems that errored so far. */
  errors: number;
}

/** GET /api/metamath/stats → a point sample of server/process metrics. Poll on
 * an interval and accumulate the time series client-side (the server is
 * stateless). `rssBytes`/`peakRssBytes` are `null` off Linux. */
export interface MmServerStats {
  /** Resident set size (bytes), or null if unavailable. */
  rssBytes: number | null;
  /** Peak resident set size (bytes), or null if unavailable. */
  peakRssBytes: number | null;
  /** Number of cached Metamath sessions. */
  sessions: number;
  /** Total per-theorem results cached across all sessions. */
  theoremsCached: number;
  /** Server uptime in seconds. */
  uptimeSecs: number;
}

/** One named Metamath definition (a syntactic former or a `df-*`) and its HOL
 * encoding (GET /api/metamath/session/{hash}/hol → `defs`). */
export interface MmDef {
  /** The Metamath label (the definition's name). */
  label: string;
  /** `'former'` (a wff/class/… syntax constructor) or `'def'` (a `df-*`). */
  kind: 'former' | 'def';
  /** Rendered Metamath statement. */
  mm: string;
  /** Rendered HOL term (the encoded conclusion). */
  hol: string;
}

/** GET /api/metamath/session/{hash}/hol → pass-1 surface stats + definitions.
 * The interned (hash-consed) HOL surface of the whole database: every theorem's
 * conclusion built once on a single thread into a shared DAG, plus the named
 * definitions used to read it. */
export interface MmHolInfo {
  /** Summed statement-tree nodes over all conclusions (un-interned). */
  surfaceNodes: number;
  /** Distinct nodes after interning (the shared DAG). */
  dagNodes: number;
  /** `surfaceNodes / dagNodes` — the dedup factor. */
  dedup: number;
  /** The database's named definitions (formers + df-*). */
  defs: MmDef[];
}

/** One entry of GET /api/metamath/dbs → all cached sessions on the server. */
export interface MmDbListEntry {
  file: Hash;
  /** The per-session user key, if any. */
  user?: string | null;
  /** Provenance (a URL or label), if known. */
  origin?: string | null;
  total: number;
  /** Theorems proved so far. */
  proved: number;
}

/** One node of the cached static declaration graph
 * (GET /api/metamath/db/{hash}/graph). */
export interface ImportDecl {
  label: string;
  /** Rendered Metamath conclusion (`typecode sym ...`). */
  mm: string;
  /** Deduped logical (`|-`) assertions the proof references, first-seen order. */
  deps?: ImportDep[];
}

/** GET /api/metamath/db/{hash}/graph */
export interface MmGraphResponse {
  total: number;
  theorems: ImportDecl[];
}

/** The live status of one theorem-as-task. The seed of a general multi-logic
 * "task view": later states (e.g. `translating`) and per-logic columns slot in
 * over the same graph. */
export type ImportStatus = 'pending' | 'proving' | 'proved' | 'error';

/** GET /api/metamath/db/{hash}/theorem/{name} — one theorem's full detail:
 * static fields (always present) plus dynamic fields once it has been proved
 * (`status` is `pending` until then). */
export interface ImportTheoremDetail {
  label: string;
  /** Rendered Metamath conclusion. */
  mm: string;
  /** Rendered essential ($e) hypotheses. */
  ess: string[];
  /** Direct logical dependencies. */
  deps: ImportDep[];
  /** Rendered Metamath proof code (normal or compressed). */
  proof: string;
  /** Current import status. */
  status: ImportStatus;
  /** Whether the kernel import succeeded (present once proved/error). */
  ok?: boolean;
  /** Number of HOL hypotheses (present when ok). */
  hyps?: number;
  /** True if the imported theorem is oracle-free (present when ok). */
  genuine?: boolean;
  /** First ~400 chars of the `⊢ Derivable_L ⌜S⌝` conclusion (present when ok). */
  holPreview?: string;
  /** Failure reason (present when !ok). */
  error?: string;
  /** Wall-clock ms to derive this theorem (the HOL import time). */
  importMs?: number;
  /** The interned/encoded HOL conclusion term. Served from the cached pass-1
   * surface (folded to definition names) when ready, else encoded on demand
   * (unfolded) so it's available even mid-import. */
  holTerm?: string;
}

/** A frame forwarded over the thin status WebSocket
 * (WS /api/metamath/db/{hash}/status). On connect the server sends a
 * `snapshot`; then `proving` → `proved` flip each theorem live, terminated by
 * `done`. */
export type MmStatusMessage =
  | { type: 'snapshot'; total: number; results: { label: string; ok: boolean }[] }
  | { type: 'proving'; label: string }
  | {
      type: 'proved';
      done: number;
      total: number;
      label: string;
      ok: boolean;
      hyps?: number;
      genuine?: boolean;
      holPreview?: string;
      error?: string;
      importMs?: number;
    }
  | { type: 'done'; ok: number; total: number; elapsedMs: number }
  | { type: 'error'; message: string };

/** One imported theorem, as accumulated by the demo page: the static graph
 * fields plus a live `status` and the dynamic prove-phase results. */
export interface ImportedTheorem {
  label: string;
  status: ImportStatus;
  /** Static (graph) fields. */
  mm: string;
  deps?: ImportDep[];
  /** Dynamic (prove-phase) fields. */
  ok: boolean;
  hyps?: number;
  genuine?: boolean;
  holPreview?: string;
  error?: string;
  importMs?: number;
}
