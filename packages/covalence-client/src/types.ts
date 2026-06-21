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
// TEMPORARY/DEMO: Metamath import (the `/metamath` page).
// Streamed over the `/api/mm/import` WebSocket; see CovalenceClient.connectMmImport.
// ---------------------------------------------------------------------------

/** A logical (`|-`) assertion referenced by a theorem's proof. */
export interface ImportDep {
  label: string;
  kind: 'axiom' | 'def' | 'thm';
}

/** The **static** declaration of one theorem (graph-phase payload): everything
 * known before its proof is (re-)derived through the kernel. */
export interface ImportDecl {
  label: string;
  /** Rendered Metamath conclusion (`typecode sym ...`). */
  mm: string;
  /** Rendered essential ($e) hypotheses, if any. */
  ess?: string[];
  /** Deduped logical (`|-`) assertions the proof references, first-seen order. */
  deps?: ImportDep[];
  /** Rendered Metamath proof code (normal or compressed). */
  proof?: string;
}

/** The dynamic result of (re-)deriving one theorem through the HOL kernel
 * (prove-phase completion frame). Static fields (mm/ess/deps/proof) are NOT
 * repeated here — they arrived earlier in a `decl` frame. */
export interface ImportProvedMessage {
  type: 'proved';
  done: number;
  total: number;
  label: string;
  ok: boolean;
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
}

/** A streamed frame from the Metamath import WebSocket. Two phases: the static
 * declaration graph (`decl` … `graphDone`) streams first, then a parallel prove
 * phase flips each theorem live (`proving` → `proved`). */
export type ImportMessage =
  | { type: 'parsed'; total: number }
  | { type: 'decl'; items: ImportDecl[] }
  | { type: 'graphDone' }
  | { type: 'proving'; label: string }
  | ImportProvedMessage
  | { type: 'done'; ok: number; total: number; elapsedMs: number }
  | { type: 'error'; message: string };

/** The live status of one theorem-as-task. The seed of a general multi-logic
 * "task view": later states (e.g. `translating`) and per-logic columns slot in
 * over the same graph. */
export type ImportStatus = 'pending' | 'proving' | 'proved' | 'error';

/** One imported theorem, as accumulated by the demo page: the static fields
 * (from `decl`) plus a live `status` and the dynamic prove-phase results. */
export interface ImportedTheorem {
  label: string;
  status: ImportStatus;
  /** Static (graph-phase) fields. */
  mm: string;
  ess: string[];
  proof?: string;
  deps?: ImportDep[];
  /** Dynamic (prove-phase) fields. */
  ok: boolean;
  hyps?: number;
  genuine?: boolean;
  holPreview?: string;
  error?: string;
  importMs?: number;
}
