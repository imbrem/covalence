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

/** POST /api/metamath/upload → the session handle. */
export interface MmDbResponse {
  /** Content hash of the `.mm` source (the session id). */
  file: Hash;
  /** Logical (`|-`) `$p` theorem count. */
  total: number;
  /** Provenance (a URL or label) recorded via `?from=`, if any. */
  origin?: string | null;
}

/** GET /api/metamath/session/{hash} → lightweight session metadata (the
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
  /** Whether pass 1 has finished. When false, only the progress fields are set. */
  ready: boolean;
  /** Summed statement-tree nodes over all conclusions (un-interned). Ready only. */
  surfaceNodes?: number;
  /** Distinct nodes after interning (the shared DAG). Ready only. */
  dagNodes?: number;
  /** `surfaceNodes / dagNodes` — the dedup factor. Ready only. */
  dedup?: number;
  /** The database's named definitions (formers + df-*). Ready only. */
  defs?: MmDef[];
  /** Theorems interned so far (while not ready). */
  done?: number;
  /** Total theorems to intern (while not ready). */
  total?: number;
  /** Distinct DAG nodes so far (while not ready). */
  nodes?: number;
}

/** One entry of GET /api/metamath/sessions → all cached sessions on the server. */
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
 * (GET /api/metamath/session/{hash}/graph). */
export interface ImportDecl {
  label: string;
  /** Rendered Metamath conclusion (`typecode sym ...`). */
  mm: string;
  /** Deduped logical (`|-`) assertions the proof references, first-seen order. */
  deps?: ImportDep[];
}

/** GET /api/metamath/session/{hash}/graph */
export interface MmGraphResponse {
  total: number;
  theorems: ImportDecl[];
}

/** The live status of one theorem-as-task. The seed of a general multi-logic
 * "task view": later states (e.g. `translating`) and per-logic columns slot in
 * over the same graph. */
export type ImportStatus = 'pending' | 'proving' | 'proved' | 'error';

/** GET /api/metamath/session/{hash}/theorem/{name} — one theorem's full detail:
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
 * (WS /api/metamath/session/{hash}/status). On connect the server sends a
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
  | { type: 'error'; message: string }
  /** Pass-1 interner progress: theorems interned so far / total, and distinct
   * shared-DAG nodes so far. */
  | { type: 'interning'; done: number; total: number; nodes: number }
  /** Pass 1 finished: the final surface stats (defs is the count; fetch /hol for
   * the full list). */
  | { type: 'interned'; surfaceNodes: number; dagNodes: number; dedup: number; defs: number };

// ---------------------------------------------------------------------------
// Proof surface: /steps, /search, /apply, /verify.
//
// Convention shared by /steps, /apply and /verify (the `/api/lisp` one): a
// *session* problem is a non-2xx (thrown as CovalenceError), but a *proof*
// problem — the stored proof doesn't verify, the assertion doesn't match the
// goal, the user's RPN sequence is wrong — is HTTP 200 with `ok:false` and a
// checker message. Those are data, not exceptions: the UI shows the message.
// ---------------------------------------------------------------------------

/** What a label is, as classified by the server: `def` = the label starts
 * `df`, `axiom` = `$a`, `thm` = `$p` (has a proof). */
export type MmAssertionKind = 'thm' | 'def' | 'axiom';

/** What a replay step did to the stack. `save`/`heapRef` are the compressed
 * proof format's sharing operations and are *never* silently expanded — a
 * `save` records the expression on the heap (pushing nothing), a `heapRef`
 * re-pushes an earlier one. */
export type MmStepKind = 'floatHyp' | 'essentialHyp' | 'assertion' | 'save' | 'heapRef';

/** One hypothesis of an applied assertion, before and after the substitution
 * the checker derived. Invariant (server-guaranteed): for step `s`,
 * `s.hyps[k].after === s.args[k]` and `s.hyps.length === s.args.length`. */
export interface MmStepHyp {
  label: string;
  /** The hypothesis as declared, in the assertion's own variables. */
  before: string;
  /** The same hypothesis after substitution — i.e. the popped argument. */
  after: string;
}

/** One variable ↦ expression entry of a substitution. `expr` carries **no**
 * typecode (it is the bare expression, e.g. `t = t`, not `wff t = t`). */
export interface MmSubstEntry {
  var: string;
  expr: string;
}

/** One step of a verifying replay (from `/steps` or a successful `/verify`).
 *
 * `i`, `label`, `kind`, `expr` and `stackDepth` are always present; the
 * remaining fields are keyed to `kind` and are **absent** otherwise — do not
 * index them blindly. */
export interface MmProofStep {
  /** 0-based, dense, in replay order. */
  i: number;
  /** `null` for `save`/`heapRef`, which cite no label. */
  label: string | null;
  kind: MmStepKind;
  /** The expression pushed. For `save` (which pushes nothing) it is the
   * expression that was saved. */
  expr: string;
  /** Stack depth *after* the step. `save` leaves it unchanged. */
  stackDepth: number;
  /** Popped arguments, floats then essentials. `kind === 'assertion'` only. */
  args?: string[];
  /** The substitution the checker derived, sorted by variable.
   * `kind === 'assertion'` only. */
  subst?: MmSubstEntry[];
  /** The applied assertion's hypotheses, floats first then essentials.
   * `kind === 'assertion'` only. */
  hyps?: MmStepHyp[];
  /** Index into the save-order heap: equals the Nth `save` step's `expr`.
   * `kind === 'heapRef'` only. */
  heapIndex?: number;
}

/** One of a theorem's own essential (`$e`) hypotheses. */
export interface MmTheoremHyp {
  label: string;
  expr: string;
}

/** GET /api/metamath/session/{hash}/theorem/{name}/steps — a verifying replay
 * of the stored proof. `ok:false` means the proof does **not** verify; there is
 * deliberately no partial trace in that case. */
export type MmStepsResponse =
  | {
      ok: true;
      label: string;
      kind: MmAssertionKind;
      /** `true` ⇒ no proof exists ⇒ `steps` is `[]`. */
      axiom: boolean;
      conclusion: string;
      /** The theorem's own essential hypotheses (may be empty). */
      hyps: MmTheoremHyp[];
      steps: MmProofStep[];
    }
  | { ok: false; label: string; error: string };

/** One hit of the assertion search. */
export interface MmSearchHit {
  label: string;
  kind: MmAssertionKind;
  /** Rendered conclusion (`typecode sym ...`). */
  mm: string;
  /** Number of essential (`$e`) hypotheses. */
  hypCount: number;
}

/** GET /api/metamath/session/{hash}/search — always 200 (no `ok` field). */
export interface MmSearchResponse {
  /** The lowercased needle, echoed back. */
  q: string;
  /** `results.length` — the size of *this page*, not a db-wide total. */
  total: number;
  /** `true` ⇒ the limit was hit and more may exist. */
  truncated: boolean;
  /** In database (source) order. */
  results: MmSearchHit[];
}

/** One floating (`$f`) hypothesis of an applied assertion, as resolved against
 * the goal. `expr` is `null` **iff** the variable is in `unsolved` — a variable
 * occurring only in the assertion's hypotheses (like `mp`'s `P`) is not
 * determined by the conclusion and the user must supply it. Never treat
 * `subst` as total over `floats`. */
export interface MmApplyFloat {
  var: string;
  typecode: string;
  expr: string | null;
}

/** One subgoal produced by an application: an essential hypothesis of the
 * assertion, after substitution. Unsolved variables appear in it literally. */
export interface MmApplySubgoal {
  label: string;
  expr: string;
}

/** POST /api/metamath/session/{hash}/apply — match an assertion's conclusion
 * against a goal, backwards.
 *
 * A successful match is only a *suggestion*: the server re-checks that the
 * substitution reproduces the goal exactly, but grammatical well-formedness is
 * not checked, so a match can still yield an unprovable subgoal. Nothing is
 * proved until {@link MmVerifyResponse} says so. */
export type MmApplyResponse =
  | {
      ok: true;
      label: string;
      kind: MmAssertionKind;
      /** The goal, re-rendered/normalized by the server. */
      goal: string;
      /** Solved variables only, sorted; expressions carry no typecode. */
      subst: MmSubstEntry[];
      /** The assertion's essential hypotheses after substitution. */
      subgoals: MmApplySubgoal[];
      /** The assertion's floating hypotheses, **in frame order** — the order
       * their proofs must appear in an RPN sequence, ahead of the essentials. */
      floats: MmApplyFloat[];
      /** Frame variables the goal does not determine. Normal, not an error. */
      unsolved: string[];
    }
  | { ok: false; error: string };

/** POST /api/metamath/session/{hash}/verify — the request body. */
export interface MmVerifyRequest {
  /** RPN label sequence (normal-proof form). */
  steps: string[];
  /** The claimed statement, rendered; first token is the typecode. */
  goal: string;
  /** Names an existing theorem whose frame this proof is written in. Supplying
   * it makes that theorem's `$e` hypotheses citable and its `$d` declarations
   * available; omitting it means an empty frame — **no** `$e` citable and no
   * `$d`. (`$f` float labels are always citable.) */
  theorem?: string;
}

/** POST /api/metamath/session/{hash}/verify — **the only source of truth for
 * "proved"**. It runs the real checker (the same replay as {@link
 * MmStepsResponse}, with full stack/typecode/hypothesis/`$d` discipline and no
 * admit path). A UI must never render "proved" from its own bookkeeping. */
/** The kernel's verdict on a user-built proof, attempted only after the Metamath
 * replay succeeds. These are **two separate claims** and must stay separable in
 * the UI: `ok: true` on {@link MmVerifyResponse} means the Rust Metamath checker
 * replayed the steps; `hol.ok` means the HOL kernel independently *re-derived*
 * the result as `⊢ Derivable ⌜S⌝` — the construct-don't-trust status an imported
 * theorem has. A failed or skipped derivation is never a success. */
export type MmHolDerivation =
  | {
      ok: true;
      /** The kernel theorem, rendered — hypotheses included. Display VERBATIM:
       * a hypothesis-carrying theorem shown as `⊢ concl` is a false claim. */
      thm: string;
      /** The conclusion alone, without the turnstile or hypotheses. */
      statement: string;
      /** The raw HOL term behind `thm`. */
      raw: string;
      /** Hypotheses the theorem carries (empty for a closed theorem). */
      hyps: string[];
      hypCount: number;
      /** Which rule set the replay ran against (e.g. `proof-cited` — scoped to
       * just the assertions the proof references). */
      ruleSet: string;
      elapsedMs: number;
    }
  /** The kernel was asked and could not derive it — NOT a proof. */
  | { ok: false; skipped?: false; error: string }
  /** The kernel was never asked (e.g. database too large); nothing is claimed. */
  | { ok: false; skipped: true; reason: string };

export type MmVerifyResponse =
  | {
      ok: true;
      conclusion: string;
      steps: MmProofStep[];
      /** Absent if the server did not attempt a kernel derivation at all. */
      hol?: MmHolDerivation;
    }
  | { ok: false; error: string };

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
