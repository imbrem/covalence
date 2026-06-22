import { CovalenceError } from './errors.js';
import type {
  Hash,
  InfoResponse,
  HealthResponse,
  HashResponse,
  BlobStatsResponse,
  DecideResponse,
  ObjectInfoResponse,
  TreeEntry,
  MmDbResponse,
  MmDbInfo,
  MmDbListEntry,
  MmServerStats,
  MmHolInfo,
  MmGraphResponse,
  ImportTheoremDetail,
} from './types.js';

/** Build a `?user=<value>` query string (empty when no user). */
function userQuery(user?: string): string {
  return user ? `?user=${encodeURIComponent(user)}` : '';
}

export interface CovalenceClientOptions {
  /** Base URL for the cov serve backend. Empty string = same-origin. */
  baseUrl?: string;
  /** Custom fetch implementation (defaults to globalThis.fetch). */
  fetch?: typeof globalThis.fetch;
}

export class CovalenceClient {
  private readonly baseUrl: string;
  private readonly fetch: typeof globalThis.fetch;

  constructor(options: CovalenceClientOptions = {}) {
    this.baseUrl = options.baseUrl ?? '';
    this.fetch = options.fetch ?? globalThis.fetch.bind(globalThis);
  }

  // --- Info / Health ---

  async info(): Promise<InfoResponse> {
    return this.fetchJson<InfoResponse>('/api/info');
  }

  async health(): Promise<HealthResponse> {
    return this.fetchJson<HealthResponse>('/api/health');
  }

  // --- Blobs ---

  async storeBlob(data: Uint8Array | ArrayBuffer): Promise<Hash> {
    const res = await this.fetch(`${this.baseUrl}/api/blobs`, {
      method: 'POST',
      body: data as BodyInit,
    });
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    const json: HashResponse = await res.json();
    return json.hash;
  }

  async blobCount(): Promise<number | null> {
    const json = await this.fetchJson<BlobStatsResponse>('/api/blobs');
    return json.count;
  }

  async getBlob(hash: Hash): Promise<Uint8Array | null> {
    const res = await this.fetch(`${this.baseUrl}/api/blobs/${hash}`);
    if (res.status === 404) return null;
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return new Uint8Array(await res.arrayBuffer());
  }

  async hasBlob(hash: Hash): Promise<boolean> {
    const res = await this.fetch(`${this.baseUrl}/api/blobs/${hash}`, {
      method: 'HEAD',
    });
    if (res.status === 404) return false;
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return true;
  }

  // --- Decide ---

  async decide(hash: Hash): Promise<DecideResponse> {
    return this.fetchJson<DecideResponse>(`/api/decide/${hash}`);
  }

  // --- Objects ---

  async objectInfo(hash: Hash): Promise<ObjectInfoResponse | null> {
    const res = await this.fetch(`${this.baseUrl}/api/objects/info/${hash}`);
    if (res.status === 404) return null;
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.json();
  }

  async treeLs(hash: Hash): Promise<TreeEntry[]> {
    return this.fetchJson<TreeEntry[]>(`/api/objects/tree/${hash}/ls`);
  }

  async getObjectBlob(hash: Hash): Promise<Uint8Array | null> {
    const res = await this.fetch(`${this.baseUrl}/api/objects/blob/${hash}`);
    if (res.status === 404) return null;
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return new Uint8Array(await res.arrayBuffer());
  }

  // --- Convenience ---

  async storeBlobFromUrl(url: string): Promise<Hash> {
    const res = await this.fetch(`${this.baseUrl}/api/blobs/url`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ url }),
    });
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    const json: HashResponse = await res.json();
    return json.hash;
  }

  async storeBlobFromFile(path: string): Promise<Hash> {
    const res = await this.fetch(`${this.baseUrl}/api/blobs/file`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ path }),
    });
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    const json: HashResponse = await res.json();
    return json.hash;
  }

  async eval(expr: string): Promise<string> {
    const res = await this.fetch(`${this.baseUrl}/api/eval`, {
      method: 'POST',
      headers: { 'Content-Type': 'text/plain' },
      body: expr,
    });
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.text();
  }

  // --- WebSocket ---

  connectRepl(): WebSocket {
    return new WebSocket(this.wsUrl('/api/repl'));
  }

  // --- TEMPORARY / THROWAWAY DEMO: Metamath sessions (the `/metamath` page) ---

  /**
   * POST /api/metamath/upload — parse (or reuse) a `.mm` source into a cached
   * session. `opts.from` records provenance (a URL or label); `opts.user` keys
   * the session per user. Returns the content hash (`file`) + theorem count +
   * recorded origin.
   */
  async createMmDb(
    source: string,
    opts: { user?: string; from?: string } = {},
  ): Promise<MmDbResponse> {
    const params = new URLSearchParams();
    if (opts.user) params.set('user', opts.user);
    if (opts.from) params.set('from', opts.from);
    const qs = params.toString();
    const res = await this.fetch(
      `${this.baseUrl}/api/metamath/upload${qs ? `?${qs}` : ''}`,
      {
        method: 'POST',
        headers: { 'Content-Type': 'text/plain' },
        body: source,
      },
    );
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.json();
  }

  /**
   * GET /api/metamath/session/{hash} — lightweight session metadata. The
   * "attach by hash" probe: returns `null` (404) if the hash isn't loaded on
   * the server, else `{file, total, origin, proving, proved, errors}` without
   * downloading the graph.
   */
  async mmDbInfo(hash: Hash, user?: string): Promise<MmDbInfo | null> {
    const res = await this.fetch(`${this.baseUrl}/api/metamath/session/${hash}${userQuery(user)}`);
    if (res.status === 404) return null;
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.json();
  }

  /** GET /api/metamath/sessions — every cached session on the server (the
   * "loaded on server" picker). */
  async mmDbList(): Promise<MmDbListEntry[]> {
    return this.fetchJson<MmDbListEntry[]>('/api/metamath/sessions');
  }

  /** GET /api/metamath/stats — a point sample of server/process metrics (RAM,
   * cached theorems, uptime). Poll on an interval to build a time series. */
  async mmServerStats(): Promise<MmServerStats> {
    return this.fetchJson<MmServerStats>('/api/metamath/stats');
  }

  /** GET /api/metamath/session/{hash}/symbols — the database's `token → Unicode`
   * typeset map (parsed from its `$t` `althtmldef` section; empty if it has none). */
  async mmSymbols(hash: Hash, user?: string): Promise<Record<string, string>> {
    const res = await this.fetch(
      `${this.baseUrl}/api/metamath/session/${hash}/symbols${userQuery(user)}`,
    );
    if (!res.ok) return {};
    return (await res.json()) as Record<string, string>;
  }

  /** GET /api/metamath/session/{hash}/hol — pass-1 HOL surface stats + the
   * database's named definitions (formers + df-*). Triggers pass 1 server-side. */
  async mmHol(hash: Hash, user?: string): Promise<MmHolInfo> {
    const res = await this.fetch(
      `${this.baseUrl}/api/metamath/session/${hash}/hol${userQuery(user)}`,
    );
    return (await res.json()) as MmHolInfo;
  }

  /** GET /api/metamath/session/{hash}/hol/terms — the whole `label → HOL term`
   * map (pass 1; available before proving). One fetch, cached by the page. */
  async mmHolTerms(hash: Hash, user?: string): Promise<Record<string, string>> {
    const res = await this.fetch(
      `${this.baseUrl}/api/metamath/session/${hash}/hol/terms${userQuery(user)}`,
    );
    if (!res.ok) return {};
    return (await res.json()) as Record<string, string>;
  }

  /** GET /api/metamath/session/{hash}/graph — the cached static declaration graph. */
  async mmGraph(hash: Hash, user?: string): Promise<MmGraphResponse> {
    const res = await this.fetch(
      `${this.baseUrl}/api/metamath/session/${hash}/graph${userQuery(user)}`,
    );
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.json();
  }

  /** GET /api/metamath/session/{hash}/theorem/{name} — one theorem's full detail. */
  async mmTheorem(hash: Hash, name: string, user?: string): Promise<ImportTheoremDetail> {
    const res = await this.fetch(
      `${this.baseUrl}/api/metamath/session/${hash}/theorem/${encodeURIComponent(name)}${userQuery(user)}`,
    );
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.json();
  }

  /**
   * POST /api/metamath/session/{hash}/prove — kick off the parallel kernel import.
   * Idempotent: returns `{started:false}` if a prove run is already underway.
   */
  async startMmProve(hash: Hash, user?: string, workers?: number): Promise<{ started: boolean }> {
    const params = new URLSearchParams();
    if (user) params.set('user', user);
    if (workers != null) params.set('workers', String(workers));
    const qs = params.toString();
    const res = await this.fetch(
      `${this.baseUrl}/api/metamath/session/${hash}/prove${qs ? `?${qs}` : ''}`,
      { method: 'POST' },
    );
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.json();
  }

  /**
   * WS /api/metamath/session/{hash}/status — the thin live-status channel. Sends a
   * `snapshot` on connect, then `proving`/`proved`/`done` frames.
   */
  connectMmStatus(hash: Hash, user?: string): WebSocket {
    return new WebSocket(this.wsUrl(`/api/metamath/session/${hash}/status${userQuery(user)}`));
  }

  // --- Internal ---

  /** Build a `ws:`/`wss:` URL for `path`, mirroring same-origin vs baseUrl. */
  private wsUrl(path: string): string {
    if (this.baseUrl) {
      const url = new URL(path, this.baseUrl);
      url.protocol = url.protocol === 'https:' ? 'wss:' : 'ws:';
      return url.toString();
    }
    const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
    return `${proto}//${location.host}${path}`;
  }

  private async fetchJson<T>(path: string): Promise<T> {
    const res = await this.fetch(`${this.baseUrl}${path}`);
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.json();
  }
}
