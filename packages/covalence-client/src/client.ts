import { CovalenceError } from './errors.js';
import type {
  Hash,
  InfoResponse,
  HealthResponse,
  HashResponse,
  BlobStatsResponse,
  DecideResponse,
} from './types.js';

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
    let wsUrl: string;
    if (this.baseUrl) {
      const url = new URL('/api/repl', this.baseUrl);
      url.protocol = url.protocol === 'https:' ? 'wss:' : 'ws:';
      wsUrl = url.toString();
    } else {
      const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
      wsUrl = `${proto}//${location.host}/api/repl`;
    }
    return new WebSocket(wsUrl);
  }

  // --- Internal ---

  private async fetchJson<T>(path: string): Promise<T> {
    const res = await this.fetch(`${this.baseUrl}${path}`);
    if (!res.ok) throw new CovalenceError(res.status, `${res.status} ${res.statusText}`);
    return res.json();
  }
}
