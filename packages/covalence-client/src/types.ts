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
export type ObjectKind = 'blob' | 'tree' | 'commit' | 'tag';

/** GET /api/objects/info/:hash */
export interface ObjectInfoResponse {
  kind: ObjectKind;
  size: number;
}

/** Entry in a tree listing. */
export interface TreeEntry {
  name: string;
  mode: string;
  hash: Hash;
}
