/**
 * Shared plumbing for the e2e specs.
 *
 * `serverUrl()` is read per-call rather than captured at module load: the
 * worker process inherits COV_E2E_URL from global-setup, but reading it lazily
 * keeps the helper correct no matter when a spec file is imported.
 */

/** Base URL of the server under test (no trailing slash). */
export function serverUrl(): string {
	const url = process.env.COV_E2E_URL;
	if (!url) throw new Error('COV_E2E_URL is unset — global-setup did not run');
	return url.replace(/\/$/, '');
}

export type CellResponse = { ok: true; result: string } | { ok: false; error: string };

/** POST one REPL cell to `/api/lisp` or `/api/forsp`. */
export async function evalCell(
	endpoint: 'lisp' | 'forsp',
	session: string,
	src: string
): Promise<CellResponse> {
	const res = await fetch(`${serverUrl()}/api/${endpoint}`, {
		method: 'POST',
		headers: { 'Content-Type': 'application/json' },
		body: JSON.stringify({ session, src })
	});
	if (!res.ok) throw new Error(`POST /api/${endpoint} → HTTP ${res.status}`);
	return (await res.json()) as CellResponse;
}

/** POST `/api/{endpoint}/reset`, dropping the session's accumulated state. */
export async function resetSession(endpoint: 'lisp' | 'forsp', session: string): Promise<void> {
	const res = await fetch(`${serverUrl()}/api/${endpoint}/reset`, {
		method: 'POST',
		headers: { 'Content-Type': 'application/json' },
		body: JSON.stringify({ session })
	});
	if (!res.ok) throw new Error(`POST /api/${endpoint}/reset → HTTP ${res.status}`);
}

/** A session id unique to one test, so parallel workers never collide. */
export function sessionId(tag: string): string {
	return `e2e-${tag}-${Math.random().toString(36).slice(2, 10)}`;
}
