// A server-backed REPL binding for the `<Repl>` component: one persistent
// per-tab session (a random id) over a POST endpoint evaluated on the native
// kernel (`cov serve`). Shared by /lisp and /forsp so the pages stay thin.
//
// The endpoint gets `{ session, src }` and returns `{ ok, result?, error? }`;
// `<endpoint>/reset` drops the session. With `show: true`, hovering a cell
// fetches its full `hyps ⊢ concl` sequent via the `#show` directive (rendered
// verbatim by `<Repl>` — the turnstile comes from the server's kernel `Thm`).

export interface EvalResult {
	ok: boolean;
	result: string;
	error: string;
}

export interface ServerRepl {
	evalCell: (src: string) => Promise<EvalResult>;
	showCell: ((src: string) => Promise<string>) | null;
	onReset: () => void;
}

function newSession(): string {
	return typeof crypto !== 'undefined' && crypto.randomUUID
		? crypto.randomUUID()
		: `s${Math.random().toString(36).slice(2)}`;
}

/**
 * POST JSON and parse JSON back. Evaluation errors ride a 200 as
 * `{ ok: false, error }`; anything else (a 500 page, an HTML error document
 * from a proxy) is a TRANSPORT failure and is thrown with the status and a
 * snippet of the body, so the cell shows something readable instead of
 * `SyntaxError: Unexpected token '<'`.
 */
async function postJson(path: string, body: unknown): Promise<Record<string, unknown>> {
	const res = await fetch(path, {
		method: 'POST',
		headers: { 'content-type': 'application/json' },
		body: JSON.stringify(body)
	});
	const ctype = res.headers.get('content-type') ?? '';
	if (!res.ok || !ctype.includes('json')) {
		const text = await res.text().catch(() => '');
		const detail = text.trim().slice(0, 200) || res.statusText || 'no response body';
		throw new Error(`server error ${res.status}: ${detail}`);
	}
	return res.json();
}

/**
 * Sessions are memoized per endpoint: an SPA navigation away and back must
 * land in the SAME server session (the `defun`s are still there), which is
 * also what makes the persisted transcript honest.
 */
const sessions = new Map<string, ServerRepl>();

export function serverRepl(endpoint: string, opts: { show?: boolean } = {}): ServerRepl {
	const cached = sessions.get(endpoint);
	if (cached) return cached;
	const session = newSession();

	const evalCell = async (src: string): Promise<EvalResult> => {
		const r = await postJson(endpoint, { session, src });
		return { ok: !!r.ok, result: (r.result as string) ?? '', error: (r.error as string) ?? '' };
	};

	const showCell = opts.show
		? async (src: string): Promise<string> => {
				const r = await postJson(endpoint, { session, src: `#show ${src}` });
				return r.ok ? ((r.result as string) ?? '') : '';
			}
		: null;

	const onReset = () => {
		void postJson(`${endpoint}/reset`, { session });
	};

	const repl: ServerRepl = { evalCell, showCell, onReset };
	sessions.set(endpoint, repl);
	return repl;
}
