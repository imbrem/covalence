// A server-backed REPL binding for the `<Repl>` component: one persistent
// per-tab session (a random id) over a POST endpoint evaluated on the native
// kernel (`cov serve`). Shared by /lisp and /forsp so the pages stay thin.
//
// The endpoint gets `{ session, src }` and returns `{ ok, result?, error? }`;
// `<endpoint>/reset` drops the session. With `show: true`, hovering a cell
// fetches its `⊢` theorem via the `#show` directive.

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

async function postJson(path: string, body: unknown): Promise<Record<string, unknown>> {
	const res = await fetch(path, {
		method: 'POST',
		headers: { 'content-type': 'application/json' },
		body: JSON.stringify(body)
	});
	return res.json();
}

export function serverRepl(endpoint: string, opts: { show?: boolean } = {}): ServerRepl {
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

	return { evalCell, showCell, onReset };
}
