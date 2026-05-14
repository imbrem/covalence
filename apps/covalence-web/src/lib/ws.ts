const base = (import.meta.env.VITE_COV_API_BASE as string | undefined) ?? '';

/** Derive the WebSocket URL for the REPL endpoint. */
function replUrl(): string {
	if (base) {
		// Explicit base: convert http(s) to ws(s)
		const url = new URL('/api/repl', base);
		url.protocol = url.protocol === 'https:' ? 'wss:' : 'ws:';
		return url.toString();
	}
	// Same-origin
	const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
	return `${proto}//${location.host}/api/repl`;
}

export function connectRepl(): WebSocket {
	return new WebSocket(replUrl());
}
