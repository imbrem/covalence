// Base URL for the cov serve backend.
// Empty string = same-origin (default, for `cov serve` embedded mode).
// Set VITE_COV_API_BASE at build time to point at a remote backend,
// e.g. VITE_COV_API_BASE=https://cov.example.com bun run build:web
const base = (import.meta.env.VITE_COV_API_BASE as string | undefined) ?? '';

export async function fetchApi<T>(path: string): Promise<T> {
	const res = await fetch(`${base}${path}`);
	if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
	return res.json();
}
