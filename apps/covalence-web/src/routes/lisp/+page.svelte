<script lang="ts">
	// LISP REPL — connects to the RUNNING SERVER (POST /api/lisp), which evaluates
	// each cell on the NATIVE kernel in a persistent per-tab session (`defun`s
	// accumulate). No client-side WASM. Every printed value is read off a genuine
	// kernel theorem (`⊢ program = value`); hover a cell to see it (via `#show`).
	import Repl from '$lib/Repl.svelte';
	import examples from '$lib/lispExamples.json';

	// One persistent server session per tab.
	const session =
		typeof crypto !== 'undefined' && crypto.randomUUID
			? crypto.randomUUID()
			: `s${Math.random().toString(36).slice(2)}`;

	async function post(path: string, body: unknown) {
		const res = await fetch(path, {
			method: 'POST',
			headers: { 'content-type': 'application/json' },
			body: JSON.stringify(body)
		});
		return res.json();
	}

	const evalCell = async (src: string) => {
		const r = await post('/api/lisp', { session, src });
		return { ok: !!r.ok, result: r.result ?? '', error: r.error ?? '' };
	};
	// Hover → the kernel theorem behind a value, via the `#show` directive.
	const showCell = async (src: string) => {
		const r = await post('/api/lisp', { session, src: `#show ${src}` });
		return r.ok ? (r.result ?? '') : '';
	};
	const onReset = () => {
		post('/api/lisp/reset', { session });
	};
</script>

<svelte:head><title>lisp — covalence</title></svelte:head>

<main>
	<h1>lisp</h1>
	<p class="sub">
		A small, kernel-backed Lisp (<code>covalence-lisp</code>). This REPL talks to the
		running <code>cov serve</code> and evaluates each cell on the <strong>native
		kernel</strong> — <strong>every printed value is backed by a kernel theorem</strong>
		(<code>⊢ program = value</code>). <strong>Hover a result</strong> to see its proof.
	</p>
	<p class="sub">
		A real REPL: <code>defun</code>s persist across cells (a per-tab server session). Try
		the numbered examples in order — define <code>lat?</code>, then use it; or define the
		<code>★ metacircular eval</code> and run it. User definitions ride along as
		<em>hypotheses</em> (<code>definitions ⊢ program = value</code>), sound even for
		recursion that might not terminate.
	</p>

	<Repl {evalCell} {showCell} {onReset} examples={examples as any} />

	<p class="foot">
		Little Schemer ch1 primitives (<code>car cdr cons atom? null? eq?</code>) +
		<code>cond</code>/<code>lambda</code>/<code>defun</code> recursion; the metacircular
		interpreter runs its ground <code>quote/car/cdr/cons</code> fragment. Needs a running
		server (<code>cov serve</code>, or <code>cov serve --api</code> + <code>bun run dev:web</code>).
	</p>
</main>

<style>
	main {
		max-width: 60rem;
		margin: 1.5rem auto;
		padding: 0 1rem 3rem;
		font-family: var(--font-mono);
		color: var(--fg);
	}
	h1 {
		font-size: 1.4rem;
	}
	.sub {
		color: var(--muted);
		font-size: 0.85rem;
		line-height: 1.55;
		margin: 0.4rem 0 0.8rem;
	}
	.foot {
		margin-top: 1.25rem;
		font-size: 0.78rem;
		color: var(--muted);
		line-height: 1.5;
	}
	code {
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 3px;
		font-size: 0.85em;
	}
</style>
