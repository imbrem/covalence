<script lang="ts">
	// FORTH frontend page — PLACEHOLDER. The route + wasm seam
	// (`forth_eval_cell`) exist so the page renders and the pipeline is wired, but
	// there is no evaluator yet: the wasm export returns
	// `{ ok: false, error: "forth: coming soon" }`.
	import { onMount } from 'svelte';
	import examples from '$lib/forthExamples.json';

	type Example = { title: string; src: string };
	const cases = examples as Example[];

	let selected = $state(0);
	let src = $state(cases[0].src.replace(/\n$/, ''));
	let wasm = $state<any>(null);
	let loadError = $state('');

	let result = $derived.by(() => {
		if (!wasm) return { ok: true as boolean, result: '', error: '', pending: true };
		try {
			const r = JSON.parse(wasm.forth_eval_cell(src));
			return { ok: !!r.ok, result: r.result ?? '', error: r.error ?? '', pending: false };
		} catch (e) {
			return { ok: false, result: '', error: String(e), pending: false };
		}
	});

	onMount(async () => {
		try {
			const mod = await import('$lib/kernel/covalence_web_kernel.js');
			const wasmUrl = (await import('$lib/kernel/covalence_web_kernel_bg.wasm?url')).default;
			await mod.default({ module_or_path: wasmUrl });
			wasm = mod;
		} catch (e) {
			loadError = String(e);
		}
	});

	function loadExample(i: number) {
		selected = i;
		src = cases[i].src.replace(/\n$/, '');
	}
</script>

<svelte:head><title>forth — covalence</title></svelte:head>

<main>
	<h1>forth <span class="badge">coming soon</span></h1>
	<p class="sub">
		A Forth REPL demo is planned. The route and the wasm seam
		(<code>forth_eval_cell</code> in <code>covalence-web-kernel</code>) are
		already wired — the page renders and calls into the kernel wasm — but there
		is <strong>no evaluator yet</strong>, so every input reports
		<code>forth: coming soon</code>.
	</p>

	<div class="examples">
		{#each cases as c, i}
			<button class:on={selected === i} onclick={() => loadExample(i)}>{c.title}</button>
		{/each}
	</div>

	<div class="panes">
		<section class="pane">
			<header>Forth <span class="tag">editable</span></header>
			<textarea class="src" bind:value={src} spellcheck="false"></textarea>
		</section>
		<div class="mid">→</div>
		<section class="pane">
			<header>
				result
				{#if result.pending && !loadError}<span class="tag">loading…</span>{/if}
			</header>
			{#if loadError}
				<pre class="err">failed to load wasm: {loadError}</pre>
			{:else if result.pending}
				<pre class="out muted">loading the kernel WASM…</pre>
			{:else if result.ok}
				<pre class="out">{result.result}</pre>
			{:else}
				<pre class="err">{result.error}</pre>
			{/if}
		</section>
	</div>

	<p class="status">
		<strong>Status:</strong> placeholder — the wasm export exists and returns
		<code>forth: coming soon</code>. A real evaluator lands later; for a working
		concatenative language today, see <a href="/forsp">/forsp</a>.
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
		display: flex;
		align-items: center;
		gap: 0.5rem;
	}
	.badge {
		font-size: 0.65rem;
		text-transform: uppercase;
		letter-spacing: 0.05em;
		color: var(--accent);
		border: 1px solid var(--accent);
		border-radius: 4px;
		padding: 0.1rem 0.35rem;
	}
	.sub {
		color: var(--muted);
		font-size: 0.85rem;
		line-height: 1.5;
		margin: 0.4rem 0 1rem;
	}
	code {
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 3px;
		padding: 0 3px;
		font-size: 0.85em;
	}
	.examples {
		display: flex;
		flex-wrap: wrap;
		gap: 0.35rem;
		margin: 1rem 0;
	}
	button {
		font: inherit;
		font-size: 0.78rem;
		color: var(--muted);
		background: var(--surface);
		border: 1px solid var(--border);
		border-radius: 5px;
		padding: 0.25rem 0.55rem;
		cursor: pointer;
	}
	button:hover {
		color: var(--fg);
	}
	button.on {
		color: var(--fg);
		border-color: var(--accent);
		background: color-mix(in srgb, var(--accent) 18%, transparent);
	}
	.panes {
		display: grid;
		grid-template-columns: 1fr auto 1fr;
		gap: 0.75rem;
		align-items: stretch;
	}
	.pane {
		border: 1px solid var(--border);
		border-radius: 8px;
		overflow: hidden;
		background: var(--surface);
		display: flex;
		flex-direction: column;
	}
	.pane header {
		font-size: 0.72rem;
		text-transform: uppercase;
		letter-spacing: 0.04em;
		color: var(--muted);
		padding: 0.4rem 0.7rem;
		border-bottom: 1px solid var(--border);
		display: flex;
		justify-content: space-between;
	}
	.pane header .tag {
		color: var(--accent);
	}
	.pane pre,
	.pane textarea {
		padding: 0.7rem;
		font-size: 0.85rem;
		white-space: pre-wrap;
		word-break: break-word;
		line-height: 1.5;
		flex: 1;
		margin: 0;
	}
	.pane textarea {
		resize: vertical;
		min-height: 8rem;
		font-family: var(--font-mono);
		color: var(--fg);
		background: transparent;
		border: 0;
		outline: none;
	}
	.pane .out {
		color: color-mix(in srgb, #30a46c 60%, var(--fg));
	}
	.pane .out.muted {
		color: var(--muted);
	}
	.pane .err {
		color: color-mix(in srgb, #e5484d 70%, var(--fg));
	}
	.mid {
		display: flex;
		align-items: center;
		color: var(--accent);
		font-size: 1.1rem;
	}
	.status {
		margin-top: 1.25rem;
		font-size: 0.8rem;
		color: var(--muted);
	}
	.status a {
		color: var(--accent);
	}
	@media (max-width: 640px) {
		.panes {
			grid-template-columns: 1fr;
		}
		.mid {
			justify-content: center;
		}
	}
</style>
