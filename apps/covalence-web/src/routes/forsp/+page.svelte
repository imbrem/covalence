<script lang="ts">
	// FORSP frontend page — LIVE. `covalence-forsp` (crates/lang/forsp), a real
	// concatenative (Forth-meets-Lisp) evaluator, is compiled to WASM inside
	// `covalence-web-kernel` and exposed as `forsp_eval_cell`. This page runs the
	// program you type — read → compute → print — in your browser, and shows the
	// top-of-stack value as an S-expression.
	import { onMount } from 'svelte';
	import examples from '$lib/forspExamples.json';

	type Example = { title: string; src: string };
	const cases = examples as Example[];

	let selected = $state(0);
	let src = $state(cases[0].src.replace(/\n$/, ''));
	let wasm = $state<any>(null);
	let loadError = $state('');

	// Live eval: recomputed whenever `src` (or `wasm`) changes.
	let result = $derived.by(() => {
		if (!wasm) return { ok: true as boolean, result: '', error: '', pending: true };
		try {
			const r = JSON.parse(wasm.forsp_eval_cell(src));
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

<svelte:head><title>forsp — covalence</title></svelte:head>

<main>
	<h1>forsp</h1>
	<p class="sub">
		<code>covalence-forsp</code> (<code>crates/lang/forsp</code>) is a small
		concatenative language — a stack machine in the Forth tradition with
		Lisp-style closures and quotation. <strong>This page runs it live in your
		browser</strong> via WASM: it reads, computes, and prints the top of the
		resulting stack as an S-expression.
	</p>

	<p class="note">
		Programs are postfix: <code>3 4 +</code> pushes <code>3</code> and
		<code>4</code>, then applies <code>+</code>. <code>$x</code> binds the top
		of stack to <code>x</code>; <code>^x</code> pushes it back;
		<code>(…)</code> is a quotation (a closure), <code>force</code> runs one.
		The panel shows the value left on top of the stack.
	</p>

	<div class="examples">
		{#each cases as c, i}
			<button class:on={selected === i} onclick={() => loadExample(i)}>{c.title}</button>
		{/each}
	</div>

	<div class="panes">
		<section class="pane">
			<header>Forsp <span class="tag">editable</span></header>
			<textarea class="src" bind:value={src} spellcheck="false"></textarea>
		</section>
		<div class="mid">→</div>
		<section class="pane">
			<header>
				top of stack
				{#if result.pending && !loadError}<span class="tag">loading…</span>{/if}
			</header>
			{#if loadError}
				<pre class="err">failed to load wasm: {loadError}</pre>
			{:else if result.pending}
				<pre class="out muted">compiling the evaluator to WASM…</pre>
			{:else if result.ok}
				<pre class="out">{result.result}</pre>
			{:else}
				<pre class="err">{result.error}</pre>
			{/if}
		</section>
	</div>

	<p class="status">
		<strong>Status:</strong> live — read → compute → print in your browser via
		<code>forsp_eval_cell</code> (<code>covalence-web-kernel</code> WASM). This
		is a genuine concatenative evaluator (closures, recursion, content-addressed
		values); unlike <a href="/lisp">/lisp</a>, values here are not (yet) carried
		by kernel theorems.
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
	.sub,
	.note {
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
