<script lang="ts">
	// LISP frontend page — LIVE. `covalence-lisp` (crates/lang/lisp), compiled to
	// WASM inside `covalence-web-kernel` and exposed as `lisp_eval_cell`, evaluates
	// the Little Schemer ch1 form you type, in your browser. Every printed value is
	// read OFF a genuine kernel theorem (`⊢ program = value`) — the Session's
	// honesty invariant. This is chapter 1 only: primitives on quoted lists, not
	// yet recursion / a metacircular evaluator.
	import { onMount } from 'svelte';
	import examples from '$lib/lispExamples.json';

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
			const r = JSON.parse(wasm.lisp_eval_cell(src));
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

<svelte:head><title>lisp — covalence</title></svelte:head>

<main>
	<h1>lisp</h1>
	<p class="sub">
		<code>covalence-lisp</code> (<code>crates/lang/lisp</code>) is a small,
		kernel-backed Lisp. <strong>This page runs it live in your browser</strong>
		via WASM: you type a form, it is parsed, evaluated, and the value is printed.
	</p>

	<p class="note">
		<strong>Every printed value is backed by a kernel theorem.</strong> The REPL
		evaluates a program to a kernel <code>⊢ program = value</code> theorem and
		renders the value <em>off that theorem's conclusion</em> — there is no code
		path that prints a value that did not come off a proof. Use
		<code>#show EXPR</code> to see the full theorem.
	</p>

	<p class="note scope">
		<strong>Scope:</strong> this is <em>The Little Schemer</em> chapter 1 —
		primitives on quoted atom-lists (<code>car</code>, <code>cdr</code>,
		<code>cons</code>, <code>atom?</code>, <code>null?</code>,
		<code>eq?</code>). Not yet recursion or a metacircular evaluator.
	</p>

	<div class="examples">
		{#each cases as c, i}
			<button class:on={selected === i} onclick={() => loadExample(i)}>{c.title}</button>
		{/each}
	</div>

	<div class="panes">
		<section class="pane">
			<header>Lisp <span class="tag">editable</span></header>
			<textarea class="src" bind:value={src} spellcheck="false"></textarea>
		</section>
		<div class="mid">→</div>
		<section class="pane">
			<header>
				value
				{#if result.pending && !loadError}<span class="tag">loading…</span>{/if}
			</header>
			{#if loadError}
				<pre class="err">failed to load wasm: {loadError}</pre>
			{:else if result.pending}
				<pre class="out muted">compiling the kernel to WASM…</pre>
			{:else if result.ok}
				<pre class="out">{result.result}</pre>
			{:else}
				<pre class="err">{result.error}</pre>
			{/if}
		</section>
	</div>

	<p class="status">
		<strong>Status:</strong> live — parsed + evaluated in your browser via
		<code>lisp_eval_cell</code> (<code>covalence-web-kernel</code> WASM), and
		<strong>connected to the kernel</strong>: the value you see is read off a
		genuine <code>⊢ program = value</code> theorem. Little Schemer ch1 primitives
		only — recursion and the metacircular interpreter are future work.
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
	.note.scope {
		margin-top: -0.5rem;
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
