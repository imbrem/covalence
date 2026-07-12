<script lang="ts">
	// HASKELL FRONTEND page — LIVE. `covalence-haskell` (crates/lang/haskell), the
	// kernel-agnostic dialect front end, is compiled to WASM inside
	// `covalence-web-kernel` and exposed as `haskell_to_sexpr`; this page parses +
	// lowers the Haskell you type, in your browser, to the S-expression interchange:
	//
	//   Haskell dialect  ==(one canonical lowering)==>  S-expressions  ==(pluggable)==>  backend
	//
	import { onMount } from 'svelte';
	import examples from '$lib/haskellExamples.json';

	type Example = { title: string; kind: string; src: string; sexpr: string };
	const cases = examples as Example[];

	let selected = $state(0);
	let src = $state(cases[0].src.replace(/\n$/, ''));
	// The wasm-bindgen module (loaded on mount); `any` to avoid import-type churn.
	let wasm = $state<any>(null);
	let loadError = $state('');

	// Live parse: recomputed whenever `src` (or `wasm`) changes.
	let result = $derived.by(() => {
		if (!wasm) return { ok: true as boolean, sexpr: '', error: '', pending: true };
		try {
			const r = JSON.parse(wasm.haskell_to_sexpr(src));
			return { ok: !!r.ok, sexpr: r.sexpr ?? '', error: r.error ?? '', pending: false };
		} catch (e) {
			return { ok: false, sexpr: '', error: String(e), pending: false };
		}
	});

	// The same input lowered through the HOL backend to a real kernel `Term`
	// (carved sexpr) — the dialect connected to the kernel, in your browser.
	let term = $derived.by(() => {
		if (!wasm) return { ok: true as boolean, term: '', error: '', pending: true };
		try {
			const r = JSON.parse(wasm.haskell_to_hol_term(src));
			return { ok: !!r.ok, term: r.term ?? '', error: r.error ?? '', pending: false };
		} catch (e) {
			return { ok: false, term: '', error: String(e), pending: false };
		}
	});

	// The TYPED HOL lowering: an *annotated* def/expr → a well-typed kernel
	// `Term` with its HOL type (via `haskell_to_typed_hol`). Unlike the carved
	// term above, this needs annotations — unannotated input reports a clean
	// error, which is exactly the point of the typed backend.
	let typed = $derived.by(() => {
		if (!wasm) return { ok: true as boolean, term: '', type: '', error: '', pending: true };
		try {
			const r = JSON.parse(wasm.haskell_to_typed_hol(src));
			return {
				ok: !!r.ok,
				term: r.term ?? '',
				type: r.type ?? '',
				error: r.error ?? '',
				pending: false
			};
		} catch (e) {
			return { ok: false, term: '', type: '', error: String(e), pending: false };
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

<svelte:head><title>haskell frontend — covalence</title></svelte:head>

<main>
	<h1>haskell frontend</h1>
	<p class="sub">
		<code>covalence-haskell</code> (<code>crates/lang/haskell</code>) is a
		kernel-agnostic on-ramp: a small Haskell dialect lowered through ONE
		canonical desugaring into an S-expression interchange IR, then realized by
		a pluggable backend. <strong>This page runs it live in your browser</strong>
		via WASM.
	</p>

	<div class="pipeline">
		<span class="stage">Haskell dialect</span>
		<span class="arrow">→</span>
		<span class="stage">canonical lowering</span>
		<span class="arrow">→</span>
		<span class="stage">S-expression IR</span>
		<span class="arrow">→</span>
		<span class="stage muted">Realize backend<br /><em>(Text · Peano · HOL kernel term)</em></span>
	</div>

	<p class="note">
		The <strong>S-expression IR</strong> is the interchange point: third-party
		producers/consumers use it directly (text in / canonical text out) and never
		touch Haskell syntax. The <code>hol</code> feature realizes the same IR into
		carved <code>sexpr</code> kernel <code>Term</code>s.
	</p>

	<div class="examples">
		{#each cases as c, i}
			<button class:on={selected === i} onclick={() => loadExample(i)}>{c.title}</button>
		{/each}
	</div>

	<div class="panes">
		<section class="pane">
			<header>Haskell <span class="tag">editable</span></header>
			<textarea class="src" bind:value={src} spellcheck="false"></textarea>
		</section>
		<div class="mid">→</div>
		<section class="pane">
			<header>
				S-expression IR
				{#if result.pending && !loadError}<span class="tag">loading…</span>{/if}
			</header>
			{#if loadError}
				<pre class="err">failed to load wasm: {loadError}</pre>
			{:else if result.pending}
				<pre class="sexpr muted">compiling the parser to WASM…</pre>
			{:else if result.ok}
				<pre class="sexpr">{result.sexpr}</pre>
			{:else}
				<pre class="err">{result.error}</pre>
			{/if}
		</section>
	</div>

	<section class="pane kernel">
		<header>
			kernel <code>Term</code>
			<span class="tag">carved sexpr — realized by the HOL backend, in the kernel</span>
		</header>
		{#if loadError}
			<pre class="err">failed to load wasm: {loadError}</pre>
		{:else if term.pending}
			<pre class="termout muted">…</pre>
		{:else if term.ok}
			<pre class="termout">{term.term}</pre>
		{:else}
			<pre class="err">{term.error}</pre>
		{/if}
	</section>

	<section class="pane kernel">
		<header>
			typed HOL <code>Term</code>
			<span class="tag">well-typed — via the Hol/Nat traits (needs annotations)</span>
		</header>
		{#if loadError}
			<pre class="err">failed to load wasm: {loadError}</pre>
		{:else if typed.pending}
			<pre class="termout muted">…</pre>
		{:else if typed.ok}
			<pre class="termout">{typed.term}<span class="ty">  :: {typed.type}</span></pre>
		{:else}
			<pre class="err">{typed.error}</pre>
		{/if}
	</section>

	<p class="status">
		<strong>Status:</strong> live — parsed + lowered in your browser, and
		<strong>connected to the kernel</strong>: <code>haskell_to_sexpr</code> gives the
		interchange IR, and <code>haskell_to_hol_term</code> realizes the same input to a
		genuine carved <code>sexpr</code> kernel <code>Term</code>, and
		<code>haskell_to_typed_hol</code> lowers an <em>annotated</em> input
		(e.g. <code>\(x :: nat) -&gt; x</code>) to a <strong>well-typed</strong> HOL
		term with its HOL type — all <code>covalence-web-kernel</code> WASM. Edit the
		Haskell above, or pick an example — a top-level def
		(<code>compose f g x = f (g x)</code>) or a bare expression
		(<code>\x -&gt; x</code>). Proof <em>checking</em> lives on the
		<a href="/proofs">proof checker</a> page.
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
	.pipeline {
		display: flex;
		flex-wrap: wrap;
		align-items: center;
		gap: 0.5rem;
		margin: 1rem 0;
	}
	.pipeline .stage {
		border: 1px solid var(--border);
		border-radius: 6px;
		padding: 0.4rem 0.7rem;
		background: var(--surface);
		font-size: 0.8rem;
		text-align: center;
	}
	.pipeline .stage.muted {
		color: var(--muted);
	}
	.pipeline .stage em {
		font-size: 0.72rem;
		opacity: 0.75;
	}
	.pipeline .arrow {
		color: var(--accent);
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
	.pane .sexpr {
		color: color-mix(in srgb, var(--accent) 55%, var(--fg));
	}
	.pane .sexpr.muted {
		color: var(--muted);
	}
	.pane .err {
		color: color-mix(in srgb, #e5484d 70%, var(--fg));
	}
	.pane.kernel {
		margin-top: 0.75rem;
	}
	.pane.kernel header .tag {
		text-transform: none;
		letter-spacing: 0;
		font-size: 0.68rem;
	}
	.pane .termout {
		color: color-mix(in srgb, #30a46c 60%, var(--fg));
		font-size: 0.8rem;
	}
	.pane .termout.muted {
		color: var(--muted);
	}
	.pane .termout .ty {
		color: var(--accent);
	}
	.status a {
		color: var(--accent);
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
	@media (max-width: 640px) {
		.panes {
			grid-template-columns: 1fr;
		}
		.mid {
			justify-content: center;
		}
	}
</style>
