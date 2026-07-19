<script lang="ts">
	// HASKELL FRONTEND page — LIVE. `covalence-haskell` (crates/lang/haskell), the
	// kernel-agnostic dialect front end, is compiled to WASM inside
	// `covalence-web-kernel` and exposed as `haskell_to_sexpr`; this page parses +
	// lowers the Haskell you type, in your browser, to the S-expression interchange:
	//
	//   Haskell dialect  ==(one canonical lowering)==>  S-expressions  ==(pluggable)==>  backend
	//
	import '$lib/kernelPages.css';
	import { parseResult, type KernelExports } from '$lib/kernelApi';
	import { useKernel, liveCheck } from '$lib/kernelState.svelte';
	import examples from '$lib/haskellExamples.json';

	type Example = { title: string; kind: string; src: string; sexpr: string };
	const cases = examples as Example[];

	let selected = $state(0);
	let src = $state(cases[0].src.replace(/\n$/, ''));

	const k = useKernel();

	// All three lowerings of the SAME input, computed together behind ONE
	// debounce. They used to be three separate `$derived.by`, i.e. three WASM
	// calls on every keystroke; the parse is cheap but not free, and the typed
	// backend is the expensive one.
	type Lowering = {
		sexpr: { ok: boolean; sexpr: string; error: string };
		term: { ok: boolean; term: string; error: string };
		typed: { ok: boolean; term: string; type: string; error: string };
	};

	const live = liveCheck<{ kernel: KernelExports; src: string }, Lowering>({
		key: (i) => i.src,
		run: ({ kernel, src }) => {
			const sexpr = parseResult<{ sexpr: string }>(kernel.haskell_to_sexpr(src));
			const term = parseResult<{ term: string }>(kernel.haskell_to_hol_term(src));
			const typed = parseResult<{ term: string; type: string }>(
				kernel.haskell_to_typed_hol(src)
			);
			return {
				sexpr: {
					ok: sexpr.ok,
					sexpr: sexpr.ok ? sexpr.sexpr : '',
					error: sexpr.ok ? '' : sexpr.error
				},
				term: {
					ok: term.ok,
					term: term.ok ? term.term : '',
					error: term.ok ? '' : term.error
				},
				typed: {
					ok: typed.ok,
					term: typed.ok ? typed.term : '',
					type: typed.ok ? typed.type : '',
					error: typed.ok ? '' : typed.error
				}
			};
		}
	});

	// Re-lower whenever the source changes, and once the kernel arrives.
	$effect(() => {
		const kernel = k.kernel;
		const text = src;
		if (!kernel) return;
		live.schedule({ kernel, src: text });
	});

	let out = $derived(live.result);

	function loadExample(i: number) {
		selected = i;
		src = cases[i].src.replace(/\n$/, '');
	}
</script>

<svelte:head><title>haskell frontend — covalence</title></svelte:head>

<main class="demo-page">
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
			<button class:on={selected === i} onclick={() => loadExample(i)} data-testid="example-button"
				>{c.title}</button
			>
		{/each}
	</div>

	<div class="panes">
		<section class="pane">
			<header>Haskell <span class="tag">editable</span></header>
			<textarea class="src" bind:value={src} spellcheck="false" data-testid="haskell-input"
			></textarea>
		</section>
		<div class="mid">→</div>
		<section class="pane">
			<header>
				S-expression IR
				{#if live.busy}<span class="tag">…</span>{/if}
			</header>
			{#if k.error}
				<pre class="err">failed to load wasm: {k.error}</pre>
			{:else if !out}
				<pre class="sexpr muted">compiling the parser to WASM…</pre>
			{:else if out.sexpr.ok}
				<pre class="sexpr" data-testid="haskell-sexpr">{out.sexpr.sexpr}</pre>
			{:else}
				<pre class="err">{out.sexpr.error}</pre>
			{/if}
		</section>
	</div>

	<section class="pane kernel">
		<header>
			kernel <code>Term</code>
			<span class="tag quiet">carved sexpr — realized by the HOL backend, in the kernel</span>
		</header>
		{#if k.error}
			<pre class="err">failed to load wasm: {k.error}</pre>
		{:else if !out}
			<pre class="termout muted">…</pre>
		{:else if out.term.ok}
			<pre class="termout">{out.term.term}</pre>
		{:else}
			<pre class="err">{out.term.error}</pre>
		{/if}
	</section>

	<section class="pane kernel">
		<header>
			typed HOL <code>Term</code>
			<span class="tag quiet">well-typed — via the Hol/Nat traits (needs annotations)</span>
		</header>
		{#if k.error}
			<pre class="err">failed to load wasm: {k.error}</pre>
		{:else if !out}
			<pre class="termout muted">…</pre>
		{:else if out.typed.ok}
			<pre class="termout">{out.typed.term}<span class="ty">  :: {out.typed.type}</span></pre>
		{:else}
			<pre class="err">{out.typed.error}</pre>
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
	/* Page-specific layout only — the shell, pipeline, pane and example-picker
	   chrome come from `$lib/kernelPages.css`. */
	.panes {
		display: grid;
		grid-template-columns: 1fr auto 1fr;
		gap: 0.75rem;
		align-items: stretch;
	}
	.pane .sexpr {
		color: color-mix(in srgb, var(--accent) 55%, var(--fg));
	}
	.pane.kernel {
		margin-top: 0.75rem;
	}
	.pane .termout {
		color: color-mix(in srgb, var(--ok) 60%, var(--fg));
		font-size: 0.8rem;
	}
	.pane .termout.muted {
		color: var(--muted);
	}
	.pane .termout .ty {
		color: var(--accent);
	}
	.mid {
		display: flex;
		align-items: center;
		color: var(--accent);
		font-size: 1.1rem;
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
